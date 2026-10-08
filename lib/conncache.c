/***************************************************************************
 *                                  _   _ ____  _
 *  Project                     ___| | | |  _ \| |
 *                             / __| | | | |_) | |
 *                            | (__| |_| |  _ <| |___
 *                             \___|\___/|_| \_\_____|
 *
 * Copyright (C) Linus Nielsen Feltzing, <linus@haxx.se>
 * Copyright (C) Daniel Stenberg, <daniel@haxx.se>, et al.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution. The terms
 * are also available at https://curl.se/docs/copyright.html.
 *
 * You may opt to use, copy, modify, merge, publish, distribute and/or sell
 * copies of the Software, and permit persons to whom the Software is
 * furnished to do so, under the terms of the COPYING file.
 *
 * This software is distributed on an "AS IS" basis, WITHOUT WARRANTY OF ANY
 * KIND, either express or implied.
 *
 * SPDX-License-Identifier: curl
 *
 ***************************************************************************/
#include "curl_setup.h"

#include "urldata.h"
#include "url.h"
#include "cfilters.h"
#include "progress.h"
#include "multiif.h"
#include "curl_trc.h"
#include "cshutdn.h"
#include "conncache.h"
#include "curl_share.h"
#include "sigpipe.h"
#include "connect.h"
#include "select.h"
#include "curlx/strparse.h"


#define CPOOL_IS_LOCKED(c)    ((c) && (c)->locked)

#define CPOOL_LOCK(c, d)                                                \
  do {                                                                  \
    if(c) {                                                             \
      if(CURL_SHARE_KEEP_CONNECT((c)->share))                           \
        Curl_share_lock_share((c)->share, (d), CURL_LOCK_DATA_CONNECT,  \
                        CURL_LOCK_ACCESS_SINGLE);                       \
      DEBUGASSERT(!(c)->locked);                                        \
      (c)->locked = TRUE;                                               \
    }                                                                   \
  } while(0)

#define CPOOL_UNLOCK(c,d)                                               \
  do {                                                                  \
    if(c) {                                                             \
      DEBUGASSERT((c)->locked);                                         \
      (c)->locked = FALSE;                                              \
      if(CURL_SHARE_KEEP_CONNECT((c)->share))                           \
        Curl_share_unlock_share((c)->share, (d), CURL_LOCK_DATA_CONNECT); \
    }                                                                   \
  } while(0)

/* A list of connections to the same destination. */
struct cpool_bundle {
  struct Curl_llist conns; /* connections in the bundle */
  size_t dest_len; /* total length of destination, including NUL */
  char dest[1]; /* destination of bundle, allocated to keep dest_len bytes */
};

static void cpool_discard_conn(struct cpool *cpool,
                               struct Curl_easy *data,
                               struct connectdata *conn,
                               bool aborted);

static void cpool_conn_close(struct cpool *cpool,
                             struct Curl_easy *data,
                             struct connectdata *conn,
                             bool aborted);

static void cpool_evict_conn(struct cpool *cpool,
                             struct Curl_easy *admin,
                             struct connectdata *conn);

static struct cpool_bundle *cpool_bundle_create(const char *dest)
{
  struct cpool_bundle *bundle;
  size_t dest_len = strlen(dest) + 1;

  bundle = curlx_calloc(1, sizeof(*bundle) + dest_len - 1);
  if(!bundle)
    return NULL;
  Curl_llist_init(&bundle->conns, NULL);
  bundle->dest_len = dest_len;
  memcpy(bundle->dest, dest, bundle->dest_len);
  return bundle;
}

static void cpool_bundle_destroy(struct cpool_bundle *bundle)
{
  DEBUGASSERT(!Curl_llist_count(&bundle->conns));
  curlx_free(bundle);
}

/* Add a connection to a bundle */
static void cpool_bundle_add(struct cpool_bundle *bundle,
                             struct connectdata *conn)
{
  DEBUGASSERT(!Curl_node_llist(&conn->cpool_node));
  Curl_llist_append(&bundle->conns, conn, &conn->cpool_node);
  conn->bits.in_cpool = TRUE;
}

/* Remove a connection from a bundle */
static void cpool_bundle_remove(struct cpool_bundle *bundle,
                                struct connectdata *conn)
{
  (void)bundle;
  DEBUGASSERT(Curl_node_llist(&conn->cpool_node) == &bundle->conns);
  Curl_node_remove(&conn->cpool_node);
  conn->bits.in_cpool = FALSE;
}

static void cpool_bundle_free_entry(void *freethis)
{
  cpool_bundle_destroy((struct cpool_bundle *)freethis);
}

void Curl_cpool_init(struct cpool *cpool,
                     struct Curl_share *share,
                     size_t size)
{
  Curl_hash_init(&cpool->dest2bundle, size, Curl_hash_str,
                 curlx_str_key_compare, cpool_bundle_free_entry);

  cpool->share = share;
  cpool->initialised = TRUE;
}

/* Return the "first" connection in the pool or NULL. */
static struct connectdata *cpool_get_first(struct cpool *cpool)
{
  struct Curl_hash_iterator iter;
  struct Curl_hash_element *he;
  struct cpool_bundle *bundle;
  struct Curl_llist_node *conn_node;

  Curl_hash_start_iterate(&cpool->dest2bundle, &iter);
  for(he = Curl_hash_next_element(&iter); he;
      he = Curl_hash_next_element(&iter)) {
    bundle = he->ptr;
    conn_node = Curl_llist_head(&bundle->conns);
    if(conn_node)
      return Curl_node_elem(conn_node);
  }
  return NULL;
}

static struct cpool_bundle *cpool_find_bundle(struct cpool *cpool,
                                              struct connectdata *conn)
{
  return Curl_hash_pick(&cpool->dest2bundle,
                        conn->destination, strlen(conn->destination) + 1);
}

static void cpool_remove_bundle(struct cpool *cpool,
                                struct cpool_bundle *bundle)
{
  if(!cpool)
    return;
  Curl_hash_delete(&cpool->dest2bundle, bundle->dest, bundle->dest_len);
}

static void cpool_remove_conn(struct cpool *cpool,
                              struct connectdata *conn)
{
  struct Curl_llist *list = Curl_node_llist(&conn->cpool_node);
  DEBUGASSERT(cpool);
  if(list) {
    /* The connection is certainly in the pool, but where? */
    struct cpool_bundle *bundle = cpool_find_bundle(cpool, conn);
    if(bundle && (list == &bundle->conns)) {
      cpool_bundle_remove(bundle, conn);
      if(!Curl_llist_count(&bundle->conns))
        cpool_remove_bundle(cpool, bundle);
      conn->bits.in_cpool = FALSE;
      cpool->num_conn--;
    }
    else {
      /* Should have been in the bundle list */
      DEBUGASSERT(NULL);
    }
  }
}

void Curl_cpool_destroy(struct cpool *cpool, struct Curl_easy *admin)
{
  if(cpool && cpool->initialised && admin) {
    struct connectdata *conn;
    SIGPIPE_VARIABLE(pipe_st);

    CURL_TRC_M(admin, "%s[CPOOL] destroy, %zu connections",
               cpool->share ? "[SHARE] " : "", cpool->num_conn);
    /* Move all connections to the shutdown list */
    sigpipe_init(&pipe_st);
    CPOOL_LOCK(cpool, admin);
    conn = cpool_get_first(cpool);
    while(conn) {
      cpool_remove_conn(cpool, conn);
      sigpipe_apply(admin, &pipe_st);
      cpool_discard_conn(cpool, admin, conn, FALSE);
      conn = cpool_get_first(cpool);
    }
    CPOOL_UNLOCK(cpool, admin);
    sigpipe_restore(&pipe_st);
    Curl_hash_destroy(&cpool->dest2bundle);
  }
}

static struct cpool *cpool_get_instance(struct Curl_easy *data)
{
  if(data) {
    if(CURL_SHARE_KEEP_CONNECT(data->share))
      return &data->share->cpool;
    else if(data->multi_easy)
      return &data->multi_easy->cpool;
    else if(data->multi)
      return &data->multi->cpool;
  }
  return NULL;
}

struct cpool *Curl_cpool_get_instance(struct Curl_easy *data)
{
  return cpool_get_instance(data);
}

void Curl_cpool_xfer_init(struct Curl_easy *data)
{
  struct cpool *cpool = cpool_get_instance(data);

  DEBUGASSERT(cpool);
  if(cpool) {
    CPOOL_LOCK(cpool, data);
    /* the identifier inside the connection cache */
    data->id = cpool->next_easy_id++;
    if(cpool->next_easy_id <= 0)
      cpool->next_easy_id = 0;
    data->state.lastconnect_id = -1;

    CPOOL_UNLOCK(cpool, data);
  }
  else {
    /* We should not get here, but in a non-debug build, do something */
    data->id = 0;
    data->state.lastconnect_id = -1;
  }
}

static struct cpool_bundle *cpool_add_bundle(struct cpool *cpool,
                                             struct connectdata *conn)
{
  struct cpool_bundle *bundle;

  bundle = cpool_bundle_create(conn->destination);
  if(!bundle)
    return NULL;

  if(!Curl_hash_add(&cpool->dest2bundle,
                    bundle->dest, bundle->dest_len, bundle)) {
    cpool_bundle_destroy(bundle);
    return NULL;
  }
  return bundle;
}

static struct connectdata *
cpool_bundle_get_oldest_idle(struct cpool_bundle *bundle,
                             const struct curltime *pnow)
{
  struct Curl_llist_node *curr;
  timediff_t highscore = -1;
  timediff_t score;
  struct connectdata *oldest_idle = NULL;
  struct connectdata *conn;

  curr = Curl_llist_head(&bundle->conns);
  while(curr) {
    conn = Curl_node_elem(curr);

    if(!CONN_INUSE(conn)) {
      /* Set higher score for the age passed since the connection was used */
      score = curlx_ptimediff_ms(pnow, &conn->lastused);

      if(score > highscore) {
        highscore = score;
        oldest_idle = conn;
      }
    }
    curr = Curl_node_next(curr);
  }
  return oldest_idle;
}

static struct connectdata *cpool_get_oldest_idle(struct cpool *cpool,
                                                 const struct curltime *pnow)
{
  struct Curl_hash_iterator iter;
  struct Curl_llist_node *curr;
  struct Curl_hash_element *he;
  struct connectdata *oldest_idle = NULL;
  struct cpool_bundle *bundle;
  timediff_t highscore = -1;
  timediff_t score;

  Curl_hash_start_iterate(&cpool->dest2bundle, &iter);

  for(he = Curl_hash_next_element(&iter); he;
      he = Curl_hash_next_element(&iter)) {
    struct connectdata *conn;
    bundle = he->ptr;

    for(curr = Curl_llist_head(&bundle->conns); curr;
        curr = Curl_node_next(curr)) {
      conn = Curl_node_elem(curr);
      if(CONN_INUSE(conn) || conn->bits.close || conn->connect_only)
        continue;
      /* Set higher score for the age passed since the connection was used */
      score = curlx_ptimediff_ms(pnow, &conn->lastused);
      if(score > highscore) {
        highscore = score;
        oldest_idle = conn;
      }
    }
  }
  return oldest_idle;
}

/* Evict an idle connection to make room in the pool. A pool owned by
 * a share has no multi that could perform a controlled shutdown of the
 * connection; terminate it right away. Otherwise, hand it to the
 * transfer's multi for shutdown. Expects the pool to be locked. */
static void cpool_evict_conn(struct cpool *cpool,
                             struct Curl_easy *admin,
                             struct connectdata *conn)
{
  if(cpool->share) {
    cpool_remove_conn(cpool, conn);
    Curl_cshutdn_terminate(admin, conn, TRUE);
  }
  else
    cpool_conn_close(cpool, admin, conn, FALSE);
}

int Curl_cpool_check_limits(struct Curl_easy *data,
                            struct connectdata *conn)
{
  struct cpool *cpool = cpool_get_instance(data);
  struct cshutdn *cshutdn = Curl_cshutdn_get(data);
  struct Curl_easy *admin;
  struct cpool_bundle *bundle;
  size_t dest_limit = 0;
  size_t total_limit = 0;
  size_t shutdowns;
  int result = CPOOL_LIMIT_OK;

  if(!cpool)
    return CPOOL_LIMIT_OK;

  if(data->multi) {
    dest_limit = data->multi->max_host_connections;
    total_limit = data->multi->max_total_connections;
  }

  if(!dest_limit && !total_limit)
    return CPOOL_LIMIT_OK;

  admin = Curl_get_admin(data);
  CPOOL_LOCK(cpool, admin);
  if(dest_limit) {
    size_t live;

    bundle = cpool_find_bundle(cpool, conn);
    live = bundle ? Curl_llist_count(&bundle->conns) : 0;
    shutdowns = Curl_cshutdn_dest_count(cshutdn, conn->destination);
    while((live + shutdowns) >= dest_limit) {
      if(shutdowns) {
        /* close one connection in shutdown right away, if we can */
        if(!Curl_cshutdn_close_oldest(cshutdn, conn->destination))
          break;
      }
      else if(!bundle)
        break;
      else {
        struct connectdata *oldest_idle = NULL;
        /* The bundle is full. Extract the oldest connection that may
         * be removed now, if there is one. */
        oldest_idle = cpool_bundle_get_oldest_idle(bundle,
                                                   Curl_pgrs_now(data));
        if(!oldest_idle)
          break;
        /* disconnect the old conn and continue */
        CURL_TRC_M(admin, "Discarding connection #%" FMT_OFF_T
                   " from %zu to reach destination limit of %zu",
                   oldest_idle->connection_id,
                   Curl_llist_count(&bundle->conns), dest_limit);
        cpool_evict_conn(cpool, admin, oldest_idle);

        /* in case the bundle was destroyed in disconnect, look it up again */
        bundle = cpool_find_bundle(cpool, conn);
        live = bundle ? Curl_llist_count(&bundle->conns) : 0;
      }
      shutdowns = Curl_cshutdn_dest_count(cshutdn, conn->destination);
    }
    if((live + shutdowns) >= dest_limit) {
      result = CPOOL_LIMIT_DEST;
      goto out;
    }
  }

  if(total_limit) {
    shutdowns = Curl_cshutdn_count(cshutdn);
    while((cpool->num_conn + shutdowns) >= total_limit) {
      if(shutdowns) {
        /* close one connection in shutdown right away, if we can */
        if(!Curl_cshutdn_close_oldest(cshutdn, NULL))
          break;
      }
      else {
        struct connectdata *oldest_idle =
          cpool_get_oldest_idle(cpool, Curl_pgrs_now(data));
        if(!oldest_idle)
          break;
        /* disconnect the old conn and continue */
        CURL_TRC_M(admin, "Discarding connection #%"
                   FMT_OFF_T " from %zu to reach total "
                   "limit of %zu",
                   oldest_idle->connection_id, cpool->num_conn, total_limit);
        cpool_evict_conn(cpool, admin, oldest_idle);
      }
      shutdowns = Curl_cshutdn_count(cshutdn);
    }
    if((cpool->num_conn + shutdowns) >= total_limit) {
      result = CPOOL_LIMIT_TOTAL;
      goto out;
    }
  }

out:
  CPOOL_UNLOCK(cpool, admin);
  return result;
}

CURLcode Curl_cpool_add(struct Curl_easy *data,
                        struct connectdata *conn)
{
  CURLcode result = CURLE_OK;
  struct cpool_bundle *bundle = NULL;
  struct cpool *cpool = cpool_get_instance(data);
  DEBUGASSERT(conn);

  DEBUGASSERT(cpool);
  if(!cpool)
    return CURLE_FAILED_INIT;

  CPOOL_LOCK(cpool, data);
  bundle = cpool_find_bundle(cpool, conn);
  if(!bundle) {
    bundle = cpool_add_bundle(cpool, conn);
    if(!bundle) {
      result = CURLE_OUT_OF_MEMORY;
      goto out;
    }
  }

  cpool_bundle_add(bundle, conn);
  conn->connection_id = cpool->next_connection_id++;
  cpool->num_conn++;
  CURL_TRC_M(data, "[CPOOL] added connection %" FMT_OFF_T ". "
             "The cache now contains %zu members",
             conn->connection_id, cpool->num_conn);
out:
  CPOOL_UNLOCK(cpool, data);

  return result;
}

/* This function iterates the entire connection pool and calls the function
   func() with the connection pointer as the first argument and the supplied
   'param' argument as the other.

   The cpool lock is still held when the callback is called. It needs it,
   so that it can safely continue traversing the lists once the callback
   returns.

   Returns TRUE if the loop was aborted due to the callback's return code.

   Return 0 from func() to continue the loop, return 1 to abort it.
 */
static bool cpool_foreach(struct Curl_easy *data,
                          struct cpool *cpool,
                          void *param,
                          int (*func)(struct cpool *cpool,
                                      struct Curl_easy *data,
                                      struct connectdata *conn, void *param))
{
  struct Curl_hash_iterator iter;
  struct Curl_hash_element *he;

  if(!cpool)
    return FALSE;

  Curl_hash_start_iterate(&cpool->dest2bundle, &iter);

  he = Curl_hash_next_element(&iter);
  while(he) {
    struct Curl_llist_node *curr;
    struct cpool_bundle *bundle = he->ptr;
    he = Curl_hash_next_element(&iter);

    curr = Curl_llist_head(&bundle->conns);
    while(curr) {
      /* Yes, we need to update curr before calling func(), because func()
         might decide to remove the connection */
      struct connectdata *conn = Curl_node_elem(curr);
      curr = Curl_node_next(curr);

      if(func(cpool, data, conn, param) == 1) {
        return TRUE;
      }
    }
  }
  return FALSE;
}

/*
 * A connection (already in the pool) has become idle. Do any
 * cleanups in regard to the pool's limits.
 *
 * Return TRUE if idle connection kept in pool, FALSE if closed.
 */
bool Curl_cpool_conn_now_idle(struct Curl_easy *data,
                              struct connectdata *conn)
{
  unsigned int maxconnects;
  struct connectdata *oldest_idle = NULL;
  struct cpool *cpool = cpool_get_instance(data);
  bool kept = TRUE;

  if(!data)
    return kept;

  if(!data->multi->maxconnects) {
    unsigned int running = Curl_multi_xfers_running(data->multi);
    maxconnects = (running <= UINT_MAX / 4) ? running * 4 : UINT_MAX;
  }
  else {
    maxconnects = data->multi->maxconnects;
  }

  conn->lastused = *Curl_pgrs_now(data); /* it was used up until now */
  if(cpool && maxconnects) {
    /* may be called form a callback already under lock */
    bool do_lock = !CPOOL_IS_LOCKED(cpool);
    struct Curl_easy *admin;

    admin = Curl_get_admin(data);
    if(do_lock)
      CPOOL_LOCK(cpool, admin);
    if(cpool->num_conn > maxconnects) {
      infof(data, "Connection pool is full, closing the oldest of %zu/%u",
            cpool->num_conn, maxconnects);

      oldest_idle = cpool_get_oldest_idle(cpool, Curl_pgrs_now(data));
      kept = (oldest_idle != conn);
      if(oldest_idle) {
        cpool_evict_conn(cpool, admin, oldest_idle);
      }
    }
    if(do_lock)
      CPOOL_UNLOCK(cpool, admin);
  }

  return kept;
}

bool Curl_cpool_find(struct Curl_easy *data,
                     const char *destination,
                     Curl_cpool_conn_match_cb *conn_cb,
                     Curl_cpool_done_match_cb *done_cb,
                     void *userdata)
{
  struct cpool *cpool = cpool_get_instance(data);
  struct cpool_bundle *bundle;
  bool result = FALSE;

  DEBUGASSERT(cpool);
  DEBUGASSERT(conn_cb);
  if(!cpool)
    return FALSE;

  CPOOL_LOCK(cpool, data);
  bundle = Curl_hash_pick(&cpool->dest2bundle,
                          CURL_UNCONST(destination),
                          strlen(destination) + 1);
  if(bundle) {
    struct Curl_llist_node *curr = Curl_llist_head(&bundle->conns);
    while(curr) {
      struct connectdata *conn = Curl_node_elem(curr);
      /* Get next node now. callback might discard current */
      curr = Curl_node_next(curr);

      if(conn_cb(conn, userdata)) {
        result = TRUE;
        break;
      }
    }
  }

  if(done_cb) {
    result = done_cb(result, userdata);
  }
  CPOOL_UNLOCK(cpool, data);
  return result;
}

static void cpool_discard_conn(struct cpool *cpool,
                               struct Curl_easy *data,
                               struct connectdata *conn,
                               bool aborted)
{
  struct cshutdn *cshutdn;
  struct Curl_easy *admin;
  bool done = FALSE;

  DEBUGASSERT(data);
  DEBUGASSERT(!data->conn);
  DEBUGASSERT(cpool);
  DEBUGASSERT(!conn->bits.in_cpool);

  admin = Curl_get_admin(data);
  /*
   * If this connection is not marked to force-close, leave it open if there
   * are other users of it
   */
  if(CONN_INUSE(conn) && !aborted) {
    CURL_TRC_M(admin, "[CPOOL] not discarding #%" FMT_OFF_T
               " still in use by %u transfers", conn->connection_id,
               conn->attached_xfers);
    return;
  }

  /* treat the connection as aborted in CONNECT_ONLY situations, we do
   * not know what the APP did with it. */
  if(conn->connect_only)
    aborted = TRUE;
  conn->bits.aborted = aborted;

  /* We do not shutdown dead connections. The term 'dead' can be misleading
   * here, as we also mark errored connections/transfers as 'dead'.
   * If we do a shutdown for an aborted transfer, the server might think
   * it was successful otherwise (for example an ftps: upload). This is
   * not what we want. */
  if(aborted)
    done = TRUE;
  if(!done) {
    /* Attempt to shutdown the connection right away. */
    Curl_conn_shutdown_once(admin, conn, &done);
  }

  cshutdn = Curl_cshutdn_get(data);
  if(done || !cshutdn)
    Curl_cshutdn_terminate(admin, conn, FALSE);
  else
    Curl_cshutdn_add(cshutdn, conn, cpool->num_conn);
}

static void cpool_conn_close(struct cpool *cpool,
                             struct Curl_easy *data,
                             struct connectdata *conn,
                             bool aborted)
{
  struct Curl_easy *admin;
  bool do_lock;

  DEBUGASSERT(cpool);
  DEBUGASSERT(data && !data->conn);
  if(!cpool)
    return;

  /* If this connection is not marked to force-close, leave it open if there
   * are other users of it */
  if(CONN_INUSE(conn) && !aborted) {
    DEBUGASSERT(0); /* does this ever happen? */
    DEBUGF(infof(data, "conn terminate when inuse: %u", conn->attached_xfers));
    return;
  }

  /* This method may be called while we are under lock, e.g. from a
   * user callback in find. */
  admin = Curl_get_admin(data);
  do_lock = !CPOOL_IS_LOCKED(cpool);
  if(do_lock)
    CPOOL_LOCK(cpool, admin);

  if(conn->bits.in_cpool) {
    cpool_remove_conn(cpool, conn);
    DEBUGASSERT(!conn->bits.in_cpool);
  }

  /* treat the connection as aborted in CONNECT_ONLY situations,
   * so no graceful shutdown is attempted. */
  if(conn->connect_only)
    aborted = TRUE;

  if(data->multi) {
    /* Add it to the multi's cpool for shutdown handling */
    infof(data, "%s connection #%" FMT_OFF_T,
          aborted ? "closing" : "shutting down", conn->connection_id);
    cpool_discard_conn(&data->multi->cpool, data, conn, aborted);
  }
  else {
    /* No multi available, terminate */
    infof(data, "closing connection #%" FMT_OFF_T, conn->connection_id);
    Curl_cshutdn_terminate(admin, conn, !aborted);
  }

  if(do_lock)
    CPOOL_UNLOCK(cpool, admin);
}

void Curl_conn_terminate(struct Curl_easy *data,
                     struct connectdata *conn,
                     bool aborted)
{
  struct cpool *cpool = cpool_get_instance(data);
  cpool_conn_close(cpool, data, conn, aborted);
}

struct cpool_reaper_ctx {
  size_t checked;
  size_t reaped;
};

static int cpool_reap_dead_cb(struct cpool *cpool,
                              struct Curl_easy *admin,
                              struct connectdata *conn, void *param)
{
  struct cpool_reaper_ctx *reaper = param;
  bool terminate = !CONN_INUSE(conn) && conn->bits.no_reuse;

  if(!terminate) {
    reaper->checked++;
    terminate = Curl_conn_seems_dead(conn, admin);
  }
  if(terminate) {
    /* stop the iteration here, pass back the connection that was pruned */
    reaper->reaped++;
    cpool_conn_close(cpool, admin, conn, FALSE);
    return 1;
  }
  return 0; /* continue iteration */
}

/*
 * This function scans the data's connection pool for half-open/dead
 * connections, closes and removes them.
 * The cleanup is done at most once per second.
 *
 * When called, this transfer has no connection attached.
 */
void Curl_cpool_prune_dead(struct cpool *cpool,
                           struct Curl_easy *data)
{
  struct Curl_easy *admin;
  struct cpool_reaper_ctx reaper;
  timediff_t elapsed;

  if(!cpool)
    return;

  admin = Curl_get_admin(data);
  memset(&reaper, 0, sizeof(reaper));
  CPOOL_LOCK(cpool, admin);
  elapsed = curlx_ptimediff_ms(Curl_pgrs_now(data), &cpool->last_cleanup);

  if(elapsed >= 1000L) {
    while(cpool_foreach(admin, cpool, &reaper, cpool_reap_dead_cb))
      ;
    cpool->last_cleanup = *Curl_pgrs_now(data);
  }
  CPOOL_UNLOCK(cpool, admin);
}

static int conn_upkeep(struct cpool *cpool,
                       struct Curl_easy *data,
                       struct connectdata *conn,
                       void *param)
{
  (void)cpool;
  (void)param;
  Curl_conn_upkeep(data, conn);
  return 0; /* continue iteration */
}

CURLcode Curl_cpool_upkeep(struct Curl_easy *data)
{
  struct cpool *cpool = cpool_get_instance(data);

  if(!cpool)
    return CURLE_OK;

  CPOOL_LOCK(cpool, data);
  cpool_foreach(data, cpool, NULL, conn_upkeep);
  CPOOL_UNLOCK(cpool, data);
  return CURLE_OK;
}

struct cpool_find_ctx {
  curl_off_t id;
  struct connectdata *conn;
};

static int cpool_find_conn(struct cpool *cpool,
                           struct Curl_easy *data,
                           struct connectdata *conn, void *param)
{
  struct cpool_find_ctx *fctx = param;
  (void)cpool;
  (void)data;
  if(conn->connection_id == fctx->id) {
    fctx->conn = conn;
    return 1;
  }
  return 0;
}

struct connectdata *Curl_cpool_get_conn(struct Curl_easy *data,
                                        curl_off_t conn_id)
{
  struct cpool *cpool = cpool_get_instance(data);
  struct cpool_find_ctx fctx;

  if(!cpool)
    return NULL;
  fctx.id = conn_id;
  fctx.conn = NULL;
  CPOOL_LOCK(cpool, data);
  cpool_foreach(data, cpool, &fctx, cpool_find_conn);
  CPOOL_UNLOCK(cpool, data);
  return fctx.conn;
}

struct cpool_do_conn_ctx {
  curl_off_t id;
  Curl_cpool_conn_do_cb *cb;
  void *cbdata;
};

static int cpool_do_conn(struct cpool *cpool,
                         struct Curl_easy *data,
                         struct connectdata *conn, void *param)
{
  struct cpool_do_conn_ctx *dctx = param;
  (void)cpool;
  (void)data;
  if(conn->connection_id == dctx->id) {
    dctx->cb(conn, data, dctx->cbdata);
    return 1;
  }
  return 0;
}

void Curl_cpool_do_by_id(struct Curl_easy *data, curl_off_t conn_id,
                         Curl_cpool_conn_do_cb *cb, void *cbdata)
{
  struct cpool *cpool = cpool_get_instance(data);
  struct cpool_do_conn_ctx dctx;

  if(!cpool)
    return;
  dctx.id = conn_id;
  dctx.cb = cb;
  dctx.cbdata = cbdata;
  CPOOL_LOCK(cpool, data);
  cpool_foreach(data, cpool, &dctx, cpool_do_conn);
  CPOOL_UNLOCK(cpool, data);
}

void Curl_cpool_do_locked(struct Curl_easy *data,
                          struct connectdata *conn,
                          Curl_cpool_conn_do_cb *cb, void *cbdata)
{
  struct cpool *cpool = cpool_get_instance(data);
  if(cpool) {
    CPOOL_LOCK(cpool, data);
    cb(conn, data, cbdata);
    CPOOL_UNLOCK(cpool, data);
  }
  else
    cb(conn, data, cbdata);
}

static int cpool_mark_stale(struct cpool *cpool,
                            struct Curl_easy *data,
                            struct connectdata *conn, void *param)
{
  (void)cpool;
  (void)data;
  (void)param;
  conn->bits.no_reuse = TRUE;
  return 0;
}

static int cpool_reap_no_reuse(struct cpool *cpool,
                               struct Curl_easy *admin,
                               struct connectdata *conn, void *param)
{
  (void)param;
  if(!CONN_INUSE(conn) && conn->bits.no_reuse) {
    cpool_conn_close(cpool, admin, conn, FALSE);
    return 1;
  }
  return 0; /* continue iteration */
}

void Curl_cpool_nw_changed(struct cpool *cpool, struct Curl_easy *admin)
{
  if(cpool) {
    CPOOL_LOCK(cpool, admin);
    cpool_foreach(admin, cpool, NULL, cpool_mark_stale);
    while(cpool_foreach(admin, cpool, NULL, cpool_reap_no_reuse))
      ;
    CPOOL_UNLOCK(cpool, admin);
  }
}

#if 0
/* Useful for debugging the connection pool */
void Curl_cpool_print(struct cpool *cpool)
{
  struct Curl_hash_iterator iter;
  struct Curl_llist_node *curr;
  struct Curl_hash_element *he;

  if(!cpool)
    return;

  curl_mfprintf(stderr, "=Bundle cache=\n");

  Curl_hash_start_iterate(cpool->dest2bundle, &iter);

  he = Curl_hash_next_element(&iter);
  while(he) {
    struct cpool_bundle *bundle;
    struct connectdata *conn;

    bundle = he->ptr;

    curl_mfprintf(stderr, "%s -", he->key);
    curr = Curl_llist_head(bundle->conns);
    while(curr) {
      conn = Curl_node_elem(curr);

      curl_mfprintf(stderr, " [%p %d]", (void *)conn, conn->refcount);
      curr = Curl_node_next(curr);
    }
    curl_mfprintf(stderr, "\n");

    he = Curl_hash_next_element(&iter);
  }
}
#endif
