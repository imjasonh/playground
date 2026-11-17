// What both backends need beyond the tree-sitter API: pasta_parse, a parse
// with a time budget, and ts_dump_tree (adapted from dvcdsys/code-index
// tswasm), which writes the whole tree as a flat pre-order []NodeRec so the
// wasm host reads it with one Memory.Read.
#include "tree_sitter/api.h"
#include <stdbool.h>
#include <stdint.h>
#include <time.h>

typedef struct {
  const char *src;
  uint32_t len;
} pasta_string;

static const char *pasta_read(void *payload, uint32_t byte, TSPoint point, uint32_t *n) {
  pasta_string *s = payload;
  if (byte >= s->len) {
    *n = 0;
    return "";
  }
  *n = s->len - byte;
  return s->src + byte;
}

static uint64_t pasta_now_nanos(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

typedef struct {
  uint64_t deadline_nanos; // 0 means none
  const int32_t *cancel;
} pasta_budget;

static bool pasta_progress(TSParseState *state) {
  pasta_budget *b = state->payload;
  if (b->cancel != NULL && __atomic_load_n(b->cancel, __ATOMIC_RELAXED)) return true;
  return b->deadline_nanos != 0 && pasta_now_nanos() > b->deadline_nanos;
}

// pasta_parse returns NULL when timeout_micros elapses or *cancel becomes
// nonzero. The tree doesn't reference src after it returns.
TSTree *pasta_parse(TSParser *p, const char *src, uint32_t len, uint64_t timeout_micros, const int32_t *cancel) {
  pasta_string s = {src, len};
  TSInput in = {&s, pasta_read, TSInputEncodingUTF8, NULL};
  pasta_budget b = {0, cancel};
  TSParseOptions opts = {0};
  if (timeout_micros > 0) b.deadline_nanos = pasta_now_nanos() + timeout_micros * 1000u;
  if (timeout_micros > 0 || cancel != NULL) {
    opts.payload = &b;
    opts.progress_callback = pasta_progress;
  }
  return ts_parser_parse_with_options(p, NULL, in, opts);
}

// 10 × uint32 = 40 bytes. field_id is the field of this node on its parent
// (0 = none). flags: bit0 named, bit1 error, bit2 missing, bit3 extra,
// bit4 has_error (self or descendant).
typedef struct {
  uint32_t kind_id;
  uint32_t start_byte;
  uint32_t end_byte;
  uint32_t start_row;
  uint32_t start_col;
  uint32_t end_row;
  uint32_t end_col;
  uint32_t depth;
  uint32_t field_id;
  uint32_t flags;
} NodeRec;

static void emit(NodeRec *out, uint32_t i, TSNode n, uint32_t depth, TSFieldId field_id) {
  out[i].kind_id = ts_node_symbol(n);
  out[i].start_byte = ts_node_start_byte(n);
  out[i].end_byte = ts_node_end_byte(n);
  TSPoint sp = ts_node_start_point(n);
  out[i].start_row = sp.row;
  out[i].start_col = sp.column;
  TSPoint ep = ts_node_end_point(n);
  out[i].end_row = ep.row;
  out[i].end_col = ep.column;
  out[i].depth = depth;
  out[i].field_id = (uint32_t)field_id;
  uint32_t f = 0;
  if (ts_node_is_named(n)) f |= 1u;
  if (ts_node_is_error(n)) f |= 2u;
  if (ts_node_is_missing(n)) f |= 4u;
  if (ts_node_is_extra(n)) f |= 8u;
  if (ts_node_has_error(n)) f |= 16u;
  out[i].flags = f;
}

uint32_t ts_dump_tree(const TSTree *tree, NodeRec *out, uint32_t cap) {
  if (tree == 0) return 0;
  TSTreeCursor cur = ts_tree_cursor_new(ts_tree_root_node(tree));
  uint32_t count = 0;
  uint32_t depth = 0;
  for (;;) {
    if (count < cap) {
      emit(out, count, ts_tree_cursor_current_node(&cur), depth,
           ts_tree_cursor_current_field_id(&cur));
    }
    count++;
    if (ts_tree_cursor_goto_first_child(&cur)) { depth++; continue; }
    for (;;) {
      if (ts_tree_cursor_goto_next_sibling(&cur)) break;
      if (!ts_tree_cursor_goto_parent(&cur)) {
        ts_tree_cursor_delete(&cur);
        return count;
      }
      depth--;
    }
  }
}

uint32_t ts_dump_rec_size(void) { return (uint32_t)sizeof(NodeRec); }
