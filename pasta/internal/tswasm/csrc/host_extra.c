// host_extra.c — batched tree dump for wazero host (adapted from
// dvcdsys/code-index tswasm). Walks the whole tree inside the guest and
// writes a flat pre-order []NodeRec so the host does one Memory.Read.
#include "tree_sitter/api.h"
#include <stdint.h>

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
