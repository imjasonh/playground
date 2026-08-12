// Package tsutil wraps the tree-sitter Node abstraction with source
// bytes + language + file-id. The parse backend is the official C
// tree-sitter runtime compiled to WASM and driven via wazero
// (internal/tswasm) — pure Go, CGO_ENABLED=0, go install friendly.
package tsutil

import (
	"context"
	"errors"
	"fmt"
	"time"

	"github.com/imjasonh/pasta/internal/tswasm"
)

// Node is a thin wrapper around a tree-sitter node that carries the
// source bytes and language so the rest of pasta can call methods like
// Type() / ChildByFieldName() without threading the language through
// every call site.
//
// FileID identifies the source file the node belongs to. It's the
// disambiguator used by the fact store when several files share a
// single store (multi-file analysis groups). Single-file callers can
// leave it empty.
type Node struct {
	N      *tswasm.Node
	Src    []byte
	Lang   *tswasm.Language
	FileID string
}

// IsValid reports whether the node is non-nil.
func (n Node) IsValid() bool { return n.N != nil && n.N.IsValid() }

// Type returns the tree-sitter node type.
func (n Node) Type() string {
	if n.N == nil {
		return ""
	}
	return n.N.Type()
}

// IsNamed reports whether the node is a named (non-anonymous) child.
func (n Node) IsNamed() bool {
	if n.N == nil {
		return false
	}
	return n.N.IsNamed()
}

// StartByte and EndByte return the node's byte range in the source.
func (n Node) StartByte() uint32 {
	if n.N == nil {
		return 0
	}
	return n.N.StartByte()
}
func (n Node) EndByte() uint32 {
	if n.N == nil {
		return 0
	}
	return n.N.EndByte()
}

// Range returns (start, end).
func (n Node) Range() (uint32, uint32) {
	return n.StartByte(), n.EndByte()
}

// Text returns the source text covered by the node.
func (n Node) Text() string {
	return string(n.Src[n.StartByte():n.EndByte()])
}

// NamedChildren returns the named children in order.
func (n Node) NamedChildren() []Node {
	kids := n.N.NamedChildren()
	out := make([]Node, len(kids))
	for i, c := range kids {
		out[i] = Node{N: c, Src: n.Src, Lang: n.Lang, FileID: n.FileID}
	}
	return out
}

// AllChildren returns every child including anonymous ones.
func (n Node) AllChildren() []Node {
	kids := n.N.Children()
	out := make([]Node, len(kids))
	for i, c := range kids {
		out[i] = Node{N: c, Src: n.Src, Lang: n.Lang, FileID: n.FileID}
	}
	return out
}

// ChildByFieldName returns the named child bound to fieldName, or an
// invalid Node if no such field exists.
func (n Node) ChildByFieldName(fieldName string) Node {
	c := n.N.ChildByFieldName(fieldName)
	if c == nil {
		return Node{Src: n.Src, Lang: n.Lang, FileID: n.FileID}
	}
	return Node{N: c, Src: n.Src, Lang: n.Lang, FileID: n.FileID}
}

// HasFieldName reports whether the node has any child with the given field
// name. Used to drive `absent_fields`.
func (n Node) HasFieldName(fieldName string) bool {
	return n.N.ChildByFieldName(fieldName) != nil
}

// FieldNameForChildIdx returns the field name for the i-th child (including
// anonymous), or "" if none.
func (n Node) FieldNameForChildIdx(i int) string {
	return n.N.FieldNameForChild(i)
}

// Parent returns the parent node, or an invalid Node if at the root.
func (n Node) Parent() Node {
	p := n.N.Parent()
	if p == nil {
		return Node{Src: n.Src, Lang: n.Lang, FileID: n.FileID}
	}
	return Node{N: p, Src: n.Src, Lang: n.Lang, FileID: n.FileID}
}

// HasError reports whether the subtree contains a parse error.
func (n Node) HasError() bool { return n.N != nil && n.N.HasError() }

// IsError reports whether this node is an ERROR node.
func (n Node) IsError() bool { return n.N != nil && n.N.IsError() }

// IsMissing reports whether this node was inserted as a missing token
// during error recovery.
func (n Node) IsMissing() bool { return n.N != nil && n.N.IsMissing() }

// ErrorHeavy reports whether the tree is too broken to analyze
// reliably. Tree-sitter often sets HasError (and even marks the root
// ERROR) for a trailing glitch; those stay analyzable. Heavy means
// ERROR/missing named nodes dominate (>50% of named nodes) or are
// numerous (≥8).
func ErrorHeavy(root Node) bool {
	if !root.IsValid() || !root.HasError() {
		return false
	}
	var named, bad int
	Walk(root, func(n Node) bool {
		named++
		if n.IsError() || n.IsMissing() {
			bad++
		}
		return true
	})
	if bad == 0 {
		return false
	}
	return bad*2 > named || bad >= 8
}

// String returns the s-expression representation of the subtree (for tests).
func (n Node) String() string {
	if n.N == nil {
		return ""
	}
	return n.N.SExpr()
}

// ErrParseTimeout is returned when a parse hits the configured per-file
// budget (or the context is cancelled mid-parse). Callers typically
// skip the file and report it as too complex to analyze.
var ErrParseTimeout = errors.New("parse timeout")

// ErrParseResourceLimit is returned when the WASM guest stops early due
// to a resource cap (memory budget trap, …). Like ErrParseTimeout,
// callers should skip the file rather than fail the whole run.
var ErrParseResourceLimit = errors.New("parse resource limit")

// ParseOptions controls per-parse resource limits.
type ParseOptions struct {
	// Timeout bounds wall time for a single parse. Zero means no
	// budget (tree-sitter default).
	Timeout time.Duration
}

// Tree is the parse result; caller must Release() when done.
type Tree = tswasm.Tree

// Language is a grammar handle for Parse.
type Language = tswasm.Language

// Parse parses src with the given language and returns the tree and
// root Node. The caller must call tree.Release() when done.
//
// fileID disambiguates nodes from this parse from those of other files
// in the same multi-file analysis group; pass "" for single-file usage.
func Parse(ctx context.Context, lang *Language, src []byte, fileID string) (*Tree, Node, error) {
	return ParseWithOptions(ctx, lang, src, fileID, ParseOptions{})
}

// ParseWithOptions is Parse plus an optional per-file timeout.
func ParseWithOptions(ctx context.Context, lang *Language, src []byte, fileID string, opts ParseOptions) (*Tree, Node, error) {
	if err := ctx.Err(); err != nil {
		return nil, Node{}, err
	}
	tree, err := tswasm.Parse(ctx, lang, src, fileID, tswasm.ParseOptions{Timeout: opts.Timeout})
	if err != nil {
		switch {
		case errors.Is(err, tswasm.ErrTimeout), errors.Is(err, context.Canceled), errors.Is(err, context.DeadlineExceeded):
			if ctx.Err() != nil {
				return nil, Node{}, ctx.Err()
			}
			return nil, Node{}, fmt.Errorf("%w: %v", ErrParseTimeout, err)
		case errors.Is(err, tswasm.ErrResourceLimit):
			return nil, Node{}, fmt.Errorf("%w: %v", ErrParseResourceLimit, err)
		default:
			return nil, Node{}, err
		}
	}
	rootN := tree.RootNode()
	root := Node{N: rootN, Src: src, Lang: lang, FileID: fileID}
	return tree, root, nil
}

// DrainArenaPools is retained for API parity; the WASM backend pools
// engines instead of gotreesitter arenas.
func DrainArenaPools() {
	tswasm.DrainArenaPools()
}

// Walk invokes fn pre-order on every named descendant of n, including n.
// fn returning false skips traversal of n's children.
func Walk(n Node, fn func(Node) bool) {
	if !fn(n) {
		return
	}
	for _, c := range n.NamedChildren() {
		Walk(c, fn)
	}
}

// StmtListProvider returns the named children of a container that should
// be considered ordered statements for `adjacent` matching. Languages
// supply this so comments and other non-statement nodes can be skipped.
type StmtListProvider func(container Node) []Node
