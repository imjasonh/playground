package tswasm

// IsValid reports whether the node is non-nil.
func (n *Node) IsValid() bool { return n != nil && n.n != nil }

// Type returns the tree-sitter node type / kind name.
func (n *Node) Type() string {
	if !n.IsValid() {
		return ""
	}
	return n.n.kind
}

// IsNamed reports whether the node is a named (non-anonymous) child.
func (n *Node) IsNamed() bool { return n.IsValid() && n.n.named }

// StartByte and EndByte return the node's byte range in the source.
func (n *Node) StartByte() uint32 {
	if !n.IsValid() {
		return 0
	}
	return n.n.start
}
func (n *Node) EndByte() uint32 {
	if !n.IsValid() {
		return 0
	}
	return n.n.end
}

// NamedChildren returns the named children in order.
func (n *Node) NamedChildren() []*Node {
	if !n.IsValid() {
		return nil
	}
	out := make([]*Node, len(n.n.namedChildren))
	for i, c := range n.n.namedChildren {
		out[i] = &Node{n: c, tree: n.tree}
	}
	return out
}

// Children returns every child including anonymous ones.
func (n *Node) Children() []*Node {
	if !n.IsValid() {
		return nil
	}
	out := make([]*Node, len(n.n.children))
	for i, c := range n.n.children {
		out[i] = &Node{n: c, tree: n.tree}
	}
	return out
}

// ChildByFieldName returns the first child bound to fieldName, or nil.
func (n *Node) ChildByFieldName(fieldName string) *Node {
	if !n.IsValid() || n.n.fieldIndex == nil {
		return nil
	}
	c := n.n.fieldIndex[fieldName]
	if c == nil {
		return nil
	}
	return &Node{n: c, tree: n.tree}
}

// FieldNameForChild returns the field name for the i-th child (including
// anonymous), or "" if none / out of range.
func (n *Node) FieldNameForChild(i int) string {
	if !n.IsValid() || i < 0 || i >= len(n.n.children) {
		return ""
	}
	return n.n.children[i].fieldName
}

// Parent returns the parent node, or nil at the root.
func (n *Node) Parent() *Node {
	if !n.IsValid() || n.n.parent == nil {
		return nil
	}
	return &Node{n: n.n.parent, tree: n.tree}
}

// HasError reports whether the subtree contains a parse error.
func (n *Node) HasError() bool { return n.IsValid() && n.n.hasError }

// IsError reports whether this node is an ERROR node.
func (n *Node) IsError() bool { return n.IsValid() && n.n.err }

// IsMissing reports whether this node was inserted as a missing token.
func (n *Node) IsMissing() bool { return n.IsValid() && n.n.missing }

// SExpr returns a simple s-expression of the named subtree (for tests).
func (n *Node) SExpr() string {
	if !n.IsValid() {
		return ""
	}
	return sexpr(n.n)
}

func sexpr(n *node) string {
	if len(n.namedChildren) == 0 {
		return "(" + n.kind + ")"
	}
	s := "(" + n.kind
	for _, c := range n.namedChildren {
		s += " " + sexpr(c)
	}
	return s + ")"
}
