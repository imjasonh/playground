package dsl

// WalkPattern calls fn on p and on every pattern nested in it: field,
// child, adjacent, and preceding patterns, including the inline pattern
// of a capture.
func WalkPattern(p *Pattern, fn func(*Pattern)) {
	if p == nil {
		return
	}
	fn(p)
	for _, c := range p.Fields {
		walkChild(&c, fn)
	}
	for i := range p.Children {
		walkChild(&p.Children[i], fn)
	}
	for i := range p.Adjacent {
		walkChild(&p.Adjacent[i], fn)
	}
	if p.Preceding != nil {
		walkChild(p.Preceding, fn)
	}
}

func walkChild(c *Child, fn func(*Pattern)) {
	if c == nil {
		return
	}
	if c.Pattern != nil {
		WalkPattern(c.Pattern, fn)
	}
	if sub := c.AsPattern(); sub != nil && sub != c.Pattern {
		WalkPattern(sub, fn)
	}
	if c.Preceding != nil {
		walkChild(c.Preceding, fn)
	}
}

// UsesPredicate reports whether any `where` clause in r's match pattern
// calls the predicate op.
func (r *Rule) UsesPredicate(op string) bool {
	found := false
	WalkPattern(&r.Match, func(p *Pattern) {
		for _, w := range p.Where {
			if w.Op == op {
				found = true
			}
		}
	})
	return found
}
