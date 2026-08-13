// Package apply applies compiled edit operations to source bytes.
package apply

import (
	"fmt"
	"sort"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/effect"
)

// Apply applies ops to src and returns the new bytes.
//
// Ops are sorted by start offset, nested whole-node rewrites are
// resolved innermost-first (an edit that strictly contains another is
// dropped so the inner rewrite wins — pair with multipass -fix for
// layered forms like Array<Array<T>>), remaining partial overlaps are
// rejected, and surviving ops are emitted left-to-right into a
// builder: the bytes between the previous op's end and the current
// op's start, then the op's replacement text. Tail bytes after the
// last op are appended at the end.
func Apply(src []byte, ops []effect.Op, opts dsl.RewriteOpts) ([]byte, error) {
	if len(ops) == 0 {
		return src, nil
	}

	resolved, err := ResolveNested(ops)
	if err != nil {
		return nil, err
	}

	srcLen := uint32(len(src))
	for _, op := range resolved {
		if op.End > srcLen {
			return nil, fmt.Errorf("invalid edit %q: range [%d-%d) exceeds source length %d",
				op.Rule, op.Start, op.End, srcLen)
		}
	}

	var b strings.Builder
	b.Grow(len(src))
	cursor := uint32(0)
	for _, op := range resolved {
		b.Write(src[cursor:op.Start])
		b.WriteString(op.Text)
		cursor = op.End
	}
	b.Write(src[cursor:])
	return []byte(b.String()), nil
}

// ResolveNested prepares ops for application: drop edits that strictly
// contain another edit (keep the innermost), then reject any remaining
// partial overlaps. Identical ranges keep the first op. Returns ops
// sorted by start (insertions after deletions at the same point).
func ResolveNested(ops []effect.Op) ([]effect.Op, error) {
	if len(ops) == 0 {
		return nil, nil
	}

	sorted := make([]effect.Op, len(ops))
	copy(sorted, ops)
	sort.SliceStable(sorted, func(i, j int) bool {
		if sorted[i].Start != sorted[j].Start {
			return sorted[i].Start < sorted[j].Start
		}
		// Pure insertions (Start==End) at the same position go after
		// non-insertions at that position.
		iIns := sorted[i].Start == sorted[i].End
		jIns := sorted[j].Start == sorted[j].End
		if iIns != jIns {
			return !iIns
		}
		// Among overlapping spans that share a start, prefer the
		// narrower (innermost) span first so containment resolution
		// sees the inner edit before deciding to drop the outer.
		return sorted[i].End < sorted[j].End
	})

	drop := make([]bool, len(sorted))
	for i := range sorted {
		if drop[i] {
			continue
		}
		a := sorted[i]
		if a.Start > a.End {
			return nil, fmt.Errorf("invalid edit %q: start %d > end %d", a.Rule, a.Start, a.End)
		}
		for j := i + 1; j < len(sorted); j++ {
			if drop[j] {
				continue
			}
			b := sorted[j]
			if b.Start >= a.End {
				break // later ops start further right; no containment
			}
			switch {
			case strictlyContains(a, b):
				drop[i] = true // keep innermost b
			case strictlyContains(b, a):
				drop[j] = true
			case a.Start == b.Start && a.End == b.End:
				// Identical range: keep the first, drop the duplicate.
				drop[j] = true
			}
		}
	}

	out := make([]effect.Op, 0, len(sorted))
	for i, op := range sorted {
		if drop[i] {
			continue
		}
		out = append(out, op)
	}

	for i, op := range out {
		if op.Start > op.End {
			return nil, fmt.Errorf("invalid edit %q: start %d > end %d", op.Rule, op.Start, op.End)
		}
		if i == 0 {
			continue
		}
		prev := out[i-1]
		// Allow exact same point (insert at the deletion's start = end).
		if op.Start < prev.End {
			return nil, fmt.Errorf("conflicting edits: %q[%d-%d) overlaps %q[%d-%d)",
				prev.Rule, prev.Start, prev.End, op.Rule, op.Start, op.End)
		}
	}
	return out, nil
}

// strictlyContains reports whether a fully contains b and is larger.
func strictlyContains(a, b effect.Op) bool {
	return a.Start <= b.Start && b.End <= a.End && (a.Start < b.Start || b.End < a.End)
}
