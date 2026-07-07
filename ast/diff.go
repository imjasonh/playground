package main

import (
	"fmt"
	"strings"
)

// unifiedDiff returns a unified diff (3 lines of context) between the old and
// new contents of a file. It is a small, dependency-free line differ based on a
// longest-common-subsequence, sufficient for showing rewrite previews.
func unifiedDiff(path string, oldSrc, newSrc []byte) string {
	a := splitLines(string(oldSrc))
	b := splitLines(string(newSrc))

	ops := diffLines(a, b)
	hunks := groupHunks(ops, 3)
	if len(hunks) == 0 {
		return ""
	}

	var sb strings.Builder
	fmt.Fprintf(&sb, "--- a/%s\n", path)
	fmt.Fprintf(&sb, "+++ b/%s\n", path)
	for _, h := range hunks {
		fmt.Fprintf(&sb, "@@ -%d,%d +%d,%d @@\n", h.aStart, h.aLines, h.bStart, h.bLines)
		for _, ln := range h.lines {
			sb.WriteString(ln)
		}
	}
	return sb.String()
}

func splitLines(s string) []string {
	if s == "" {
		return nil
	}
	parts := strings.SplitAfter(s, "\n")
	// SplitAfter leaves a trailing "" when s ends in newline; drop it.
	if parts[len(parts)-1] == "" {
		parts = parts[:len(parts)-1]
	}
	return parts
}

type diffOp struct {
	kind byte // ' ', '-', '+'
	line string
}

// diffLines computes an edit script using an LCS table.
func diffLines(a, b []string) []diffOp {
	n, m := len(a), len(b)
	lcs := make([][]int, n+1)
	for i := range lcs {
		lcs[i] = make([]int, m+1)
	}
	for i := n - 1; i >= 0; i-- {
		for j := m - 1; j >= 0; j-- {
			if a[i] == b[j] {
				lcs[i][j] = lcs[i+1][j+1] + 1
			} else if lcs[i+1][j] >= lcs[i][j+1] {
				lcs[i][j] = lcs[i+1][j]
			} else {
				lcs[i][j] = lcs[i][j+1]
			}
		}
	}

	var ops []diffOp
	i, j := 0, 0
	for i < n && j < m {
		switch {
		case a[i] == b[j]:
			ops = append(ops, diffOp{' ', a[i]})
			i++
			j++
		case lcs[i+1][j] >= lcs[i][j+1]:
			ops = append(ops, diffOp{'-', a[i]})
			i++
		default:
			ops = append(ops, diffOp{'+', b[j]})
			j++
		}
	}
	for ; i < n; i++ {
		ops = append(ops, diffOp{'-', a[i]})
	}
	for ; j < m; j++ {
		ops = append(ops, diffOp{'+', b[j]})
	}
	return ops
}

type hunk struct {
	aStart, aLines int
	bStart, bLines int
	lines          []string
}

// groupHunks turns a flat edit script into unified-diff hunks with the given
// amount of surrounding context.
func groupHunks(ops []diffOp, context int) []hunk {
	// Identify indices of changed ops.
	changed := make([]bool, len(ops))
	any := false
	for i, o := range ops {
		if o.kind != ' ' {
			changed[i] = true
			any = true
		}
	}
	if !any {
		return nil
	}

	var hunks []hunk
	i := 0
	// Running 1-based line numbers in each file.
	aLine, bLine := 1, 1
	// Precompute cumulative line numbers per op index.
	aAt := make([]int, len(ops)+1)
	bAt := make([]int, len(ops)+1)
	for k, o := range ops {
		aAt[k] = aLine
		bAt[k] = bLine
		switch o.kind {
		case ' ':
			aLine++
			bLine++
		case '-':
			aLine++
		case '+':
			bLine++
		}
	}
	aAt[len(ops)] = aLine
	bAt[len(ops)] = bLine

	for i < len(ops) {
		if !changed[i] {
			i++
			continue
		}
		start := i - context
		if start < 0 {
			start = 0
		}
		// Extend end past changes, absorbing gaps up to 2*context of unchanged.
		end := i
		for end < len(ops) {
			if changed[end] {
				end++
				continue
			}
			// Look ahead: is there another change within context*2?
			next := end
			for next < len(ops) && !changed[next] {
				next++
			}
			if next < len(ops) && next-end <= context*2 {
				end = next
				continue
			}
			break
		}
		ctxEnd := end + context
		if ctxEnd > len(ops) {
			ctxEnd = len(ops)
		}

		var h hunk
		h.aStart = aAt[start]
		h.bStart = bAt[start]
		h.aLines = aAt[ctxEnd] - aAt[start]
		h.bLines = bAt[ctxEnd] - bAt[start]
		if h.aLines == 0 {
			h.aStart = 0
		}
		if h.bLines == 0 {
			h.bStart = 0
		}
		for k := start; k < ctxEnd; k++ {
			h.lines = append(h.lines, formatDiffLine(ops[k]))
		}
		hunks = append(hunks, h)
		i = ctxEnd
	}
	return hunks
}

func formatDiffLine(o diffOp) string {
	line := o.line
	suffix := ""
	if !strings.HasSuffix(line, "\n") {
		suffix = "\n\\ No newline at end of file\n"
	}
	return string(o.kind) + line + suffix
}
