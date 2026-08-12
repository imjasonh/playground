package pastals

import (
	"context"
	"sort"

	"github.com/imjasonh/pasta/internal/pastals/protocol"
	"github.com/imjasonh/pasta/internal/runner"
)

// handleCodeAction returns CodeActions for the diagnostics in p.
// Two kinds:
//
//	quickfix              — one per diagnostic that carried fix ops
//	source.fixAll.pasta   — applies every non-overlapping op in the file
func (s *Server) handleCodeAction(ctx context.Context, p protocol.CodeActionParams) []protocol.CodeAction {
	doc, ok := s.docs.get(p.TextDocument.URI)
	if !ok {
		return nil
	}
	snap := doc.snapshot()

	var actions []protocol.CodeAction

	// Quick fixes from the diagnostics in the request context.
	for _, d := range p.Context.Diagnostics {
		if d.Data == nil || len(d.Data.Ops) == 0 {
			continue
		}
		edits := opsToTextEdits(snap, d.Data.Ops)
		if len(edits) == 0 {
			continue
		}
		title := "pasta: fix"
		if d.Data.Rule != "" {
			title = "pasta: fix " + d.Data.Rule
		}
		actions = append(actions, protocol.CodeAction{
			Title:       title,
			Kind:        protocol.CodeActionKindQuickFix,
			Diagnostics: []protocol.Diagnostic{d},
			Edit: &protocol.WorkspaceEdit{
				Changes: map[string][]protocol.TextEdit{p.TextDocument.URI: edits},
			},
			IsPreferred: true,
		})
	}

	// Whole-file fixAll: re-run pasta to collect every op (the
	// diagnostics in p.Context may not include everything if the editor
	// filtered by range).
	if shouldOfferFixAll(p.Context.Only) {
		if action := s.buildFixAllAction(ctx, snap); action != nil {
			actions = append(actions, *action)
		}
	}

	return actions
}

// shouldOfferFixAll reports whether the client is asking for a kind
// that includes our fixAll. Empty `Only` means "all kinds".
func shouldOfferFixAll(only []string) bool {
	if len(only) == 0 {
		return true
	}
	for _, k := range only {
		// LSP allows kind prefixes — "source" matches "source.fixAll.pasta".
		if k == protocol.CodeActionKindSourceFixAll || k == "source" || k == "source.fixAll" {
			return true
		}
	}
	return false
}

// buildFixAllAction re-runs pasta over the document snapshot and
// bundles every non-overlapping op into a single CodeAction.
func (s *Server) buildFixAllAction(ctx context.Context, snap docSnapshot) *protocol.CodeAction {
	analyzers := s.analyzers()
	if len(analyzers) == 0 {
		return nil
	}
	res, err := runner.RunFile(ctx, snap.path, snap.src, analyzers, false)
	if err != nil || len(res.Ops) == 0 {
		return nil
	}
	encoded := make([]protocol.EncodedOp, 0, len(res.Ops))
	for _, op := range res.Ops {
		encoded = append(encoded, protocol.EncodedOp{Start: op.Start, End: op.End, Text: op.Text})
	}
	edits := opsToTextEdits(snap, dropOverlapping(encoded))
	if len(edits) == 0 {
		return nil
	}
	return &protocol.CodeAction{
		Title: "pasta: fix all",
		Kind:  protocol.CodeActionKindSourceFixAll,
		Edit: &protocol.WorkspaceEdit{
			Changes: map[string][]protocol.TextEdit{snap.uri: edits},
		},
	}
}

// dropOverlapping mirrors internal/apply.ResolveNested's conflict
// policy at a coarse level: nested whole-node rewrites keep the
// innermost edit; remaining partial overlaps drop the later op. For
// LSP this is gentler than apply's hard-error on partial overlaps
// because losing a fix is better than the editor rejecting the entire
// WorkspaceEdit.
func dropOverlapping(ops []protocol.EncodedOp) []protocol.EncodedOp {
	sorted := make([]protocol.EncodedOp, len(ops))
	copy(sorted, ops)
	sort.SliceStable(sorted, func(i, j int) bool {
		if sorted[i].Start != sorted[j].Start {
			return sorted[i].Start < sorted[j].Start
		}
		return sorted[i].End < sorted[j].End
	})

	drop := make([]bool, len(sorted))
	for i := range sorted {
		if drop[i] {
			continue
		}
		a := sorted[i]
		for j := i + 1; j < len(sorted); j++ {
			if drop[j] {
				continue
			}
			b := sorted[j]
			if b.Start >= a.End {
				break
			}
			switch {
			case encodedContains(a, b):
				drop[i] = true
			case encodedContains(b, a):
				drop[j] = true
			case a.Start == b.Start && a.End == b.End:
				drop[j] = true
			}
		}
	}

	out := make([]protocol.EncodedOp, 0, len(sorted))
	var lastEnd uint32
	first := true
	for i, op := range sorted {
		if drop[i] {
			continue
		}
		if !first && op.Start < lastEnd {
			continue // partial overlap: drop later
		}
		out = append(out, op)
		if op.End > lastEnd {
			lastEnd = op.End
		}
		first = false
	}
	return out
}

func encodedContains(a, b protocol.EncodedOp) bool {
	return a.Start <= b.Start && b.End <= a.End && (a.Start < b.Start || b.End < a.End)
}

// opsToTextEdits converts pasta byte-range ops to LSP TextEdits using
// the snapshot's lspconv.Doc for byte→position conversion.
func opsToTextEdits(snap docSnapshot, ops []protocol.EncodedOp) []protocol.TextEdit {
	out := make([]protocol.TextEdit, 0, len(ops))
	for _, op := range ops {
		r := snap.conv.RangeFromBytes(op.Start, op.End)
		out = append(out, protocol.TextEdit{
			Range:   toLSPRange(r),
			NewText: op.Text,
		})
	}
	return out
}
