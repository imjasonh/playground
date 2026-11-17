package engine

import (
	"context"
	"errors"
	"io/fs"
	"slices"
	"sort"
	"sync/atomic"
	"time"

	"golang.org/x/sync/errgroup"

	"github.com/imjasonh/playground/pasta/internal/effect"
	"github.com/imjasonh/playground/pasta/internal/factstore"
	"github.com/imjasonh/playground/pasta/internal/prefilter"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// DefaultTreeBudget is the estimated heap that the in-memory path may
// spend on parse trees it keeps between passes when the caller doesn't
// set WithTreeBudget.
const DefaultTreeBudget = 4 << 30

// treeBytesPerNode estimates the heap one node of a retained tree
// holds: the Go node, its slots in its parent's child slices, and its
// entry in the match index.
const treeBytesPerNode = 200

// memRun is one run of the in-memory path.
type memRun struct {
	groups  []ruleGroup
	store   *factstore.Store
	o       *runOpts
	workers int
	// files holds the files that need a rule pass, in input order.
	files []*memFile
}

// memFile is one file of an in-memory run.
type memFile struct {
	index int
	// state.tree is nil when the tree was released after the first
	// pass; prepare parses the file again for a later pass.
	state fileState
	// outs holds what each group produced for this file until it's
	// reassembled in schedule order.
	outs []groupOutput
}

// runInMemory is the path used when the schedule has cross-file or
// fixpoint dependencies: a consumer group must see the facts that
// producer groups emitted on every file.
//
// Files are parsed in parallel, and the first level of groups (see
// groupLevels) runs on each file as soon as it's parsed. Later levels
// run one pass at a time over the files they apply to. A tree that a
// later pass needs is kept while the estimated size of every kept tree
// stays within the tree budget; past it, the tree is released and the
// file is parsed again for each later pass. Fixpoint groups iterate
// over files in parallel, except a group that reads not_has_fact,
// which iterates over files in order. Each file's diagnostics and ops
// are reassembled in schedule order, so the output doesn't depend on
// goroutine timing or on which trees were kept.
func runInMemory(
	ctx context.Context,
	files []FileInput,
	groups []ruleGroup,
	o *runOpts,
) ([]Result, error) {
	results := make([]Result, len(files))
	r := &memRun{
		groups:  groups,
		store:   factstore.New(),
		o:       o,
		workers: workerCount(len(files)),
	}
	defer func() {
		for _, f := range r.files {
			if f.state.tree != nil {
				f.state.tree.Release()
			}
		}
		tsutil.DrainArenaPools()
	}()

	levels := groupLevels(groups)
	if err := r.parseAll(ctx, files, results, levels); err != nil {
		return nil, err
	}
	for li, level := range levels {
		if err := r.runLevel(ctx, level, li == 0); err != nil {
			return nil, err
		}
	}
	for _, f := range r.files {
		out := &results[f.index]
		sort.SliceStable(f.outs, func(a, b int) bool { return f.outs[a].group < f.outs[b].group })
		for _, part := range f.outs {
			out.Diagnostics = append(out.Diagnostics, part.diagnostics...)
			out.Ops = append(out.Ops, part.ops...)
		}
		out.Diagnostics = append(out.Diagnostics, unusedIgnoreDiagnostics(f.state.suppress)...)
	}
	return results, nil
}

// parseAll parses every file, records its definitions, and runs the
// non-fixpoint groups of the first level on it. Those groups require
// no fact that another group provides, so they don't need every file's
// definitions first. It keeps the trees that later passes need, within
// the tree budget.
func (r *memRun) parseAll(ctx context.Context, files []FileInput, results []Result, levels [][]int) error {
	var first []int
	if len(levels) > 0 {
		for _, gi := range levels[0] {
			if !r.groups[gi].fixpoint {
				first = append(first, gi)
			}
		}
	}
	var later []ruleGroup
	for gi, g := range r.groups {
		if !slices.Contains(first, gi) {
			later = append(later, g)
		}
	}
	parseTimeout := time.Duration(0)
	var budget int64
	if r.o != nil {
		parseTimeout = r.o.parseTimeout
		budget = r.o.treeBudget
	}
	var kept atomic.Int64
	parsed := make([]*memFile, len(files))
	g, gctx := errgroup.WithContext(ctx)
	g.SetLimit(r.workers)
	for i := range files {
		g.Go(func() error {
			if err := gctx.Err(); err != nil {
				r.o.syncAdmit(i, 0)
				return err
			}
			s, err := parseInMemory(gctx, i, files[i], r.groups, r.store, &results[i], parseTimeout, r.o)
			if err != nil || s == nil {
				return err
			}
			f := &memFile{index: i, state: *s}
			parsed[i] = f
			for _, gi := range first {
				var res Result
				if err := runGroupOnFile(r.groups[gi], f.state, r.store, &res); err != nil {
					return err
				}
				f.outs = appendGroupOutput(f.outs, gi, res)
			}
			if needsPass(later, f.state.input) && (budget <= 0 || reserveBytes(&kept, budget, int64(f.state.nodes)*treeBytesPerNode)) {
				return nil
			}
			f.state.release()
			return nil
		})
	}
	if err := g.Wait(); err != nil {
		return err
	}
	for _, f := range parsed {
		if f != nil {
			r.files = append(r.files, f)
		}
	}
	return nil
}

// runLevel runs one level of groups. When first is true, the level's
// non-fixpoint groups already ran in parseAll.
//
// The non-fixpoint groups and the first iteration of the fixpoint
// groups share a pass. A fixpoint group that reads only has_fact
// reaches the same facts in any order, because a new fact can only
// make has_fact true and payloads are never read back, so its
// iterations run over files in parallel and collect results as they
// go. Once an iteration adds no fact, every file in it saw the final
// facts, and its results stand.
func (r *memRun) runLevel(ctx context.Context, level []int, first bool) error {
	var plain, fix, ordered []int
	for _, gi := range level {
		switch g := r.groups[gi]; {
		case !g.fixpoint:
			if !first {
				plain = append(plain, gi)
			}
		case readsAbsentFacts(g):
			ordered = append(ordered, gi)
		default:
			fix = append(fix, gi)
		}
	}
	gis := append(plain, fix...)
	for iter := 0; len(gis) > 0; iter++ {
		before := r.store.Len()
		if err := r.collect(ctx, gis); err != nil {
			return err
		}
		if r.store.Len() == before || len(fix) == 0 {
			break
		}
		if iter+1 >= MaxFixpointIterations {
			if err := r.collect(ctx, fix); err != nil {
				return err
			}
			break
		}
		gis = fix
	}
	for _, gi := range ordered {
		if err := r.runOrdered(ctx, gi); err != nil {
			return err
		}
	}
	return nil
}

// collect runs gis on every file they apply to, in parallel, and
// replaces each file's results for those groups.
func (r *memRun) collect(ctx context.Context, gis []int) error {
	return r.pass(ctx, gis, func(f *memFile, s fileState) error {
		for _, gi := range gis {
			var res Result
			if err := runGroupOnFile(r.groups[gi], s, r.store, &res); err != nil {
				return err
			}
			f.outs = setGroupOutput(f.outs, gi, res)
		}
		return nil
	})
}

// runOrdered runs the fixpoint group gi, which reads not_has_fact.
// Whether that predicate holds depends on which facts exist so far, so
// each emit-only iteration visits files in input order, as a serial run
// does. One collecting pass follows convergence.
func (r *memRun) runOrdered(ctx context.Context, gi int) error {
	group := []ruleGroup{r.groups[gi]}
	for iter := 0; iter < MaxFixpointIterations; iter++ {
		before := r.store.Len()
		for _, f := range r.files {
			if !needsPass(group, f.state.input) {
				continue
			}
			s, release, err := r.prepare(ctx, f)
			if err != nil {
				return err
			}
			err = runGroupOnFile(r.groups[gi], s, r.store, nil)
			release()
			if err != nil {
				return err
			}
		}
		if r.store.Len() == before {
			break
		}
	}
	return r.collect(ctx, []int{gi})
}

// pass calls fn, in parallel, for every file that one of gis applies
// to, with that file's prepared state.
func (r *memRun) pass(ctx context.Context, gis []int, fn func(*memFile, fileState) error) error {
	groups := make([]ruleGroup, len(gis))
	for i, gi := range gis {
		groups[i] = r.groups[gi]
	}
	g, gctx := errgroup.WithContext(ctx)
	g.SetLimit(r.workers)
	for _, f := range r.files {
		if !needsPass(groups, f.state.input) {
			continue
		}
		g.Go(func() error {
			s, release, err := r.prepare(gctx, f)
			if err != nil {
				return err
			}
			defer release()
			return fn(f, s)
		})
	}
	return g.Wait()
}

// prepare returns f's state with a tree, parsing f again when its tree
// was released. The release function frees a tree that prepare parsed.
// The file parsed within the parse timeout once, so the second parse
// has none: a slow machine must not drop a file between passes.
func (r *memRun) prepare(ctx context.Context, f *memFile) (fileState, func(), error) {
	if f.state.tree != nil {
		return f.state, func() {}, nil
	}
	s, err := newFileState(ctx, f.state.input, r.store, 0, false)
	if err != nil {
		return fileState{}, nil, err
	}
	s.suppress = f.state.suppress
	if r.o != nil && r.o.stats != nil {
		r.o.stats.Reparsed.Add(1)
	}
	return s, s.release, nil
}

// needsPass reports whether a rule in groups applies to f and could
// match its source.
func needsPass(groups []ruleGroup, f FileInput) bool {
	rules := applicableRules(groups, f.Lang, fileName(f))
	return len(rules) > 0 && prefilter.MayMatch(f.Src, prefilter.ForRules(rules))
}

// readsAbsentFacts reports whether a rule in g uses not_has_fact.
func readsAbsentFacts(g ruleGroup) bool {
	for i := range g.rules {
		if g.rules[i].rule.UsesPredicate("not_has_fact") {
			return true
		}
	}
	return false
}

// parseInMemory loads and parses one file for runInMemory. It returns
// nil when the file needs no rule pass: no applicable rules, a
// prefilter miss, or a skip recorded in out.SkipReason. Every path
// calls o.syncAdmit exactly once, so a memory budget can't stall the
// files after this one.
func parseInMemory(ctx context.Context, index int, f FileInput, groups []ruleGroup, store *factstore.Store, out *Result, parseTimeout time.Duration, o *runOpts) (*fileState, error) {
	src, err := loadSource(f)
	if err != nil {
		o.syncAdmit(index, 0)
		if errors.Is(err, fs.ErrNotExist) {
			out.SkipReason = "file not found"
			return nil, nil
		}
		return nil, err
	}
	f.Src = src
	out.Src = src
	applicable := applicableRules(groups, f.Lang, fileName(f))
	if len(applicable) == 0 {
		o.syncAdmit(index, 0)
		if hasPastaIgnore(src) {
			return nil, emitUnusedIgnoresOnly(ctx, f, out, o)
		}
		return nil, nil
	}
	if o != nil && o.stats != nil {
		o.stats.Walked.Add(1)
	}
	if !prefilter.MayMatch(src, prefilter.ForRules(applicable)) {
		o.syncAdmit(index, 0)
		if o != nil && o.stats != nil {
			o.stats.PrefilterSkipped.Add(1)
		}
		if hasPastaIgnore(src) {
			return nil, emitUnusedIgnoresOnly(ctx, f, out, o)
		}
		return nil, nil
	}
	if !o.syncAdmit(index, int64(len(src))) {
		out.SkipReason = "memory budget exceeded"
		if o != nil && o.stats != nil {
			o.stats.MemorySkipped.Add(1)
		}
		return nil, nil
	}
	s, err := newFileState(ctx, f, store, parseTimeout, o != nil && o.defineNames)
	if err != nil {
		releaseParse(o, int64(len(src)))
		if errors.Is(err, tsutil.ErrParseTimeout) || errors.Is(err, tsutil.ErrParseResourceLimit) {
			out.SkipReason = "too complex to analyze"
			if o != nil && o.stats != nil {
				o.stats.TimedOut.Add(1)
			}
			return nil, nil
		}
		return nil, err
	}
	if tsutil.ErrorHeavy(s.root) {
		releaseParse(o, int64(len(src)))
		out.SkipReason = "parse errors"
		if o != nil && o.stats != nil {
			o.stats.ParseErrors.Add(1)
		}
		s.tree.Release()
		return nil, nil
	}
	if o != nil && o.stats != nil {
		if s.root.HasError() {
			o.stats.ParseDegraded.Add(1)
		}
		o.stats.Parsed.Add(1)
	}
	return &s, nil
}

// groupOutput is what one rule group produced for one file.
type groupOutput struct {
	group       int
	diagnostics []effect.Diagnostic
	ops         []effect.Op
}

// appendGroupOutput appends r to outs, tagged with group, when r has
// any diagnostics or ops.
func appendGroupOutput(outs []groupOutput, group int, r Result) []groupOutput {
	if len(r.Diagnostics) == 0 && len(r.Ops) == 0 {
		return outs
	}
	return append(outs, groupOutput{group: group, diagnostics: r.Diagnostics, ops: r.Ops})
}

// setGroupOutput replaces group's entry in outs with r.
func setGroupOutput(outs []groupOutput, group int, r Result) []groupOutput {
	outs = slices.DeleteFunc(outs, func(o groupOutput) bool { return o.group == group })
	return appendGroupOutput(outs, group, r)
}
