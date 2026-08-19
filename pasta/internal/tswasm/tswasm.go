// Package tswasm is pasta's pure-Go tree-sitter backend: the official
// tree-sitter C runtime + grammars, compiled to one wasm32-wasi module
// (ts-core.wasm via build.sh) and driven through wazero — no cgo.
//
// Prior art: dvcdsys/code-index PR #81 (server/internal/chunker/tswasm).
// Parse dumps the whole tree inside the guest via ts_dump_tree; the host
// does one Memory.Read and rebuilds a Go node graph with parent/child
// and field-name links so the rest of pasta keeps its Node API.
//
// Concurrency: each wazero module instance has its own linear memory and
// is not safe for concurrent calls. Parses borrow an *engine from a pool.
package tswasm

import (
	"bytes"
	"context"
	_ "embed"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"sync"
	"sync/atomic"
	"time"

	"github.com/andybalholm/brotli"
	"github.com/tetratelabs/wazero"
	"github.com/tetratelabs/wazero/api"
	"github.com/tetratelabs/wazero/experimental"
	"github.com/tetratelabs/wazero/imports/wasi_snapshot_preview1"
)

//go:embed ts-core.wasm.br
var wasmBrotli []byte

// recSize must match sizeof(NodeRec) in csrc/host_extra.c (10 × uint32).
const recSize = 40

// ExportName returns the wasm export for a pasta grammar id (e.g. "go" → "tree_sitter_go").
func ExportName(grammar string) string {
	return "tree_sitter_" + grammar
}

var (
	// MaxConcurrentInstances caps live engines (each holds grammar tables in
	// its own linear memory). 0 → 4.
	MaxConcurrentInstances = 4
	// MemLimitPages caps linear memory (64 KiB pages). 4096 = 256 MiB.
	MemLimitPages uint32 = 4096
	// RecycleGrowthBytes closes instances that grew this far above baseline.
	RecycleGrowthBytes uint64 = 128 << 20
	// MaxIdleInstances bounds pooled idle engines. 0 → MaxConcurrentInstances.
	MaxIdleInstances = 2
)

// ---------------------------------------------------------------------------
// Public tree / node types
// ---------------------------------------------------------------------------

// Language is a grammar handle. Cheap; just the export name.
type Language struct {
	Grammar string // pasta grammar id, e.g. "go"
}

// Tree owns a parsed node graph. The WASM engine is released as soon as
// the graph is built (nodes live in Go), so Release is a no-op retained
// for API parity with the old gotreesitter Tree.
type Tree struct {
	root   *node
	src    []byte
	fileID string
	lang   *Language
}

// RootNode returns the root.
func (t *Tree) RootNode() *Node {
	if t == nil || t.root == nil {
		return nil
	}
	return &Node{n: t.root, tree: t}
}

// Release is a no-op; kept so callers can defer tree.Release().
func (t *Tree) Release() {}

// Node is a tree-sitter node in the rebuilt Go graph.
type Node struct {
	n    *node
	tree *Tree
}

type node struct {
	kind                string
	start, end          uint32
	named, err, missing bool
	extra, hasError     bool
	fieldName           string
	parent              *node
	children            []*node
	namedChildren       []*node
	fieldIndex          map[string]*node // first child per field name
}

// ---------------------------------------------------------------------------
// Runtime / pool
// ---------------------------------------------------------------------------

type runtime struct {
	ctx context.Context
	wz  wazero.Runtime
	cm  wazero.CompiledModule
}

var (
	rtOnce        sync.Once
	rt            *runtime
	rtErr         error
	gpool         enginePool
	instN         atomic.Int64
	instLim       *concLimiter
	baselineBytes atomic.Uint64
)

type concLimiter struct {
	mu    sync.Mutex
	cond  *sync.Cond
	inUse int
	max   int
}

func newConcLimiter(max int) *concLimiter {
	if max < 1 {
		max = 1
	}
	l := &concLimiter{max: max}
	l.cond = sync.NewCond(&l.mu)
	return l
}

func (l *concLimiter) acquire() {
	l.mu.Lock()
	for l.inUse >= l.max {
		l.cond.Wait()
	}
	l.inUse++
	l.mu.Unlock()
}

func (l *concLimiter) release() {
	l.mu.Lock()
	l.inUse--
	l.cond.Signal()
	l.mu.Unlock()
}

func initRuntime() {
	ctx := context.Background()
	if a := linearMemoryAllocator(); a != nil {
		ctx = experimental.WithMemoryAllocator(ctx, a)
	}
	n := MaxConcurrentInstances
	if n <= 0 {
		n = 4
	}
	instLim = newConcLimiter(n)
	cfg := wazero.NewRuntimeConfigCompiler()
	if MemLimitPages > 0 {
		cfg = cfg.WithMemoryLimitPages(MemLimitPages)
	}
	wz := wazero.NewRuntimeWithConfig(ctx, cfg)
	if _, err := wasi_snapshot_preview1.Instantiate(ctx, wz); err != nil {
		rtErr = fmt.Errorf("wasi: %w", err)
		return
	}
	raw, err := io.ReadAll(brotli.NewReader(bytes.NewReader(wasmBrotli)))
	if err != nil {
		rtErr = fmt.Errorf("decompress ts-core.wasm.br: %w", err)
		return
	}
	cm, err := wz.CompileModule(ctx, raw)
	if err != nil {
		rtErr = fmt.Errorf("compile ts-core.wasm: %w", err)
		return
	}
	rt = &runtime{ctx: ctx, wz: wz, cm: cm}
}

type engine struct {
	ctx context.Context
	mod api.Module
	mem api.Memory

	malloc, free                         api.Function
	parserNew, parserDelete, parserReset api.Function
	setLang, parse, treeDelete           api.Function
	setTimeout                           api.Function
	dumpTree                             api.Function
	langSymCount, langSymName            api.Function
	langFieldCount, langFieldName        api.Function

	langPtr map[string]uint32
}

var (
	symNameMu      sync.Mutex
	symNameCache   = map[string]map[uint32]string{}
	fieldNameMu    sync.Mutex
	fieldNameCache = map[string]map[uint32]string{}
)

func newEngine() (*engine, error) {
	rtOnce.Do(initRuntime)
	if rtErr != nil {
		return nil, rtErr
	}
	name := fmt.Sprintf("ts-%d", instN.Add(1))
	mod, err := rt.wz.InstantiateModule(rt.ctx, rt.cm,
		wazero.NewModuleConfig().WithName(name).WithStartFunctions("_initialize"))
	if err != nil {
		return nil, fmt.Errorf("instantiate: %w", err)
	}
	e := &engine{
		ctx: rt.ctx, mod: mod, mem: mod.Memory(),
		malloc:         mod.ExportedFunction("malloc"),
		free:           mod.ExportedFunction("free"),
		parserNew:      mod.ExportedFunction("ts_parser_new"),
		parserDelete:   mod.ExportedFunction("ts_parser_delete"),
		parserReset:    mod.ExportedFunction("ts_parser_reset"),
		setLang:        mod.ExportedFunction("ts_parser_set_language"),
		parse:          mod.ExportedFunction("ts_parser_parse_string"),
		treeDelete:     mod.ExportedFunction("ts_tree_delete"),
		setTimeout:     mod.ExportedFunction("ts_parser_set_timeout_micros"),
		dumpTree:       mod.ExportedFunction("ts_dump_tree"),
		langSymCount:   mod.ExportedFunction("ts_language_symbol_count"),
		langSymName:    mod.ExportedFunction("ts_language_symbol_name"),
		langFieldCount: mod.ExportedFunction("ts_language_field_count"),
		langFieldName:  mod.ExportedFunction("ts_language_field_name_for_id"),
		langPtr:        map[string]uint32{},
	}
	if rs := e.call(mod.ExportedFunction("ts_dump_rec_size")); rs != recSize {
		mod.Close(rt.ctx)
		return nil, fmt.Errorf("NodeRec size mismatch: guest=%d host=%d", rs, recSize)
	}
	baselineBytes.CompareAndSwap(0, e.memSize())
	return e, nil
}

func (e *engine) close()          { e.mod.Close(e.ctx) }
func (e *engine) memSize() uint64 { return uint64(e.mem.Size()) }

type enginePool struct {
	mu       sync.Mutex
	free     []*engine
	created  atomic.Int64
	closed   atomic.Int64
	recycled atomic.Int64
}

func (p *enginePool) maxIdle() int {
	if MaxIdleInstances > 0 {
		return MaxIdleInstances
	}
	if MaxConcurrentInstances > 0 {
		return MaxConcurrentInstances
	}
	return 4
}

func (p *enginePool) acquire() (*engine, error) {
	rtOnce.Do(initRuntime)
	if rtErr != nil {
		return nil, rtErr
	}
	instLim.acquire()
	p.mu.Lock()
	if n := len(p.free); n > 0 {
		e := p.free[n-1]
		p.free[n-1] = nil
		p.free = p.free[:n-1]
		p.mu.Unlock()
		return e, nil
	}
	p.mu.Unlock()
	e, err := newEngine()
	if err != nil {
		instLim.release()
		return nil, err
	}
	p.created.Add(1)
	return e, nil
}

func (p *enginePool) release(e *engine, tainted bool) {
	defer instLim.release()
	switch {
	case tainted:
		p.discard(e)
	case RecycleGrowthBytes > 0 && e.memSize() > baselineBytes.Load()+RecycleGrowthBytes:
		p.recycled.Add(1)
		p.discard(e)
	default:
		p.mu.Lock()
		if len(p.free) >= p.maxIdle() {
			p.mu.Unlock()
			p.discard(e)
			return
		}
		p.free = append(p.free, e)
		p.mu.Unlock()
	}
}

func (p *enginePool) discard(e *engine) {
	e.close()
	p.closed.Add(1)
}

// ---------------------------------------------------------------------------
// Parse
// ---------------------------------------------------------------------------

// ErrTimeout is returned when the per-parse budget elapses or ctx cancels.
var ErrTimeout = errors.New("parse timeout")

// ErrResourceLimit is returned when the guest traps (e.g. memory cap).
var ErrResourceLimit = errors.New("parse resource limit")

// ParseOptions controls a single parse.
type ParseOptions struct {
	Timeout time.Duration
}

// Parse parses src with lang and returns a Tree. Caller must Release().
func Parse(ctx context.Context, lang *Language, src []byte, fileID string, opts ParseOptions) (tree *Tree, err error) {
	if lang == nil || lang.Grammar == "" {
		return nil, fmt.Errorf("tswasm: nil language")
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	e, err := gpool.acquire()
	if err != nil {
		return nil, err
	}
	root, perr := e.parseRoot(ctx, ExportName(lang.Grammar), src, opts)
	// Nodes are copied into Go; return the engine immediately so parse
	// concurrency is not limited by how long analysis holds the tree.
	gpool.release(e, perr != nil)
	if perr != nil {
		return nil, perr
	}
	return &Tree{root: root, src: src, fileID: fileID, lang: lang}, nil
}

// HasGrammar reports whether the embedded module exports the grammar.
func HasGrammar(grammar string) bool {
	e, err := gpool.acquire()
	if err != nil {
		return false
	}
	defer gpool.release(e, false)
	return e.mod.ExportedFunction(ExportName(grammar)) != nil
}

func (e *engine) call(f api.Function, args ...uint64) uint64 {
	r, err := f.Call(e.ctx, args...)
	if err != nil {
		panic(err)
	}
	if len(r) == 0 {
		return 0
	}
	return r[0]
}

func (e *engine) language(export string) (uint32, bool) {
	if p, ok := e.langPtr[export]; ok {
		return p, p != 0
	}
	fn := e.mod.ExportedFunction(export)
	if fn == nil {
		e.langPtr[export] = 0
		return 0, false
	}
	p := uint32(e.call(fn))
	e.langPtr[export] = p
	return p, p != 0
}

func (e *engine) symbolNames(export string, lang uint32) map[uint32]string {
	symNameMu.Lock()
	m, ok := symNameCache[export]
	symNameMu.Unlock()
	if ok {
		return m
	}
	count := uint32(e.call(e.langSymCount, uint64(lang)))
	m = make(map[uint32]string, count)
	for id := range count {
		ptr := uint32(e.call(e.langSymName, uint64(lang), uint64(id)))
		m[id] = e.readCStr(ptr)
	}
	symNameMu.Lock()
	symNameCache[export] = m
	symNameMu.Unlock()
	return m
}

func (e *engine) fieldNames(export string, lang uint32) map[uint32]string {
	fieldNameMu.Lock()
	m, ok := fieldNameCache[export]
	fieldNameMu.Unlock()
	if ok {
		return m
	}
	// Field ids are 1-based; id 0 means "no field".
	count := uint32(e.call(e.langFieldCount, uint64(lang)))
	m = make(map[uint32]string, count+1)
	m[0] = ""
	for id := uint32(1); id <= count; id++ {
		ptr := uint32(e.call(e.langFieldName, uint64(lang), uint64(id)))
		m[id] = e.readCStr(ptr)
	}
	fieldNameMu.Lock()
	fieldNameCache[export] = m
	fieldNameMu.Unlock()
	return m
}

func (e *engine) parseRoot(ctx context.Context, langExport string, src []byte, opts ParseOptions) (root *node, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("%w: wasm trap: %v", ErrResourceLimit, r)
		}
	}()

	lang, ok := e.language(langExport)
	if !ok {
		return nil, fmt.Errorf("unknown grammar export %q", langExport)
	}
	parser := e.call(e.parserNew)
	defer e.call(e.parserDelete, parser)

	e.call(e.setLang, parser, uint64(lang))
	if opts.Timeout > 0 {
		micros := opts.Timeout / time.Microsecond
		if micros < 1 {
			micros = 1
		}
		e.call(e.setTimeout, parser, uint64(micros))
	}

	sp := uint32(e.call(e.malloc, uint64(len(src)+1)))
	if sp == 0 {
		return nil, fmt.Errorf("%w: malloc source failed", ErrResourceLimit)
	}
	e.mem.Write(sp, src)
	e.mem.WriteByte(sp+uint32(len(src)), 0)
	defer e.call(e.free, uint64(sp))

	// Do not write a guest cancellation flag from AfterFunc: that
	// races with wazero Memory.Grow during parse. Bound in-flight
	// work with opts.Timeout; if ctx is done, discard the result.
	tree := e.call(e.parse, parser, 0, uint64(sp), uint64(len(src)))
	if ctx.Err() != nil {
		return nil, ctx.Err()
	}
	if tree == 0 {
		if opts.Timeout > 0 {
			return nil, fmt.Errorf("%w: null tree", ErrTimeout)
		}
		return nil, fmt.Errorf("parse returned null tree")
	}
	defer e.call(e.treeDelete, tree)

	n := uint32(e.call(e.dumpTree, tree, 0, 0))
	if n == 0 {
		return &node{kind: "ERROR"}, nil
	}
	buf := uint32(e.call(e.malloc, uint64(n)*recSize))
	if buf == 0 {
		return nil, fmt.Errorf("%w: malloc dump failed", ErrResourceLimit)
	}
	defer e.call(e.free, uint64(buf))
	got := uint32(e.call(e.dumpTree, tree, uint64(buf), uint64(n)))
	if got != n {
		return nil, fmt.Errorf("dump count changed: %d vs %d", n, got)
	}
	raw, ok2 := e.mem.Read(buf, n*recSize)
	if !ok2 {
		return nil, fmt.Errorf("read dump buffer failed")
	}

	kinds := e.symbolNames(langExport, lang)
	fields := e.fieldNames(langExport, lang)
	if ctx.Err() != nil {
		return nil, ctx.Err()
	}
	return buildGraph(raw, n, kinds, fields), nil
}

func buildGraph(raw []byte, n uint32, kinds, fields map[uint32]string) *node {
	nodes := make([]*node, n)
	for i := uint32(0); i < n; i++ {
		o := i * recSize
		kindID := binary.LittleEndian.Uint32(raw[o:])
		flags := binary.LittleEndian.Uint32(raw[o+36:])
		fieldID := binary.LittleEndian.Uint32(raw[o+32:])
		kind := kinds[kindID]
		isErr := flags&2 != 0
		isMissing := flags&4 != 0
		// ERROR/MISSING nodes' TSSymbol often has an empty
		// ts_language_symbol_name; ts_node_type would return "ERROR".
		if isErr {
			kind = "ERROR"
		} else if isMissing && kind == "" {
			kind = "MISSING"
		}
		nodes[i] = &node{
			kind:      kind,
			start:     binary.LittleEndian.Uint32(raw[o+4:]),
			end:       binary.LittleEndian.Uint32(raw[o+8:]),
			fieldName: fields[fieldID],
			named:     flags&1 != 0,
			err:       isErr,
			missing:   isMissing,
			extra:     flags&8 != 0,
			hasError:  flags&16 != 0,
		}
	}
	// Reconstruct parent/child from pre-order depths.
	type frame struct {
		idx   uint32
		depth uint32
	}
	stack := make([]frame, 0, 64)
	for i := uint32(0); i < n; i++ {
		o := i * recSize
		depth := binary.LittleEndian.Uint32(raw[o+28:])
		for len(stack) > 0 && stack[len(stack)-1].depth >= depth {
			stack = stack[:len(stack)-1]
		}
		if len(stack) > 0 {
			p := nodes[stack[len(stack)-1].idx]
			c := nodes[i]
			c.parent = p
			p.children = append(p.children, c)
			if c.named {
				p.namedChildren = append(p.namedChildren, c)
			}
			if c.fieldName != "" {
				if p.fieldIndex == nil {
					p.fieldIndex = map[string]*node{}
				}
				if _, exists := p.fieldIndex[c.fieldName]; !exists {
					p.fieldIndex[c.fieldName] = c
				}
			}
		}
		stack = append(stack, frame{idx: i, depth: depth})
	}
	return nodes[0]
}

func (e *engine) readCStr(ptr uint32) string {
	if ptr == 0 {
		return ""
	}
	var b []byte
	for off := ptr; ; off++ {
		c, ok := e.mem.ReadByte(off)
		if !ok || c == 0 {
			break
		}
		b = append(b, c)
	}
	return string(b)
}

// DrainArenaPools is a no-op retained for API parity with the old
// gotreesitter backend (wasm instances are pooled separately).
func DrainArenaPools() {}
