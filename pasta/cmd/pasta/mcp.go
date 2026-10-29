package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"sort"
	"strings"
	"sync"

	"github.com/imjasonh/playground/pasta/internal/codefacts"
)

// runMCP serves the codefacts tools over the Model Context Protocol on stdio
// (newline-delimited JSON-RPC 2.0). It is pasta's agent-facing, non-deterministic
// half: an agent explores AST cleanup facts here, then judges and acts.
//
//	pasta mcp [--root <dir>] [--exclude <glob,...>] [--no-tests] [--no-generated]
//
// The server parses each (roots, options) tree once and caches the index, so a
// report plus its follow-up queries share one parse.
func runMCP(args []string) int {
	fs := flag.NewFlagSet("pasta mcp", flag.ExitOnError)
	root := fs.String("root", ".", "default root directory when a tool call omits paths")
	exclude := fs.String("exclude", "", "default comma-separated slash-path globs to drop")
	noTests := fs.Bool("no-tests", false, "skip test-convention files by default")
	noGen := fs.Bool("no-generated", false, "skip generated files by default")
	langs := fs.String("lang", "", "default comma-separated languages to include")
	if err := fs.Parse(args); err != nil {
		return 2
	}
	srv := &mcpServer{
		defaultRoot: *root,
		baseOpts:    buildOptsFrom(*langs, *exclude, *noTests, *noGen),
		cache:       map[string]*codefacts.Index{},
	}
	if err := srv.serve(os.Stdin, os.Stdout); err != nil {
		fmt.Fprintf(os.Stderr, "pasta mcp: %v\n", err)
		return 1
	}
	return 0
}

func buildOptsFrom(langs, exclude string, noTests, noGen bool) codefacts.BuildOptions {
	o := codefacts.DefaultBuildOptions()
	o.IncludeTests = !noTests
	o.IncludeGen = !noGen
	if langs != "" {
		o.Langs = splitComma(langs)
	}
	if exclude != "" {
		o.Exclude = splitComma(exclude)
	}
	return o
}

const mcpProtocolVersion = "2024-11-05"

type mcpServer struct {
	defaultRoot string
	baseOpts    codefacts.BuildOptions
	mu          sync.Mutex
	cache       map[string]*codefacts.Index
}

type rpcRequest struct {
	JSONRPC string          `json:"jsonrpc"`
	ID      json.RawMessage `json:"id,omitempty"`
	Method  string          `json:"method"`
	Params  json.RawMessage `json:"params,omitempty"`
}

type rpcError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

type rpcResponse struct {
	JSONRPC string          `json:"jsonrpc"`
	ID      json.RawMessage `json:"id,omitempty"`
	Result  any             `json:"result,omitempty"`
	Error   *rpcError       `json:"error,omitempty"`
}

func (s *mcpServer) serve(in *os.File, out *os.File) error {
	sc := bufio.NewScanner(in)
	sc.Buffer(make([]byte, 1024*1024), 16*1024*1024)
	enc := json.NewEncoder(out)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "" {
			continue
		}
		var req rpcRequest
		if err := json.Unmarshal([]byte(line), &req); err != nil {
			_ = enc.Encode(rpcResponse{JSONRPC: "2.0", Error: &rpcError{Code: -32700, Message: "parse error"}})
			continue
		}
		resp, notify := s.handle(&req)
		if notify {
			continue // notifications get no response
		}
		if err := enc.Encode(resp); err != nil {
			return err
		}
	}
	return sc.Err()
}

func (s *mcpServer) handle(req *rpcRequest) (rpcResponse, bool) {
	switch req.Method {
	case "initialize":
		return rpcResponse{JSONRPC: "2.0", ID: req.ID, Result: map[string]any{
			"protocolVersion": mcpProtocolVersion,
			"capabilities":    map[string]any{"tools": map[string]any{}},
			"serverInfo":      map[string]any{"name": "pasta-codefacts", "version": "1.0.0"},
		}}, false
	case "notifications/initialized", "notifications/cancelled":
		return rpcResponse{}, true
	case "ping":
		return rpcResponse{JSONRPC: "2.0", ID: req.ID, Result: map[string]any{}}, false
	case "tools/list":
		return rpcResponse{JSONRPC: "2.0", ID: req.ID, Result: map[string]any{"tools": s.toolSchemas()}}, false
	case "tools/call":
		return s.callTool(req), false
	default:
		if len(req.ID) == 0 {
			return rpcResponse{}, true // unknown notification
		}
		return rpcResponse{JSONRPC: "2.0", ID: req.ID, Error: &rpcError{Code: -32601, Message: "method not found: " + req.Method}}, false
	}
}

// sharedParams documents the scope arguments every tool accepts.
func sharedParams() map[string]any {
	return map[string]any{
		"paths":             map[string]any{"type": "array", "items": map[string]any{"type": "string"}, "description": "roots to index (default: the server root)"},
		"langs":             map[string]any{"type": "array", "items": map[string]any{"type": "string"}, "description": "limit to these language names"},
		"exclude":           map[string]any{"type": "array", "items": map[string]any{"type": "string"}, "description": "slash-path globs to drop (e.g. litestream/**)"},
		"include_tests":     map[string]any{"type": "boolean", "description": "index test-convention files (default true)"},
		"include_generated": map[string]any{"type": "boolean", "description": "index generated files (default true)"},
	}
}

func (s *mcpServer) toolSchemas() []map[string]any {
	tools := codefacts.Tools()
	sort.Slice(tools, func(i, j int) bool { return tools[i].Name < tools[j].Name })
	out := make([]map[string]any, 0, len(tools))
	for _, t := range tools {
		props := sharedParams()
		for k, v := range t.Params {
			props[k] = v
		}
		out = append(out, map[string]any{
			"name":        t.Name,
			"description": t.Description,
			"inputSchema": map[string]any{"type": "object", "properties": props},
		})
	}
	return out
}

func (s *mcpServer) callTool(req *rpcRequest) rpcResponse {
	var params struct {
		Name      string         `json:"name"`
		Arguments map[string]any `json:"arguments"`
	}
	if err := json.Unmarshal(req.Params, &params); err != nil {
		return rpcResponse{JSONRPC: "2.0", ID: req.ID, Error: &rpcError{Code: -32602, Message: "invalid params"}}
	}
	tool, ok := codefacts.ToolByName(params.Name)
	if !ok {
		return s.toolError(req.ID, "unknown tool: "+params.Name)
	}
	args := params.Arguments
	if args == nil {
		args = map[string]any{}
	}
	roots := s.rootsFrom(args)
	opts := s.optsFrom(args)

	ctx := context.Background()
	var result any
	var err error
	if tool.NeedsRoots != nil {
		result, err = tool.NeedsRoots(ctx, roots, args)
	} else {
		var idx *codefacts.Index
		idx, err = s.index(ctx, roots, opts)
		if err == nil {
			result, err = tool.Indexed(idx, args)
		}
	}
	if err != nil {
		return s.toolError(req.ID, err.Error())
	}
	blob, err := json.MarshalIndent(result, "", " ")
	if err != nil {
		return s.toolError(req.ID, err.Error())
	}
	return rpcResponse{JSONRPC: "2.0", ID: req.ID, Result: map[string]any{
		"content": []map[string]any{{"type": "text", "text": string(blob)}},
	}}
}

func (s *mcpServer) toolError(id json.RawMessage, msg string) rpcResponse {
	return rpcResponse{JSONRPC: "2.0", ID: id, Result: map[string]any{
		"isError": true,
		"content": []map[string]any{{"type": "text", "text": "error: " + msg}},
	}}
}

func (s *mcpServer) rootsFrom(args map[string]any) []string {
	if raw, ok := args["paths"].([]any); ok && len(raw) > 0 {
		var out []string
		for _, r := range raw {
			if str, ok := r.(string); ok && str != "" {
				out = append(out, str)
			}
		}
		if len(out) > 0 {
			return out
		}
	}
	return []string{s.defaultRoot}
}

func (s *mcpServer) optsFrom(args map[string]any) codefacts.BuildOptions {
	o := s.baseOpts
	if raw, ok := args["langs"].([]any); ok {
		o.Langs = toStrings(raw)
	}
	if raw, ok := args["exclude"].([]any); ok {
		o.Exclude = toStrings(raw)
	}
	if v, ok := args["include_tests"].(bool); ok {
		o.IncludeTests = v
	}
	if v, ok := args["include_generated"].(bool); ok {
		o.IncludeGen = v
	}
	return o
}

func toStrings(raw []any) []string {
	var out []string
	for _, r := range raw {
		if s, ok := r.(string); ok && s != "" {
			out = append(out, s)
		}
	}
	return out
}

// index returns a cached index for (roots, opts), building it once.
func (s *mcpServer) index(ctx context.Context, roots []string, opts codefacts.BuildOptions) (*codefacts.Index, error) {
	key := cacheKey(roots, opts)
	s.mu.Lock()
	if idx, ok := s.cache[key]; ok {
		s.mu.Unlock()
		return idx, nil
	}
	s.mu.Unlock()
	idx, err := codefacts.Build(ctx, roots, opts)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	s.cache[key] = idx
	s.mu.Unlock()
	return idx, nil
}

func cacheKey(roots []string, opts codefacts.BuildOptions) string {
	rs := append([]string(nil), roots...)
	sort.Strings(rs)
	ls := append([]string(nil), opts.Langs...)
	sort.Strings(ls)
	ex := append([]string(nil), opts.Exclude...)
	sort.Strings(ex)
	return strings.Join(rs, ",") + "|" + strings.Join(ls, ",") + "|" + strings.Join(ex, ",") +
		fmt.Sprintf("|t=%v|g=%v", opts.IncludeTests, opts.IncludeGen)
}
