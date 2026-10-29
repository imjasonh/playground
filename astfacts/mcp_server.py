#!/usr/bin/env python3
"""MCP stdio server over the astfacts code-facts engine.

Newline-delimited JSON-RPC 2.0 (the MCP stdio transport), no third-party
dependencies beyond the tree-sitter parsers. The engine parses a tree once and
caches the index, so a session's many follow-up queries are cheap — the reason
to expose this as a server rather than reparse per CLI call.
"""

from __future__ import annotations

import json
import sys
from dataclasses import asdict, is_dataclass

import analyzer

PROTOCOL_VERSION = "2024-11-05"
_CACHE: dict[tuple, analyzer.Index] = {}


def _index(path, langs):
    key = (path, tuple(sorted(langs)) if langs else None)
    idx = _CACHE.get(key)
    if idx is None:
        print(f"[astfacts] indexing {path} (langs={langs or 'all'})", file=sys.stderr)
        idx = analyzer.build_index(path, langs)
        _CACHE[key] = idx
        print(f"[astfacts] cached: {idx.files} files, {len(idx.calls)} call names, "
              f"{len(idx.defs_by_id)} defs", file=sys.stderr)
    else:
        print(f"[astfacts] cache hit {path}", file=sys.stderr)
    return idx


def _rows(objs):
    return [asdict(o) if is_dataclass(o) else o for o in objs]


def _scope(rows, paths):
    if not paths:
        return rows
    s = set(paths)
    return [r for r in rows if not isinstance(r, dict) or "path" not in r or r["path"] in s]


# Each entry: (handler(idx_or_args) -> json-able, schema-extra-properties, requires-index)
def _h_constants(idx, a):
    cands = _rows(analyzer.constant_arguments(idx, a.get("min_calls", 2)))
    if a.get("literals_only"):
        cands = [c for c in cands if c["value_kind"] in ("literal", "const")]
    return {"count": len(cands), "candidates": _scope(cands, a.get("paths"))}


INDEXED = {
    "constant_arguments": (
        "parameters every call passes the same value (candidate for removal), "
        "with value_kind/export/collision/confidence evidence",
        {"min_calls": {"type": "integer", "default": 2},
         "literals_only": {"type": "boolean", "default": False}},
        _h_constants,
    ),
    "unused_symbols": (
        "definitions nothing in the tree references (name-based, conservative)",
        {"include_exported": {"type": "boolean", "default": True}},
        lambda idx, a: {"unused": _scope(_rows(
            analyzer.unused_symbols(idx, a.get("include_exported", True))), a.get("paths"))},
    ),
    "dead_code": (
        "transitively unreachable definitions via the call graph (DCE-lite): defs "
        "with no path from any root (entrypoint, exported, test, or value-referenced)",
        {}, lambda idx, a: {"dead_code": _scope(analyzer.dead_code(idx), a.get("paths"))},
    ),
    "unused_parameters": (
        "parameters declared but never read in the function body",
        {}, lambda idx, a: {"unused_parameters": _scope(
            analyzer.unused_parameters(idx), a.get("paths"))},
    ),
    "unreachable_code": (
        "statements after a return/throw/break/continue",
        {}, lambda idx, a: {"unreachable": _scope(
            analyzer.unreachable_code(idx), a.get("paths"))},
    ),
    "unused_imports": (
        "imports whose bound name is never used (Go, Python)",
        {}, lambda idx, a: {"unused_imports": _scope(
            analyzer.unused_imports(idx), a.get("paths"))},
    ),
    "constant_returns": (
        "functions that always return the same literal (callers can inline)",
        {}, lambda idx, a: {"constant_returns": _scope(
            analyzer.constant_returns(idx), a.get("paths"))},
    ),
    "redundant_conditions": (
        "conditions compared to a boolean literal (if x == true)",
        {}, lambda idx, a: {"redundant": _scope(
            analyzer.redundant_conditions(idx), a.get("paths"))},
    ),
    "constant_conditions": (
        "branches whose condition is a literal constant (if true / if false)",
        {}, lambda idx, a: {"conditions": _scope(
            analyzer.constant_conditions(idx), a.get("paths"))},
    ),
    "unexport_candidates": (
        "exported definitions whose every in-tree caller is in the same package dir",
        {}, lambda idx, a: {"unexport": _scope(
            analyzer.unexport_candidates(idx), a.get("paths"))},
    ),
    "duplicate_bodies": (
        "functions with identical body structure (copy-paste to dedupe)",
        {"min_size": {"type": "integer", "default": 40}},
        lambda idx, a: {"duplicates": analyzer.duplicate_bodies(idx, a.get("min_size", 40))},
    ),
    "definitions": (
        "every function/method with location, params, export status, metrics, call count",
        {"only_lang": {"type": "string"}, "exported": {"type": "boolean"}},
        lambda idx, a: {"definitions": _scope(analyzer.definitions(
            idx, a.get("only_lang"), a.get("exported")), a.get("paths"))},
    ),
    "hotspots": (
        "definitions ranked by complexity/size/fan-in (refactor targets)",
        {"by": {"type": "string", "enum": ["branches", "lines", "params", "fan_in", "depth"],
                "default": "branches"},
         "limit": {"type": "integer", "default": 25}},
        lambda idx, a: {"hotspots": analyzer.hotspots(idx, a.get("by", "branches"), a.get("limit", 25))},
    ),
    "coverage": (
        "what parsed, per language — flags a missing language mapping",
        {}, lambda idx, a: analyzer.coverage(idx),
    ),
    "report": (
        "one-shot cleanup summary across every sweep",
        {}, lambda idx, a: analyzer.report(idx),
    ),
    "references": (
        "every occurrence of a name, with call/def/value-ref breakdown",
        {"name": {"type": "string"}}, lambda idx, a: analyzer.references(idx, a["name"]),
    ),
    "impact": (
        "transitive callers of a name (what a change to it could affect)",
        {"name": {"type": "string"}}, lambda idx, a: analyzer.impact(idx, a["name"]),
    ),
    "argument_values": (
        "full value distribution for one parameter (by callee name + position)",
        {"name": {"type": "string"}, "index": {"type": "integer"}},
        lambda idx, a: analyzer.argument_values(idx, a["name"], a["index"]),
    ),
    "call_sites": (
        "locations that call a name, with qualifier/form/args",
        {"name": {"type": "string"}}, lambda idx, a: {"call_sites": analyzer.call_sites(idx, a["name"])},
    ),
    "symbol_info": (
        "definition + reachability facts for a name (export, qualifiers, unused params, const return)",
        {"name": {"type": "string"}}, lambda idx, a: analyzer.symbol_info(idx, a["name"]),
    ),
}

_NAME_REQUIRED = {"references", "impact", "argument_values", "call_sites", "symbol_info"}


def _schema(extra, needs_name_or_index):
    props = {"path": {"type": "string"},
             "langs": {"type": "array", "items": {"type": "string"}},
             "paths": {"type": "array", "items": {"type": "string"},
                       "description": "scope path-bearing findings to these files"}}
    props.update(extra)
    required = ["path"]
    for k in ("name", "index"):
        if k in extra:
            required.append(k)
    return {"type": "object", "properties": props, "required": required}


def _tool_list():
    tools = []
    for name, (desc, extra, _fn) in INDEXED.items():
        tools.append({"name": name, "description": desc, "inputSchema": _schema(extra, name)})
    tools.append({
        "name": "ast_query",
        "description": ("run a raw tree-sitter S-expression query across a tree and "
                        "return captures with file/line/snippet. The escape hatch for "
                        "any structural pattern no sweep covers."),
        "inputSchema": {"type": "object", "properties": {
            "path": {"type": "string"}, "lang": {"type": "string"},
            "query": {"type": "string"}, "limit": {"type": "integer", "default": 200}},
            "required": ["path", "lang", "query"]},
    })
    return tools


def _call_tool(name, args):
    if name == "ast_query":
        return analyzer.ast_query(args["path"], args["lang"], args["query"], args.get("limit", 200))
    entry = INDEXED.get(name)
    if entry is None:
        raise ValueError(f"unknown tool: {name}")
    _desc, _extra, fn = entry
    idx = _index(args["path"], args.get("langs"))
    return fn(idx, args)


def _handle(msg):
    method, mid = msg.get("method"), msg.get("id")
    if method == "initialize":
        return _ok(mid, {"protocolVersion": PROTOCOL_VERSION,
                         "capabilities": {"tools": {}},
                         "serverInfo": {"name": "astfacts", "version": "0.2.0"}})
    if method == "tools/list":
        return _ok(mid, {"tools": _tool_list()})
    if method == "tools/call":
        params = msg.get("params", {})
        try:
            result = _call_tool(params["name"], params.get("arguments", {}))
            return _ok(mid, {"content": [{"type": "text", "text": json.dumps(result, indent=2)}]})
        except Exception as e:
            return _ok(mid, {"content": [{"type": "text", "text": f"error: {e}"}],
                             "isError": True})
    if method == "ping":
        return _ok(mid, {})
    if method is not None and mid is None:
        return None
    return _err(mid, -32601, f"method not found: {method}")


def _ok(mid, result):
    return {"jsonrpc": "2.0", "id": mid, "result": result}


def _err(mid, code, message):
    return {"jsonrpc": "2.0", "id": mid, "error": {"code": code, "message": message}}


def main():
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        resp = _handle(msg)
        if resp is not None:
            sys.stdout.write(json.dumps(resp) + "\n")
            sys.stdout.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
