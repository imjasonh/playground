#!/usr/bin/env python3
"""Minimal MCP stdio server over the constant-argument analysis.

Speaks newline-delimited JSON-RPC 2.0 (the MCP stdio transport) with no
third-party dependencies beyond the tree-sitter parsers the analyzer uses. The
point this server makes over the CLI: it parses a tree once and keeps the index
in memory, so an agent can ask many follow-up questions in a session
(``argument_values``, ``call_sites``, ``symbol_info``) without reparsing.
"""

from __future__ import annotations

import json
import sys
from dataclasses import asdict

import analyzer

PROTOCOL_VERSION = "2024-11-05"

# Parsed indexes are cached per (root, langs) so a session's follow-up queries
# are cheap. This is the core reason to expose the analysis as a server.
_CACHE: dict[tuple, analyzer.Index] = {}


def _index(path: str, langs) -> analyzer.Index:
    key = (path, tuple(sorted(langs)) if langs else None)
    idx = _CACHE.get(key)
    if idx is None:
        print(f"[astfacts] indexing {path} (langs={langs or 'all'})", file=sys.stderr)
        idx = analyzer.build_index(path, langs)
        _CACHE[key] = idx
        print(
            f"[astfacts] cached index: {idx.files} files, "
            f"{len(idx.calls)} call names",
            file=sys.stderr,
        )
    else:
        print(f"[astfacts] cache hit for {path}", file=sys.stderr)
    return idx


TOOLS = [
    {
        "name": "constant_arguments",
        "description": (
            "List parameters that every in-tree call passes the same value, a "
            "candidate for removal. Each result carries evidence to judge it: "
            "value_kind (literal values are strong, bare identifiers are usually "
            "naming noise), whether the definition is in the tree, export status, "
            "how many definitions share the name, and a used-as-value estimate."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "root dir to analyze"},
                "min_calls": {"type": "integer", "default": 2},
                "literals_only": {"type": "boolean", "default": False},
                "langs": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["path"],
        },
    },
    {
        "name": "argument_values",
        "description": (
            "Full distribution of values passed to one parameter (by callee name "
            "and zero-based position). Reveals how lopsided a constant really is, "
            "e.g. 47x nil vs 0x anything else."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "name": {"type": "string"},
                "index": {"type": "integer"},
                "langs": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["path", "name", "index"],
        },
    },
    {
        "name": "call_sites",
        "description": "Locations that call a given name, with their arguments.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "name": {"type": "string"},
                "langs": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["path", "name"],
        },
    },
    {
        "name": "symbol_info",
        "description": (
            "Definition and reachability facts for a name: where it is defined, "
            "its params, export status, call count, and a used-as-value estimate "
            "(whether the name is referenced as a value, not only called)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "name": {"type": "string"},
                "langs": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["path", "name"],
        },
    },
]


def _call_tool(name: str, args: dict):
    langs = args.get("langs")
    path = args["path"]
    if name == "constant_arguments":
        idx = _index(path, langs)
        cands = analyzer.constant_arguments(idx, min_calls=args.get("min_calls", 2))
        if args.get("literals_only"):
            cands = [c for c in cands if c.value_kind in ("literal", "const")]
        return {"count": len(cands), "candidates": [asdict(c) for c in cands]}
    if name == "argument_values":
        return analyzer.argument_values(_index(path, langs), args["name"], args["index"])
    if name == "call_sites":
        return {"call_sites": analyzer.call_sites(_index(path, langs), args["name"])}
    if name == "symbol_info":
        return analyzer.symbol_info(_index(path, langs), args["name"])
    raise ValueError(f"unknown tool: {name}")


def _handle(msg: dict):
    method = msg.get("method")
    mid = msg.get("id")
    if method == "initialize":
        return _ok(mid, {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "astfacts", "version": "0.1.0"},
        })
    if method == "tools/list":
        return _ok(mid, {"tools": TOOLS})
    if method == "tools/call":
        params = msg.get("params", {})
        try:
            result = _call_tool(params["name"], params.get("arguments", {}))
            text = json.dumps(result, indent=2)
            return _ok(mid, {"content": [{"type": "text", "text": text}]})
        except Exception as e:  # surface tool errors as MCP tool errors
            return _ok(mid, {
                "content": [{"type": "text", "text": f"error: {e}"}],
                "isError": True,
            })
    if method == "ping":
        return _ok(mid, {})
    if method is not None and mid is None:
        return None  # a notification (e.g. notifications/initialized): no reply
    return _err(mid, -32601, f"method not found: {method}")


def _ok(mid, result):
    return {"jsonrpc": "2.0", "id": mid, "result": result}


def _err(mid, code, message):
    return {"jsonrpc": "2.0", "id": mid, "error": {"code": code, "message": message}}


def main() -> int:
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
