#!/usr/bin/env python3
"""CLI front-end for the constant-argument analysis.

Subcommands mirror the MCP tools so the same engine can be driven either way:

    astfacts.py constants <path> [--min-calls N] [--lang go,python]
    astfacts.py arg-values <path> <name> <index>
    astfacts.py call-sites <path> <name>
    astfacts.py symbol <path> <name>

Pass --json for machine-readable output.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict

import analyzer


def _langs(arg: str | None):
    return [s.strip() for s in arg.split(",")] if arg else None


def cmd_constants(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    cands = analyzer.constant_arguments(idx, min_calls=args.min_calls)
    if args.literals_only:
        cands = [c for c in cands if c.value_kind in ("literal", "const")]
    if args.json:
        print(json.dumps([asdict(c) for c in cands], indent=2))
        return 0
    print(
        f"indexed {idx.files} files across {', '.join(sorted(idx.langs)) or '(none)'}; "
        f"{len(cands)} constant-argument candidate(s)\n"
    )
    for c in cands:
        where = f"{c.param}" if c.param else f"arg{c.index}"
        exported = {True: "exported", False: "unexported", None: "export?"}[c.exported]
        tags = [exported]
        if not c.has_def:
            tags.append("no def in tree")
        if c.def_count > 1:
            tags.append(f"{c.def_count} defs share name")
        if c.value_used:
            tags.append(f"{c.value_used} value refs")
        print(
            f"[{c.confidence:^6}|{c.value_kind:^7}] {c.name}(…, {where}=…)  "
            f"always {c.value!r}  across {c.call_count} calls  "
            f"({', '.join(tags)})"
        )
    return 0


def cmd_unused(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    rows = analyzer.unused_symbols(idx, include_exported=not args.skip_exported)
    if args.json:
        print(json.dumps([asdict(u) for u in rows], indent=2))
        return 0
    print(f"{len(rows)} never-referenced definition(s)\n")
    for u in rows:
        exported = {True: "exported", False: "unexported", None: "export?"}[u.exported]
        extra = f", {u.def_count} defs share name" if u.def_count > 1 else ""
        print(
            f"[{u.confidence:^6}] {u.name}  {u.path}:{u.line}  ({u.lang}, {exported}{extra})"
        )
    return 0


def cmd_dead_branches(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    rows = analyzer.constant_conditions(idx)
    if args.json:
        print(json.dumps(rows, indent=2))
        return 0
    print(f"{len(rows)} literal-constant condition(s)\n")
    for r in rows:
        print(
            f"{r['path']}:{r['line']}  {r['construct']} (condition {r['value']!r}) "
            f"-> branch {r['effect']}  [{r['lang']}]"
        )
    return 0


def cmd_definitions(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    exported = True if args.exported else (False if args.unexported else None)
    rows = analyzer.definitions(idx, lang=args.only_lang, exported=exported)
    print(json.dumps(rows, indent=2) if args.json else
          "\n".join(f"{d['path']}:{d['line']}  {d['name']}({', '.join(d['params'])})"
                    f"  calls={d['call_count']}" for d in rows))
    return 0


def cmd_query(args) -> int:
    res = analyzer.ast_query(args.path, args.lang, args.query, limit=args.limit)
    print(json.dumps(res, indent=2))
    return 0


def cmd_arg_values(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    print(json.dumps(analyzer.argument_values(idx, args.name, args.index), indent=2))
    return 0


def cmd_call_sites(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    print(json.dumps(analyzer.call_sites(idx, args.name), indent=2))
    return 0


def cmd_symbol(args) -> int:
    idx = analyzer.build_index(args.path, _langs(args.lang))
    print(json.dumps(analyzer.symbol_info(idx, args.name), indent=2))
    return 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lang", help="comma-separated languages to include")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("constants", help="list constant-argument candidates")
    c.add_argument("path")
    c.add_argument("--min-calls", type=int, default=2)
    c.add_argument(
        "--literals-only",
        action="store_true",
        help="keep only literal/qualified-constant values (drop bare-ident noise)",
    )
    c.set_defaults(fn=cmd_constants)

    u = sub.add_parser("unused", help="definitions nothing in the tree references")
    u.add_argument("path")
    u.add_argument("--skip-exported", action="store_true")
    u.set_defaults(fn=cmd_unused)

    d = sub.add_parser("dead-branches", help="branches with a literal constant condition")
    d.add_argument("path")
    d.set_defaults(fn=cmd_dead_branches)

    df = sub.add_parser("definitions", help="list recognized function/method definitions")
    df.add_argument("path")
    df.add_argument("--only-lang", help="restrict to one language")
    df.add_argument("--exported", action="store_true")
    df.add_argument("--unexported", action="store_true")
    df.set_defaults(fn=cmd_definitions)

    q = sub.add_parser("query", help="run a raw tree-sitter S-expression query")
    q.add_argument("path")
    q.add_argument("lang")
    q.add_argument("query")
    q.add_argument("--limit", type=int, default=200)
    q.set_defaults(fn=cmd_query)

    a = sub.add_parser("arg-values", help="value distribution for one parameter")
    a.add_argument("path")
    a.add_argument("name")
    a.add_argument("index", type=int)
    a.set_defaults(fn=cmd_arg_values)

    s = sub.add_parser("call-sites", help="locations that call a name")
    s.add_argument("path")
    s.add_argument("name")
    s.set_defaults(fn=cmd_call_sites)

    y = sub.add_parser("symbol", help="definition + reachability facts for a name")
    y.add_argument("path")
    y.add_argument("name")
    y.set_defaults(fn=cmd_symbol)

    args = p.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
