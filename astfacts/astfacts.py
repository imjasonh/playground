#!/usr/bin/env python3
"""CLI front-end for the astfacts code-facts engine.

Sweeps (cleanup candidates), each with evidence to judge it:

    constants       parameters every call passes the same value
    unused          definitions nothing in the tree references
    dead-code       transitively unreachable definitions (call-graph DCE)
    unused-params   parameters never read in the body
    unreachable     statements after a return/throw/break
    unused-imports  imports never used (Go, Python)
    const-returns   functions that always return the same literal
    redundant       conditions compared to a boolean literal
    unexport        exported defs whose callers are all in-package
    duplicates      functions with identical body structure
    dead-branches   conditions that are a literal constant

Facts (compose your own cleanup):

    definitions     every function/method, with metrics
    references      every occurrence of a name
    impact          transitive callers of a name
    hotspots        defs ranked by complexity/size/fan-in
    coverage        what parsed, per language
    report          one-shot summary across every sweep
    symbol          definition + reachability facts for a name
    arg-values      value distribution for one parameter
    call-sites      locations that call a name
    query           raw tree-sitter S-expression query

Scope any path-bearing output to a changeset with --changed or --paths.
Add --json for machine-readable output.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import asdict, is_dataclass

import analyzer


def _langs(arg):
    return [s.strip() for s in arg.split(",")] if arg else None


def _rows(objs):
    return [asdict(o) if is_dataclass(o) else o for o in objs]


def _scope(args, path) -> set | None:
    if args.paths:
        return {p.strip() for p in args.paths.split(",")}
    if args.changed:
        try:
            out = subprocess.run(
                ["git", "-C", path, "diff", "--name-only", "HEAD"],
                capture_output=True, text=True, check=True,
            ).stdout
            base = subprocess.run(
                ["git", "-C", path, "rev-parse", "--show-prefix"],
                capture_output=True, text=True, check=True,
            ).stdout.strip()
            names = [ln[len(base):] if base and ln.startswith(base) else ln
                     for ln in out.split("\n") if ln.strip()]
            return set(names)
        except Exception as e:
            print(f"warning: --changed failed: {e}", file=sys.stderr)
            return None
    return None


def _emit(args, rows, path, title=None):
    rows = _rows(rows)
    scope = _scope(args, path)
    if scope is not None:
        rows = [r for r in rows if "path" not in r or r["path"] in scope]
    if args.json or not title:
        print(json.dumps(rows, indent=2))
        return 0
    print(f"{len(rows)} {title}\n")
    for r in rows:
        print(json.dumps(r))
    return 0


def _idx(args):
    return analyzer.build_index(args.path, _langs(args.lang))


def cmd_constants(args):
    cands = _rows(analyzer.constant_arguments(_idx(args), min_calls=args.min_calls))
    if args.literals_only:
        cands = [c for c in cands if c["value_kind"] in ("literal", "const")]
    if args.json:
        print(json.dumps(cands, indent=2)); return 0
    print(f"{len(cands)} constant-argument candidate(s)\n")
    for c in cands:
        where = c["param"] or f"arg{c['index']}"
        exp = {True: "exported", False: "unexported", None: "export?"}[c["exported"]]
        tags = [exp]
        if not c["has_def"]:
            tags.append("no def in tree")
        if c["def_count"] > 1:
            tags.append(f"{c['def_count']} defs share name")
        if c["value_used"]:
            tags.append(f"{c['value_used']} value refs")
        print(f"[{c['confidence']:^6}|{c['value_kind']:^7}] {c['name']}(…, {where}=…)  "
              f"always {c['value']!r}  x{c['call_count']}  ({', '.join(tags)})")
    return 0


def cmd_unused(args):
    rows = _rows(analyzer.unused_symbols(_idx(args), include_exported=not args.skip_exported))
    scope = _scope(args, args.path)
    if scope is not None:
        rows = [r for r in rows if r["path"] in scope]
    if args.json:
        print(json.dumps(rows, indent=2)); return 0
    print(f"{len(rows)} never-referenced definition(s)\n")
    for u in rows:
        exp = {True: "exported", False: "unexported", None: "export?"}[u["exported"]]
        extra = f", {u['def_count']} defs share name" if u["def_count"] > 1 else ""
        print(f"[{u['confidence']:^6}] {u['name']}  {u['path']}:{u['line']}-{u['end_line']}"
              f"  ({u['lang']}, {exp}{extra})")
    return 0


def cmd_report(args):
    print(json.dumps(analyzer.report(_idx(args)), indent=2)); return 0


def main(argv):
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--lang", help="comma-separated languages to include")
    p.add_argument("--json", action="store_true")
    p.add_argument("--changed", action="store_true", help="scope to git-changed files")
    p.add_argument("--paths", help="comma-separated paths to scope output to")
    sub = p.add_subparsers(dest="cmd", required=True)

    def simple(name, fn, title, help):
        s = sub.add_parser(name, help=help)
        s.add_argument("path")
        s.set_defaults(fn=lambda a, _fn=fn, _t=title: _emit(a, _fn(_idx(a)), a.path, _t))
        return s

    c = sub.add_parser("constants", help="parameters every call passes the same value")
    c.add_argument("path"); c.add_argument("--min-calls", type=int, default=2)
    c.add_argument("--literals-only", action="store_true")
    c.set_defaults(fn=cmd_constants)

    u = sub.add_parser("unused", help="definitions nothing references")
    u.add_argument("path"); u.add_argument("--skip-exported", action="store_true")
    u.set_defaults(fn=cmd_unused)

    simple("dead-code", analyzer.dead_code, "transitively dead definition(s)",
           "transitively unreachable definitions")
    simple("unused-params", analyzer.unused_parameters, "unused parameter(s)",
           "parameters never read in the body")
    simple("unreachable", analyzer.unreachable_code, "unreachable statement(s)",
           "statements after a terminator")
    simple("unused-imports", analyzer.unused_imports, "unused import(s)",
           "imports never used (Go, Python)")
    simple("const-returns", analyzer.constant_returns, "constant-return function(s)",
           "functions that always return the same literal")
    simple("redundant", analyzer.redundant_conditions, "redundant condition(s)",
           "conditions compared to a boolean literal")
    simple("unexport", analyzer.unexport_candidates, "unexport candidate(s)",
           "exported defs whose callers are all in-package")
    simple("duplicates", analyzer.duplicate_bodies, "duplicate body group(s)",
           "functions with identical body structure")
    simple("dead-branches", analyzer.constant_conditions, "literal-constant condition(s)",
           "branches with a literal condition")

    r = sub.add_parser("report", help="one-shot summary across every sweep")
    r.add_argument("path"); r.set_defaults(fn=cmd_report)

    cov = sub.add_parser("coverage", help="what parsed, per language")
    cov.add_argument("path")
    cov.set_defaults(fn=lambda a: print(json.dumps(analyzer.coverage(_idx(a)), indent=2)))

    df = sub.add_parser("definitions", help="list definitions with metrics")
    df.add_argument("path"); df.add_argument("--only-lang")
    df.add_argument("--exported", action="store_true")
    df.add_argument("--unexported", action="store_true")
    df.set_defaults(fn=lambda a: _emit(
        a, analyzer.definitions(_idx(a), a.only_lang,
                                True if a.exported else (False if a.unexported else None)),
        a.path))

    hs = sub.add_parser("hotspots", help="defs ranked by complexity/size/fan-in")
    hs.add_argument("path")
    hs.add_argument("--by", default="branches",
                    choices=["branches", "lines", "params", "fan_in", "depth"])
    hs.add_argument("--limit", type=int, default=25)
    hs.set_defaults(fn=lambda a: print(json.dumps(
        analyzer.hotspots(_idx(a), a.by, a.limit), indent=2)))

    for nm, fn in (("references", analyzer.references), ("impact", analyzer.impact),
                   ("symbol", analyzer.symbol_info)):
        s = sub.add_parser(nm, help=f"{nm} for a name")
        s.add_argument("path"); s.add_argument("name")
        s.set_defaults(fn=lambda a, _fn=fn: print(json.dumps(_fn(_idx(a), a.name), indent=2)))

    s = sub.add_parser("call-sites", help="locations that call a name")
    s.add_argument("path"); s.add_argument("name")
    s.set_defaults(fn=lambda a: print(json.dumps(analyzer.call_sites(_idx(a), a.name), indent=2)))

    av = sub.add_parser("arg-values", help="value distribution for one parameter")
    av.add_argument("path"); av.add_argument("name"); av.add_argument("index", type=int)
    av.set_defaults(fn=lambda a: print(json.dumps(
        analyzer.argument_values(_idx(a), a.name, a.index), indent=2)))

    q = sub.add_parser("query", help="raw tree-sitter S-expression query")
    q.add_argument("path"); q.add_argument("qlang"); q.add_argument("query")
    q.add_argument("--limit", type=int, default=200)
    q.set_defaults(fn=lambda a: print(json.dumps(
        analyzer.ast_query(a.path, a.qlang, a.query, a.limit), indent=2)))

    args = p.parse_args(argv)
    rv = args.fn(args)
    return rv if isinstance(rv, int) else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
