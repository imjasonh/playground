"""Multi-language constant-argument analysis over tree-sitter ASTs.

The analysis indexes a source tree, records every call site and function
definition it recognizes, then reports parameters that every in-tree call
passes the same value. Such a parameter is a candidate for removal, but the
finding is only evidence: whether it is safe depends on facts (is the symbol
exported, does the name collide, is it referenced as a value) that this module
surfaces so a caller can judge.

Binding is by callee name plus arity, not by resolved symbol identity.
Tree-sitter has no name resolution or types, so same-named functions in
different scopes share a bucket. The imprecision is reported, not hidden.
"""

from __future__ import annotations

import os
import warnings
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable, Optional

warnings.filterwarnings("ignore", category=FutureWarning)

from tree_sitter_languages import get_parser  # noqa: E402


# Per-language node vocabulary. Tree-sitter grammars disagree on node names, so
# each language maps the few shapes the analysis needs: how a call names its
# callee and holds its arguments, and how a definition names itself and lists
# its parameters. Adding a language is an entry here, nothing more.
@dataclass(frozen=True)
class LangSpec:
    exts: tuple[str, ...]
    call_types: frozenset[str]
    def_types: frozenset[str]
    args_field: str = "arguments"
    func_field: str = "function"
    callee_name_on_call: Optional[str] = None  # java: name is a field of the call
    callee_name_fields: tuple[str, ...] = ()  # fields that hold the trailing name
    name_field: str = "name"
    params_field: str = "parameters"
    stop_arg_types: frozenset[str] = frozenset()  # first of these ends positional args
    exported: str = ""  # heuristic key, see is_exported


SPECS: dict[str, LangSpec] = {
    "go": LangSpec(
        exts=(".go",),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_declaration"}),
        callee_name_fields=("field",),
        params_field="parameters",
        exported="go",
    ),
    "python": LangSpec(
        exts=(".py",),
        call_types=frozenset({"call"}),
        def_types=frozenset({"function_definition"}),
        callee_name_fields=("attribute",),
        stop_arg_types=frozenset(
            {"keyword_argument", "dictionary_splat", "list_splat"}
        ),
        exported="python",
    ),
    "javascript": LangSpec(
        exts=(".js", ".jsx", ".mjs", ".cjs"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_definition"}),
        callee_name_fields=("property",),
        params_field="parameters",
        stop_arg_types=frozenset({"spread_element"}),
        exported="js",
    ),
    "typescript": LangSpec(
        exts=(".ts", ".tsx"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_definition"}),
        callee_name_fields=("property",),
        params_field="parameters",
        stop_arg_types=frozenset({"spread_element"}),
        exported="js",
    ),
    "rust": LangSpec(
        exts=(".rs",),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_item"}),
        callee_name_fields=("field", "name"),
        params_field="parameters",
        exported="rust",
    ),
    "java": LangSpec(
        exts=(".java",),
        call_types=frozenset({"method_invocation"}),
        def_types=frozenset({"method_declaration"}),
        callee_name_on_call="name",
        params_field="parameters",
        exported="java",
    ),
    "c": LangSpec(
        exts=(".c", ".h"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_definition"}),
        exported="",
    ),
    "cpp": LangSpec(
        exts=(".cc", ".cpp", ".cxx", ".hpp"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_definition"}),
        callee_name_fields=("field", "name"),
        exported="",
    ),
    "ruby": LangSpec(
        exts=(".rb",),
        call_types=frozenset({"call", "method_call", "command", "command_call"}),
        def_types=frozenset({"method", "singleton_method"}),
        callee_name_on_call="method",
        params_field="parameters",
        exported="",
    ),
}

_EXT_TO_LANG = {ext: lang for lang, spec in SPECS.items() for ext in spec.exts}
_SKIP_DIRS = {
    ".git", "node_modules", "vendor", "target", "dist", "build", ".venv",
    "venv", "__pycache__", "testdata", "DerivedData", ".pasta",
}
_IDENT_TYPES = {"identifier", "type_identifier", "field_identifier", "constant"}


def _norm(text: bytes) -> str:
    """Collapse whitespace so call-site values compare as source text."""
    return " ".join(text.decode("utf-8", "replace").split())


@dataclass
class Call:
    name: str
    args: list[str]
    kinds: list[str]  # per-arg category: literal | const | ident | expr
    path: str
    line: int


@dataclass
class Definition:
    name: str
    params: list[str]
    path: str
    line: int
    exported: Optional[bool]


@dataclass
class Index:
    calls: dict[str, list[Call]] = field(default_factory=lambda: defaultdict(list))
    defs: dict[str, list[Definition]] = field(default_factory=lambda: defaultdict(list))
    # Count of bare-identifier occurrences per name, used to estimate whether a
    # function name is also referenced as a value (callback, pointer).
    ident_uses: dict[str, int] = field(default_factory=lambda: defaultdict(int))
    files: int = 0
    langs: set[str] = field(default_factory=set)


def _trailing_name(node, spec: LangSpec) -> Optional[str]:
    """Return the name an expression ultimately calls (``pkg.Foo`` -> ``Foo``)."""
    if node is None:
        return None
    if node.type in _IDENT_TYPES:
        return node.text.decode("utf-8", "replace")
    for fname in spec.callee_name_fields:
        child = node.child_by_field_name(fname)
        if child is not None:
            got = _trailing_name(child, spec)
            if got:
                return got
    # Fall back to the last identifier among direct children.
    for child in reversed(node.named_children):
        if child.type in _IDENT_TYPES:
            return child.text.decode("utf-8", "replace")
    return None


_LITERAL_WORDS = {"true", "false", "nil", "null", "none", "undefined"}
_LITERAL_SUBSTR = (
    "literal", "string", "number", "integer", "float", "char", "boolean", "rune",
)
_QUALIFIED_TYPES = {
    "selector_expression", "scoped_identifier", "attribute", "field_expression",
    "member_expression", "qualified_identifier", "scoped_type_identifier",
}


def _classify_arg(node) -> str:
    """Category of a call argument, driving how interesting a constant is.

    A literal (``true``, ``0``, ``"x"``) that never varies is the strong
    removal signal. A bare local identifier that never varies is usually just a
    shared naming convention (every test's variable is named ``t``), not one
    value, so it ranks far lower.
    """
    t = node.type
    if t in _LITERAL_WORDS or any(s in t for s in _LITERAL_SUBSTR):
        return "literal"
    if t in _IDENT_TYPES:
        txt = node.text.decode("utf-8", "replace")
        if txt[:1].isupper() or txt.isupper():
            return "const"
        return "ident"
    if t in _QUALIFIED_TYPES:
        return "const"
    return "expr"


def _positional_args(container, spec: LangSpec) -> tuple[list[str], list[str]]:
    if container is None:
        return [], []
    texts: list[str] = []
    kinds: list[str] = []
    for child in container.named_children:
        if child.type == "comment":
            continue
        if child.type in spec.stop_arg_types:
            break  # keyword/spread: positions past here are not comparable
        texts.append(_norm(child.text))
        kinds.append(_classify_arg(child))
    return texts, kinds


def _param_names(container, spec: LangSpec) -> list[str]:
    if container is None:
        return []
    out: list[str] = []
    for i, child in enumerate(container.named_children):
        if child.type == "comment":
            continue
        name = child.child_by_field_name("name")
        if name is not None and name.type in _IDENT_TYPES:
            out.append(name.text.decode("utf-8", "replace"))
            continue
        ident = _first_ident(child)
        out.append(ident if ident else f"arg{i}")
    return out


def _first_ident(node) -> Optional[str]:
    stack = list(node.named_children)
    while stack:
        n = stack.pop(0)
        if n.type in _IDENT_TYPES:
            return n.text.decode("utf-8", "replace")
        stack.extend(n.named_children)
    return None


def _is_exported(name: str, def_node, spec: LangSpec) -> Optional[bool]:
    key = spec.exported
    if key == "go":
        return name[:1].isupper()
    if key == "python":
        return not name.startswith("_")
    if key == "rust":
        return _has_descendant_type(def_node, {"visibility_modifier"}, depth=2)
    if key == "java":
        mods = def_node.child_by_field_name("modifiers")
        if mods is None:
            for c in def_node.named_children:
                if c.type == "modifiers":
                    mods = c
                    break
        return mods is not None and "public" in mods.text.decode("utf-8", "replace")
    if key == "js":
        anc = def_node.parent
        hops = 0
        while anc is not None and hops < 4:
            if anc.type in {"export_statement", "export_specifier"}:
                return True
            anc = anc.parent
            hops += 1
        return False
    return None


def _has_descendant_type(node, types: set[str], depth: int) -> bool:
    if node is None or depth < 0:
        return False
    for c in node.named_children:
        if c.type in types:
            return True
        if _has_descendant_type(c, types, depth - 1):
            return True
    return False


def _walk_file(path: str, lang: str, src: bytes, idx: Index) -> None:
    spec = SPECS[lang]
    parser = get_parser(lang)
    tree = parser.parse(src)
    stack = [tree.root_node]
    while stack:
        node = stack.pop()
        t = node.type
        if t in spec.call_types:
            if spec.callee_name_on_call:
                name_node = node.child_by_field_name(spec.callee_name_on_call)
                name = (
                    name_node.text.decode("utf-8", "replace")
                    if name_node is not None
                    else None
                )
            else:
                name = _trailing_name(
                    node.child_by_field_name(spec.func_field), spec
                )
            if name:
                args, kinds = _positional_args(
                    node.child_by_field_name(spec.args_field), spec
                )
                idx.calls[name].append(
                    Call(name, args, kinds, path, node.start_point[0] + 1)
                )
        elif t in spec.def_types:
            name_node = node.child_by_field_name(spec.name_field)
            name = (
                name_node.text.decode("utf-8", "replace")
                if name_node is not None
                else _first_ident(node)
            )
            if name:
                params = _param_names(
                    node.child_by_field_name(spec.params_field), spec
                )
                idx.defs[name].append(
                    Definition(
                        name, params, path, node.start_point[0] + 1,
                        _is_exported(name, node, spec),
                    )
                )
        elif t in _IDENT_TYPES:
            idx.ident_uses[node.text.decode("utf-8", "replace")] += 1
        stack.extend(node.children)


def build_index(root: str, langs: Optional[Iterable[str]] = None) -> Index:
    want = set(langs) if langs else None
    idx = Index()
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for fn in filenames:
            lang = _EXT_TO_LANG.get(os.path.splitext(fn)[1])
            if lang is None or (want and lang not in want):
                continue
            full = os.path.join(dirpath, fn)
            try:
                with open(full, "rb") as fh:
                    src = fh.read()
            except OSError:
                continue
            if len(src) > 2_000_000:
                continue
            try:
                _walk_file(os.path.relpath(full, root), lang, src, idx)
            except Exception:
                continue
            idx.files += 1
            idx.langs.add(lang)
    return idx


@dataclass
class Candidate:
    name: str
    index: int
    param: Optional[str]
    value: str
    value_kind: str  # literal | const | ident | expr
    call_count: int
    exported: Optional[bool]
    def_count: int
    has_def: bool
    value_used: int  # non-call references to the name; a used-as-value estimate
    confidence: str


def _confidence(c_exported, def_count, has_def, value_used, calls) -> str:
    if not has_def:
        return "low"  # definition is outside the tree: likely external/public API
    if def_count > 1 or c_exported or value_used > 0:
        return "medium"
    if calls >= 3:
        return "high"
    return "medium"


def constant_arguments(idx: Index, min_calls: int = 2) -> list[Candidate]:
    """Report parameters every call passes one identical value."""
    out: list[Candidate] = []
    for name, calls in idx.calls.items():
        max_arity = max((len(c.args) for c in calls), default=0)
        defs = idx.defs.get(name, [])
        has_def = bool(defs)
        def_count = len(defs)
        exported = defs[0].exported if defs else None
        # References to the name that are not its own definition sites: a rough
        # signal that the symbol is also used as a value, not only called.
        value_used = max(
            idx.ident_uses.get(name, 0) - len(calls) - def_count, 0
        )
        for i in range(max_arity):
            supplying = [c for c in calls if len(c.args) > i]
            if len(supplying) < min_calls:
                continue
            values = {c.args[i] for c in supplying}
            if len(values) != 1:
                continue
            value = next(iter(values))
            kinds = {c.kinds[i] for c in supplying if i < len(c.kinds)}
            value_kind = next(iter(kinds)) if len(kinds) == 1 else "expr"
            param = None
            for d in defs:
                if i < len(d.params):
                    param = d.params[i]
                    break
            out.append(
                Candidate(
                    name=name,
                    index=i,
                    param=param,
                    value=value,
                    value_kind=value_kind,
                    call_count=len(supplying),
                    exported=exported,
                    def_count=def_count,
                    has_def=has_def,
                    value_used=value_used,
                    confidence=_confidence(
                        exported, def_count, has_def, value_used, len(supplying)
                    ),
                )
            )
    # Rank literals first, then qualified constants; bare-identifier "constants"
    # are usually naming-convention noise, so they sink to the bottom.
    kind_rank = {"literal": 0, "const": 1, "expr": 2, "ident": 3}
    conf_rank = {"high": 0, "medium": 1, "low": 2}
    out.sort(
        key=lambda c: (
            kind_rank.get(c.value_kind, 4),
            conf_rank.get(c.confidence, 3),
            -c.call_count,
        )
    )
    return out


def argument_values(idx: Index, name: str, index: int) -> dict:
    calls = idx.calls.get(name, [])
    dist: dict[str, int] = defaultdict(int)
    kinds: dict[str, str] = {}
    for c in calls:
        if len(c.args) > index:
            v = c.args[index]
            dist[v] += 1
            if index < len(c.kinds):
                kinds[v] = c.kinds[index]
    return {
        "name": name,
        "index": index,
        "call_count": len(calls),
        "supplying_count": sum(dist.values()),
        "distinct": len(dist),
        "distribution": [
            {"value": v, "count": n, "kind": kinds.get(v, "expr")}
            for v, n in sorted(dist.items(), key=lambda kv: -kv[1])
        ],
    }


def call_sites(idx: Index, name: str, limit: int = 50) -> list[dict]:
    return [
        {"path": c.path, "line": c.line, "args": c.args}
        for c in idx.calls.get(name, [])[:limit]
    ]


def symbol_info(idx: Index, name: str) -> dict:
    defs = idx.defs.get(name, [])
    calls = idx.calls.get(name, [])
    value_used = max(idx.ident_uses.get(name, 0) - len(calls) - len(defs), 0)
    return {
        "name": name,
        "has_def": bool(defs),
        "def_count": len(defs),
        "exported": defs[0].exported if defs else None,
        "call_count": len(calls),
        "value_used_estimate": value_used,
        "definitions": [
            {"path": d.path, "line": d.line, "params": d.params, "exported": d.exported}
            for d in defs[:20]
        ],
    }
