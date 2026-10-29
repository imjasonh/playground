"""Multi-language code-facts engine over tree-sitter ASTs.

A substrate for agents doing cleanup and refactoring: it indexes a source tree
into a call graph plus a symbol/reference index, then answers composable fact
queries (definitions, references, impact) and runs cleanup sweeps (unused code,
constant arguments, dead branches, and more). Findings carry evidence — export
status, call-graph reachability, name collisions, confidence — so a caller
judges rather than trusts.

Binding is by callee name (with a recorded qualifier) and arity, not by resolved
symbol identity: tree-sitter has no name resolution or types. The imprecision is
reported, never hidden.
"""

from __future__ import annotations

import hashlib
import os
import re
import sys
import warnings
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable, Optional

warnings.filterwarnings("ignore", category=FutureWarning)

from tree_sitter_languages import get_parser  # noqa: E402

sys.setrecursionlimit(30000)


@dataclass(frozen=True)
class LangSpec:
    exts: tuple[str, ...]
    call_types: frozenset[str]
    def_types: frozenset[str]
    args_field: str = "arguments"
    func_field: str = "function"
    callee_name_on_call: Optional[str] = None  # java/ruby: name is a field of the call
    callee_name_fields: tuple[str, ...] = ()
    name_field: str = "name"
    params_field: str = "parameters"
    body_field: str = "body"
    stop_arg_types: frozenset[str] = frozenset()
    exported: str = ""
    cond_types: frozenset[str] = frozenset()
    cond_field: str = "condition"
    import_types: frozenset[str] = frozenset()  # drives unused-import detection
    self_params: frozenset[str] = frozenset({"self", "this", "cls", "_"})


SPECS: dict[str, LangSpec] = {
    "go": LangSpec(
        exts=(".go",),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_declaration"}),
        callee_name_fields=("field",),
        exported="go",
        cond_types=frozenset({"if_statement"}),
        import_types=frozenset({"import_declaration"}),
    ),
    "python": LangSpec(
        exts=(".py",),
        call_types=frozenset({"call"}),
        def_types=frozenset({"function_definition"}),
        callee_name_fields=("attribute",),
        stop_arg_types=frozenset({"keyword_argument", "dictionary_splat", "list_splat"}),
        exported="python",
        cond_types=frozenset({"if_statement", "elif_clause"}),
        import_types=frozenset({"import_statement", "import_from_statement"}),
    ),
    "javascript": LangSpec(
        exts=(".js", ".jsx", ".mjs", ".cjs"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_definition"}),
        callee_name_fields=("property",),
        stop_arg_types=frozenset({"spread_element"}),
        exported="js",
        cond_types=frozenset({"if_statement"}),
    ),
    "typescript": LangSpec(
        exts=(".ts", ".tsx"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration", "method_definition"}),
        callee_name_fields=("property",),
        stop_arg_types=frozenset({"spread_element"}),
        exported="js",
        cond_types=frozenset({"if_statement"}),
    ),
    "rust": LangSpec(
        exts=(".rs",),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_item"}),
        callee_name_fields=("field", "name"),
        exported="rust",
        cond_types=frozenset({"if_expression"}),
    ),
    "java": LangSpec(
        exts=(".java",),
        call_types=frozenset({"method_invocation"}),
        def_types=frozenset({"method_declaration"}),
        callee_name_on_call="name",
        exported="java",
        cond_types=frozenset({"if_statement"}),
    ),
    "c": LangSpec(
        exts=(".c", ".h"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_definition"}),
        cond_types=frozenset({"if_statement"}),
    ),
    "cpp": LangSpec(
        exts=(".cc", ".cpp", ".cxx", ".hpp"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_definition"}),
        callee_name_fields=("field", "name"),
        cond_types=frozenset({"if_statement"}),
    ),
    "ruby": LangSpec(
        exts=(".rb",),
        call_types=frozenset({"call", "method_call", "command", "command_call"}),
        def_types=frozenset({"method", "singleton_method"}),
        callee_name_on_call="method",
        cond_types=frozenset({"if"}),
    ),
    "php": LangSpec(
        exts=(".php",),
        call_types=frozenset({"function_call_expression", "member_call_expression",
                              "scoped_call_expression"}),
        def_types=frozenset({"function_definition", "method_declaration"}),
        callee_name_fields=("name",),
        cond_types=frozenset({"if_statement"}),
    ),
    "kotlin": LangSpec(
        exts=(".kt", ".kts"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_declaration"}),
        cond_types=frozenset({"if_expression"}),
    ),
    "c_sharp": LangSpec(
        exts=(".cs",),
        call_types=frozenset({"invocation_expression"}),
        def_types=frozenset({"method_declaration", "local_function_statement"}),
        callee_name_fields=("name",),
        cond_types=frozenset({"if_statement"}),
    ),
    "scala": LangSpec(
        exts=(".scala", ".sc"),
        call_types=frozenset({"call_expression"}),
        def_types=frozenset({"function_definition"}),
        cond_types=frozenset({"if_expression"}),
    ),
}

_EXT_TO_LANG = {ext: lang for lang, spec in SPECS.items() for ext in spec.exts}
_SKIP_DIRS = {
    ".git", "node_modules", "vendor", "target", "dist", "build", ".venv",
    "venv", "__pycache__", "testdata", "DerivedData", ".pasta",
}
_IDENT_TYPES = {"identifier", "type_identifier", "field_identifier", "constant",
                "simple_identifier", "shorthand_property_identifier"}
_LITERAL_WORDS = {"true", "false", "nil", "null", "none", "undefined"}
_STRING_TYPES = {
    "string", "string_literal", "interpreted_string_literal", "raw_string_literal",
    "string_content", "string_fragment", "quoted_string", "char_literal",
    "verbatim_string_literal",
}
_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
# Ancestors that make a function a method (dynamically dispatched; name-based
# "unused" is unreliable). Go/Java/C#/Ruby already use method-named node types.
_METHOD_CONTAINERS = {
    "impl_item", "trait_item", "class_body", "class_definition",
    "class_declaration", "class_specifier", "struct_specifier",
    "object_declaration", "interface_declaration", "interface_body",
    "trait_declaration", "object_definition", "template", "protocol_declaration",
}
_LITERAL_SUBSTR = ("literal", "string", "number", "integer", "float", "char", "boolean", "rune")
_QUALIFIED_TYPES = {
    "selector_expression", "scoped_identifier", "attribute", "field_expression",
    "member_expression", "qualified_identifier", "scoped_type_identifier",
}
_QUALIFIER_FIELDS = ("operand", "object", "value", "path", "receiver")
_PAREN_TYPES = {"parenthesized_expression", "parenthesized"}
_BLOCK_TYPES = {"block", "statement_block", "suite", "compound_statement"}
_TERMINATORS = {
    "return_statement", "raise_statement", "throw_statement", "break_statement",
    "continue_statement", "return_expression", "goto_statement",
}
_RETURN_TYPES = {"return_statement", "return_expression"}
_BRANCH_HINTS = ("if", "for", "while", "case", "catch", "switch", "when", "and", "or")
_ENTRYPOINTS = {"main", "init", "__init__", "__main__", "setUp", "tearDown", "TestMain"}
_TEST_PREFIX = ("Test", "Benchmark", "Example", "Fuzz", "test_")


def _norm(text: bytes) -> str:
    return " ".join(text.decode("utf-8", "replace").split())


def _canon_value(text: str) -> str:
    """Light value canonicalization so trivially-equal literals compare equal."""
    low = text.lower()
    if low in {"null", "none", "nil"}:
        return "nil"
    return text


def _classify_arg(node) -> str:
    t = node.type
    if t in _LITERAL_WORDS or any(s in t for s in _LITERAL_SUBSTR):
        return "literal"
    if t in _IDENT_TYPES:
        txt = node.text.decode("utf-8", "replace")
        if txt in _LITERAL_WORDS:
            return "literal"
        if txt[:1].isupper() or txt.isupper():
            return "const"
        return "ident"
    if t in _QUALIFIED_TYPES:
        return "const"
    return "expr"


@dataclass
class Call:
    name: str
    qualifier: Optional[str]
    form: str  # free | qualified
    args: list[str]
    kinds: list[str]
    path: str
    line: int
    lang: str
    caller_id: Optional[int]


@dataclass
class Definition:
    id: int
    name: str
    params: list[str]
    unused_params: list[str]
    path: str
    line: int
    end_line: int
    start_byte: int
    end_byte: int
    exported: Optional[bool]
    lang: str
    directory: str
    branches: int  # cyclomatic proxy
    depth: int  # max body nesting
    lines: int
    body_hash: str
    body_size: int
    const_return: Optional[str]  # literal every return yields, else None
    runtime_root: bool = False  # invoked by a runtime/test harness, not by name
    is_method: bool = False  # methods are often dynamically dispatched


@dataclass
class DeadBranch:
    construct: str
    value: str
    always: bool
    path: str
    line: int
    lang: str


@dataclass
class Unreachable:
    path: str
    line: int
    lang: str
    after: str  # the terminating statement type


@dataclass
class UnusedImport:
    name: str
    path: str
    line: int
    lang: str
    statement: str


@dataclass
class Redundant:
    path: str
    line: int
    lang: str
    snippet: str
    kind: str


@dataclass
class Index:
    calls: dict[str, list[Call]] = field(default_factory=lambda: defaultdict(list))
    defs: dict[str, list[Definition]] = field(default_factory=lambda: defaultdict(list))
    defs_by_id: dict[int, Definition] = field(default_factory=dict)
    ident_uses: dict[str, int] = field(default_factory=lambda: defaultdict(int))
    ident_sites: dict[str, list[tuple[str, int]]] = field(
        default_factory=lambda: defaultdict(list))
    call_edges: dict[int, set[str]] = field(default_factory=lambda: defaultdict(set))
    toplevel_called: set[str] = field(default_factory=set)
    dead: list[DeadBranch] = field(default_factory=list)
    unreachable: list[Unreachable] = field(default_factory=list)
    unused_imports: list[UnusedImport] = field(default_factory=list)
    redundant: list[Redundant] = field(default_factory=list)
    suppressed: dict[str, set[int]] = field(default_factory=dict)
    string_refs: set[str] = field(default_factory=set)
    files: int = 0
    file_count_by_lang: dict[str, int] = field(default_factory=lambda: defaultdict(int))
    langs: set[str] = field(default_factory=set)
    _next_id: int = 0


_IDENT_SITE_CAP = 400


def _trailing_name(node, spec: LangSpec) -> Optional[str]:
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
    for child in reversed(node.named_children):
        if child.type in _IDENT_TYPES:
            return child.text.decode("utf-8", "replace")
    return None


def _qualifier(func_node) -> Optional[str]:
    for f in _QUALIFIER_FIELDS:
        c = func_node.child_by_field_name(f)
        if c is not None:
            return _norm(c.text)
    return None


def _const_condition(node) -> Optional[tuple[str, bool]]:
    if node is None:
        return None
    while node.type in _PAREN_TYPES and len(node.named_children) == 1:
        node = node.named_children[0]
    txt = node.text.decode("utf-8", "replace").strip()
    low = txt.lower()
    if low == "true":
        return "true", True
    if low == "false":
        return "false", False
    if txt == "1":
        return "1", True
    if txt == "0":
        return "0", False
    return None


_REDUNDANT_RE = re.compile(r"[!=]=\s*(true|false|True|False)\b")


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
        return _has_descendant_type(def_node, {"visibility_modifier"}, 2)
    if key == "java":
        for c in def_node.named_children:
            if c.type == "modifiers":
                return "public" in c.text.decode("utf-8", "replace")
        return False
    if key == "js":
        anc, hops = def_node.parent, 0
        while anc is not None and hops < 4:
            if anc.type in {"export_statement", "export_specifier"}:
                return True
            anc, hops = anc.parent, hops + 1
        return False
    return None


def _has_descendant_type(node, types: set[str], depth: int) -> bool:
    if node is None or depth < 0:
        return False
    for c in node.named_children:
        if c.type in types or _has_descendant_type(c, types, depth - 1):
            return True
    return False


@dataclass
class _BodyFacts:
    idents: set
    returns: list  # (text, is_literal)
    branches: int
    depth: int
    node_count: int
    type_hash: str


def _analyze_body(body) -> _BodyFacts:
    """One pass over a function body collecting the facts several sweeps need."""
    idents: set = set()
    returns: list = []
    branches = 0
    node_count = 0
    seq: list[str] = []
    max_depth = 0

    def rec(node, depth):
        nonlocal branches, node_count, max_depth
        node_count += 1
        max_depth = max(max_depth, depth)
        t = node.type
        seq.append(t)
        if t in _IDENT_TYPES:
            idents.add(node.text.decode("utf-8", "replace"))
        if any(h in t for h in _BRANCH_HINTS) and (
            "statement" in t or "expression" in t or "clause" in t or t.endswith("_when")
        ):
            branches += 1
        if t in _RETURN_TYPES:
            val = None
            for c in node.named_children:
                if c.type != "comment":
                    val = c
                    break
            # Go wraps the returned value in a single-element expression_list.
            if val is not None and val.type == "expression_list" and \
                    len(val.named_children) == 1:
                val = val.named_children[0]
            if val is not None:
                returns.append((_norm(val.text), _classify_arg(val) == "literal"))
            else:
                returns.append(("", False))
        for c in node.children:
            rec(c, depth + 1)

    if body is not None:
        rec(body, 0)
    type_hash = hashlib.blake2b(
        "\x1f".join(seq).encode("utf-8"), digest_size=12
    ).hexdigest()
    return _BodyFacts(idents, returns, branches, max_depth, node_count, type_hash)


def _const_return(returns) -> Optional[str]:
    lit = [v for v, is_lit in returns if is_lit]
    if lit and len(lit) == len(returns) and len(set(map(_canon_value, lit))) == 1:
        return lit[0]
    return None


def _import_bindings(node, lang: str):
    """(bound-name, statement-text) pairs an import introduces, for Go/Python."""
    text = _norm(node.text)
    out = []
    if lang == "go":
        for spec in _descendants(node, {"import_spec"}):
            alias = spec.child_by_field_name("name")
            path = spec.child_by_field_name("path")
            if path is None:
                continue
            raw = path.text.decode("utf-8", "replace").strip('"')
            if alias is not None:
                bound = alias.text.decode("utf-8", "replace")
            else:
                bound = raw.rsplit("/", 1)[-1]
            if bound in {"_", "."}:
                continue
            out.append((bound, f'import "{raw}"'))
    elif lang == "python":
        if node.type == "import_from_statement":
            names = [c for c in node.named_children if c.type in {"dotted_name", "aliased_import"}]
            # first dotted_name is the module; the rest are imports
            for c in node.named_children:
                if c.type == "aliased_import":
                    alias = c.child_by_field_name("alias")
                    nm = c.child_by_field_name("name")
                    if alias is not None:
                        out.append((alias.text.decode(), text))
                    elif nm is not None:
                        out.append((nm.text.decode().split(".")[0], text))
                elif c.type == "dotted_name" and c is not names[0]:
                    out.append((c.text.decode().split(".")[-1], text))
        else:  # import_statement
            for c in node.named_children:
                if c.type == "aliased_import":
                    alias = c.child_by_field_name("alias")
                    if alias is not None:
                        out.append((alias.text.decode(), text))
                elif c.type == "dotted_name":
                    out.append((c.text.decode().split(".")[0], text))
    return out


def _descendants(node, types: set[str]):
    out = []
    stack = [node]
    while stack:
        n = stack.pop()
        if n.type in types:
            out.append(n)
        stack.extend(n.children)
    return out


def _walk_file(path: str, lang: str, src: bytes, idx: Index) -> None:
    spec = SPECS[lang]
    parser = get_parser(lang)
    tree = parser.parse(src)
    directory = os.path.dirname(path)
    file_idents: set = set()
    file_imports: list = []

    if b"astfacts:ignore" in src:
        lines = {
            i + 1 for i, ln in enumerate(src.split(b"\n"))
            if b"astfacts:ignore" in ln
        }
        if lines:
            idx.suppressed.setdefault(path, set()).update(lines)

    def _in_method_container(node) -> bool:
        p, hops = node.parent, 0
        while p is not None and hops < 8:
            if p.type in _METHOD_CONTAINERS:
                return True
            p, hops = p.parent, hops + 1
        return False

    def _runtime_root(node, name) -> bool:
        if name in _ENTRYPOINTS or name.startswith(_TEST_PREFIX):
            return True
        # Rust/attribute test functions: #[test], #[tokio::test], #[rstest], ...
        prev = node.prev_sibling
        hops = 0
        while prev is not None and hops < 6:
            if prev.type in {"attribute_item", "attribute", "attribute_list",
                             "annotation", "marker_annotation"}:
                txt = prev.text.decode("utf-8", "replace").lower()
                if "test" in txt or "bench" in txt:
                    return True
            elif prev.type not in {"line_comment", "block_comment", "comment"}:
                break
            prev, hops = prev.prev_sibling, hops + 1
        return False

    def new_def(node) -> Definition:
        name_node = node.child_by_field_name(spec.name_field)
        name = (name_node.text.decode("utf-8", "replace") if name_node is not None
                else _first_ident(node) or "?")
        params = _param_names(node.child_by_field_name(spec.params_field), spec)
        body = node.child_by_field_name(spec.body_field)
        bf = _analyze_body(body)
        unused = [
            p for p in params
            if p not in bf.idents and p not in spec.self_params and not p.startswith("arg")
        ]
        did = idx._next_id
        idx._next_id += 1
        d = Definition(
            id=did, name=name, params=params, unused_params=unused, path=path,
            line=node.start_point[0] + 1, end_line=node.end_point[0] + 1,
            start_byte=node.start_byte, end_byte=node.end_byte,
            exported=_is_exported(name, node, spec), lang=lang, directory=directory,
            branches=bf.branches + 1, depth=bf.depth,
            lines=node.end_point[0] - node.start_point[0] + 1,
            body_hash=bf.type_hash, body_size=bf.node_count,
            const_return=_const_return(bf.returns),
            runtime_root=_runtime_root(node, name),
            is_method="method" in node.type or _in_method_container(node),
        )
        idx.defs[name].append(d)
        idx.defs_by_id[did] = d
        return d

    def record_call(node, caller_id):
        if spec.callee_name_on_call:
            nn = node.child_by_field_name(spec.callee_name_on_call)
            name = nn.text.decode("utf-8", "replace") if nn is not None else None
            obj = node.child_by_field_name("object")
            qualifier = _norm(obj.text) if obj is not None else None
        else:
            func = node.child_by_field_name(spec.func_field)
            if func is None:
                return
            if func.type in _IDENT_TYPES:
                name, qualifier = func.text.decode("utf-8", "replace"), None
            else:
                name, qualifier = _trailing_name(func, spec), _qualifier(func)
        if not name:
            return
        args, kinds = [], []
        container = node.child_by_field_name(spec.args_field)
        if container is not None:
            for child in container.named_children:
                if child.type == "comment":
                    continue
                if child.type in spec.stop_arg_types:
                    break
                args.append(_norm(child.text))
                kinds.append(_classify_arg(child))
        idx.calls[name].append(Call(
            name, qualifier, "qualified" if qualifier else "free",
            args, kinds, path, node.start_point[0] + 1, lang, caller_id,
        ))
        if caller_id is None:
            idx.toplevel_called.add(name)
        else:
            idx.call_edges[caller_id].add(name)

    def check_block(node):
        stmts = [c for c in node.named_children if c.type != "comment"]
        for i, s in enumerate(stmts[:-1]):
            if s.type in _TERMINATORS:
                nxt = stmts[i + 1]
                idx.unreachable.append(
                    Unreachable(path, nxt.start_point[0] + 1, lang, s.type)
                )
                break

    def visit(node, caller_id):
        t = node.type
        if t in spec.import_types:
            file_imports.extend(
                (b, stmt, node.start_point[0] + 1) for b, stmt in _import_bindings(node, lang)
            )
            return  # don't count import-internal idents as uses
        if t in spec.def_types:
            d = new_def(node)
            for c in node.children:
                visit(c, d.id)
            return
        if t in spec.call_types:
            record_call(node, caller_id)
            for c in node.children:
                visit(c, caller_id)
            return
        if t in spec.cond_types:
            verdict = _const_condition(node.child_by_field_name(spec.cond_field))
            if verdict is not None:
                idx.dead.append(DeadBranch(
                    t, verdict[0], verdict[1], path, node.start_point[0] + 1, lang))
        elif t in _BLOCK_TYPES:
            check_block(node)
        elif t in _IDENT_TYPES:
            nm = node.text.decode("utf-8", "replace")
            idx.ident_uses[nm] += 1
            file_idents.add(nm)
            sites = idx.ident_sites[nm]
            if len(sites) < _IDENT_SITE_CAP:
                sites.append((path, node.start_point[0] + 1))
        elif t in _STRING_TYPES:
            # A bareword string ("default_poll_secs") is how serde defaults, DI,
            # reflection, and test registries reference a function by name. Treat
            # such names as referenced so we do not flag them unused.
            inner = node.text.decode("utf-8", "replace").strip().strip("\"'`")
            if _IDENT_RE.match(inner):
                idx.string_refs.add(inner)
        if ("binary" in t or t == "comparison_operator") and _REDUNDANT_RE.search(
            node.text.decode("utf-8", "replace")
        ):
            idx.redundant.append(Redundant(
                path, node.start_point[0] + 1, lang,
                _norm(node.text)[:120], "compare-to-boolean-literal"))
        for c in node.children:
            visit(c, caller_id)

    visit(tree.root_node, None)

    # Unused imports: a bound name that never appears as an identifier in code.
    # file_idents is the exact per-file identifier set, so this is reliable even
    # for very common package names.
    for bound, stmt, line in file_imports:
        if bound not in file_idents:
            idx.unused_imports.append(UnusedImport(bound, path, line, lang, stmt))


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
            idx.file_count_by_lang[lang] += 1
            idx.langs.add(lang)
    return idx


def _suppressed(idx: Index, path: str, line: int) -> bool:
    s = idx.suppressed.get(path)
    return bool(s and line in s)


# --------------------------------------------------------------------------
# Fact queries
# --------------------------------------------------------------------------


def _value_refs(idx: Index, name: str) -> int:
    return max(idx.ident_uses.get(name, 0) - len(idx.calls.get(name, [])) -
               len(idx.defs.get(name, [])), 0)


@dataclass
class Candidate:
    name: str
    index: int
    param: Optional[str]
    value: str
    value_kind: str
    call_count: int
    distinct_qualifiers: int
    exported: Optional[bool]
    def_count: int
    has_def: bool
    value_used: int
    confidence: str


def constant_arguments(idx: Index, min_calls: int = 2) -> list[Candidate]:
    out: list[Candidate] = []
    for name, calls in idx.calls.items():
        max_arity = max((len(c.args) for c in calls), default=0)
        defs = idx.defs.get(name, [])
        exported = defs[0].exported if defs else None
        value_used = _value_refs(idx, name)
        for i in range(max_arity):
            supplying = [c for c in calls if len(c.args) > i]
            if len(supplying) < min_calls:
                continue
            values = {_canon_value(c.args[i]) for c in supplying}
            if len(values) != 1:
                continue
            d0 = supplying[0]
            if _suppressed(idx, d0.path, d0.line):
                continue
            kinds = {c.kinds[i] for c in supplying if i < len(c.kinds)}
            value_kind = next(iter(kinds)) if len(kinds) == 1 else "expr"
            quals = {c.qualifier for c in supplying}
            param = next((d.params[i] for d in defs if i < len(d.params)), None)
            out.append(Candidate(
                name, i, param, supplying[0].args[i], value_kind, len(supplying),
                len([q for q in quals if q is not None]) or (0 if None in quals else 0),
                exported, len(defs), bool(defs), value_used,
                _conf_const(exported, len(defs), bool(defs), value_used, len(supplying)),
            ))
    kind_rank = {"literal": 0, "const": 1, "expr": 2, "ident": 3}
    conf_rank = {"high": 0, "medium": 1, "low": 2}
    out.sort(key=lambda c: (kind_rank.get(c.value_kind, 4),
                            conf_rank.get(c.confidence, 3), -c.call_count))
    return out


def _conf_const(exported, def_count, has_def, value_used, calls) -> str:
    if not has_def:
        return "low"
    if def_count > 1 or exported or value_used > 0:
        return "medium"
    return "high" if calls >= 3 else "medium"


@dataclass
class Unused:
    name: str
    path: str
    line: int
    end_line: int
    params: list[str]
    exported: Optional[bool]
    lang: str
    def_count: int
    confidence: str


def unused_symbols(idx: Index, include_exported: bool = True) -> list[Unused]:
    out: list[Unused] = []
    for name, defs in idx.defs.items():
        if idx.ident_uses.get(name, 0) - len(defs) > 0:
            continue
        if name in idx.string_refs:  # referenced by name in a string literal
            continue
        for d in defs:
            # Entrypoints, tests, and attribute-invoked functions are called by a
            # runtime or test harness, not by name, so they are never "unused".
            if d.runtime_root:
                continue
            if (d.exported and not include_exported) or _suppressed(idx, d.path, d.line):
                continue
            if d.exported or d.exported is None or d.is_method:
                conf = "low" if (d.exported or d.exported is None) else "medium"
            else:
                conf = "high" if len(defs) == 1 else "medium"
            out.append(Unused(name, d.path, d.line, d.end_line, d.params,
                              d.exported, d.lang, len(defs), conf))
    rank = {"high": 0, "medium": 1, "low": 2}
    out.sort(key=lambda u: (rank.get(u.confidence, 3), u.path, u.line))
    return out


def dead_code(idx: Index) -> list[dict]:
    """Transitively unreachable definitions via the call graph (DCE-lite)."""
    reachable: set[str] = set(idx.toplevel_called)
    for name, defs in idx.defs.items():
        for d in defs:
            if (d.exported or d.runtime_root or _value_refs(idx, name) > 0
                    or name in idx.string_refs):
                reachable.add(name)
    frontier = list(reachable)
    while frontier:
        nm = frontier.pop()
        for d in idx.defs.get(nm, []):
            for callee in idx.call_edges.get(d.id, ()):
                if callee not in reachable:
                    reachable.add(callee)
                    frontier.append(callee)
    out: list[dict] = []
    for name, defs in idx.defs.items():
        if name in reachable:
            continue
        for d in defs:
            if _suppressed(idx, d.path, d.line):
                continue
            out.append({
                "name": name, "path": d.path, "line": d.line, "end_line": d.end_line,
                "lang": d.lang, "exported": d.exported, "def_count": len(defs),
                "reason": "no path from any root (entrypoint/exported/test/value-ref)",
            })
    out.sort(key=lambda d: (d["path"], d["line"]))
    return out


def unused_parameters(idx: Index) -> list[dict]:
    out: list[dict] = []
    for name, defs in idx.defs.items():
        for d in defs:
            if _suppressed(idx, d.path, d.line):
                continue
            for p in d.unused_params:
                out.append({
                    "function": name, "param": p, "path": d.path, "line": d.line,
                    "lang": d.lang, "exported": d.exported,
                })
    out.sort(key=lambda r: (r["path"], r["line"]))
    return out


def unreachable_code(idx: Index) -> list[dict]:
    return [
        {"path": u.path, "line": u.line, "lang": u.lang, "after": u.after}
        for u in sorted(idx.unreachable, key=lambda u: (u.path, u.line))
        if not _suppressed(idx, u.path, u.line)
    ]


def unused_imports(idx: Index) -> list[dict]:
    return [
        {"name": u.name, "path": u.path, "line": u.line, "lang": u.lang,
         "statement": u.statement}
        for u in sorted(idx.unused_imports, key=lambda u: (u.path, u.line))
        if not _suppressed(idx, u.path, u.line)
    ]


def constant_conditions(idx: Index) -> list[dict]:
    return [
        {"path": d.path, "line": d.line, "lang": d.lang, "construct": d.construct,
         "value": d.value, "effect": "always runs" if d.always else "never runs"}
        for d in sorted(idx.dead, key=lambda d: (d.path, d.line))
        if not _suppressed(idx, d.path, d.line)
    ]


def redundant_conditions(idx: Index) -> list[dict]:
    return [
        {"path": r.path, "line": r.line, "lang": r.lang, "snippet": r.snippet,
         "kind": r.kind}
        for r in sorted(idx.redundant, key=lambda r: (r.path, r.line))
        if not _suppressed(idx, r.path, r.line)
    ]


def constant_returns(idx: Index, min_returns: int = 1) -> list[dict]:
    out: list[dict] = []
    for name, defs in idx.defs.items():
        for d in defs:
            if d.const_return is None or _suppressed(idx, d.path, d.line):
                continue
            out.append({
                "function": name, "value": d.const_return, "path": d.path,
                "line": d.line, "lang": d.lang, "exported": d.exported,
                "call_count": len(idx.calls.get(name, [])),
            })
    out.sort(key=lambda r: -r["call_count"])
    return out


def unexport_candidates(idx: Index) -> list[dict]:
    """Exported defs whose every call site is in the same directory (package)."""
    out: list[dict] = []
    for name, defs in idx.defs.items():
        calls = idx.calls.get(name, [])
        if not calls:
            continue
        for d in defs:
            if not d.exported or _suppressed(idx, d.path, d.line):
                continue
            caller_dirs = {os.path.dirname(c.path) for c in calls}
            if caller_dirs <= {d.directory} and _value_refs(idx, name) == 0:
                out.append({
                    "name": name, "path": d.path, "line": d.line, "lang": d.lang,
                    "package_dir": d.directory, "call_count": len(calls),
                    "note": "all in-tree callers share the package; name-based",
                })
    out.sort(key=lambda r: -r["call_count"])
    return out


def duplicate_bodies(idx: Index, min_size: int = 40) -> list[dict]:
    groups: dict[str, list[Definition]] = defaultdict(list)
    for defs in idx.defs.values():
        for d in defs:
            if d.body_size >= min_size:
                groups[d.body_hash].append(d)
    out: list[dict] = []
    for h, members in groups.items():
        if len(members) < 2:
            continue
        out.append({
            "body_hash": h, "count": len(members), "body_size": members[0].body_size,
            "members": [{"name": m.name, "path": m.path, "line": m.line} for m in members],
        })
    out.sort(key=lambda g: (-g["count"], -g["body_size"]))
    return out


def definitions(idx: Index, lang: Optional[str] = None,
                exported: Optional[bool] = None) -> list[dict]:
    out: list[dict] = []
    for name, defs in idx.defs.items():
        for d in defs:
            if lang and d.lang != lang:
                continue
            if exported is not None and d.exported is not exported:
                continue
            out.append({
                "name": d.name, "path": d.path, "line": d.line, "end_line": d.end_line,
                "params": d.params, "exported": d.exported, "lang": d.lang,
                "call_count": len(idx.calls.get(name, [])),
                "lines": d.lines, "branches": d.branches,
            })
    out.sort(key=lambda d: (d["path"], d["line"]))
    return out


def references(idx: Index, name: str) -> dict:
    sites = idx.ident_sites.get(name, [])
    return {
        "name": name,
        "total_occurrences": idx.ident_uses.get(name, 0),
        "definitions": len(idx.defs.get(name, [])),
        "calls": len(idx.calls.get(name, [])),
        "value_refs": _value_refs(idx, name),
        "truncated": len(sites) >= _IDENT_SITE_CAP,
        "sites": [{"path": p, "line": ln} for p, ln in sites],
    }


def impact(idx: Index, name: str, max_depth: int = 6) -> dict:
    reverse: dict[str, set[str]] = defaultdict(set)
    for cid, callees in idx.call_edges.items():
        caller = idx.defs_by_id[cid].name
        for callee in callees:
            reverse[callee].add(caller)
    seen: set[str] = set()
    layers: list[list[str]] = []
    frontier = {name}
    depth = 0
    while frontier and depth < max_depth:
        nxt: set[str] = set()
        for nm in frontier:
            for caller in reverse.get(nm, ()):
                if caller not in seen and caller != name:
                    seen.add(caller)
                    nxt.add(caller)
        if nxt:
            layers.append(sorted(nxt))
        frontier = nxt
        depth += 1
    return {
        "name": name,
        "direct_callers": sorted(reverse.get(name, [])),
        "transitive_caller_count": len(seen),
        "layers": layers,
    }


def hotspots(idx: Index, by: str = "branches", limit: int = 25) -> list[dict]:
    rows = [d for defs in idx.defs.values() for d in defs]
    key = {
        "branches": lambda d: d.branches,
        "lines": lambda d: d.lines,
        "params": lambda d: len(d.params),
        "fan_in": lambda d: len(idx.calls.get(d.name, [])),
        "depth": lambda d: d.depth,
    }.get(by, lambda d: d.branches)
    rows.sort(key=key, reverse=True)
    return [{
        "name": d.name, "path": d.path, "line": d.line, "lang": d.lang,
        "branches": d.branches, "lines": d.lines, "params": len(d.params),
        "depth": d.depth, "fan_in": len(idx.calls.get(d.name, [])),
    } for d in rows[:limit]]


def coverage(idx: Index) -> dict:
    defs_by_lang: dict[str, int] = defaultdict(int)
    for defs in idx.defs.values():
        for d in defs:
            defs_by_lang[d.lang] += 1
    calls_by_lang: dict[str, int] = defaultdict(int)
    for calls in idx.calls.values():
        for c in calls:
            calls_by_lang[c.lang] += 1
    return {
        "files": idx.files,
        "languages": sorted(idx.langs),
        "per_language": {
            lang: {
                "files": idx.file_count_by_lang.get(lang, 0),
                "definitions": defs_by_lang.get(lang, 0),
                "calls": calls_by_lang.get(lang, 0),
            }
            for lang in sorted(idx.langs)
        },
        "supported_languages": sorted(SPECS),
    }


def report(idx: Index) -> dict:
    """One-shot cleanup summary across every sweep."""
    unused = unused_symbols(idx)
    return {
        "coverage": coverage(idx),
        "counts": {
            "unused_symbols": len(unused),
            "dead_code_transitive": len(dead_code(idx)),
            "unused_parameters": len(unused_parameters(idx)),
            "unreachable_code": len(unreachable_code(idx)),
            "unused_imports": len(unused_imports(idx)),
            "constant_arguments": len(constant_arguments(idx, min_calls=2)),
            "constant_conditions": len(constant_conditions(idx)),
            "redundant_conditions": len(redundant_conditions(idx)),
            "constant_returns": len(constant_returns(idx)),
            "unexport_candidates": len(unexport_candidates(idx)),
            "duplicate_body_groups": len(duplicate_bodies(idx)),
        },
        "high_confidence_unused": [
            {"name": u.name, "path": u.path, "line": u.line}
            for u in unused if u.confidence == "high"
        ][:25],
    }


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
        "name": name, "index": index, "call_count": len(calls),
        "supplying_count": sum(dist.values()), "distinct": len(dist),
        "distribution": [
            {"value": v, "count": n, "kind": kinds.get(v, "expr")}
            for v, n in sorted(dist.items(), key=lambda kv: -kv[1])
        ],
    }


def call_sites(idx: Index, name: str, limit: int = 50) -> list[dict]:
    return [
        {"path": c.path, "line": c.line, "qualifier": c.qualifier,
         "form": c.form, "args": c.args}
        for c in idx.calls.get(name, [])[:limit]
    ]


def symbol_info(idx: Index, name: str) -> dict:
    defs = idx.defs.get(name, [])
    calls = idx.calls.get(name, [])
    quals = {c.qualifier for c in calls if c.qualifier}
    return {
        "name": name, "has_def": bool(defs), "def_count": len(defs),
        "exported": defs[0].exported if defs else None,
        "call_count": len(calls), "distinct_qualifiers": sorted(quals)[:20],
        "value_used_estimate": _value_refs(idx, name),
        "definitions": [
            {"path": d.path, "line": d.line, "end_line": d.end_line,
             "params": d.params, "exported": d.exported, "lang": d.lang,
             "lines": d.lines, "branches": d.branches,
             "unused_params": d.unused_params, "const_return": d.const_return}
            for d in defs[:20]
        ],
    }


def ast_query(root: str, lang: str, query: str, limit: int = 200) -> dict:
    from tree_sitter_languages import get_language
    if lang not in SPECS:
        return {"error": f"unknown language: {lang}", "matches": []}
    spec = SPECS[lang]
    try:
        compiled = get_language(lang).query(query)
    except Exception as e:
        return {"error": f"invalid query: {e}", "matches": []}
    parser = get_parser(lang)
    matches: list[dict] = []
    truncated = False
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for fn in filenames:
            if os.path.splitext(fn)[1] not in spec.exts:
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
                tree = parser.parse(src)
                for node, cap in compiled.captures(tree.root_node):
                    matches.append({
                        "capture": cap, "path": os.path.relpath(full, root),
                        "line": node.start_point[0] + 1, "text": _norm(node.text)[:200],
                    })
                    if len(matches) >= limit:
                        truncated = True
                        break
            except Exception:
                continue
            if truncated:
                break
        if truncated:
            break
    return {"count": len(matches), "truncated": truncated, "matches": matches}
