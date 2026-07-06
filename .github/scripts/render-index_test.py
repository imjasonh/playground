#!/usr/bin/env python3
"""Dependency-free tests for render-index.py.

Run locally with:  python3 .github/scripts/render-index_test.py
Exits non-zero on the first failed assertion.
"""
from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib.util

spec = importlib.util.spec_from_file_location(
    "render_index", Path(__file__).resolve().parent / "render-index.py"
)
ri = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ri)


TEMPLATE = (
    "T=__TITLE__ H=__HEADING__ R=__REPO_URL__\n"
    "<ul>\n__ITEMS__\n</ul>\n__PREVIEWS__END"
)


def make_site(tmp: Path) -> Path:
    """Build a small fake published-site tree for scanning tests."""
    (tmp / "kanoodle").mkdir()
    (tmp / "kanoodle" / "index.html").write_text("x")
    (tmp / "artillery").mkdir()
    (tmp / "artillery" / "index.html").write_text("x")
    # Not a browser app (no index.html) -> ignored.
    (tmp / "gitdb").mkdir()
    (tmp / "gitdb" / "go.mod").write_text("module gitdb")
    # Hidden dir -> ignored.
    (tmp / ".git").mkdir()
    (tmp / ".git" / "index.html").write_text("x")

    preview = tmp / "preview"
    (preview / "pr-7").mkdir(parents=True)
    (preview / "pr-7" / "preview.json").write_text(
        json.dumps({"number": 7, "title": "Add feature", "apps": ["kanoodle"]})
    )
    (preview / "pr-12").mkdir(parents=True)
    (preview / "pr-12" / "preview.json").write_text(
        json.dumps({"number": 12, "title": "Fix bug", "apps": ["artillery", "git"]})
    )
    # Preview dir without a manifest (non-browser PR) -> not listed.
    (preview / "pr-3").mkdir(parents=True)
    (preview / "pr-3" / "index.html").write_text("x")
    return tmp


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def test_scan_apps() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        apps = ri.scan_apps(root)
        check(apps == ["artillery", "kanoodle"], f"scan_apps sorted browser apps: {apps}")


def test_scan_previews_sorted_and_filtered() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        previews = ri.scan_previews(root)
        numbers = [p["number"] for p in previews]
        check(numbers == [12, 7], f"previews sorted desc, manifest-only: {numbers}")
        check(previews[0]["apps"] == ["artillery", "git"], "preview apps preserved")


def test_render_site_has_apps_and_previews() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        out = ri.render(
            "Playground",
            "Playground",
            ri.scan_apps(root),
            ri.scan_previews(root),
            "https://github.com/o/r",
            template=TEMPLATE,
        )
        check('<a href="kanoodle/">kanoodle</a>' in out, "app link rendered")
        check('href="preview/pr-12/"' in out, "preview open link rendered")
        check('href="https://github.com/o/r/pull/12"' in out, "PR link rendered")
        check('class="count">2<' in out, "preview count rendered")
        check("__PREVIEWS__" not in out, "previews placeholder replaced")
        check("__REPO_URL__" not in out, "repo url placeholder replaced")


def test_render_without_previews_omits_section() -> None:
    out = ri.render("t", "h", ["hello"], [], "", template=TEMPLATE)
    check(out.rstrip().endswith("END"), "previews section empty when no previews")
    check("preview-card" not in out, "no preview cards when empty")


def test_render_escapes_title() -> None:
    out = ri.render(
        "P",
        "P",
        [],
        [{"number": 1, "title": "<script>&", "apps": ["a<b"]}],
        "https://x/r",
        template=TEMPLATE,
    )
    check("<script>&" not in out, "raw title not injected")
    check("&lt;script&gt;&amp;" in out, "title HTML-escaped")
    check("a&lt;b" in out, "apps HTML-escaped")


def main() -> None:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok - {t.__name__}")
    print(f"\n{len(tests)} tests passed")


if __name__ == "__main__":
    main()
