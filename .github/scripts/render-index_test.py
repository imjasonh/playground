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
    "__POSTS__"
    "<ul>\n__ITEMS__\n</ul>\n__PREVIEWS__\n__WORKERS__END"
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
    # Cloudflare Worker apps (wrangler.toml) -> not browser apps, listed
    # separately. web-push also has an index.html-free demo companion.
    (tmp / "web-push").mkdir()
    (tmp / "web-push" / "wrangler.toml").write_text("name = 'web-push'")
    (tmp / "cors-proxy").mkdir()
    (tmp / "cors-proxy" / "wrangler.toml").write_text("name = 'cors-proxy'")
    # Hidden dir -> ignored.
    (tmp / ".git").mkdir()
    (tmp / ".git" / "index.html").write_text("x")
    (tmp / ".hidden-worker").mkdir()
    (tmp / ".hidden-worker" / "wrangler.toml").write_text("x")
    # Generated posts catalog looks like a browser app (index.html) but is
    # not one — scan_apps must skip it.
    (tmp / "posts").mkdir()
    (tmp / "posts" / "index.html").write_text("x")
    (tmp / "posts" / "index.json").write_text(
        json.dumps(
            [
                {
                    "slug": "pasta",
                    "title": "pasta",
                    "published": "2026-08-19",
                    "updated": "2026-08-19",
                }
            ]
        )
    )

    preview = tmp / "preview"
    (preview / "pr-7").mkdir(parents=True)
    (preview / "pr-7" / "preview.json").write_text(
        json.dumps({"number": 7, "title": "Add feature", "apps": ["kanoodle"]})
    )
    (preview / "pr-12").mkdir(parents=True)
    (preview / "pr-12" / "preview.json").write_text(
        json.dumps(
            {
                "number": 12,
                "title": "Fix bug",
                "apps": ["artillery", "git"],
                "posts": True,
            }
        )
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


def test_scan_workers() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        workers = ri.scan_workers(root)
        check(
            workers == ["cors-proxy", "web-push"],
            f"scan_workers sorted, hidden excluded: {workers}",
        )


def test_scan_previews_sorted_and_filtered() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        previews = ri.scan_previews(root)
        numbers = [p["number"] for p in previews]
        check(numbers == [12, 7], f"previews sorted desc, manifest-only: {numbers}")
        check(previews[0]["apps"] == ["artillery", "git"], "preview apps preserved")
        check(previews[0]["posts"] is True, "preview posts flag preserved")


def test_render_site_has_apps_previews_and_workers() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        out = ri.render(
            "Playground",
            "Playground",
            ri.scan_apps(root),
            ri.scan_previews(root),
            "https://github.com/o/r",
            workers=ri.scan_workers(root),
            posts=ri.scan_posts(root),
            template=TEMPLATE,
        )
        check('<a href="kanoodle/">kanoodle</a>' in out, "app link rendered")
        check('href="preview/pr-12/"' in out, "preview open link rendered")
        check('href="https://github.com/o/r/pull/12"' in out, "PR link rendered")
        check('class="count">2<' in out, "preview count rendered")
        check("Cloudflare Workers apps" in out, "workers heading rendered")
        check(
            '<a href="https://github.com/o/r/tree/main/web-push">web-push</a>' in out,
            "worker source link rendered",
        )
        check("__PREVIEWS__" not in out, "previews placeholder replaced")
        check("__WORKERS__" not in out, "workers placeholder replaced")
        check("__REPO_URL__" not in out, "repo url placeholder replaced")
        check("__POSTS__" not in out, "posts placeholder replaced")
        check('href="posts/pasta/"' in out, "post link rendered")
        check("August 19, 2026" in out, "post published date rendered")
        check('href="posts/feed.xml"' in out, "posts section links the RSS feed")
        check(">posts<" in out or ", posts" in out, "preview card mentions posts")


def test_render_posts_updated_date_is_marked() -> None:
    posts = [
        {
            "slug": "app",
            "title": "Hello",
            "published": "2026-01-15",
            "updated": "2026-03-02",
        }
    ]
    out = ri.render_posts_section(posts)
    check("January 15, 2026" in out, "published date")
    check("Updated March 2, 2026" in out, "updated date")
    check('class="updated"' in out, "updated date marked")
    check("August" not in out, "fixture-only dates")


def test_render_without_previews_or_workers_omits_sections() -> None:
    out = ri.render("t", "h", ["hello"], [], "", template=TEMPLATE)
    check(out.rstrip().endswith("END"), "trailing sections empty when nothing to show")
    check("preview-card" not in out, "no preview cards when empty")
    check("Cloudflare Workers apps" not in out, "no workers section when empty")
    check("post-list" not in out, "no posts section when empty")


def test_render_workers_relative_link_without_repo_url() -> None:
    out = ri.render("t", "h", [], [], "", workers=["web-push"], template=TEMPLATE)
    check('<a href="web-push">web-push</a>' in out, "relative worker link fallback")


def test_scan_posts() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        posts = ri.scan_posts(root)
        check(len(posts) == 1, f"one post: {posts}")
        check(posts[0]["slug"] == "pasta", "slug")
        check(posts[0]["published"] == "2026-08-19", "published")


def test_scan_apps_skips_generated_posts_dir() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = make_site(Path(d))
        apps = ri.scan_apps(root)
        check("posts" not in apps, f"posts dir is not an app: {apps}")


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
