#!/usr/bin/env python3
"""Dependency-free tests for build-blog.py.

Run locally with:  python3 .github/scripts/build-blog_test.py
Exits non-zero on the first failed assertion.
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


spec = importlib.util.spec_from_file_location(
    "build_blog", Path(__file__).resolve().parent / "build-blog.py"
)
bb = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = bb
spec.loader.exec_module(bb)

REPO_ROOT = Path(__file__).resolve().parents[2]


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def test_find_posts_nested_and_skips_junk() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "pasta").mkdir()
        (root / "pasta" / "blog-post.md").write_text("# Pasta\n")
        nested = root / "ios" / "Sources" / "Experiments" / "LocalLens"
        nested.mkdir(parents=True)
        (nested / "blog-post.md").write_text("# Lens\n")
        (root / "node_modules" / "pkg").mkdir(parents=True)
        (root / "node_modules" / "pkg" / "blog-post.md").write_text("# no\n")
        (root / ".hidden").mkdir()
        (root / ".hidden" / "blog-post.md").write_text("# no\n")
        paths = [p.relative_to(root).as_posix() for p in bb.find_post_paths(root)]
        check(
            paths == [
                "ios/Sources/Experiments/LocalLens/blog-post.md",
                "pasta/blog-post.md",
            ],
            f"nested kept, junk skipped: {paths}",
        )


def test_slug_collision_uses_relative_parent() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "a" / "foo").mkdir(parents=True)
        (root / "b" / "foo").mkdir(parents=True)
        p1 = root / "a" / "foo" / "blog-post.md"
        p2 = root / "b" / "foo" / "blog-post.md"
        p1.write_text("# A\n")
        p2.write_text("# B\n")
        slugs = bb.assign_slugs([p1, p2], root)
        check(set(slugs.values()) == {"a-foo", "b-foo"}, f"colliding slugs: {slugs}")


def test_root_post_slug_is_home() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        path = root / "blog-post.md"
        path.write_text("# Root\n")
        slugs = bb.assign_slugs([path], root)
        check(slugs[path] == "home", f"root slug: {slugs[path]}")


def test_markdown_basics() -> None:
    html = bb.markdown_to_html(
        "# Title\n\n"
        "A paragraph with **bold**, *em*, `code`, and [a link](https://example.com/x).\n\n"
        "![alt text](./pic.jpg)\n\n"
        "> a quote\n\n"
        "1. one\n"
        "2. two\n\n"
        "- bullet\n\n"
        "See https://example.com/z.\n"
    )
    check("<h1>Title</h1>" in html, "heading")
    check("<strong>bold</strong>" in html, "bold")
    check("<em>em</em>" in html, "italic")
    check("<code>code</code>" in html, "code")
    check('<a href="https://example.com/x">a link</a>' in html, "link")
    check('<img src="./pic.jpg" alt="alt text">' in html, "image alt")
    check("<blockquote>" in html and "a quote" in html, "blockquote")
    check("<ol>" in html and "<li>one</li>" in html, "ordered list")
    check("<ul>" in html and "<li>bullet</li>" in html, "unordered list")
    check(
        '<a href="https://example.com/z">https://example.com/z</a>' in html,
        "autolink",
    )


def test_markdown_github_alert_and_inline_code_heading() -> None:
    html = bb.markdown_to_html(
        "# `pasta`\n\n"
        "> [!IMPORTANT]\n"
        "> Be careful with `cue`.\n"
    )
    check("<h1><code>pasta</code></h1>" in html, "code in heading")
    check('class="alert alert-important"' in html, "alert class")
    check("Important" in html, "alert label")
    check("<code>cue</code>" in html, "code inside alert")


def test_markdown_escapes_html() -> None:
    html = bb.markdown_to_html("Use <script>alert(1)</script> & more.")
    check("<script>" not in html, "raw script not injected")
    check("&lt;script&gt;" in html, "script escaped")
    check("&amp;" in html, "ampersand escaped")


def test_underscore_emphasis_skips_identifiers() -> None:
    html = bb.render_inline("see file_match and _before_ LLMs")
    check("file_match" in html, "identifier underscores kept")
    check("<em>before</em>" in html, "word-boundary italic")


def test_extract_title_strips_h1() -> None:
    title, body = bb.extract_title("# `pasta`\n\nHello.\n", "fallback")
    check(title == "`pasta`", f"title: {title}")
    check(body == "Hello.", f"body: {body!r}")


def test_missing_image_fails_build() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "app").mkdir()
        (root / "app" / "blog-post.md").write_text("# Hi\n\n![x](./gone.jpg)\n")
        try:
            bb.build(root, root / "out")
        except bb.BuildError as exc:
            check("missing image" in str(exc), f"message: {exc}")
        else:
            raise AssertionError("expected BuildError for missing image")


def test_escaped_image_path_fails_build() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "app").mkdir()
        (root / "secret.jpg").write_text("x")
        (root / "app" / "blog-post.md").write_text("# Hi\n\n![x](../secret.jpg)\n")
        try:
            bb.build(root, root / "out")
        except bb.BuildError as exc:
            check("escapes" in str(exc), f"message: {exc}")
        else:
            raise AssertionError("expected BuildError for escaped path")


def test_copies_local_image_and_remote_urls_stay() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "app").mkdir()
        (root / "app" / "pic.jpg").write_bytes(b"jpeg")
        (root / "app" / "blog-post.md").write_text(
            "# Hi\n\n![local](./pic.jpg)\n\n![remote](https://example.com/x.png)\n"
        )
        bb.build(root, root / "out")
        copied = root / "out" / "app" / "pic.jpg"
        check(copied.is_file(), "local image copied")
        html = (root / "out" / "app" / "index.html").read_text()
        check('src="./pic.jpg"' in html, "local src preserved")
        check('src="https://example.com/x.png"' in html, "remote src preserved")


def _git(repo: Path, *args: str, env: dict[str, str] | None = None) -> None:
    import os

    full_env = dict(os.environ)
    if env:
        full_env.update(env)
    subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        env=full_env,
    )


def test_git_dates_first_and_last() -> None:
    with tempfile.TemporaryDirectory() as d:
        repo = Path(d)
        _git(repo, "init")
        _git(repo, "config", "user.email", "dev@example.com")
        _git(repo, "config", "user.name", "Dev")
        (repo / "app").mkdir()
        post = repo / "app" / "blog-post.md"
        post.write_text("# Hi\n\nfirst\n")
        _git(repo, "add", "app/blog-post.md")
        _git(
            repo,
            "commit",
            "-m",
            "add",
            env={
                "GIT_AUTHOR_DATE": "2026-01-15T12:00:00-05:00",
                "GIT_COMMITTER_DATE": "2026-01-15T12:00:00-05:00",
            },
        )
        post.write_text("# Hi\n\nsecond\n")
        _git(repo, "add", "app/blog-post.md")
        _git(
            repo,
            "commit",
            "-m",
            "update",
            env={
                "GIT_AUTHOR_DATE": "2026-03-02T09:00:00-05:00",
                "GIT_COMMITTER_DATE": "2026-03-02T09:00:00-05:00",
            },
        )
        published, updated = bb.git_author_dates(repo, "app/blog-post.md")
        check(published is not None and updated is not None, "dates present")
        check(published.date().isoformat() == "2026-01-15", f"published {published}")
        check(updated.date().isoformat() == "2026-03-02", f"updated {updated}")
        posts = bb.build(repo, repo / "out")
        html = (repo / "out" / "app" / "index.html").read_text()
        check("Published January 15, 2026" in html, "published label")
        check("Updated March 2, 2026" in html, "updated label")
        check(posts[0].slug == "app", "slug from parent")


def test_sort_is_reverse_chronological() -> None:
    older = bb.Post(
        path=Path("old.md"),
        slug="old",
        title_md="Old",
        body_md="",
        published=datetime(2026, 1, 1, tzinfo=timezone.utc),
        updated=None,
    )
    newer = bb.Post(
        path=Path("new.md"),
        slug="new",
        title_md="New",
        body_md="",
        published=datetime(2026, 8, 1, tzinfo=timezone.utc),
        updated=None,
    )
    undated = bb.Post(
        path=Path("x.md"),
        slug="x",
        title_md="X",
        body_md="",
        published=None,
        updated=None,
    )
    ordered = bb.sort_posts([older, undated, newer])
    check([p.slug for p in ordered] == ["new", "old", "x"], "newest dated first")


def test_real_repo_posts_build() -> None:
    with tempfile.TemporaryDirectory() as d:
        dest = Path(d) / "posts"
        posts = bb.build(REPO_ROOT, dest)
        slugs = [p.slug for p in posts]
        check("pasta" in slugs, f"pasta post present: {slugs}")
        check("its-not-jaws" in slugs, f"its-not-jaws post present: {slugs}")
        check(slugs[0] == "pasta", f"pasta is newest: {slugs}")
        pasta_html = (dest / "pasta" / "index.html").read_text()
        check("__SHARED_CSS__" not in pasta_html, "shared CSS inlined")
        check("--font-text" in pasta_html, "reading theme tokens present")
        check("Newsreader" in pasta_html, "screen reading face linked")
        check("<code>pasta</code>" in pasta_html, "pasta title code")
        check('src="./monorepo.jpg"' in pasta_html, "monorepo image")
        check((dest / "pasta" / "monorepo.jpg").is_file(), "monorepo.jpg copied")
        check("alert-important" in pasta_html, "important alert")
        jaws = (dest / "its-not-jaws" / "index.html").read_text()
        check("It" in jaws and "Jaws" in jaws, "jaws title")
        index = json.loads((dest / "index.json").read_text())
        check(index[0]["slug"] == "pasta", "index.json newest first")
        check("published" in index[0], "index.json has published")


def main() -> None:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok - {t.__name__}")
    print(f"\n{len(tests)} tests passed")


if __name__ == "__main__":
    main()
