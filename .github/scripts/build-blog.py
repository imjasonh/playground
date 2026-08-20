#!/usr/bin/env python3
"""Build the published /posts/ catalog from blog-post.md files.

Discovers every ``blog-post.md`` in a repository source tree, converts the
Markdown to HTML, copies local images the posts reference, and writes a
reverse-chronological index. Publication and update dates come from git
author dates (oldest commit that touched the file, newest commit that
touched it).

Usage:
  python3 .github/scripts/build-blog.py --out dist/posts
  python3 .github/scripts/build-blog.py --source /path/to/repo --out /tmp/posts
"""
from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from urllib.parse import unquote, urlparse


SCRIPT_DIR = Path(__file__).resolve().parent
PAGES_DIR = SCRIPT_DIR.parent / "pages"
INDEX_TEMPLATE_PATH = PAGES_DIR / "blog-index.html.tmpl"
POST_TEMPLATE_PATH = PAGES_DIR / "blog-post.html.tmpl"
SOURCE_ROOT = SCRIPT_DIR.parents[1]

POST_FILENAME = "blog-post.md"
SKIP_DIR_NAMES = {
    ".git",
    ".venv",
    "__pycache__",
    "node_modules",
    "target",
    "dist",
    "DerivedData",
    "vendor",
    "coverage",
    "test-results",
}

ALERT_TYPES = {
    "NOTE": "Note",
    "TIP": "Tip",
    "IMPORTANT": "Important",
    "WARNING": "Warning",
    "CAUTION": "Caution",
}

IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".avif"}


class BuildError(Exception):
    """A catalog build failed (missing image, escaped path, and similar)."""


@dataclass
class Post:
    path: Path
    slug: str
    title_md: str
    body_md: str
    published: datetime | None
    updated: datetime | None

    @property
    def title_text(self) -> str:
        return strip_markup(self.title_md)

    @property
    def title_html(self) -> str:
        return render_inline(self.title_md)


def find_post_paths(root: Path) -> list[Path]:
    """Return blog-post.md paths under ``root``, skipping generated/hidden trees."""
    found: list[Path] = []
    root = root.resolve()
    for path in root.rglob(POST_FILENAME):
        if not path.is_file():
            continue
        rel_parts = path.relative_to(root).parts
        if any(part.startswith(".") or part in SKIP_DIR_NAMES for part in rel_parts[:-1]):
            continue
        found.append(path)
    found.sort()
    return found


def assign_slugs(paths: list[Path], root: Path) -> dict[Path, str]:
    """Map each post path to a URL slug.

    The default slug is the parent directory name, or ``home`` when the file
    sits at the repository root. If two posts share that name, colliding
    paths use a hyphenated relative-parent slug instead.
    """
    root = root.resolve()
    prelim: dict[Path, str] = {}
    counts: dict[str, int] = {}
    for path in paths:
        if path.parent.resolve() == root:
            slug = "home"
        else:
            slug = path.parent.name
        prelim[path] = slug
        counts[slug] = counts.get(slug, 0) + 1

    slugs: dict[Path, str] = {}
    used: set[str] = set()
    for path in paths:
        slug = prelim[path]
        if counts[slug] > 1:
            rel_parent = path.parent.relative_to(root)
            slug = "-".join(rel_parent.parts) if rel_parent.parts else slug
        original = slug
        n = 2
        while slug in used:
            slug = f"{original}-{n}"
            n += 1
        used.add(slug)
        slugs[path] = slug
    return slugs


def git_author_dates(repo: Path, rel_path: str) -> tuple[datetime | None, datetime | None]:
    """Return (first published, last updated) author dates for ``rel_path``.

    ``git log`` lists newest first. Missing history (untracked file, not a
    git repo) yields ``(None, None)``.
    """
    result = subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "log",
            "--follow",
            "--format=%aI",
            "--",
            rel_path,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    lines = [ln.strip() for ln in result.stdout.splitlines() if ln.strip()]
    if not lines:
        return None, None
    return _parse_iso(lines[-1]), _parse_iso(lines[0])


def _parse_iso(value: str) -> datetime | None:
    try:
        return datetime.fromisoformat(value)
    except ValueError:
        return None


def format_date(value: datetime) -> str:
    """Format an author-date in the author's calendar day, e.g. August 19, 2026."""
    return f"{value.strftime('%B')} {value.day}, {value.year}"


def iso_date(value: datetime | None) -> str | None:
    if value is None:
        return None
    return value.date().isoformat()


def extract_title(body: str, fallback: str) -> tuple[str, str]:
    """Take the first ATX h1 as the title and remove it from the body."""
    lines = body.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("# "):
            title = line[2:].strip()
            rest = "\n".join(lines[:i] + lines[i + 1 :]).lstrip("\n")
            return title or fallback, rest
    return fallback, body


def strip_markup(text: str) -> str:
    """Approximate plain text for titles and ``<title>`` tags."""
    text = re.sub(r"!\[([^\]]*)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"`([^`]+)`", r"\1", text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
    text = re.sub(r"__([^_]+)__", r"\1", text)
    text = re.sub(r"~~([^~]+)~~", r"\1", text)
    text = re.sub(r"(?<![A-Za-z0-9])_([^_]+)_(?![A-Za-z0-9])", r"\1", text)
    text = re.sub(r"(?<![A-Za-z0-9])\*([^*]+)\*(?![A-Za-z0-9])", r"\1", text)
    return re.sub(r"\s+", " ", text).strip()


def local_asset_refs(markdown: str) -> list[str]:
    """Relative image destinations referenced in Markdown."""
    return [m.group(1).strip() for m in re.finditer(r"!\[[^\]]*\]\(([^)]+)\)", markdown)]


def resolve_local_asset(post_dir: Path, ref: str) -> Path | None:
    """Return the on-disk path for a same-directory relative asset, or None.

    Rejects URLs and absolute paths. Destinations that escape the post
    directory raise ``BuildError``.
    """
    raw = unquote(ref.strip())
    if raw.startswith("<") and raw.endswith(">"):
        raw = raw[1:-1]
    parsed = urlparse(raw)
    if parsed.scheme or parsed.netloc:
        return None
    if raw.startswith("/") or raw.startswith("\\"):
        raise BuildError(f"absolute image path is not allowed: {ref}")
    dest = (post_dir / raw).resolve()
    try:
        dest.relative_to(post_dir.resolve())
    except ValueError as exc:
        raise BuildError(f"image path escapes the post directory: {ref}") from exc
    return dest


def copy_local_assets(markdown: str, post_dir: Path, dest_dir: Path) -> None:
    """Copy local image files next to the generated HTML.

    Missing files and path-escape attempts raise ``BuildError``.
    """
    seen: set[Path] = set()
    for ref in local_asset_refs(markdown):
        src = resolve_local_asset(post_dir, ref)
        if src is None:
            continue
        if src.suffix.lower() not in IMAGE_EXTS:
            continue
        if src in seen:
            continue
        seen.add(src)
        rel = src.relative_to(post_dir.resolve())
        dest = dest_dir / rel
        if not src.is_file():
            raise BuildError(f"missing image {post_dir / rel}")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dest)


# --- Markdown --------------------------------------------------------------

_HEADING_RE = re.compile(r"^(#{1,6}) (.+)$")
_UL_RE = re.compile(r"^([-*]) (.+)$")
_OL_RE = re.compile(r"^(\d+)\. (.+)$")
_HR_RE = re.compile(r"^(\*\*\*|---)\s*$")
_ALERT_RE = re.compile(r"^\[!(NOTE|TIP|IMPORTANT|WARNING|CAUTION)\]\s*$", re.I)


def markdown_to_html(text: str) -> str:
    """Render a small Markdown dialect used by playground posts."""
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = text.split("\n")
    blocks: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith("```"):
            info = line[3:].strip()
            fence: list[str] = []
            i += 1
            while i < n and not lines[i].startswith("```"):
                fence.append(lines[i])
                i += 1
            if i < n:
                i += 1
            klass = f' class="language-{html.escape(info)}"' if info else ""
            code = html.escape("\n".join(fence), quote=False)
            blocks.append(f"<pre><code{klass}>{code}\n</code></pre>")
            continue
        heading = _HEADING_RE.match(line)
        if heading:
            level = len(heading.group(1))
            blocks.append(f"<h{level}>{render_inline(heading.group(2).strip())}</h{level}>")
            i += 1
            continue
        if _HR_RE.match(line):
            blocks.append("<hr>")
            i += 1
            continue
        if line.startswith(">"):
            quote_lines: list[str] = []
            while i < n and (lines[i].startswith(">") or not lines[i].strip()):
                if not lines[i].strip():
                    if i + 1 < n and lines[i + 1].startswith(">"):
                        quote_lines.append("")
                        i += 1
                        continue
                    break
                raw = lines[i][1:]
                if raw.startswith(" "):
                    raw = raw[1:]
                quote_lines.append(raw)
                i += 1
            blocks.append(_render_blockquote(quote_lines))
            continue
        if _UL_RE.match(line) or _OL_RE.match(line):
            html_list, i = _render_list(lines, i)
            blocks.append(html_list)
            continue
        para = [line]
        i += 1
        while i < n and lines[i].strip() and not _starts_block(lines[i]):
            para.append(lines[i])
            i += 1
        blocks.append(f"<p>{render_inline(' '.join(para))}</p>")
    return "\n".join(blocks)


def _starts_block(line: str) -> bool:
    if line.startswith("```") or line.startswith(">"):
        return True
    if _HEADING_RE.match(line) or _HR_RE.match(line):
        return True
    if _UL_RE.match(line) or _OL_RE.match(line):
        return True
    return False


def _render_blockquote(quote_lines: list[str]) -> str:
    if quote_lines:
        alert = _ALERT_RE.match(quote_lines[0].strip())
        if alert:
            kind = alert.group(1).upper()
            label = ALERT_TYPES[kind]
            css = kind.lower()
            inner = markdown_to_html("\n".join(quote_lines[1:]))
            return (
                f'<aside class="alert alert-{css}" role="note">\n'
                f'<p class="alert-label">{html.escape(label)}</p>\n'
                f"{inner}\n"
                "</aside>"
            )
    inner = markdown_to_html("\n".join(quote_lines))
    return f"<blockquote>\n{inner}\n</blockquote>"


def _render_list(lines: list[str], start: int) -> tuple[str, int]:
    first = lines[start]
    ordered = bool(_OL_RE.match(first))
    tag = "ol" if ordered else "ul"
    items: list[str] = []
    i = start
    n = len(lines)
    while i < n:
        raw = lines[i]
        match = _OL_RE.match(raw) if ordered else _UL_RE.match(raw)
        if not match:
            break
        items.append(f"<li>{render_inline(match.group(2).strip())}</li>")
        i += 1
    return f"<{tag}>\n" + "\n".join(items) + f"\n</{tag}>", i


def render_inline(text: str) -> str:
    """Render inline Markdown: images, links, code, emphasis, autolinks."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("![", i):
            consumed = _consume_image(text, i, out)
            if consumed:
                i = consumed
                continue
        if text[i] == "[":
            consumed = _consume_link(text, i, out)
            if consumed:
                i = consumed
                continue
        if text[i] == "`":
            consumed = _consume_code(text, i, out)
            if consumed:
                i = consumed
                continue
        if text.startswith("~~", i):
            end = text.find("~~", i + 2)
            if end > i + 2:
                out.append(f"<del>{render_inline(text[i + 2 : end])}</del>")
                i = end + 2
                continue
        if text.startswith("**", i):
            end = text.find("**", i + 2)
            if end > i + 2:
                out.append(f"<strong>{render_inline(text[i + 2 : end])}</strong>")
                i = end + 2
                continue
        if text.startswith("__", i) and _left_open(text, i):
            end = text.find("__", i + 2)
            if end > i + 2 and _right_close(text, end + 1):
                out.append(f"<strong>{render_inline(text[i + 2 : end])}</strong>")
                i = end + 2
                continue
        if text[i] == "*" and _left_open(text, i):
            end = _find_closing_mark(text, i + 1, "*")
            if end is not None:
                out.append(f"<em>{render_inline(text[i + 1 : end])}</em>")
                i = end + 1
                continue
        if text[i] == "_" and _left_open(text, i):
            end = _find_closing_mark(text, i + 1, "_")
            if end is not None:
                out.append(f"<em>{render_inline(text[i + 1 : end])}</em>")
                i = end + 1
                continue
        if text.startswith("http://", i) or text.startswith("https://", i):
            consumed = _consume_autolink(text, i, out)
            if consumed:
                i = consumed
                continue
        out.append(html.escape(text[i], quote=False))
        i += 1
    return "".join(out)


def _left_open(text: str, i: int) -> bool:
    return i == 0 or not text[i - 1].isalnum()


def _right_close(text: str, last: int) -> bool:
    return last + 1 >= len(text) or not text[last + 1].isalnum()


def _find_closing_mark(text: str, start: int, mark: str) -> int | None:
    j = start
    while j < len(text):
        if text[j] == "`":
            skip = _skip_code(text, j)
            if skip is None:
                return None
            j = skip
            continue
        if text[j] == mark and _right_close(text, j) and j > start:
            return j
        j += 1
    return None


def _skip_code(text: str, i: int) -> int | None:
    ticks = 0
    while i + ticks < len(text) and text[i + ticks] == "`":
        ticks += 1
    if ticks == 0:
        return None
    end = text.find("`" * ticks, i + ticks)
    if end < 0:
        return None
    return end + ticks


def _consume_code(text: str, i: int, out: list[str]) -> int | None:
    ticks = 0
    while i + ticks < len(text) and text[i + ticks] == "`":
        ticks += 1
    end = text.find("`" * ticks, i + ticks)
    if end < 0:
        return None
    out.append(f"<code>{html.escape(text[i + ticks : end], quote=False)}</code>")
    return end + ticks


def _consume_image(text: str, i: int, out: list[str]) -> int | None:
    parsed = _parse_link_dest(text, i + 1)
    if parsed is None:
        return None
    alt, dest, end = parsed
    out.append(
        f'<img src="{html.escape(dest, quote=True)}" alt="{html.escape(alt, quote=True)}">'
    )
    return end


def _consume_link(text: str, i: int, out: list[str]) -> int | None:
    parsed = _parse_link_dest(text, i)
    if parsed is None:
        return None
    label, dest, end = parsed
    out.append(f'<a href="{html.escape(dest, quote=True)}">{render_inline(label)}</a>')
    return end


def _parse_link_dest(text: str, i: int) -> tuple[str, str, int] | None:
    """Parse ``[label](dest)`` starting at the opening ``[``."""
    if i >= len(text) or text[i] != "[":
        return None
    depth = 1
    j = i + 1
    while j < len(text) and depth:
        if text[j] == "\\":
            j += 2
            continue
        if text[j] == "[":
            depth += 1
        elif text[j] == "]":
            depth -= 1
        j += 1
    if depth != 0 or j >= len(text) or text[j] != "(":
        return None
    label = text[i + 1 : j - 1]
    k = j + 1
    dest_chars: list[str] = []
    while k < len(text) and text[k] != ")":
        dest_chars.append(text[k])
        k += 1
    if k >= len(text) or text[k] != ")":
        return None
    return label, "".join(dest_chars).strip(), k + 1


def _consume_autolink(text: str, i: int, out: list[str]) -> int | None:
    match = re.match(r"https?://[^\s<>]+", text[i:])
    if not match:
        return None
    url = match.group(0)
    while url and url[-1] in ".,;:!?":
        url = url[:-1]
    if not url:
        return None
    out.append(f'<a href="{html.escape(url, quote=True)}">{html.escape(url, quote=False)}</a>')
    return i + len(url)


# --- Load / render ---------------------------------------------------------


def load_post(root: Path, path: Path, slug: str) -> Post:
    raw = path.read_text(encoding="utf-8")
    fallback = "home" if path.parent.resolve() == root.resolve() else path.parent.name
    title_md, body = extract_title(raw, fallback)
    rel = str(path.relative_to(root))
    published, updated = git_author_dates(root, rel)
    return Post(
        path=path,
        slug=slug,
        title_md=title_md,
        body_md=body,
        published=published,
        updated=updated,
    )


def dates_html(post: Post) -> str:
    if post.published is None and post.updated is None:
        return ""
    bits: list[str] = []
    if post.published is not None:
        bits.append(f"Published {html.escape(format_date(post.published))}")
    if (
        post.updated is not None
        and (post.published is None or post.updated.date() != post.published.date())
    ):
        bits.append(f"Updated {html.escape(format_date(post.updated))}")
    if not bits:
        return ""
    return f'      <p class="meta">{" · ".join(bits)}</p>\n'


def render_post(post: Post, template: str) -> str:
    body = markdown_to_html(post.body_md)
    page_title = f"{post.title_text} · Posts"
    return (
        template.replace("__TITLE__", html.escape(page_title))
        .replace("__TITLE_HTML__", post.title_html)
        .replace("__DATES__", dates_html(post))
        .replace("__BODY__", body)
    )


def render_index_items(posts: list[Post]) -> str:
    if not posts:
        return '    <li class="empty">No posts yet.</li>'
    items: list[str] = []
    for post in posts:
        items.append(
            "    <li>\n"
            f'      <a href="{html.escape(post.slug, quote=True)}/">\n'
            f'        <span class="title">{post.title_html}</span>\n'
            f'        <span class="meta">{html.escape(dates_label(post))}</span>\n'
            "      </a>\n"
            "    </li>"
        )
    return "\n".join(items)


def dates_label(post: Post) -> str:
    bits: list[str] = []
    if post.published is not None:
        bits.append(format_date(post.published))
    if (
        post.updated is not None
        and (post.published is None or post.updated.date() != post.published.date())
    ):
        bits.append(f"Updated {format_date(post.updated)}")
    return " · ".join(bits)


def posts_to_json(posts: list[Post]) -> list[dict[str, str | None]]:
    return [
        {
            "slug": post.slug,
            "title": post.title_text,
            "published": iso_date(post.published),
            "updated": iso_date(post.updated),
        }
        for post in posts
    ]


def sort_posts(posts: list[Post]) -> list[Post]:
    def key(post: Post) -> tuple:
        stamp = post.published or post.updated
        has_date = 0 if stamp is None else 1
        return (has_date, stamp or datetime.min, post.slug)

    return sorted(posts, key=key, reverse=True)


def build(
    source: Path,
    dest: Path,
    index_template: str | None = None,
    post_template: str | None = None,
) -> list[Post]:
    """Write the catalog into ``dest``. Raises ``BuildError`` on missing images."""
    source = source.resolve()
    dest = dest.resolve()
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)

    paths = find_post_paths(source)
    slugs = assign_slugs(paths, source)
    posts: list[Post] = []
    post_tmpl = post_template if post_template is not None else POST_TEMPLATE_PATH.read_text()
    for path in paths:
        post = load_post(source, path, slugs[path])
        post_dir = dest / post.slug
        post_dir.mkdir(parents=True, exist_ok=True)
        copy_local_assets(path.read_text(encoding="utf-8"), path.parent, post_dir)
        (post_dir / "index.html").write_text(render_post(post, post_tmpl), encoding="utf-8")
        posts.append(post)

    posts = sort_posts(posts)
    index_html = (
        (index_template if index_template is not None else INDEX_TEMPLATE_PATH.read_text())
        .replace("__TITLE__", "Posts · Playground")
        .replace("__HEADING__", "Posts")
        .replace("__ITEMS__", render_index_items(posts))
    )
    (dest / "index.html").write_text(index_html, encoding="utf-8")
    (dest / "index.json").write_text(
        json.dumps(posts_to_json(posts), indent=2) + "\n", encoding="utf-8"
    )
    return posts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        default=str(SOURCE_ROOT),
        help="repository source tree to scan (default: this checkout)",
    )
    parser.add_argument("--out", required=True, help="directory to write the generated catalog")
    args = parser.parse_args(argv)
    try:
        posts = build(Path(args.source), Path(args.out))
    except BuildError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    print(f"Wrote {len(posts)} post(s) to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
