#!/usr/bin/env python3
"""Render the GitHub Pages index.html from the shared template.

Two modes:

  site     Render the production root index for a published site directory
           (typically a gh-pages checkout). Apps are discovered by scanning
           top-level directories that contain index.html; active previews are
           discovered from preview/pr-<N>/preview.json files (written by the
           preview workflow only for pull requests that change a browser app).

  preview  Render the per-PR preview index for a single preview directory. It
           lists the apps bundled in that preview and never shows a previews
           section.

The template lives at ../pages/index.html.tmpl relative to this script and
exposes four placeholders: __TITLE__, __HEADING__, __ITEMS__, __PREVIEWS__ and
__REPO_URL__.
"""
from __future__ import annotations

import argparse
import html
import json
from pathlib import Path

TEMPLATE_PATH = Path(__file__).resolve().parents[1] / "pages" / "index.html.tmpl"


def scan_apps(root: Path) -> list[str]:
    """Top-level browser apps in ``root`` (directories containing index.html).

    Hidden directories and the ``preview`` directory are ignored, matching the
    deploy/preview definition of a browser app.
    """
    apps = []
    if not root.is_dir():
        return apps
    for child in sorted(root.iterdir(), key=lambda p: p.name):
        if not child.is_dir():
            continue
        name = child.name
        if name.startswith(".") or name == "preview":
            continue
        if (child / "index.html").is_file():
            apps.append(name)
    return apps


def scan_previews(root: Path) -> list[dict]:
    """Active previews under ``root/preview`` from preview.json manifests.

    Returns a list of ``{"number", "title", "apps"}`` dicts sorted by PR number
    descending. Directories without a valid preview.json are skipped, so only
    previews recorded for browser-app PRs are listed.
    """
    previews = []
    preview_root = root / "preview"
    if not preview_root.is_dir():
        return previews
    for child in sorted(preview_root.iterdir(), key=lambda p: p.name):
        if not child.is_dir():
            continue
        manifest = child / "preview.json"
        if not manifest.is_file():
            continue
        try:
            data = json.loads(manifest.read_text())
            number = int(data["number"])
        except (ValueError, KeyError, TypeError, OSError):
            continue
        previews.append(
            {
                "number": number,
                "title": str(data.get("title", "")),
                "apps": [str(a) for a in data.get("apps", []) if a],
            }
        )
    previews.sort(key=lambda p: p["number"], reverse=True)
    return previews


def render_items(apps: list[str]) -> str:
    return "\n".join(
        f'      <li><a href="{html.escape(a)}/">{html.escape(a)}</a></li>' for a in apps
    )


def render_previews_section(previews: list[dict], repo_url: str) -> str:
    if not previews:
        return ""
    cards = []
    for p in previews:
        n = p["number"]
        title = html.escape(p["title"]) if p["title"] else f"PR #{n}"
        apps_line = ""
        if p["apps"]:
            apps_line = (
                '        <span class="apps">'
                + html.escape(", ".join(p["apps"]))
                + "</span>\n"
            )
        pr_link = f"{repo_url}/pull/{n}" if repo_url else f"pull/{n}"
        cards.append(
            '      <div class="preview-card">\n'
            f'        <span class="pr">PR #{n}</span>\n'
            f'        <span class="title">{title}</span>\n'
            f"{apps_line}"
            '        <span class="links">\n'
            f'          <a class="open" href="preview/pr-{n}/">Open preview</a>\n'
            f'          <a href="{html.escape(pr_link)}">View PR</a>\n'
            "        </span>\n"
            "      </div>"
        )
    return (
        '\n  <section class="previews">\n'
        f'    <h2>Active previews <span class="count">{len(previews)}</span></h2>\n'
        '    <div class="preview-list">\n'
        + "\n".join(cards)
        + "\n"
        "    </div>\n"
        "  </section>\n"
    )


def render(
    title: str,
    heading: str,
    apps: list[str],
    previews: list[dict],
    repo_url: str,
    template: str | None = None,
) -> str:
    tmpl = template if template is not None else TEMPLATE_PATH.read_text()
    return (
        tmpl.replace("__TITLE__", html.escape(title))
        .replace("__HEADING__", html.escape(heading))
        .replace("__ITEMS__", render_items(apps))
        .replace("__PREVIEWS__", render_previews_section(previews, repo_url))
        .replace("__REPO_URL__", html.escape(repo_url))
    )


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)

    site = sub.add_parser("site", help="render the production root index")
    site.add_argument("--dir", required=True, help="published site directory to scan")
    site.add_argument("--repo-url", default="", help="repository URL, e.g. https://github.com/owner/repo")
    site.add_argument("--title", default="Playground")
    site.add_argument("--heading", default="Playground")
    site.add_argument("--output", required=True)

    preview = sub.add_parser("preview", help="render a per-PR preview index")
    preview.add_argument("--dir", required=True, help="preview directory to scan")
    preview.add_argument("--pr", required=True, type=int)
    preview.add_argument("--repo-url", default="")
    preview.add_argument("--output", required=True)

    args = parser.parse_args(argv)
    root = Path(args.dir)

    if args.mode == "site":
        content = render(
            args.title,
            args.heading,
            scan_apps(root),
            scan_previews(root),
            args.repo_url,
        )
    else:
        label = f"Preview — PR #{args.pr}"
        content = render(label, label, scan_apps(root), [], args.repo_url)

    Path(args.output).write_text(content)


if __name__ == "__main__":
    main()
