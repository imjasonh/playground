#!/usr/bin/env python3
"""Create-or-get the Cloudflare KV namespaces a Worker needs and rewrite the
placeholder ids in its wrangler.toml with the real ones, in place.

Run this from the Worker app directory (wrangler-action sets its
workingDirectory), so it edits ./wrangler.toml. It is idempotent: a namespace is
created only when one with the derived title does not already exist, and a
wrangler.toml entry is rewritten only when its id is still a placeholder, so
re-running (or deploying an app whose ids are already real) is a no-op.

Namespaces are titled `<worker-name>-<binding>` (and `<worker-name>-<binding>_preview`
for the preview id), matching wrangler's own convention, so this shares the same
namespaces wrangler would create by hand.

Environment:
  CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID  (wrangler-action provides both)
"""

from __future__ import annotations

import json
import os
import sys
import tomllib
import urllib.error
import urllib.request

CONFIG = "wrangler.toml"
API_BASE = "https://api.cloudflare.com/client/v4"


def die(msg: str) -> "None":
    print(f"provision-worker-kv: {msg}", file=sys.stderr)
    sys.exit(1)


def is_placeholder(value: str | None) -> bool:
    """A KV id we should provision: missing, or still a REPLACE_WITH_* stub."""
    return not value or "REPLACE" in value.upper()


def cf_api(token: str, method: str, path: str, body: dict | None = None) -> dict:
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(
        f"{API_BASE}{path}",
        data=data,
        method=method,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(req) as resp:
            payload = json.load(resp)
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode(errors="replace")
        die(f"Cloudflare API {method} {path} failed: HTTP {exc.code} {detail}")
    except urllib.error.URLError as exc:
        die(f"Cloudflare API {method} {path} failed: {exc.reason}")
    if not payload.get("success", False):
        die(f"Cloudflare API {method} {path} returned errors: {payload.get('errors')}")
    return payload


def kv_namespace_id(token: str, account_id: str, title: str) -> str:
    """Return the id of the KV namespace titled `title`, creating it if absent."""
    listing = cf_api(
        token, "GET", f"/accounts/{account_id}/storage/kv/namespaces?per_page=100"
    )
    for ns in listing.get("result", []):
        if ns.get("title") == title:
            print(f"  found KV namespace '{title}' -> {ns['id']}")
            return ns["id"]
    created = cf_api(
        token,
        "POST",
        f"/accounts/{account_id}/storage/kv/namespaces",
        {"title": title},
    )
    ns_id = created.get("result", {}).get("id")
    if not ns_id:
        die(f"created KV namespace '{title}' but got no id back")
    print(f"  created KV namespace '{title}' -> {ns_id}")
    return ns_id


def main() -> int:
    if not os.path.isfile(CONFIG):
        print(f"No {CONFIG} in {os.getcwd()}; nothing to provision.")
        return 0

    token = os.environ.get("CLOUDFLARE_API_TOKEN")
    account_id = os.environ.get("CLOUDFLARE_ACCOUNT_ID")
    if not token:
        die("CLOUDFLARE_API_TOKEN must be set")
    if not account_id:
        die("CLOUDFLARE_ACCOUNT_ID must be set")

    with open(CONFIG, "rb") as fh:
        cfg = tomllib.load(fh)

    worker_name = cfg.get("name")
    namespaces = cfg.get("kv_namespaces", [])
    if not namespaces:
        print("No [[kv_namespaces]] entries; nothing to provision.")
        return 0
    if not worker_name:
        die(f"{CONFIG} has [[kv_namespaces]] but no top-level `name`")

    text = open(CONFIG, encoding="utf-8").read()
    changed = False

    for ns in namespaces:
        binding = ns.get("binding")
        if not binding:
            die("a [[kv_namespaces]] entry is missing `binding`")
        for field, suffix in (("id", ""), ("preview_id", "_preview")):
            current = ns.get(field)
            if not is_placeholder(current):
                continue
            title = f"{worker_name}-{binding}{suffix}"
            print(f"Provisioning {binding}.{field} from KV namespace '{title}'")
            real_id = kv_namespace_id(token, account_id, title)
            if current:
                needle = f'"{current}"'
                if needle not in text:
                    die(f"could not find {needle} in {CONFIG} to substitute")
                text = text.replace(needle, f'"{real_id}"')
                changed = True
            else:
                die(
                    f"{binding}.{field} is empty in {CONFIG}; add a placeholder "
                    f'like `{field} = "REPLACE_WITH_..."` so it can be substituted'
                )

    if changed:
        with open(CONFIG, "w", encoding="utf-8") as fh:
            fh.write(text)
        print(f"Updated {CONFIG} with real KV namespace ids.")
    else:
        print(f"{CONFIG} already has real KV namespace ids; nothing to do.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
