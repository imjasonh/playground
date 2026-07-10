#!/usr/bin/env python3
"""Create the Cloudflare R2 buckets a Worker needs, if they don't exist yet.

The R2 analog of provision-worker-kv.py, run from the Worker app directory
(wrangler-action sets its workingDirectory) before `wrangler deploy`. Unlike KV
namespaces, R2 buckets are referenced from wrangler.toml by *name* rather than
by a generated id, so nothing needs to be rewritten — each [[r2_buckets]]
entry's `bucket_name` is simply created when absent. Idempotent: existing
buckets are left untouched, so re-running is a no-op.

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
    print(f"provision-worker-r2: {msg}", file=sys.stderr)
    sys.exit(1)


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


def bucket_exists(token: str, account_id: str, name: str) -> bool:
    """True if the account already has a bucket called `name`."""
    cursor = ""
    while True:
        path = f"/accounts/{account_id}/r2/buckets?per_page=100"
        if cursor:
            path += f"&cursor={cursor}"
        payload = cf_api(token, "GET", path)
        result = payload.get("result", {})
        for bucket in result.get("buckets", []):
            if bucket.get("name") == name:
                return True
        cursor = payload.get("result_info", {}).get("cursor") or ""
        if not cursor:
            return False


def main() -> int:
    if not os.path.isfile(CONFIG):
        print(f"No {CONFIG} in {os.getcwd()}; nothing to provision.")
        return 0

    with open(CONFIG, "rb") as fh:
        cfg = tomllib.load(fh)

    buckets = cfg.get("r2_buckets", [])
    if not buckets:
        print("No [[r2_buckets]] entries; nothing to provision.")
        return 0

    token = os.environ.get("CLOUDFLARE_API_TOKEN")
    account_id = os.environ.get("CLOUDFLARE_ACCOUNT_ID")
    if not token:
        die("CLOUDFLARE_API_TOKEN must be set")
    if not account_id:
        die("CLOUDFLARE_ACCOUNT_ID must be set")

    for bucket in buckets:
        name = bucket.get("bucket_name")
        if not name:
            die("a [[r2_buckets]] entry is missing `bucket_name`")
        if bucket_exists(token, account_id, name):
            print(f"R2 bucket '{name}' already exists; nothing to do.")
            continue
        cf_api(token, "POST", f"/accounts/{account_id}/r2/buckets", {"name": name})
        print(f"Created R2 bucket '{name}'.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
