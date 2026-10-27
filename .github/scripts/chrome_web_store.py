#!/usr/bin/env python3
"""Upload a Chrome extension zip and publish it with the Chrome Web Store API v2.

The item already exists. This script does not create an item and does not
change its visibility. publishType DEFAULT_PUBLISH releases the uploaded
version to the item's current audience after review.

Required environment variables:

  CHROME_WEB_STORE_PUBLISHER_ID

  Plus one way to get a chromewebstore-scoped access token. Either:

    CHROME_WEB_STORE_ACCESS_TOKEN
      An already-minted access token, good for this call only. The
      workflow gets this from google-github-actions/auth impersonating a
      Workload Identity Federation service account (see
      gcp/terraform and chrome-extension/README.md), so no refresh token
      is stored as a GitHub secret.

  Or, the older OAuth refresh-token flow:

    CHROME_WEB_STORE_CLIENT_ID
    CHROME_WEB_STORE_CLIENT_SECRET
    CHROME_WEB_STORE_REFRESH_TOKEN

Optional:

  CHROME_WEB_STORE_ITEM_ID       default cfmebakopkdpedmdbpcpfibhodmppigj
  CHROME_WEB_STORE_PUBLISH_TYPE  DEFAULT_PUBLISH or STAGED_PUBLISH
  CHROME_WEB_STORE_API_ORIGIN    tests only; must be http://127.0.0.1 or http://localhost
  CHROME_WEB_STORE_TOKEN_URL     tests only; same loopback rule
"""

from __future__ import annotations

import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from dataclasses import dataclass

DEFAULT_ITEM_ID = "cfmebakopkdpedmdbpcpfibhodmppigj"
API_ORIGIN = "https://chromewebstore.googleapis.com"
TOKEN_URL = "https://oauth2.googleapis.com/token"
PUBLISH_TYPES = ("DEFAULT_PUBLISH", "STAGED_PUBLISH")
LIVE_STATES = ("PUBLISHED", "PUBLISHED_TO_TESTERS")
OPEN_REVIEW = ("PENDING_REVIEW", "STAGED")
CLOSED_REVIEW = ("REJECTED", "CANCELLED")
UPLOAD_OK = ("SUCCEEDED",)
UPLOAD_WAIT = ("IN_PROGRESS",)
UPLOAD_FAIL = ("FAILED", "NOT_FOUND", "UPLOAD_STATE_UNSPECIFIED")
PUBLISH_OK = ("PENDING_REVIEW", "PUBLISHED", "PUBLISHED_TO_TESTERS", "STAGED")


class PublishError(Exception):
    """The store refused the package, or the package is not a newer version."""


@dataclass(frozen=True)
class Decision:
    action: str
    message: str


def parse_version(value: str) -> tuple[int, int, int, int]:
    parts = value.split(".")
    if not 1 <= len(parts) <= 4:
        raise PublishError(f"version {value!r} must have 1 to 4 numbers")
    numbers: list[int] = []
    for part in parts:
        if part == "" or not part.isdigit() or (len(part) > 1 and part.startswith("0")):
            raise PublishError(f"version {value!r} has an invalid component")
        number = int(part)
        if number > 65535:
            raise PublishError(f"version {value!r} has a component above 65535")
        numbers.append(number)
    while len(numbers) < 4:
        numbers.append(0)
    return (numbers[0], numbers[1], numbers[2], numbers[3])


def compare_versions(left: str, right: str) -> int:
    parsed_left = parse_version(left)
    parsed_right = parse_version(right)
    if parsed_left < parsed_right:
        return -1
    if parsed_left > parsed_right:
        return 1
    return 0


def versions_match(left: str, right: str) -> bool:
    return compare_versions(left, right) == 0


def channel_versions(revision: dict | None) -> list[str]:
    if not revision:
        return []
    found: list[str] = []
    for channel in revision.get("distributionChannels") or []:
        version = channel.get("crxVersion")
        if isinstance(version, str) and version != "":
            found.append(version)
    return found


def _matches(version: str, candidates: list[str]) -> bool:
    for candidate in candidates:
        if versions_match(version, candidate):
            return True
    return False


def decide(status: dict, version: str) -> Decision:
    """Choose skip, upload, or fail from a fetchStatus response."""
    if status.get("takenDown") is True:
        return Decision("fail", "The Chrome Web Store item is taken down. Check the developer dashboard.")
    published = status.get("publishedItemRevisionStatus") or {}
    submitted = status.get("submittedItemRevisionStatus") or {}
    published_versions = channel_versions(published)
    submitted_versions = channel_versions(submitted)
    published_state = published.get("state") or ""
    submitted_state = submitted.get("state") or ""

    if published_state in LIVE_STATES and _matches(version, published_versions):
        return Decision("skip", f"Version {version} is already {published_state}.")
    if submitted_state in OPEN_REVIEW + LIVE_STATES and _matches(version, submitted_versions):
        return Decision("skip", f"Version {version} is already {submitted_state}.")
    if submitted_state in CLOSED_REVIEW and _matches(version, submitted_versions):
        return Decision(
            "fail",
            f"Version {version} was {submitted_state}. Increase the version in manifest.json and merge again.",
        )
    if submitted_state in OPEN_REVIEW and submitted_versions and not _matches(version, submitted_versions):
        blocking = submitted_versions[0]
        return Decision(
            "fail",
            f"Version {blocking} is {submitted_state}. Wait for that review to finish before uploading {version}.",
        )
    for existing in published_versions:
        if published_state in LIVE_STATES and compare_versions(existing, version) > 0:
            return Decision(
                "fail",
                f"Published version {existing} is newer than {version}. Increase the version in manifest.json.",
            )
    return Decision("upload", f"Upload version {version}.")


def manifest_version(path: str) -> str:
    try:
        with zipfile.ZipFile(path) as archive:
            manifest = json.loads(archive.read("manifest.json"))
    except (OSError, zipfile.BadZipFile, KeyError, json.JSONDecodeError) as error:
        raise PublishError(f"cannot read manifest.json from {path}: {error}") from error
    version = manifest.get("version")
    if not isinstance(version, str):
        raise PublishError("manifest.json has no version string")
    parse_version(version)
    return version


def _hostname_ok(url: str, production_host: str) -> None:
    parsed = urllib.parse.urlparse(url)
    host = parsed.hostname or ""
    if parsed.scheme == "https" and host == production_host:
        return
    if parsed.scheme == "http" and host in ("127.0.0.1", "localhost"):
        return
    raise PublishError(f"refusing URL {url}")


def resolve_endpoints(env: dict[str, str]) -> tuple[str, str]:
    origin = env.get("CHROME_WEB_STORE_API_ORIGIN", API_ORIGIN).rstrip("/")
    token_url = env.get("CHROME_WEB_STORE_TOKEN_URL", TOKEN_URL)
    _hostname_ok(origin, "chromewebstore.googleapis.com")
    _hostname_ok(token_url, "oauth2.googleapis.com")
    return origin, token_url


def _error_detail(payload: dict, raw_text: str) -> str:
    """Pull whatever detail an error response carries.

    The Chrome Web Store API nests detail under error.message. The OAuth
    token endpoint instead puts a short code directly in error, with the
    human-readable text in a sibling error_description. A response that is
    not a JSON object at all (a proxy's HTML error page, for example) still
    has text worth showing, so that is the last resort.
    """
    error_body = payload.get("error")
    if isinstance(error_body, dict):
        message = str(error_body.get("message") or "").strip()
        if message:
            return message
    if isinstance(error_body, str) and error_body:
        description = payload.get("error_description")
        if isinstance(description, str) and description:
            return f"{error_body}: {description}"
        return error_body
    return raw_text.strip()[:500]


def _request(url: str, method: str, headers: dict[str, str], body: bytes | None, timeout: float) -> tuple[int, dict]:
    request = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            raw = response.read()
            status = response.status
    except urllib.error.HTTPError as error:
        raw = error.read()
        status = error.code
    except urllib.error.URLError as error:
        raise PublishError(f"{method} {url} failed: {error.reason}") from error
    text = raw.decode("utf-8", "replace") if raw else ""
    payload: dict = {}
    not_an_object = False
    if raw:
        try:
            parsed = json.loads(text)
        except json.JSONDecodeError:
            not_an_object = True
        else:
            if isinstance(parsed, dict):
                payload = parsed
            else:
                not_an_object = True
    error_status = status < 200 or status >= 300
    if error_status:
        detail = _error_detail(payload, text if not_an_object else "")
        if detail:
            raise PublishError(f"Chrome Web Store API request failed: {detail}")
        raise PublishError(f"Chrome Web Store API request failed: HTTP {status}")
    if not_an_object:
        raise PublishError(f"{method} {url} returned a body that is not a JSON object")
    return status, payload


def fetch_token(token_url: str, client_id: str, client_secret: str, refresh_token: str) -> str:
    form = urllib.parse.urlencode(
        {
            "client_id": client_id,
            "client_secret": client_secret,
            "refresh_token": refresh_token,
            "grant_type": "refresh_token",
        }
    ).encode()
    _status, payload = _request(
        token_url,
        "POST",
        {"Content-Type": "application/x-www-form-urlencoded"},
        form,
        30,
    )
    token = payload.get("access_token")
    if not isinstance(token, str) or token == "":
        raise PublishError("token response did not include an access token")
    return token


def resolve_token(env: dict[str, str], token_url: str) -> str:
    """Get a chromewebstore-scoped access token, preferring one already minted.

    The workflow mints CHROME_WEB_STORE_ACCESS_TOKEN itself, by having
    google-github-actions/auth impersonate a Workload Identity Federation
    service account with that scope. When that is set, this script never
    talks to the OAuth token endpoint and no refresh token needs to exist.
    Otherwise it falls back to exchanging a stored refresh token, which is
    still useful outside CI.
    """
    access_token = env.get("CHROME_WEB_STORE_ACCESS_TOKEN", "").strip()
    if access_token:
        return access_token
    client_id = _env_required(env, "CHROME_WEB_STORE_CLIENT_ID")
    client_secret = _env_required(env, "CHROME_WEB_STORE_CLIENT_SECRET")
    refresh_token = _env_required(env, "CHROME_WEB_STORE_REFRESH_TOKEN")
    return fetch_token(token_url, client_id, client_secret, refresh_token)


def item_name(publisher_id: str, item_id: str) -> str:
    if not publisher_id or any(char in publisher_id for char in "/?# "):
        raise PublishError("CHROME_WEB_STORE_PUBLISHER_ID is missing or not a single path segment")
    if len(item_id) != 32 or any(char < "a" or char > "p" for char in item_id):
        raise PublishError("CHROME_WEB_STORE_ITEM_ID must be 32 characters from a to p")
    return f"publishers/{urllib.parse.quote(publisher_id, safe='')}/items/{item_id}"


def fetch_status(origin: str, name: str, token: str) -> dict:
    _status, payload = _request(
        f"{origin}/v2/{name}:fetchStatus",
        "GET",
        {"Authorization": f"Bearer {token}"},
        None,
        30,
    )
    return payload


def upload_zip(origin: str, name: str, token: str, path: str) -> dict:
    with open(path, "rb") as handle:
        blob = handle.read()
    _status, payload = _request(
        f"{origin}/upload/v2/{name}:upload",
        "POST",
        {"Authorization": f"Bearer {token}", "Content-Type": "application/zip"},
        blob,
        120,
    )
    return payload


def publish_item(origin: str, name: str, token: str, publish_type: str, skip_review: bool = False) -> dict:
    body_fields: dict[str, str | bool] = {"publishType": publish_type}
    if skip_review:
        body_fields["skipReview"] = True
    body = json.dumps(body_fields).encode()
    _status, payload = _request(
        f"{origin}/v2/{name}:publish",
        "POST",
        {"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
        body,
        60,
    )
    return payload


def submit_for_publish(origin: str, name: str, token: str, publish_type: str, version: str) -> Decision:
    """Publish without review when the store allows it, otherwise submit for review."""
    try:
        published = publish_item(origin, name, token, publish_type, skip_review=True)
        skipped_review = True
    except PublishError as error:
        detail = str(error).rstrip(".")
        print(
            f"The store did not skip review: {detail}. Submitting version {version} for review.",
            file=sys.stderr,
        )
        published = publish_item(origin, name, token, publish_type, skip_review=False)
        skipped_review = False
    state = published.get("state") or ""
    if state not in PUBLISH_OK:
        raise PublishError(f"Chrome Web Store publish returned state {state or '(missing)'}")
    warnings = ((published.get("warningInfo") or {}).get("warnings")) or []
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    if skipped_review and state in ("PUBLISHED", "PUBLISHED_TO_TESTERS"):
        return Decision("submitted", f"Published version {version} without review. Store state: {state}.")
    return Decision("submitted", f"Submitted version {version} for review. Store state: {state}.")


def wait_for_upload(origin: str, name: str, token: str, sleep, attempts: int = 24) -> dict:
    """Poll fetchStatus until the latest upload is no longer in progress."""
    status: dict = {}
    for _attempt in range(attempts):
        status = fetch_status(origin, name, token)
        state = status.get("lastAsyncUploadState") or ""
        if state in UPLOAD_OK:
            return status
        if state in UPLOAD_FAIL:
            raise PublishError(f"Chrome Web Store upload failed with state {state}")
        if state not in UPLOAD_WAIT and state != "":
            raise PublishError(f"Chrome Web Store returned an unknown upload state {state}")
        sleep(5)
    raise PublishError("timed out waiting for the Chrome Web Store upload to finish")


def _env_required(env: dict[str, str], key: str) -> str:
    value = env.get(key, "").strip()
    if value == "":
        raise PublishError(f"{key} is required")
    return value


def publish_package(path: str, env: dict[str, str] | None = None, sleep=time.sleep) -> Decision:
    """Upload path when its manifest version is newer, then publish it."""
    values = os.environ if env is None else env
    version = manifest_version(path)
    origin, token_url = resolve_endpoints(values)
    publisher_id = _env_required(values, "CHROME_WEB_STORE_PUBLISHER_ID")
    item_id = values.get("CHROME_WEB_STORE_ITEM_ID", DEFAULT_ITEM_ID).strip() or DEFAULT_ITEM_ID
    publish_type = values.get("CHROME_WEB_STORE_PUBLISH_TYPE", "DEFAULT_PUBLISH").strip() or "DEFAULT_PUBLISH"
    if publish_type not in PUBLISH_TYPES:
        raise PublishError(
            "CHROME_WEB_STORE_PUBLISH_TYPE must be DEFAULT_PUBLISH or STAGED_PUBLISH. "
            "The Chrome Web Store API v2 has no trusted-tester publish type. "
            "The audience is the one saved on the item in the developer dashboard."
        )
    name = item_name(publisher_id, item_id)
    token = resolve_token(values, token_url)
    status = fetch_status(origin, name, token)
    if status.get("lastAsyncUploadState") in UPLOAD_WAIT:
        status = wait_for_upload(origin, name, token, sleep)
    decision = decide(status, version)
    if decision.action != "upload":
        return decision
    uploaded = upload_zip(origin, name, token, path)
    upload_state = uploaded.get("uploadState") or ""
    crx_version = uploaded.get("crxVersion")
    if isinstance(crx_version, str) and crx_version != "" and not versions_match(crx_version, version):
        raise PublishError(f"store accepted version {crx_version}, package is {version}")
    if upload_state in UPLOAD_WAIT:
        wait_for_upload(origin, name, token, sleep)
    elif upload_state not in UPLOAD_OK:
        raise PublishError(f"Chrome Web Store upload returned state {upload_state or '(missing)'}")
    return submit_for_publish(origin, name, token, publish_type, version)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        print("usage: chrome_web_store.py <extension.zip>", file=sys.stderr)
        return 2
    try:
        decision = publish_package(args[0])
    except PublishError as error:
        print(str(error), file=sys.stderr)
        return 1
    print(decision.message)
    if decision.action == "fail":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
