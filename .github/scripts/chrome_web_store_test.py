#!/usr/bin/env python3
"""Tests for the Chrome Web Store publish client."""

from __future__ import annotations

import io
import json
import threading
import unittest
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import chrome_web_store as store

ITEM = "canmakefmjmnhhaobdeipbamnalcloap"
PUBLISHER = "pub-1"


def make_zip(version: str) -> str:
    path = f"/tmp/duplicate-tabs-{version}.zip"
    payload = json.dumps({"manifest_version": 3, "version": version, "name": "Close Duplicate Tabs"}).encode()
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("manifest.json", payload)
    return path


class Handler(BaseHTTPRequestHandler):
    server_version = "TestStore"

    def log_message(self, fmt: str, *args) -> None:
        return

    def _read(self) -> bytes:
        length = int(self.headers.get("Content-Length", "0"))
        return self.rfile.read(length) if length else b""

    def _send(self, status: int, payload: dict) -> None:
        body = json.dumps(payload).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        self.server.calls.append(("GET", self.path, self.headers.get("Authorization")))
        self._send(200, self.server.next_status())

    def do_POST(self) -> None:
        body = self._read()
        self.server.calls.append(("POST", self.path, self.headers.get("Authorization"), body))
        if self.path == "/token":
            self._send(200, {"access_token": "test-token"})
            return
        if self.path.endswith(":upload"):
            self._send(200, self.server.upload_response)
            return
        if self.path.endswith(":publish"):
            self.server.publish_body = json.loads(body.decode())
            self._send(200, {"state": "PENDING_REVIEW"})
            return
        self._send(404, {"error": {"message": "not found"}})


class StoreServer(ThreadingHTTPServer):
    def __init__(self):
        super().__init__(("127.0.0.1", 0), Handler)
        self.calls = []
        self.statuses = []
        self.upload_response = {"uploadState": "SUCCEEDED", "crxVersion": "0.1.0"}
        self.publish_body = None

    def next_status(self) -> dict:
        if self.statuses:
            return self.statuses.pop(0)
        return {}


class DecideTest(unittest.TestCase):
    def test_upload_when_nothing_is_published(self):
        decision = store.decide({}, "0.1.0")
        self.assertEqual(decision.action, "upload")

    def test_upload_when_the_published_version_is_older(self):
        status = {
            "publishedItemRevisionStatus": {
                "state": "PUBLISHED",
                "distributionChannels": [{"crxVersion": "0.0.2"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "upload")

    def test_skip_when_this_version_is_live(self):
        status = {
            "publishedItemRevisionStatus": {
                "state": "PUBLISHED_TO_TESTERS",
                "distributionChannels": [{"crxVersion": "0.1.0"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "skip")

    def test_skip_when_this_version_is_in_review(self):
        status = {
            "submittedItemRevisionStatus": {
                "state": "PENDING_REVIEW",
                "distributionChannels": [{"crxVersion": "0.1.0.0"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "skip")

    def test_fail_when_this_version_was_rejected(self):
        status = {
            "submittedItemRevisionStatus": {
                "state": "REJECTED",
                "distributionChannels": [{"crxVersion": "0.1.0"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "fail")

    def test_fail_when_another_version_is_in_review(self):
        status = {
            "submittedItemRevisionStatus": {
                "state": "STAGED",
                "distributionChannels": [{"crxVersion": "0.0.9"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "fail")

    def test_fail_when_the_published_version_is_newer(self):
        status = {
            "publishedItemRevisionStatus": {
                "state": "PUBLISHED",
                "distributionChannels": [{"crxVersion": "0.2.0"}],
            }
        }
        self.assertEqual(store.decide(status, "0.1.0").action, "fail")

    def test_fail_when_the_item_is_taken_down(self):
        self.assertEqual(store.decide({"takenDown": True}, "0.1.0").action, "fail")

    def test_version_order(self):
        self.assertEqual(store.compare_versions("0.0.2", "0.1.0"), -1)
        self.assertEqual(store.compare_versions("1.0", "1.0.0.0"), 0)
        self.assertEqual(store.compare_versions("1.2", "1.1.9"), 1)
        with self.assertRaises(store.PublishError):
            store.parse_version("01.2")
        with self.assertRaises(store.PublishError):
            store.parse_version("1.70000")


class PublishFlowTest(unittest.TestCase):
    def setUp(self):
        self.server = StoreServer()
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        host, port = self.server.server_address
        origin = f"http://{host}:{port}"
        self.env = {
            "CHROME_WEB_STORE_CLIENT_ID": "client",
            "CHROME_WEB_STORE_CLIENT_SECRET": "secret",
            "CHROME_WEB_STORE_REFRESH_TOKEN": "refresh",
            "CHROME_WEB_STORE_PUBLISHER_ID": PUBLISHER,
            "CHROME_WEB_STORE_ITEM_ID": ITEM,
            "CHROME_WEB_STORE_PUBLISH_TYPE": "DEFAULT_PUBLISH",
            "CHROME_WEB_STORE_API_ORIGIN": origin,
            "CHROME_WEB_STORE_TOKEN_URL": origin + "/token",
        }
        self.zip_path = make_zip("0.1.0")

    def tearDown(self):
        self.server.shutdown()
        self.thread.join(timeout=5)
        self.server.server_close()

    def test_uploads_and_publishes_with_default_publish(self):
        self.server.statuses = [
            {"publishedItemRevisionStatus": {"state": "PUBLISHED", "distributionChannels": [{"crxVersion": "0.0.2"}]}},
            {"lastAsyncUploadState": "IN_PROGRESS"},
            {"lastAsyncUploadState": "SUCCEEDED"},
        ]
        self.server.upload_response = {"uploadState": "IN_PROGRESS"}
        decision = store.publish_package(self.zip_path, self.env, sleep=lambda _seconds: None)
        self.assertEqual(decision.action, "submitted")
        self.assertIn("PENDING_REVIEW", decision.message)
        paths = [call[1] for call in self.server.calls]
        self.assertIn("/token", paths)
        self.assertTrue(any(path.endswith(":upload") for path in paths))
        self.assertEqual(self.server.publish_body, {"publishType": "DEFAULT_PUBLISH"})
        upload = next(call for call in self.server.calls if call[1].endswith(":upload"))
        self.assertEqual(upload[2], "Bearer test-token")
        with zipfile.ZipFile(io.BytesIO(upload[3])) as archive:
            manifest = json.loads(archive.read("manifest.json"))
        self.assertEqual(manifest["version"], "0.1.0")

    def test_skips_a_version_that_is_already_live(self):
        self.server.statuses = [
            {"publishedItemRevisionStatus": {"state": "PUBLISHED", "distributionChannels": [{"crxVersion": "0.1.0"}]}}
        ]
        decision = store.publish_package(self.zip_path, self.env, sleep=lambda _seconds: None)
        self.assertEqual(decision.action, "skip")
        paths = [call[1] for call in self.server.calls]
        self.assertFalse(any(path.endswith(":upload") or path.endswith(":publish") for path in paths))

    def test_does_not_upload_a_rejected_version(self):
        self.server.statuses = [
            {"submittedItemRevisionStatus": {"state": "REJECTED", "distributionChannels": [{"crxVersion": "0.1.0"}]}}
        ]
        decision = store.publish_package(self.zip_path, self.env, sleep=lambda _seconds: None)
        self.assertEqual(decision.action, "fail")
        paths = [call[1] for call in self.server.calls]
        self.assertFalse(any(path.endswith(":upload") for path in paths))

    def test_refuses_a_non_loopback_origin(self):
        env = dict(self.env)
        env["CHROME_WEB_STORE_API_ORIGIN"] = "http://example.com"
        with self.assertRaises(store.PublishError):
            store.publish_package(self.zip_path, env, sleep=lambda _seconds: None)
        self.assertEqual(self.server.calls, [])

    def test_refuses_a_bad_item_id(self):
        env = dict(self.env)
        env["CHROME_WEB_STORE_ITEM_ID"] = "not-an-id"
        with self.assertRaises(store.PublishError):
            store.publish_package(self.zip_path, env, sleep=lambda _seconds: None)


if __name__ == "__main__":
    unittest.main()
