#!/usr/bin/env python3
"""Push an mcu-lab firmware .bin + gzipped symbolized ELF as a two-layer OCI artifact to GHCR.

Layer 0 (`application/octet-stream`): raw espflash .bin for BLE OTA from iOS.
Layer 1 (`application/vnd.mculab.elf.v1+gzip`): gzipped ELF with line-tables-only
DWARF symbols for automatic server-side symbolization in `xiao-otel`.
"""

import base64
import gzip
import hashlib
import json
import os
import sys
import urllib.request

ELF_MEDIA_TYPE = "application/vnd.mculab.elf.v1+gzip"
BIN_MEDIA_TYPE = "application/octet-stream"
EMPTY_CONFIG_MEDIA_TYPE = "application/vnd.oci.empty.v1+json"


def sha256_digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def fetch_token(registry: str, repo: str, user: str, password: str) -> str:
    url = f"https://{registry}/token?service={registry}&scope=repository:{repo}:pull,push"
    auth = base64.b64encode(f"{user}:{password}".encode()).decode()
    req = urllib.request.Request(url, headers={"Authorization": f"Basic {auth}"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read())["token"]


def upload_blob(registry: str, repo: str, token: str, data: bytes) -> str:
    digest = sha256_digest(data)
    head_req = urllib.request.Request(
        f"https://{registry}/v2/{repo}/blobs/{digest}",
        method="HEAD",
        headers={"Authorization": f"Bearer {token}"},
    )
    try:
        with urllib.request.urlopen(head_req, timeout=30):
            return digest
    except urllib.error.HTTPError as err:
        if err.code != 404:
            raise

    init_req = urllib.request.Request(
        f"https://{registry}/v2/{repo}/blobs/uploads/",
        method="POST",
        data=b"",
        headers={"Authorization": f"Bearer {token}"},
    )
    with urllib.request.urlopen(init_req, timeout=30) as resp:
        location = resp.headers["Location"]

    if location.startswith("/"):
        location = f"https://{registry}{location}"
    sep = "&" if "?" in location else "?"
    put_req = urllib.request.Request(
        f"{location}{sep}digest={digest}",
        method="PUT",
        data=data,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/octet-stream",
            "Content-Length": str(len(data)),
        },
    )
    with urllib.request.urlopen(put_req, timeout=120):
        return digest


def put_manifest(registry: str, repo: str, token: str, tag: str, manifest_bytes: bytes) -> str:
    req = urllib.request.Request(
        f"https://{registry}/v2/{repo}/manifests/{tag}",
        method="PUT",
        data=manifest_bytes,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/vnd.oci.image.manifest.v1+json",
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return resp.headers.get("Docker-Content-Digest", sha256_digest(manifest_bytes))


def main() -> int:
    if len(sys.argv) != 5:
        print("usage: publish-oci.py <repo> <git-sha> <firmware.bin> <firmware.elf>", file=sys.stderr)
        return 2

    repo, git_sha, bin_path, elf_path = sys.argv[1], sys.argv[2].lower(), sys.argv[3], sys.argv[4]
    if len(git_sha) != 40 or any(c not in "0123456789abcdef" for c in git_sha):
        print(f"invalid git commit sha: {git_sha!r}", file=sys.stderr)
        return 2

    app_name = repo.rsplit("/", 1)[-1]
    registry = os.environ.get("OCI_REGISTRY", "ghcr.io")
    user = os.environ["GH_ACTOR"]
    password = os.environ["GH_TOKEN"]

    with open(bin_path, "rb") as f:
        bin_bytes = f.read()
    with open(elf_path, "rb") as f:
        elf_bytes = f.read()

    elf_gz = gzip.compress(elf_bytes, compresslevel=6)
    empty_cfg = b"{}"

    token = fetch_token(registry, repo, user, password)
    cfg_digest = upload_blob(registry, repo, token, empty_cfg)
    bin_digest = upload_blob(registry, repo, token, bin_bytes)
    elf_digest = upload_blob(registry, repo, token, elf_gz)

    elf_build_id = hashlib.sha256(elf_bytes).hexdigest()[:40]

    manifest = {
        "schemaVersion": 2,
        "mediaType": "application/vnd.oci.image.manifest.v1+json",
        "config": {
            "mediaType": EMPTY_CONFIG_MEDIA_TYPE,
            "digest": cfg_digest,
            "size": len(empty_cfg),
        },
        "layers": [
            {
                "mediaType": BIN_MEDIA_TYPE,
                "digest": bin_digest,
                "size": len(bin_bytes),
                "annotations": {"org.opencontainers.image.title": f"{app_name}.bin"},
            },
            {
                "mediaType": ELF_MEDIA_TYPE,
                "digest": elf_digest,
                "size": len(elf_gz),
                "annotations": {
                    "org.opencontainers.image.title": f"{app_name}.elf.gz",
                    "org.opencontainers.image.revision": git_sha,
                    "vnd.mculab.build_id": elf_build_id,
                },
            },
        ],
    }
    manifest_bytes = json.dumps(manifest, separators=(",", ":")).encode()

    digest = put_manifest(registry, repo, token, git_sha, manifest_bytes)
    print(f"published {registry}/{repo}:{git_sha} ({digest})")
    build_id_tag = f"buildid-{elf_build_id}"
    put_manifest(registry, repo, token, build_id_tag, manifest_bytes)
    print(f"published {registry}/{repo}:{build_id_tag} ({digest})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
