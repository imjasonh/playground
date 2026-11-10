# fakestore

fakestore is a test-only Sigstore. It runs a Fulcio certificate authority, a
Rekor v2 transparency log, a certificate transparency (CT) log, and an
RFC 3161 timestamp authority (TSA) from keys that it generates and keeps in a
local directory. It signs any file and writes a Sigstore bundle with the same
profile as one that Sigstore issues to a GitHub Actions workflow, so you can
test c3-boot devices and tools end to end without network access.

> **Warning:** fakestore is for tests only. Anyone who can read its directory
> can sign anything as any identity. Never put a trusted root that fakestore
> writes, or a trust-root blob built from one, on a production device or in a
> production build.

## What a bundle contains

Each bundle matches `../testdata/conformance/rekor2-happy-path`, a real
bundle from Sigstore staging, field for field:

- `mediaType` is `application/vnd.dev.sigstore.bundle.v0.3+json`.
- `verificationMaterial.certificate` is a Fulcio leaf certificate for a
  GitHub Actions identity. It has an empty subject, a 10-minute validity, a
  P-256 key, and an `ecdsa-with-SHA384` signature from a P-384 intermediate
  with the subject `O=sigstore.dev, CN=sigstore-intermediate`. Its extensions
  are the ones Fulcio writes, in Fulcio's order: critical `keyUsage`
  (`digitalSignature`), `extKeyUsage` (`codeSigning`), subject and authority
  key identifiers, a critical SAN URI, the identity extensions
  `1.3.6.1.4.1.57264.1.1` through `.1.6` as raw strings and `.1.8` through
  `.1.22` as DER `UTF8String` values, and an embedded SCT list. As Fulcio
  does, fakestore first signs a precertificate with the CT poison extension,
  gets an SCT for it from its CT log, and then signs the final certificate.
- `verificationMaterial.tlogEntries[0]` is a Rekor v2 `hashedrekord` 0.0.2
  entry: its canonical JSON body, an inclusion proof into a tree with filler
  entries, and a C2SP checkpoint signed by the log's Ed25519 key. The log ID
  is `SHA-256(origin || 0x0A || 0x01 || public key)`, as Rekor v2 defines it.
- `verificationMaterial.timestampVerificationData` holds a DER
  `TimeStampResp`, status granted, from
  [digitorus/timestamp](https://github.com/digitorus/timestamp), which
  Sigstore's timestamp-authority uses. Its token is signed by a P-384 TSA
  leaf certificate (`CN=sigstore-tsa`, critical `timeStamping` key usage)
  that it embeds, with policy `1.3.6.1.4.1.57264.2`, a nonce, a 1-second
  accuracy, and the signed attributes `contentType`, `signingTime`,
  `messageDigest`, and `signingCertificateV2`.
- `messageSignature` holds the SHA-256 digest of the file and a DER ECDSA
  signature over it.

For the byte layouts that c3-boot checks, see
[`../docs/formats.md`](../docs/formats.md).

## Before you begin

Install Go 1.22 or later. The module needs a newer Go, which the `go`
command downloads when `GOTOOLCHAIN=auto` is set, as it is by default.

## Create an instance

To generate the keys, certificates, and trusted root, run the following
command:

```bash
go run . init -dir DIR
```

Replace `DIR` with an empty or new directory.

The command writes PEM private keys and certificates, and a
`trusted_root.json` file in Sigstore's `TrustedRoot` format with one
certificate authority, one Rekor v2 log, one CT log, and one TSA.

The following flags are optional:

- `-origin`: the log's checkpoint origin. The default is `log.c3-boot.test`.
  The log's `baseUrl` is `https://` followed by the origin, because
  sigstore-go reads the origin from the `baseUrl` host.
- `-not-before` and `-not-after`: the validity window, in RFC 3339 format, of
  every certificate and trusted-root entry. The defaults are
  `2020-01-01T00:00:00Z` and `2040-12-31T23:59:59Z`.

## Sign a file

To sign a file, run the following command:

```bash
go run . sign -dir DIR -artifact FILE -out BUNDLE
```

Replace the following:

- `DIR`: the directory that `init` wrote.
- `FILE`: the file to sign.
- `BUNDLE`: the path to write the bundle JSON to.

The command generates a new P-256 key for each signature and writes nothing
except the bundle. The following flags are optional:

| Flag | Default | Sets |
| --- | --- | --- |
| `-issuer` | `https://token.actions.githubusercontent.com` | Extensions `.1.1` and `.1.8` |
| `-build-signer-uri` | `https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main` | The SAN URI and extensions `.1.9` and `.1.18`; the repository, owner, and ref extensions come from it |
| `-repository-id` | `1234` | Extension `.1.15` |
| `-owner-id` | `5678` | Extension `.1.17` |
| `-trigger` | `push` | Extensions `.1.2` and `.1.20` |
| `-commit` | Random | The commit SHA in extensions `.1.3`, `.1.10`, `.1.13`, and `.1.19` |
| `-time` | Now | The TSA time, in RFC 3339 format. The leaf certificate is valid from 1 minute before it through 9 minutes after it |
| `-tree-size` | `8` | The size of the log tree that the checkpoint signs |
| `-leaf-index` | `-tree-size` minus 1 | The entry's log index |

The `-build-signer-uri` value must have the form
`https://HOST/OWNER/REPO/WORKFLOW_PATH@REF`. Hashing the tree visits every
leaf, so the time that `sign` takes grows with `-tree-size`.

## Verify a bundle

To verify a bundle with
[sigstore-go](https://github.com/sigstore/sigstore-go), run the following
command:

```bash
go run . verify -trusted-root DIR/trusted_root.json -bundle BUNDLE -artifact FILE
```

The command prints `OK` and exits with status 0, or prints the error and
exits with status 1. It requires one RFC 3161 timestamp, one transparency log
entry, and one SCT, and a certificate whose issuer and SAN URI equal the
`-issuer` and `-build-signer-uri` values exactly. Those flags have the same
defaults as in `sign`.

## Run the tests

To run the tests, run the following commands:

```bash
go vet ./...
go test ./...
```

The tests sign random files and verify them with sigstore-go. They check
that sigstore-go rejects a different file, a changed signature, a changed
checkpoint root, a trusted root from another instance, and a different
identity. They also compare the leaf certificate, the timestamp, and the log
ID derivation with the real bundle and trusted root in
`../testdata/conformance`.
