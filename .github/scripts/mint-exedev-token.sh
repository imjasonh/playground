#!/usr/bin/env bash
# Mint an exe.dev HTTPS API bearer token (exe0) by signing permissions with an
# OpenSSH private key. Writes EXEDEV_TOKEN into $GITHUB_ENV when set, and always
# prints a redacted confirmation to stdout.
#
# Token format matches https://exe.dev/docs/https-api (local signing):
#   payload = base64url(permissions JSON)
#   sigblob = base64url(SSH signature body without BEGIN/END lines)
# Do not re-base64-encode the signature body — it is already base64.
#
# Environment:
#   EXEDEV_SSH_PRIVATE_KEY     OpenSSH private key whose public half is on exe.dev
#   EXEDEV_SSH_PASSPHRASE      Optional passphrase if the private key is encrypted
#   EXEDEV_TOKEN_PERMS         Optional JSON permissions object (default: deploy cmds)
set -euo pipefail

: "${EXEDEV_SSH_PRIVATE_KEY:?EXEDEV_SSH_PRIVATE_KEY must be set}"

perms=${EXEDEV_TOKEN_PERMS:-'{"cmds":["ls","new","rm","rename","resize","ssh-key list","ssh-key add","ssh-key remove","ssh-key rename"]}'}

key_file=$(mktemp)
askpass_file=""
pass_file=""
cleanup() {
  rm -f "$key_file" "$askpass_file" "$pass_file"
}
trap cleanup EXIT

printf '%s\n' "$EXEDEV_SSH_PRIVATE_KEY" >"$key_file"
chmod 600 "$key_file"

# Normalize Windows newlines if a pasted secret included them.
if grep -q $'\r' "$key_file"; then
  tr -d '\r' <"$key_file" >"${key_file}.unix"
  mv "${key_file}.unix" "$key_file"
  chmod 600 "$key_file"
fi

# ssh-keygen prompts on a TTY for encrypted keys. In Actions there is no TTY, so
# either feed the passphrase via SSH_ASKPASS or fail with a clear message.
if [ -n "${EXEDEV_SSH_PASSPHRASE:-}" ]; then
  pass_file=$(mktemp)
  askpass_file=$(mktemp)
  printf '%s' "$EXEDEV_SSH_PASSPHRASE" >"$pass_file"
  chmod 600 "$pass_file"
  cat >"$askpass_file" <<EOF
#!/bin/sh
cat $(printf '%q' "$pass_file")
EOF
  chmod 700 "$askpass_file"
  export SSH_ASKPASS="$askpass_file"
  export SSH_ASKPASS_REQUIRE=force
  # ssh-keygen only consults SSH_ASKPASS when it believes a display exists.
  export DISPLAY="${DISPLAY:-:0}"
else
  # Never hang waiting for a passphrase in CI.
  export SSH_ASKPASS_REQUIRE=never
fi

# RFC 4648 base64url: strip newlines/padding and map +/ -> -_.
# Input is already standard base64 (payload from `base64`, or SSH signature body).
b64url() { tr -d '\n=' | tr '+/' '-_'; }

payload=$(printf '%s' "$perms" | base64 | b64url)

set +e
sig=$(printf '%s' "$perms" | ssh-keygen -Y sign -f "$key_file" -n v0@exe.dev 2>/tmp/exedev-sign.err)
sign_status=$?
set -e

if [ "$sign_status" -ne 0 ]; then
  echo "ssh-keygen -Y sign failed:" >&2
  cat /tmp/exedev-sign.err >&2 || true
  if grep -qiE 'passphrase|decrypt|encrypted' /tmp/exedev-sign.err 2>/dev/null; then
    echo >&2
    echo "EXEDEV_SSH_PRIVATE_KEY appears encrypted. Either store an unencrypted" >&2
    echo "key in that secret (GitHub encrypts secrets at rest), or set" >&2
    echo "EXEDEV_SSH_PASSPHRASE to the key's passphrase." >&2
  fi
  exit "$sign_status"
fi

# Strip -----BEGIN/END SSH SIGNATURE-----; body is already base64.
sigblob=$(printf '%s\n' "$sig" | sed '1d;$d' | b64url)

token="exe0.${payload}.${sigblob}"

if [ -n "${GITHUB_ENV:-}" ]; then
  {
    echo "EXEDEV_TOKEN<<EOF"
    echo "$token"
    echo "EOF"
  } >>"$GITHUB_ENV"
fi

export EXEDEV_TOKEN="$token"
echo "Minted EXEDEV_TOKEN (${#token} chars) for exe.dev API access."

# Fail fast if the signature or key is wrong (avoids a late terraform 401).
whoami_code=$(curl -sS -o /tmp/exedev-whoami.txt -w '%{http_code}' \
  -X POST https://exe.dev/exec \
  -H "Authorization: Bearer ${EXEDEV_TOKEN}" \
  -d 'whoami' || true)
if [ "$whoami_code" != "200" ]; then
  echo "exe.dev rejected the minted token (HTTP ${whoami_code}):" >&2
  cat /tmp/exedev-whoami.txt >&2 || true
  echo >&2
  echo "Check that the public half of EXEDEV_SSH_PRIVATE_KEY is registered" >&2
  echo "(ssh exe.dev ssh-key list) and that the token encoding matches" >&2
  echo "https://exe.dev/docs/https-api" >&2
  exit 1
fi
echo "Verified EXEDEV_TOKEN against exe.dev whoami."
