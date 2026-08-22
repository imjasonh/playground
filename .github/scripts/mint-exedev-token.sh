#!/usr/bin/env bash
# Mint an exe.dev HTTPS API bearer token (exe0) by signing permissions with an
# OpenSSH private key. Writes EXEDEV_TOKEN into $GITHUB_ENV when set, and always
# prints a redacted confirmation to stdout.
#
# Environment:
#   EXEDEV_SSH_PRIVATE_KEY  OpenSSH private key whose public half is on exe.dev
#   EXEDEV_TOKEN_PERMS      Optional JSON permissions object (default: deploy cmds)
set -euo pipefail

: "${EXEDEV_SSH_PRIVATE_KEY:?EXEDEV_SSH_PRIVATE_KEY must be set}"

perms=${EXEDEV_TOKEN_PERMS:-'{"cmds":["ls","new","rm","rename","resize","ssh-key list","ssh-key add","ssh-key remove","ssh-key rename"]}'}

key_file=$(mktemp)
cleanup() { rm -f "$key_file"; }
trap cleanup EXIT

printf '%s\n' "$EXEDEV_SSH_PRIVATE_KEY" >"$key_file"
chmod 600 "$key_file"

# Normalize Windows newlines if a pasted secret included them.
if grep -q $'\r' "$key_file"; then
  tr -d '\r' <"$key_file" >"${key_file}.unix"
  mv "${key_file}.unix" "$key_file"
  chmod 600 "$key_file"
fi

b64url() {
  # stdin -> base64url without padding
  openssl base64 -A | tr '+/' '-_' | tr -d '='
}

payload=$(printf '%s' "$perms" | b64url)
sig=$(printf '%s' "$perms" | ssh-keygen -Y sign -f "$key_file" -n v0@exe.dev)
sigblob=$(printf '%s\n' "$sig" | sed '1d;$d' | tr -d '\n' | b64url)

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
