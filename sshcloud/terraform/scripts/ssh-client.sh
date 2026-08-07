#!/usr/bin/env bash
# Shared strict SSH client setup for Terraform's private demo provisioners.

SSHCLOUD_SSH_BASE=()

ssh_client_init() {
  SSHCLOUD_SSH_IP="${1:?gateway IP}"
  SSHCLOUD_SSH_REQUEST_TIMEOUT="${2:-360}"

  if [[ -z "${DEMO_KEY_PEM:-}" || -z "${HOST_PUB:-}" ]]; then
    echo "DEMO_KEY_PEM and HOST_PUB env vars are required" >&2
    return 1
  fi
  if [[ ! "$SSHCLOUD_SSH_REQUEST_TIMEOUT" =~ ^[0-9]+$ ]] ||
    [[ "$SSHCLOUD_SSH_REQUEST_TIMEOUT" -eq 0 ]]; then
    echo "SSH request timeout must be a positive integer" >&2
    return 1
  fi

  SSHCLOUD_SSH_TMPDIR="$(mktemp -d)"
  trap 'rm -rf "$SSHCLOUD_SSH_TMPDIR"' EXIT
  local key="$SSHCLOUD_SSH_TMPDIR/demo"
  local known_hosts="$SSHCLOUD_SSH_TMPDIR/known_hosts"
  local pub_type pub_b64

  printf '%s\n' "$DEMO_KEY_PEM" >"$key"
  chmod 600 "$key"
  pub_type="$(awk '{print $1; exit}' <<<"$HOST_PUB")"
  pub_b64="$(awk '{print $2; exit}' <<<"$HOST_PUB")"
  if [[ -z "$pub_type" || -z "$pub_b64" ]]; then
    echo "HOST_PUB is not an OpenSSH public key" >&2
    return 1
  fi
  printf '%s %s %s\n' "$SSHCLOUD_SSH_IP" "$pub_type" "$pub_b64" >"$known_hosts"

  SSHCLOUD_SSH_BASE=(
    ssh
    -p 22
    -i "$key"
    -o IdentitiesOnly=yes
    -o UserKnownHostsFile="$known_hosts"
    -o GlobalKnownHostsFile=/dev/null
    -o StrictHostKeyChecking=yes
    -o ConnectTimeout=10
    -o BatchMode=yes
  )
}

ssh_run_with_timeout() {
  local seconds="$1"
  shift
  local timeout_bin
  timeout_bin="$(command -v timeout || command -v gtimeout || true)"
  if [[ -n "$timeout_bin" ]]; then
    "$timeout_bin" --signal=TERM --kill-after=5 "$seconds" "$@"
    return
  fi

  "$@" &
  local command_pid=$!
  (
    sleep "$seconds"
    if kill -0 "$command_pid" 2>/dev/null; then
      kill "$command_pid" 2>/dev/null || true
      sleep 5
      kill -9 "$command_pid" 2>/dev/null || true
    fi
  ) &
  local watchdog_pid=$!
  local rc=0
  wait "$command_pid" || rc=$?
  kill "$watchdog_pid" 2>/dev/null || true
  wait "$watchdog_pid" 2>/dev/null || true
  return "$rc"
}

ssh_run() {
  ssh_run_with_timeout "$SSHCLOUD_SSH_REQUEST_TIMEOUT" "${SSHCLOUD_SSH_BASE[@]}" "$@"
}

ssh_port_open() {
  if command -v nc >/dev/null 2>&1; then
    nc -z -w 2 "$SSHCLOUD_SSH_IP" 22
  else
    ssh_run_with_timeout 2 bash -c "echo >/dev/tcp/${SSHCLOUD_SSH_IP}/22"
  fi
}
