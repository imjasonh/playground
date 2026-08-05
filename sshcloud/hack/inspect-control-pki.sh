#!/usr/bin/env bash
# Print only public metadata for one mounted or staged control identity.
set -euo pipefail
set +x
umask 077

usage() {
  cat <<'EOF'
Usage: inspect-control-pki.sh [options]

Options:
  --control-dir DIR    Directory containing tls.crt, tls.key,
                       ca-current.pem (slot A), and ca-previous.pem (slot B)
                       (default: /var/lib/sshcloud/control)
  --active-slot a|b    Label the configured leaf-signing slot (required)
  --expected-role ROLE Require gateway, orchestrator, agent, or snapshot
  --mode all|ca|leaf   Limit output (default: all)
  --ca-a FILE          Override the slot-A certificate path
  --ca-b FILE          Override the slot-B certificate path
  --cert FILE          Override the leaf certificate path
  --key FILE           Override the leaf private-key path

The script reads a private key only to prove it matches the certificate. It
prints certificate fingerprints, validity, URI identity, issuer slot, and the
boolean key-match result; it never prints PEM, public-key lines, or key bytes.
EOF
}

control_dir="/var/lib/sshcloud/control"
active_slot=""
expected_role=""
mode="all"
ca_a=""
ca_b=""
cert=""
key=""

while (($#)); do
  case "$1" in
    --control-dir)
      control_dir="${2:?missing value for --control-dir}"
      shift 2
      ;;
    --active-slot)
      active_slot="${2:?missing value for --active-slot}"
      shift 2
      ;;
    --expected-role)
      expected_role="${2:?missing value for --expected-role}"
      shift 2
      ;;
    --mode)
      mode="${2:?missing value for --mode}"
      shift 2
      ;;
    --ca-a)
      ca_a="${2:?missing value for --ca-a}"
      shift 2
      ;;
    --ca-b)
      ca_b="${2:?missing value for --ca-b}"
      shift 2
      ;;
    --cert)
      cert="${2:?missing value for --cert}"
      shift 2
      ;;
    --key)
      key="${2:?missing value for --key}"
      shift 2
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

case "$active_slot" in
  a | b) ;;
  *)
    echo "--active-slot must be a or b" >&2
    exit 2
    ;;
esac
case "$mode" in
  all | ca | leaf) ;;
  *)
    echo "--mode must be all, ca, or leaf" >&2
    exit 2
    ;;
esac
case "$expected_role" in
  "" | gateway | orchestrator | agent | snapshot) ;;
  *)
    echo "--expected-role must be gateway, orchestrator, agent, or snapshot" >&2
    exit 2
    ;;
esac

ca_a="${ca_a:-$control_dir/ca-current.pem}"
ca_b="${ca_b:-$control_dir/ca-previous.pem}"
cert="${cert:-$control_dir/tls.crt}"
key="${key:-$control_dir/tls.key}"

for command in openssl sed tr; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "required command not found: $command" >&2
    exit 1
  }
done

cert_fingerprint() {
  openssl x509 -in "$1" -noout -fingerprint -sha256 2>/dev/null |
    sed 's/^[^=]*=//'
}

cert_date() {
  local field="$1" file="$2"
  openssl x509 -in "$file" -noout "-$field" 2>/dev/null |
    sed 's/^[^=]*=//'
}

expiry_state() {
  local file="$1"
  if ! openssl x509 -in "$file" -noout -checkend 0 >/dev/null 2>&1; then
    printf 'expired'
  elif ! openssl x509 -in "$file" -noout -checkend 2592000 >/dev/null 2>&1; then
    printf 'expires_within_30d'
  else
    printf 'valid_over_30d'
  fi
}

inspect_ca() {
  local slot="$1" file="$2" usage="standby" trust_file="previous"
  [[ "$slot" == "a" ]] && trust_file="current"
  [[ -s "$file" ]] || {
    echo "slot-$slot CA certificate is missing or empty" >&2
    exit 1
  }
  openssl x509 -in "$file" -noout >/dev/null 2>&1 || {
    echo "slot-$slot CA certificate is invalid" >&2
    exit 1
  }
  if [[ "$slot" == "$active_slot" ]]; then
    usage="active"
  fi
  printf 'control_ca slot=%s usage=%s trust_file=%s fingerprint=%s not_before=%q not_after=%q expiry=%s\n' \
    "$slot" \
    "$usage" \
    "$trust_file" \
    "$(cert_fingerprint "$file")" \
    "$(cert_date startdate "$file")" \
    "$(cert_date enddate "$file")" \
    "$(expiry_state "$file")"
}

uri_role() {
  case "$1" in
    spiffe://sshcloud.internal/control/gateway) printf 'gateway' ;;
    spiffe://sshcloud.internal/control/orchestrator) printf 'orchestrator' ;;
    spiffe://sshcloud.internal/control/agent) printf 'agent' ;;
    spiffe://sshcloud.internal/control/snapshot) printf 'snapshot' ;;
    *) return 1 ;;
  esac
}

leaf_uri() {
  local san
  san="$(openssl x509 -in "$1" -noout -ext subjectAltName 2>/dev/null)"
  printf '%s\n' "$san" |
    tr ',' '\n' |
    sed -n 's/.*URI:\([^[:space:]]*\).*/\1/p'
}

public_digest_from_cert() {
  openssl x509 -in "$1" -pubkey -noout 2>/dev/null |
    openssl pkey -pubin -outform DER 2>/dev/null |
    openssl dgst -sha256 -binary 2>/dev/null |
    openssl base64 -A
}

public_digest_from_key() {
  openssl pkey -in "$1" -pubout -outform DER 2>/dev/null |
    openssl dgst -sha256 -binary 2>/dev/null |
    openssl base64 -A
}

inspect_leaf() {
  [[ -s "$cert" ]] || {
    echo "control leaf certificate is missing or empty" >&2
    exit 1
  }
  [[ -s "$key" ]] || {
    echo "control leaf private key is missing or empty" >&2
    exit 1
  }

  local uris uri role issuer_slot="" verifies_a="no" verifies_b="no"
  uris="$(leaf_uri "$cert")"
  if [[ "$(printf '%s\n' "$uris" | sed '/^$/d' | wc -l)" -ne 1 ]]; then
    echo "control leaf must contain exactly one URI SAN" >&2
    exit 1
  fi
  uri="$uris"
  role="$(uri_role "$uri")" || {
    echo "control leaf has an unrecognized URI identity" >&2
    exit 1
  }
  if [[ -n "$expected_role" && "$role" != "$expected_role" ]]; then
    echo "control leaf role mismatch: got $role, expected $expected_role" >&2
    exit 1
  fi

  if openssl verify -CAfile "$ca_a" "$cert" >/dev/null 2>&1; then
    verifies_a="yes"
  fi
  if openssl verify -CAfile "$ca_b" "$cert" >/dev/null 2>&1; then
    verifies_b="yes"
  fi
  case "$verifies_a:$verifies_b" in
    yes:no) issuer_slot="a" ;;
    no:yes) issuer_slot="b" ;;
    yes:yes)
      echo "control leaf unexpectedly verifies under both CA slots" >&2
      exit 1
      ;;
    *)
      echo "control leaf does not verify under either CA slot" >&2
      exit 1
      ;;
  esac

  if [[ "$(public_digest_from_cert "$cert")" != "$(public_digest_from_key "$key")" ]]; then
    echo "control leaf certificate/private-key mismatch" >&2
    exit 1
  fi

  printf 'control_leaf role=%s uri=%s issuer_slot=%s fingerprint=%s not_before=%q not_after=%q expiry=%s key_match=yes\n' \
    "$role" \
    "$uri" \
    "$issuer_slot" \
    "$(cert_fingerprint "$cert")" \
    "$(cert_date startdate "$cert")" \
    "$(cert_date enddate "$cert")" \
    "$(expiry_state "$cert")"
}

if [[ "$mode" == "all" || "$mode" == "ca" ]]; then
  inspect_ca a "$ca_a"
  inspect_ca b "$ca_b"
fi
if [[ "$mode" == "all" || "$mode" == "leaf" ]]; then
  inspect_leaf
fi
