#!/usr/bin/env bash
# Spin up a KinD cluster, deploy mux + hello with ko, and exercise SSH routing.
# Invoked by go test ./e2e when SSHAPP_KIND_E2E=1 (CI sets this for sshapp PRs).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLUSTER_NAME="${SSHAPP_KIND_CLUSTER:-sshapp-e2e}"
WORKDIR="${TMPDIR:-/tmp}/sshapp-kind-e2e-$$"
PORT_FORWARD_PID=""
KIND_CREATED=0

cleanup() {
  if [[ -n "${PORT_FORWARD_PID}" ]] && kill -0 "${PORT_FORWARD_PID}" 2>/dev/null; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
    wait "${PORT_FORWARD_PID}" 2>/dev/null || true
  fi
  if [[ "${SSHAPP_KIND_KEEP:-}" != "1" && "${KIND_CREATED}" -eq 1 ]]; then
    kind delete cluster --name "${CLUSTER_NAME}" >/dev/null 2>&1 || true
  fi
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

install_kind() {
  if command -v kind >/dev/null 2>&1; then
    return
  fi
  local ver="${KIND_VERSION:-v0.27.0}"
  local os arch url
  os="$(uname -s | tr '[:upper:]' '[:lower:]')"
  arch="$(uname -m)"
  case "${arch}" in
    x86_64) arch=amd64 ;;
    aarch64 | arm64) arch=arm64 ;;
  esac
  url="https://kind.sigs.k8s.io/dl/${ver}/kind-${os}-${arch}"
  echo "Installing kind ${ver} from ${url}"
  curl -fsSL -o "${WORKDIR}/kind" "${url}"
  chmod +x "${WORKDIR}/kind"
  export PATH="${WORKDIR}:${PATH}"
}

install_ko() {
  if command -v ko >/dev/null 2>&1; then
    return
  fi
  echo "Installing ko"
  GOBIN="${WORKDIR}" go install github.com/google/ko@v0.17.1
  export PATH="${WORKDIR}:${PATH}"
}

ssh_mux() {
  # shellcheck disable=SC2086
  ssh \
    -i "${WORKDIR}/client_ed25519" \
    -o BatchMode=yes \
    -o StrictHostKeyChecking=no \
    -o UserKnownHostsFile=/dev/null \
    -o IdentitiesOnly=yes \
    -o ConnectTimeout=10 \
    -p "${LOCAL_PORT}" \
    e2e@127.0.0.1 \
    "$@"
}

await_tcp() {
  local host=$1 port=$2 deadline=$((SECONDS + 60))
  while ((SECONDS < deadline)); do
    if (echo >/dev/tcp/"${host}"/"${port}") >/dev/null 2>&1; then
      return 0
    fi
    sleep 1
  done
  echo "timed out waiting for ${host}:${port}" >&2
  return 1
}

mkdir -p "${WORKDIR}"
need_cmd docker
need_cmd kubectl
need_cmd curl
need_cmd ssh
need_cmd ssh-keygen
need_cmd go
install_kind
install_ko

if ! docker info >/dev/null 2>&1; then
  echo "docker daemon is not reachable" >&2
  exit 1
fi

echo "::group::Create KinD cluster ${CLUSTER_NAME}"
if ! kind get clusters 2>/dev/null | grep -qx "${CLUSTER_NAME}"; then
  kind create cluster --name "${CLUSTER_NAME}"
  KIND_CREATED=1
else
  echo "Reusing existing cluster ${CLUSTER_NAME}"
  KIND_CREATED=0
fi
kubectl cluster-info --context "kind-${CLUSTER_NAME}" >/dev/null
echo "::endgroup::"

echo "::group::Build images into KinD with ko"
export KIND_CLUSTER_NAME="${CLUSTER_NAME}"
export KO_DOCKER_REPO=kind.local
# Single-arch keeps CI fast; KinD nodes are linux/amd64 on GHA.
HELLO_IMAGE="$(cd "${ROOT}" && ko build --platform=linux/amd64 ./apps/hello)"
MUX_IMAGE="$(cd "${ROOT}" && ko build --platform=linux/amd64 ./apps/mux)"
echo "hello image: ${HELLO_IMAGE}"
echo "mux image: ${MUX_IMAGE}"
echo "::endgroup::"

echo "::group::Apply manifests"
ssh-keygen -t ed25519 -f "${WORKDIR}/hello_host" -N "" -q
ssh-keygen -t ed25519 -f "${WORKDIR}/mux_host" -N "" -q
ssh-keygen -t ed25519 -f "${WORKDIR}/client_ed25519" -N "" -q

kubectl --context "kind-${CLUSTER_NAME}" delete namespace sshapps --ignore-not-found --wait=true
kubectl --context "kind-${CLUSTER_NAME}" create namespace sshapps
kubectl --context "kind-${CLUSTER_NAME}" -n sshapps create secret generic hello-ssh-host-key \
  --from-file=host_ed25519="${WORKDIR}/hello_host"
kubectl --context "kind-${CLUSTER_NAME}" -n sshapps create secret generic mux-ssh-host-key \
  --from-file=host_ed25519="${WORKDIR}/mux_host"

sed \
  -e "s|HELLO_IMAGE|${HELLO_IMAGE}|g" \
  -e "s|MUX_IMAGE|${MUX_IMAGE}|g" \
  "${ROOT}/e2e/manifests/sshapp.yaml" \
  | kubectl --context "kind-${CLUSTER_NAME}" apply -f -

kubectl --context "kind-${CLUSTER_NAME}" -n sshapps rollout status deployment/ssh-mux --timeout=180s
echo "::endgroup::"

dump_debug() {
  kubectl --context "kind-${CLUSTER_NAME}" -n sshapps get pods,deploy,svc -o wide >&2 || true
  kubectl --context "kind-${CLUSTER_NAME}" -n sshapps logs deploy/ssh-mux --tail=120 >&2 || true
  kubectl --context "kind-${CLUSTER_NAME}" -n sshapps logs deploy/hello --tail=120 >&2 || true
}

expect_greeting() {
  local label=$1
  shift
  local out="" attempt
  for attempt in 1 2 3 4 5 6 7 8; do
    out="$("$@" 2>"${WORKDIR}/ssh-stderr.txt" || true)"
    echo "${label} attempt ${attempt}: ${out}"
    if [[ -s "${WORKDIR}/ssh-stderr.txt" ]]; then
      echo "${label} stderr: $(cat "${WORKDIR}/ssh-stderr.txt")"
    fi
    if grep -q 'hello,' <<<"${out}"; then
      printf '%s\n' "${out}"
      return 0
    fi
    sleep 2
  done
  echo "expected hello greeting for ${label}, last output: ${out}" >&2
  dump_debug
  return 1
}

LOCAL_PORT=2222
echo "::group::Port-forward mux :${LOCAL_PORT}"
kubectl --context "kind-${CLUSTER_NAME}" -n sshapps port-forward svc/ssh-mux "${LOCAL_PORT}:22" \
  >"${WORKDIR}/port-forward.log" 2>&1 &
PORT_FORWARD_PID=$!
await_tcp 127.0.0.1 "${LOCAL_PORT}"
echo "::endgroup::"

echo "::group::SSH command path (ssh … hello)"
if ! expect_greeting "command-path" ssh_mux hello >/dev/null; then
  exit 1
fi
echo "::endgroup::"

echo "::group::SSH registry menu (select 1)"
out=""
for attempt in 1 2 3 4 5 6 7 8; do
  out="$(printf '1\n' | ssh_mux 2>"${WORKDIR}/ssh-stderr.txt" || true)"
  echo "menu attempt ${attempt}: ${out}"
  if [[ -s "${WORKDIR}/ssh-stderr.txt" ]]; then
    echo "menu stderr: $(cat "${WORKDIR}/ssh-stderr.txt")"
  fi
  if grep -q 'available apps:' <<<"${out}" && grep -q 'hello,' <<<"${out}"; then
    break
  fi
  out=""
  sleep 2
done
if ! grep -q 'available apps:' <<<"${out}" || ! grep -q 'hello,' <<<"${out}"; then
  echo "expected menu + hello greeting, got: ${out}" >&2
  dump_debug
  exit 1
fi
echo "::endgroup::"

echo "::group::Wait for hello to scale to zero"
deadline=$((SECONDS + 90))
while ((SECONDS < deadline)); do
  replicas="$(kubectl --context "kind-${CLUSTER_NAME}" -n sshapps get deploy hello -o jsonpath='{.spec.replicas}')"
  ready="$(kubectl --context "kind-${CLUSTER_NAME}" -n sshapps get deploy hello -o jsonpath='{.status.readyReplicas}')"
  ready="${ready:-0}"
  echo "hello replicas=${replicas} ready=${ready}"
  if [[ "${replicas}" == "0" && "${ready}" == "0" ]]; then
    echo "scaled to zero"
    echo "::endgroup::"
    echo "KinD e2e passed"
    exit 0
  fi
  sleep 3
done
echo "hello did not scale to zero within timeout" >&2
dump_debug
exit 1
