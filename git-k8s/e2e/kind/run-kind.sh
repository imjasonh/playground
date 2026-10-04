#!/usr/bin/env bash
# Install git-k8s and its checks in a kind cluster with kube's generate
# command, which pushes their images to a local registry, then push
# branches to a git server and check that they're fixed, gated, and
# fast-forwarded. go test ./e2e/kind runs this when GIT_K8S_KIND_E2E=1,
# which CI sets when git-k8s changes.
#
# The git server runs on this machine and requires a password. Pods reach it
# through the kind network's gateway, so the nodes need no internet access.
#
# GIT_K8S_KIND_CHAINGUARD is where Chainguard's images come from
# (cgr.dev/chainguard; docker.io/chainguard is a mirror).
# GIT_K8S_KIND_KEEP=1 keeps the cluster, registry, and git server afterward.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CLUSTER="${GIT_K8S_KIND_CLUSTER:-git-k8s-e2e}"
CONTEXT="kind-${CLUSTER}"
REGISTRY="${GIT_K8S_KIND_REGISTRY:-git-k8s-e2e-registry}"
PORT="${GIT_K8S_KIND_REGISTRY_PORT:-5002}"
GIT_PORT="${GIT_K8S_KIND_GIT_PORT:-18418}"
CHAINGUARD="${GIT_K8S_KIND_CHAINGUARD:-cgr.dev/chainguard}"
PLATFORM="linux/$(go env GOARCH)"
NS=git-k8s-e2e
CHECKS=(check-base check-gofmt check-risk check-approval check-gotest)
WORKDIR="$(mktemp -d)"
WORK="${WORKDIR}/work"
PASSWORD="$(od -An -N12 -tx1 /dev/urandom | tr -d ' \n')"
CREATED_CLUSTER=0
CREATED_REGISTRY=0
GIT_SERVER_PID=""
PORT_FORWARD_PID=""

k() { kubectl --context "${CONTEXT}" "$@"; }

# g runs git in the working repository, without the machine's git config.
g() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${WORK}" \
    -c user.name=e2e -c user.email=e2e@example.com "$@"
}

diagnose() {
  echo "::group::Cluster state"
  k get nodes -o wide || true
  k -n "${NS}" get gitrepositories,gitbranches -o yaml || true
  k -n "${NS}" get pods -o wide || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=check-gotest || true
  for program in git-k8s "${CHECKS[@]}"; do
    k -n "${program}" describe pods || true
    k -n "${program}" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${program}" || true
  done
  echo "--- git server log"
  cat "${WORKDIR}/gitserver.log" || true
  echo "::endgroup::"
}

finish() {
  local status=$?
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  if [[ -n "${PORT_FORWARD_PID}" ]]; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
  fi
  if [[ "${GIT_K8S_KIND_KEEP:-}" == 1 ]]; then
    echo "Kept the cluster ${CLUSTER}, the registry ${REGISTRY}, and the git server in ${WORKDIR}"
    exit "${status}"
  fi
  if [[ -n "${GIT_SERVER_PID}" ]]; then
    kill "${GIT_SERVER_PID}" 2>/dev/null || true
  fi
  if [[ ${CREATED_CLUSTER} -eq 1 ]]; then
    kind delete cluster --name "${CLUSTER}" || true
  fi
  if [[ ${CREATED_REGISTRY} -eq 1 ]]; then
    docker rm -f "${REGISTRY}" >/dev/null || true
  fi
  rm -rf "${WORKDIR}"
  exit "${status}"
}
trap finish EXIT

# eventually runs a command until it succeeds, for up to $1 seconds.
eventually() {
  local timeout=$1
  shift
  local deadline=$((SECONDS + timeout))
  until "$@"; do
    if ((SECONDS >= deadline)); then
      echo "timed out after ${timeout}s: $*" >&2
      return 1
    fi
    sleep 2
  done
}

need() {
  command -v "$1" >/dev/null || {
    echo "$1 is required" >&2
    exit 1
  }
}

install_kind() {
  if command -v kind >/dev/null; then
    return
  fi
  local arch
  arch="$(go env GOARCH)"
  echo "Installing kind ${KIND_VERSION:-v0.33.0}"
  curl -fsSL -o "${WORKDIR}/kind" "https://kind.sigs.k8s.io/dl/${KIND_VERSION:-v0.33.0}/kind-linux-${arch}"
  chmod +x "${WORKDIR}/kind"
  export PATH="${WORKDIR}:${PATH}"
}

need docker
need kubectl
need go
need git
need curl
install_kind
docker info >/dev/null

echo "::group::Start a registry, a kind cluster, and a git server"
# As in https://kind.sigs.k8s.io/docs/user/local-registry/: nodes pull
# localhost:PORT/... from the registry container, which is on kind's
# network.
if [[ "$(docker inspect -f '{{.State.Running}}' "${REGISTRY}" 2>/dev/null || true)" != true ]]; then
  docker run -d --restart=always -p "127.0.0.1:${PORT}:5000" --name "${REGISTRY}" registry:2
  CREATED_REGISTRY=1
fi
if ! kind get clusters 2>/dev/null | grep -x "${CLUSTER}" >/dev/null; then
  kind create cluster --name "${CLUSTER}" --wait 120s --config - <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
networking:
  kubeProxyMode: nftables
EOF
  CREATED_CLUSTER=1
fi
for node in $(kind get nodes --name "${CLUSTER}"); do
  docker exec "${node}" mkdir -p "/etc/containerd/certs.d/localhost:${PORT}"
  printf '[host."http://%s:5000"]\n' "${REGISTRY}" |
    docker exec -i "${node}" cp /dev/stdin "/etc/containerd/certs.d/localhost:${PORT}/hosts.toml"
done
if [[ "$(docker inspect -f '{{json .NetworkSettings.Networks.kind}}' "${REGISTRY}")" == null ]]; then
  docker network connect kind "${REGISTRY}"
fi
k version

# Pods reach the git server on this machine through the gateway of kind's
# Docker network.
GATEWAY="$(docker network inspect kind -f '{{range .IPAM.Config}}{{.Gateway}} {{end}}' | tr ' ' '\n' |
  grep -E '^[0-9]+[.][0-9]+[.][0-9]+[.][0-9]+$' | head -n 1)"
(cd "${ROOT}" && go build -o "${WORKDIR}/gitserver" ./e2e/gitserver)
mkdir -p "${WORKDIR}/repos"
GITSERVER_PASSWORD="${PASSWORD}" "${WORKDIR}/gitserver" -addr="0.0.0.0:${GIT_PORT}" -root="${WORKDIR}/repos" \
  >"${WORKDIR}/gitserver.log" 2>&1 &
GIT_SERVER_PID=$!
HOST_URL="http://git-k8s:${PASSWORD}@127.0.0.1:${GIT_PORT}"
CLUSTER_URL="http://${GATEWAY}:${GIT_PORT}"
listening() { (echo >"/dev/tcp/127.0.0.1/${GIT_PORT}") 2>/dev/null; }
eventually 30 listening
echo "Pods reach the git server at ${CLUSTER_URL}"
echo "::endgroup::"

echo "::group::Install the admission policies and git-k8s with generate"
cd "${ROOT}"
# The policies go first. In an upgrade, they stop the old checks' status
# writes before git-k8s makes status.checks an atomic map, and let the new
# git-k8s write results.
k apply -f "${ROOT}/config/policy.yaml"
generate() {
  local program=$1
  shift
  go run "./cmd/${program}" generate -registry="localhost:${PORT}/git-k8s-e2e" \
    -base="${CHAINGUARD}/git:latest" -platform="${PLATFORM}" -replicas=1 "$@"
}
install() {
  generate "$@" | k apply -f -
}
# The gotest check's Pods use these images. Copying them into the local
# registry lets the nodes pull them without reaching the internet.
GO_IMAGE="localhost:${PORT}/chainguard/go:latest"
GIT_IMAGE="localhost:${PORT}/chainguard/git:latest"
crane() { go run github.com/google/go-containerregistry/cmd/crane@v0.22.1 "$@"; }
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/go:latest" "${GO_IMAGE}"
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/git:latest" "${GIT_IMAGE}"
# git-k8s installs the CustomResourceDefinitions that the checks watch. Its
# second replica is a standby, which answers some of the checks' results
# with 503, so they try again.
install git-k8s -replicas=2
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
echo "::endgroup::"

echo "::group::Upgrading moves check results to the core program"
# Before the results endpoint, status.checks was a granular map, and each
# check controller applied its own entry. Stop the core program, put the map
# back the way an older release installed it, and apply two entries as the
# old check controllers did, one for a check that the policy doesn't list.
k -n git-k8s scale deployment/git-k8s --replicas=0
no_core_pods() { [[ -z "$(k -n git-k8s get pods -l app.kubernetes.io/name=git-k8s -o name)" ]]; }
eventually 120 no_core_pods
k patch crd gitbranches.git-k8s.imjasonh.com --type=json -p \
  '[{"op":"remove","path":"/spec/versions/0/schema/openAPIV3Schema/properties/status/properties/checks/x-kubernetes-map-type"}]'
OLD=1111111111111111111111111111111111111111
k create namespace git-k8s-upgrade
k -n git-k8s-upgrade apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitBranch
metadata:
  name: app-c-old
spec:
  repository: app
  branch: c/old
  head: "${OLD}"
  parent: main
  parentHead: "2222222222222222222222222222222222222222"
  merge:
    checks:
      - name: gofmt
EOF
for check in gofmt risk; do
  k -n git-k8s-upgrade apply --server-side --subresource=status --field-manager="check-${check}" -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitBranch
metadata:
  name: app-c-old
status:
  checks:
    ${check}:
      commit: "${OLD}"
      state: Failed
EOF
done
status_managers() {
  k -n git-k8s-upgrade get gitbranch app-c-old \
    -o jsonpath='{range .metadata.managedFields[?(@.subresource=="status")]}{.manager} {end}'
}
echo "Status managers before the upgrade: $(status_managers)"
k -n git-k8s scale deployment/git-k8s --replicas=2
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
old_field() { k -n git-k8s-upgrade get gitbranch app-c-old -o jsonpath="$1"; }
upgraded() {
  local managers
  managers=" $(status_managers) "
  [[ "${managers}" == *" results "* && "${managers}" != *" check-"* ]] &&
    [[ "$(old_field '{.status.checks.gofmt.commit}')" == "${OLD}" && -z "$(old_field '{.status.checks.risk}')" ]]
}
eventually 60 upgraded
echo "Status managers after the upgrade: $(status_managers)"
k delete namespace git-k8s-upgrade --wait=false
echo "The core program's results controller took over status.checks from the old check managers, kept the gofmt result, and removed the risk result."
echo "::endgroup::"

echo "::group::Install the checks"
for program in "${CHECKS[@]}"; do
  case "${program}" in
    check-risk) install "${program}" -- '-sensitive=auth/**' ;;
    check-gotest)
      install "${program}" -- "-go-image=${GO_IMAGE}" "-git-image=${GIT_IMAGE}" -timeout=5m
      ;;
    *) install "${program}" ;;
  esac
done
for program in "${CHECKS[@]}"; do
  k -n "${program}" rollout status "deployment/${program}" --timeout=180s
done
echo "::endgroup::"

echo "::group::Track a repository"
git init -q -b main "${WORK}"
printf 'module example.com/app\n\ngo 1.24\n' >"${WORK}/go.mod"
printf 'package main\n\nfunc main() {}\n' >"${WORK}/main.go"
g add -A
g commit -qm "Initial commit"
g push -q "${HOST_URL}/app.git" HEAD:main

k create namespace "${NS}"
k -n "${NS}" create secret generic app-creds --type=kubernetes.io/basic-auth \
  --from-literal=username=git-k8s --from-literal=password="${PASSWORD}"
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: app
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/app.git
  secretRef:
    name: app-creds
  pollInterval: 2s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gofmt
            mayPush: true
          - name: risk
          - name: approval
        when: >-
          checks.base.passed && checks.gofmt.passed &&
          (checks.risk.outputs.level == "low" || checks.approval.passed)
        deleteMergedBranches: true
    - match: c/**
      parent: main
EOF
repository_ready() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="Ready")].status}')" == True ]]
}
eventually 120 repository_ready
policies_installed() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="PoliciesInstalled")].status}')" == True ]]
}
eventually 60 policies_installed
# A policy from another release makes the condition False until the
# policies from this release are applied again.
k annotate validatingadmissionpolicy git-k8s-check-results git-k8s.imjasonh.com/policy-version=1 --overwrite
policies_outdated() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="PoliciesInstalled")].reason}')" == Outdated ]]
}
eventually 60 policies_outdated
k apply -f "${ROOT}/config/policy.yaml"
eventually 60 policies_installed
k -n "${NS}" get gitrepositories,gitbranches
echo "::endgroup::"

# remote_head prints a branch's commit in repository $2, or app.
remote_head() { git ls-remote "${HOST_URL}/${2:-app}.git" "refs/heads/$1" | cut -f1; }
# branch_object prints the GitBranch for a branch of repository $2, or app.
branch_object() {
  k -n "${NS}" get gitbranches -l "git-k8s.imjasonh.com/repository=${2:-app}" \
    -o jsonpath="{.items[?(@.spec.branch==\"$1\")].metadata.name}"
}
fetch_main() { g fetch -q "${HOST_URL}/app.git" main; }
branch_gone() { [[ -z "$(remote_head "$1")" && -z "$(branch_object "$1")" ]]; }

echo "::group::A branch with unformatted Go lands formatted"
g checkout -q -b c/fmt
mkdir -p "${WORK}/util"
printf 'package util\nfunc  Add(a,b int)int{return a+b}\n' >"${WORK}/util/add.go"
g add -A
g commit -qm "Add util.Add"
g push -q "${HOST_URL}/app.git" HEAD:c/fmt
formatted='package util

func Add(a, b int) int { return a + b }'
formatted_on_main() { fetch_main && [[ "$(g show FETCH_HEAD:util/add.go 2>/dev/null)" == "${formatted}" ]]; }
eventually 120 formatted_on_main
g log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: gofmt'
eventually 60 branch_gone c/fmt
g log --oneline FETCH_HEAD
echo "The gofmt check pushed a fix, main fast-forwarded to it, and c/fmt was deleted."
echo "::endgroup::"

echo "::group::A risky branch waits for approval"
g checkout -q -B c/auth FETCH_HEAD
mkdir -p "${WORK}/auth"
printf 'package auth\n\n// Allow reports whether user can continue.\nfunc Allow(user string) bool { return user != "" }\n' \
  >"${WORK}/auth/policy.go"
g add -A
g commit -qm "Add auth.Allow"
AUTH="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:c/auth
field() { k -n "${NS}" get gitbranch "$(branch_object c/auth)" -o jsonpath="$1"; }
waiting_for_approval() {
  [[ -n "$(branch_object c/auth)" ]] &&
    [[ "$(field '{.status.state}')" == WaitingForChecks ]] &&
    [[ "$(field '{.status.checks.risk.outputs.level}')" == high ]] &&
    [[ "$(field '{.status.checks.approval.state}')" == Failed ]] &&
    [[ "$(field '{.status.checks.gofmt.state}')" == Passed ]]
}
eventually 120 waiting_for_approval
main_before="$(remote_head main)"
sleep 6
[[ "$(remote_head main)" == "${main_before}" ]]
field '{.status.conditions[?(@.type=="Merged")].message}'
echo
k -n "${NS}" annotate gitbranch "$(branch_object c/auth)" "git-k8s.imjasonh.com/approve=${AUTH}"
auth_landed() { [[ "$(remote_head main)" == "${AUTH}" ]]; }
eventually 120 auth_landed
eventually 60 branch_gone c/auth
echo "c/auth waited with a high risk rating until it was approved, then landed."
echo "::endgroup::"

echo "::group::Two branches from the same commit both land"
fetch_main
g checkout -q -B c/one FETCH_HEAD
echo one >"${WORK}/one.txt"
g add -A
g commit -qm "Add one.txt"
g checkout -q -B c/two FETCH_HEAD
echo two >"${WORK}/two.txt"
g add -A
g commit -qm "Add two.txt"
g push -q "${HOST_URL}/app.git" c/one:c/one c/two:c/two
both_landed() {
  branch_gone c/one && branch_gone c/two && fetch_main &&
    g cat-file -e FETCH_HEAD:one.txt && g cat-file -e FETCH_HEAD:two.txt
}
eventually 180 both_landed
g log --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: base'
g log --graph --oneline FETCH_HEAD
echo "One branch landed, the base check merged main into the other, and it landed too."
echo "::endgroup::"

echo "::group::Only the core program writes check results"
server="$(k config view --minify -o jsonpath='{.clusters[0].cluster.server}')"
k config view --raw --minify -o jsonpath='{.clusters[0].cluster.certificate-authority-data}' |
  base64 -d >"${WORKDIR}/ca.crt"
token="$(k -n check-gofmt create token check-gofmt)"
status_url="${server}/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/${NS}/gitbranches/$(branch_object main)/status?dryRun=All"
patch_status() {
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/patch.json" -w '%{http_code}' -X PATCH \
    -H "Authorization: Bearer ${2:-${token}}" -H 'Content-Type: application/merge-patch+json' \
    --data "$1" "${status_url}"
}
result='{"status":{"checks":{"gofmt":{"commit":"0000000","state":"Passed"}}}}'
code="$(patch_status "${result}")"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 403 ]]
grep -q 'cannot patch resource' "${WORKDIR}/patch.json"
grep -q 'gitbranches/status' "${WORKDIR}/patch.json"
# Checks read the token that generate mounts in their Pods, so they may not
# create tokens.
[[ "$(k auth can-i create serviceaccounts --subresource=token -n check-gofmt --as=system:serviceaccount:check-gofmt:check-gofmt)" == no ]]

# The results endpoint takes a check's result only with a token for the
# check's own service account and the endpoint's audience.
k -n git-k8s port-forward svc/git-k8s 0:80 >"${WORKDIR}/port-forward.log" 2>&1 &
PORT_FORWARD_PID=$!
forwarding() { grep -q '^Forwarding from 127.0.0.1:' "${WORKDIR}/port-forward.log"; }
eventually 30 forwarding
forward_port="$(sed -n 's/^Forwarding from 127[.]0[.]0[.]1:\([0-9]*\) .*/\1/p' "${WORKDIR}/port-forward.log" | head -n 1)"
send_result() {
  curl -sS -o "${WORKDIR}/result.txt" -w '%{http_code}' -X PUT -H "Authorization: ${3:-Bearer} $1" \
    -H 'Content-Type: application/json' --data '{"commit":"0000000","state":"Passed"}' \
    "http://127.0.0.1:${forward_port}/results/${NS}/$(branch_object main)/$2"
}
risk_token="$(k -n check-risk create token check-risk --audience=git-k8s-results)"
code="$(send_result "${risk_token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 403 ]]
grep -q "check-risk is the risk check, so it can't write the gofmt check's result" "${WORKDIR}/result.txt"
code="$(send_result "${token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 401 ]]
# The scheme is case-insensitive.
code="$(send_result "${risk_token}" risk bearer)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 409 ]]
grep -q "main has no parent, so it takes no check results" "${WORKDIR}/result.txt"
kill "${PORT_FORWARD_PID}"
PORT_FORWARD_PID=""

# If a role lets a check or another service account write status anyway,
# the admission policy still lets only the core program write results.
k -n "${NS}" create serviceaccount rogue
k apply -f - <<EOF
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: git-k8s-e2e-status
rules:
  - apiGroups: [git-k8s.imjasonh.com]
    resources: [gitbranches/status]
    verbs: [patch]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: git-k8s-e2e-status
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: git-k8s-e2e-status
subjects:
  - kind: ServiceAccount
    namespace: check-gofmt
    name: check-gofmt
  - kind: ServiceAccount
    namespace: ${NS}
    name: rogue
EOF
rogue_token="$(k -n "${NS}" create token rogue)"
rejected() { [[ "$(patch_status "${result}" "$1")" == 422 ]] && grep -q "$2" "${WORKDIR}/patch.json"; }
eventually 30 rejected "${token}" "the gofmt check can't write GitBranch status"
cat "${WORKDIR}/patch.json"
echo
eventually 30 rejected "${rogue_token}" "system:serviceaccount:${NS}:rogue isn't the core program's service account"
cat "${WORKDIR}/patch.json"
echo
core_token="$(k -n git-k8s create token git-k8s)"
[[ "$(patch_status "${result}" "${core_token}")" == 200 ]]
k -n "${NS}" patch gitbranch "$(branch_object main)" --subresource=status --type=merge --dry-run=server -p "${result}"
k delete clusterrolebinding,clusterrole git-k8s-e2e-status
echo "Checks can't write GitBranch status, the results endpoint refuses a check's token for another check's entry, and only the core program and people can write status.checks."
echo "::endgroup::"

echo "::group::Controllers can't approve branches"
branch_url="${server}/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/${NS}/gitbranches/$(branch_object main)?dryRun=All"
patch_branch() {
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/patch.json" -w '%{http_code}' -X PATCH \
    -H "Authorization: Bearer $1" -H 'Content-Type: application/merge-patch+json' \
    --data "$2" "${branch_url}"
}
approve='{"metadata":{"annotations":{"git-k8s.imjasonh.com/approve":"0000000"}}}'
core_token="$(k -n git-k8s create token git-k8s)"
for bearer in "${token}" "${core_token}"; do
  code="$(patch_branch "${bearer}" "${approve}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]]
  grep -q "git-k8s controllers can't approve branches" "${WORKDIR}/patch.json"
done
code="$(patch_branch "${token}" '{"metadata":{"labels":{"e2e":"changed"}}}')"
[[ "${code}" == 422 ]]
grep -q "the gofmt check can't change GitBranch objects" "${WORKDIR}/patch.json"
echo "Neither a check nor the core controller can approve a branch, and a check can't change one."
echo "::endgroup::"

echo "::group::Tests run in a sandboxed Pod"
TESTED="${WORKDIR}/tested"
git init -q -b main "${TESTED}"
t() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${TESTED}" \
    -c user.name=e2e -c user.email=e2e@example.com "$@"
}
printf 'module example.com/tested\n\ngo 1.24\n' >"${TESTED}/go.mod"
printf 'package tested\n\nfunc Add(a, b int) int { return a + b }\n' >"${TESTED}/add.go"
cat >"${TESTED}/add_test.go" <<'GO'
package tested

import "testing"

func TestAdd(t *testing.T) {
	if got := Add(2, 3); got != 5 {
		t.Errorf("Add(2, 3) = %d, want 5", got)
	}
}
GO
t add -A
t commit -qm "Add Add"
t push -q "${HOST_URL}/tested.git" HEAD:main
tested_main="$(t rev-parse HEAD)"
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: tested
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/tested.git
  secretRef:
    name: app-creds
  pollInterval: 2s
  branches:
    - match: main
      merge:
        checks:
          - name: gotest
        deleteMergedBranches: true
    - match: c/**
      parent: main
EOF

t checkout -q -b c/broken
printf 'package tested\n\nfunc Add(a, b int) int { return a - b }\n' >"${TESTED}/add.go"
t commit -qam "Break Add"
t push -q "${HOST_URL}/tested.git" HEAD:c/broken
gotest() { k -n "${NS}" get gitbranch "$(branch_object "$1" tested)" -o jsonpath="{.status.checks.gotest.$2}"; }
broken_failed() { [[ -n "$(branch_object c/broken tested)" && "$(gotest c/broken state)" == Failed ]]; }
eventually 300 broken_failed
gotest c/broken message
echo
gotest c/broken message | grep -q -- '--- FAIL: TestAdd'
[[ "$(remote_head main tested)" == "${tested_main}" ]]
# kube deletes a test Pod once the check stops declaring it.
no_test_pods() { [[ -z "$(k -n "${NS}" get pods -l app.kubernetes.io/name=check-gotest -o name)" ]]; }
eventually 60 no_test_pods

t checkout -q -b c/fixed main
printf 'package tested\n\n// Add returns the sum of a and b.\nfunc Add(a, b int) int { return a + b }\n' >"${TESTED}/add.go"
t commit -qam "Document Add"
fixed="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/fixed
fixed_landed() { [[ "$(remote_head main tested)" == "${fixed}" ]]; }
eventually 300 fixed_landed
eventually 60 no_test_pods
echo "A branch that breaks a test failed in a sandboxed Pod, and a fixed branch landed."
echo "::endgroup::"

echo "::group::Nothing writes while nothing changes"
snapshot() {
  k -n "${NS}" get gitrepositories,gitbranches \
    -o jsonpath='{range .items[*]}{.kind}/{.metadata.name}={.metadata.resourceVersion} {end}'
}
idle() {
  local before after
  before="$(snapshot)"
  sleep 8
  after="$(snapshot)"
  echo "resource versions: ${after}"
  [[ "${before}" == "${after}" ]]
}
eventually 60 idle
echo "Four polls of the remote wrote nothing."
echo "::endgroup::"

echo "kind e2e passed"
