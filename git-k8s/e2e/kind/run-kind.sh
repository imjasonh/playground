#!/usr/bin/env bash
# Install git-k8s and its checks in a kind cluster with kube's generate
# command, which pushes their images to a local registry, then push
# branches to a git server and check that they're fixed, gated, and
# fast-forwarded. go test ./e2e/kind runs this when GIT_K8S_KIND_E2E=1,
# which CI sets when git-k8s changes.
#
# The git server runs on this machine and requires a password. Pods reach it
# through the kind network's gateway, so the nodes need no internet access.
# A module proxy on this machine serves the one module that a tested branch
# depends on, as go-cache's upstream.
#
# GIT_K8S_KIND_CHAINGUARD is where Chainguard's images come from
# (cgr.dev/chainguard; docker.io/chainguard is a mirror).
# GIT_K8S_KIND_KEEP=1 keeps the cluster, registry, git server, and module
# proxy afterward.
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
MOD_PROXY_PID=""

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
  for program in git-k8s go-cache "${CHECKS[@]}"; do
    k -n "${program}" describe pods || true
    k -n "${program}" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${program}" || true
  done
  echo "--- git server log"
  cat "${WORKDIR}/gitserver.log" || true
  echo "--- module proxy log"
  cat "${WORKDIR}/modproxy.log" || true
  echo "::endgroup::"
}

finish() {
  local status=$?
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  if [[ "${GIT_K8S_KIND_KEEP:-}" == 1 ]]; then
    echo "Kept the cluster ${CLUSTER}, the registry ${REGISTRY}, and the git server and module proxy in ${WORKDIR}"
    exit "${status}"
  fi
  for pid in "${GIT_SERVER_PID}" "${MOD_PROXY_PID}"; do
    if [[ -n "${pid}" ]]; then
      kill "${pid}" 2>/dev/null || true
    fi
  done
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

echo "::group::Start a registry, a kind cluster, a git server, and a module proxy"
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
# example.com/greet isn't on the internet, so test Pods can get it only
# through go-cache.
GREET="${WORKDIR}/modules/example.com/greet@v1.0.0"
mkdir -p "${GREET}"
printf 'module example.com/greet\n\ngo 1.24\n' >"${GREET}/go.mod"
printf 'package greet\n\nfunc Hello(name string) string { return "Hello, " + name }\n' >"${GREET}/greet.go"
(cd "${ROOT}" && go build -o "${WORKDIR}/modproxy" ./e2e/modproxy)
"${WORKDIR}/modproxy" -addr=0.0.0.0:0 -dir="${WORKDIR}/modules" >"${WORKDIR}/modproxy.log" 2>&1 &
MOD_PROXY_PID=$!
mod_port() { sed -nE 's/.* serving .* on .*:([0-9]+)$/\1/p' "${WORKDIR}/modproxy.log"; }
mod_proxy_listening() { [[ -n "$(mod_port)" ]]; }
eventually 30 mod_proxy_listening
MOD_PORT="$(mod_port)"
echo "go-cache fetches modules from http://${GATEWAY}:${MOD_PORT}"
echo "::endgroup::"

echo "::group::Install git-k8s and the checks with generate"
cd "${ROOT}"
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
# git-k8s installs the CustomResourceDefinitions that the checks watch.
install git-k8s
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
install go-cache -base="${CHAINGUARD}/static:latest" -tmp-size=1Gi -- \
  "-upstream=http://${GATEWAY}:${MOD_PORT}" -max-size=512Mi
k apply -f "${ROOT}/config/go-cache.yaml"
for program in "${CHECKS[@]}"; do
  case "${program}" in
    check-risk) install "${program}" -- '-sensitive=auth/**' ;;
    check-gotest)
      install "${program}" -- "-go-image=${GO_IMAGE}" "-git-image=${GIT_IMAGE}" -timeout=5m \
        -go-cache=http://go-cache.go-cache
      ;;
    *) install "${program}" ;;
  esac
done
for program in go-cache "${CHECKS[@]}"; do
  k -n "${program}" rollout status "deployment/${program}" --timeout=180s
done
k apply -f "${ROOT}/config/policy.yaml"
echo "::endgroup::"

echo "::group::Track a repository"
git init -q -b main "${WORK}"
printf 'module example.com/app\n\ngo 1.24\n' >"${WORK}/go.mod"
printf 'package main\n\nfunc main() {}\n' >"${WORK}/main.go"
g add -A
g commit -qm "Initial commit"
g push -q "${HOST_URL}/app.git" HEAD:main

k create namespace "${NS}"
# The gotest check runs Pods only in namespaces that opt in and enforce Pod
# Security.
k label namespace "${NS}" git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
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
k -n "${NS}" get gitrepositories,gitbranches
echo "::endgroup::"

echo "::group::The API server rejects a URL that git could read as an option"
url_repository() {
  cat <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: url-check
  namespace: ${NS}
spec:
  url: '$1'
EOF
}
for url in '--upload-pack=touch /tmp/pwned' 'ssh://%2doProxyCommand=touch/app.git' \
  'ssh://[-oProxyCommand=touch]/app.git' 'ssh://[-oProxyCommand=touch]@example.com/app.git'; do
  if url_repository "${url}" | k apply --dry-run=server -f - 2>"${WORKDIR}/apply.err"; then
    echo "the API server accepted ${url}" >&2
    exit 1
  fi
  cat "${WORKDIR}/apply.err"
  grep -q 'spec.url' "${WORKDIR}/apply.err"
done
url_repository "git@[${GATEWAY}:2222]:app.git" | k apply --dry-run=server -f -
echo "The API server rejected URLs that git could read as options and accepted an scp-like address."
echo "::endgroup::"

# remote_head prints a branch's commit in repository $2, or app.
remote_head() { g ls-remote "${HOST_URL}/${2:-app}.git" "refs/heads/$1" | cut -f1; }
# branch_object prints the GitBranch for a branch of repository $2, or app.
branch_object() {
  k -n "${NS}" get gitbranches -l "git-k8s.imjasonh.com/repository=${2:-app}" \
    -o jsonpath="{.items[?(@.spec.branch==\"$1\")].metadata.name}"
}
fetch_main() { g fetch -q "${HOST_URL}/app.git" main; }
# A failed ls-remote prints nothing too, so it must not count as gone.
branch_gone() {
  local head
  head="$(remote_head "$1")" && [[ -z "${head}" && -z "$(branch_object "$1")" ]]
}

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
# grep -q would exit at the first match and fail the pipeline with SIGPIPE.
g log -1 --format=%B FETCH_HEAD | grep -x 'Git-K8s-Fixer: gofmt' >/dev/null
eventually 60 branch_gone c/fmt
g log --oneline FETCH_HEAD
echo "The gofmt check pushed a fix, main fast-forwarded to it, and c/fmt was deleted."
echo "::endgroup::"

echo "::group::The fix, the landing, and the deletion are events"
# has_event succeeds when controller $1 recorded an event with reason $2 and
# message $3, and prints the message.
has_event() {
  k -n "${NS}" get events --field-selector "reportingComponent=$1,reason=$2" \
    -o jsonpath='{range .items[*]}{.message}{"\n"}{end}' | grep -Fx -- "$3"
}
fmt_fix="$(g rev-parse FETCH_HEAD)"
fmt_from="$(g rev-parse FETCH_HEAD~2)"
eventually 30 has_event check-gofmt PushedFix "pushed ${fmt_fix:0:12} to c/fmt: 1 of 2 Go files need gofmt: util/add.go"
eventually 30 has_event merge Landed "fast-forwarded main from ${fmt_from:0:12} to c/fmt at ${fmt_fix:0:12}"
eventually 30 has_event merge DeletedBranch "deleted c/fmt at ${fmt_fix:0:12} after it landed on main"
k -n "${NS}" get events --sort-by=.metadata.creationTimestamp
echo "kubectl get events lists the gofmt check's fix and the merge controller's landing and deletion of c/fmt."
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
g log --format=%B FETCH_HEAD | grep -x 'Git-K8s-Fixer: base' >/dev/null
g log --graph --oneline FETCH_HEAD
echo "One branch landed, the base check merged main into the other, and it landed too."
echo "::endgroup::"

echo "::group::A check can write only its own result"
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
code="$(patch_status '{"status":{"checks":{"risk":{"commit":"0000000","state":"Passed"}}}}')"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 422 ]]
grep -q 'the gofmt check can only write status.checks.gofmt' "${WORKDIR}/patch.json"
code="$(patch_status '{"status":{"checks":{"gofmt":{"commit":"0000000","state":"Passed"}}}}')"
[[ "${code}" == 200 ]]
# A service account with check-gofmt's permissions but another name isn't a
# check, so it can't write any result.
k -n "${NS}" create serviceaccount rogue
k create clusterrolebinding git-k8s-e2e-rogue --clusterrole=check-gofmt --serviceaccount="${NS}:rogue"
rogue_token="$(k -n "${NS}" create token rogue)"
code="$(patch_status '{"status":{"checks":{"gofmt":{"commit":"0000000","state":"Passed"}}}}' "${rogue_token}")"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 422 ]]
grep -q "isn't a check's service account, so it can't write status.checks" "${WORKDIR}/patch.json"
echo "check-gofmt can write status.checks.gofmt but not status.checks.risk, and other service accounts can't write either."
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
# check-gotest owns Pods, so generate lets it patch GitBranch objects, and
# only the policy stops it.
gotest_token="$(k -n check-gotest create token check-gotest)"
for bearer in "${gotest_token}" "${core_token}"; do
  code="$(patch_branch "${bearer}" "${approve}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]]
  grep -q "git-k8s controllers can't approve branches" "${WORKDIR}/patch.json"
done
code="$(patch_branch "${gotest_token}" '{"metadata":{"labels":{"e2e":"changed"}}}')"
[[ "${code}" == 422 ]]
grep -q "the gotest check can't change GitBranch objects" "${WORKDIR}/patch.json"
# check-gofmt owns nothing, so generate doesn't let it patch GitBranch
# objects at all.
code="$(patch_branch "${token}" "${approve}")"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 403 ]]
grep -q 'cannot patch resource' "${WORKDIR}/patch.json"
echo "Neither a check nor the core controller can approve a branch, a check can't change one, and check-gofmt can't patch one."
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
gotest c/broken message | grep -- '--- FAIL: TestAdd' >/dev/null
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

echo "::group::Test Pods get modules and build outputs from go-cache"
# This is the README's NetworkPolicy: test Pods reach DNS, go-cache, and the
# git server, and nothing else.
k apply -f - <<EOF
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: test-pods
  namespace: ${NS}
spec:
  podSelector:
    matchLabels:
      app.kubernetes.io/name: check-gotest
  policyTypes: [Ingress, Egress]
  egress:
    - to:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: kube-system
          podSelector:
            matchLabels:
              k8s-app: kube-dns
      ports:
        - {protocol: UDP, port: 53}
        - {protocol: TCP, port: 53}
    - to:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: go-cache
          podSelector:
            matchLabels:
              app.kubernetes.io/name: go-cache
      ports:
        - {protocol: TCP, port: 8080}
    - to:
        - ipBlock:
            cidr: ${GATEWAY}/32
      ports:
        - {protocol: TCP, port: ${GIT_PORT}}
EOF
metrics() { k get --raw /api/v1/namespaces/go-cache/services/go-cache:http/proxy/metrics; }
# metric prints the value of a sample, such as
# go_cache_module_requests_total{result="hit"}, from the metrics in file $1.
metric() { awk -v sample="$2" '$1 == sample { print $2 }' "$1"; }
# grew prints how much sample $3 grew from metrics file $1 to file $2.
grew() { echo $(($(metric "$2" "$3") - $(metric "$1" "$3"))); }
GET_HIT='go_cache_build_requests_total{method="GET",result="hit"}'
GET_MISS='go_cache_build_requests_total{method="GET",result="miss"}'
PUT_CREATED='go_cache_build_requests_total{method="PUT",result="created"}'
PUT_DENIED='go_cache_build_requests_total{method="PUT",result="denied"}'
MOD_FETCHED='go_cache_module_requests_total{result="fetched"}'
MOD_HIT='go_cache_module_requests_total{result="hit"}'
metrics >"${WORKDIR}/metrics-0.txt"

t checkout -q -b c/greet "${fixed}"
printf '\nrequire example.com/greet v1.0.0\n' >>"${TESTED}/go.mod"
printf 'package tested\n\nimport "example.com/greet"\n\n// Greeting greets the cluster.\nfunc Greeting() string { return greet.Hello("kind") }\n' \
  >"${TESTED}/greeting.go"
cat >"${TESTED}/greeting_test.go" <<'GO'
package tested

import "testing"

func TestGreeting(t *testing.T) {
	if got := Greeting(); got != "Hello, kind" {
		t.Errorf("Greeting() = %q, want %q", got, "Hello, kind")
	}
}
GO
GOPROXY="http://127.0.0.1:${MOD_PORT}" GOSUMDB=off GOFLAGS=-modcacherw GOMODCACHE="${WORKDIR}/gomodcache" \
  go -C "${TESTED}" mod tidy
t add -A
t commit -qm "Greet the cluster"
greet="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/greet
greet_landed() { [[ "$(remote_head main tested)" == "${greet}" ]]; }
eventually 300 greet_landed
eventually 60 no_test_pods
metrics >"${WORKDIR}/metrics-1.txt"
(($(grew "${WORKDIR}/metrics-0.txt" "${WORKDIR}/metrics-1.txt" "${MOD_FETCHED}") > 0))

# A Pod that NetworkPolicies treat as a test Pod tries to reach the module
# proxy itself. kind's network plugin enforces NetworkPolicies, except on
# hosts that lack the kernel support that it needs. Like a test Pod, the
# probe meets the restricted Pod Security Standard.
k apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: np-probe
  namespace: ${NS}
  labels:
    app.kubernetes.io/name: check-gotest
spec:
  restartPolicy: Never
  activeDeadlineSeconds: 30
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: probe
      image: ${GO_IMAGE}
      command: [go, mod, download, -x, example.com/greet@v1.0.0]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
      env:
        - {name: HOME, value: /tmp}
        - {name: GOFLAGS, value: -modcacherw}
        - {name: GOPROXY, value: "http://${GATEWAY}:${MOD_PORT}"}
        - {name: GOSUMDB, value: "off"}
        - {name: GOTOOLCHAIN, value: local}
EOF
probe_phase() { k -n "${NS}" get pod np-probe -o jsonpath='{.status.phase}'; }
probe_done() { [[ "$(probe_phase)" == Succeeded || "$(probe_phase)" == Failed ]]; }
eventually 120 probe_done
k -n "${NS}" logs np-probe --tail=5 || true
if [[ "$(probe_phase)" == Succeeded ]]; then
  echo "This cluster doesn't enforce NetworkPolicies, so test Pods could have reached the module proxy."
else
  echo "The NetworkPolicy kept a test Pod from reaching the module proxy."
fi
k -n "${NS}" delete pod np-probe

# go-cache serves the module from its store now.
kill "${MOD_PROXY_PID}"
wait "${MOD_PROXY_PID}" 2>/dev/null || true
MOD_PROXY_PID=""
t checkout -q -b c/greet-docs
printf '# tested\n\nGreeting greets the cluster.\n' >"${TESTED}/README.md"
t add -A
t commit -qm "Add a README"
docs="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/greet-docs
docs_landed() { [[ "$(remote_head main tested)" == "${docs}" ]]; }
eventually 300 docs_landed
eventually 60 no_test_pods
metrics >"${WORKDIR}/metrics-2.txt"
m1="${WORKDIR}/metrics-1.txt"
m2="${WORKDIR}/metrics-2.txt"
grep '^go_cache_' "${m2}"
stored="$(grew "${WORKDIR}/metrics-0.txt" "${m1}" "${PUT_CREATED}")"
read_back="$(grew "${m1}" "${m2}" "${GET_HIT}")"
missed="$(grew "${m1}" "${m2}" "${GET_MISS}")"
stored_again="$(grew "${m1}" "${m2}" "${PUT_CREATED}")"
(($(grew "${m1}" "${m2}" "${MOD_HIT}") > 0 && $(grew "${m1}" "${m2}" "${MOD_FETCHED}") == 0))
((read_back >= 100 && stored_again < 10))
# go-cache turned away none of check-gotest's uploads.
(($(metric "${m2}" "${PUT_DENIED}") == 0))
echo "c/greet's Pod got example.com/greet through go-cache and stored ${stored} build outputs."
echo "With the module proxy stopped, c/greet-docs's Pod got the module from go-cache's store, read ${read_back} build outputs, missed ${missed}, and stored ${stored_again}."
k -n "${NS}" delete networkpolicy test-pods
echo "::endgroup::"

echo "::group::Only check-gotest's Pending Pods write to the build caches"
# Two Pods get tokens that can write tested's build cache. check-gotest
# doesn't own cache-writer, and a scheduling gate keeps it Pending, so it
# never runs. cache-runner has check-gotest's label, and runs.
k apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: cache-writer
  namespace: ${NS}
spec:
  schedulingGates:
    - name: git-k8s.imjasonh.com/e2e
  automountServiceAccountToken: false
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: writer
      image: ${GO_IMAGE}
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
---
apiVersion: v1
kind: Pod
metadata:
  name: cache-runner
  namespace: ${NS}
  labels:
    kube.imjasonh.github.io/controller: check-gotest
spec:
  automountServiceAccountToken: false
  terminationGracePeriodSeconds: 1
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: runner
      image: ${GO_IMAGE}
      command: [sleep, "600"]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
EOF
# write_token prints a token that can write tested's build cache, bound to
# the Pod named $1.
write_token() {
  k -n "${NS}" create token default --duration=10m \
    --audience="git-k8s.imjasonh.com/go-cache/write/${NS}/tested" \
    --bound-object-kind=Pod --bound-object-name="$1"
}
writer_token="$(write_token cache-writer)"
cache_ip="$(k -n go-cache get service go-cache -o jsonpath='{.spec.clusterIP}')"
probe_output="$(printf probe | sha256sum | cut -d ' ' -f 1)"
# put_probe uploads an output with token $2 while its Pod is $1, from a
# node, which reaches go-cache's Service like a test Pod. It writes the
# response to /tmp/probe.txt on the node, logs the status and the body, and
# prints the status.
put_probe() {
  local action code
  action="$(printf '%s' "$1" | sha256sum | cut -d ' ' -f 1)"
  code="$(docker exec "${CLUSTER}-control-plane" curl -sS -o /tmp/probe.txt -w '%{http_code}' -X PUT \
    -H "Authorization: Bearer $2" -H "Go-Output-Id: ${probe_output}" \
    --data-binary probe "http://${cache_ip}/cache/${NS}/tested/${action}")"
  echo "A write while the Pod is $1: ${code} $(docker exec "${CLUSTER}-control-plane" cat /tmp/probe.txt)" >&2
  echo "${code}"
}
pod_phase() { k -n "${NS}" get pod "$1" -o jsonpath='{.status.phase}'; }
code="$(put_probe unlabeled "${writer_token}")"
[[ "${code}" == 403 ]]
docker exec "${CLUSTER}-control-plane" grep -q "Pod ${NS}/cache-writer isn't check-gotest's" /tmp/probe.txt
# Anyone who can create Pods in the namespace can set check-gotest's label.
# go-cache remembers for 10 seconds that the Pod failed the check.
k -n "${NS}" label pod cache-writer kube.imjasonh.github.io/controller=check-gotest
[[ "$(pod_phase cache-writer)" == Pending ]]
labeled() { [[ "$(put_probe labeled "${writer_token}")" == 201 ]]; }
eventually 30 labeled
k -n "${NS}" delete pod cache-writer
code="$(put_probe deleted "${writer_token}")"
[[ "${code}" == 403 ]]
# check-gotest's Pods upload from an init container, while they're Pending.
runner_running() { [[ "$(pod_phase cache-runner)" == Running ]]; }
eventually 120 runner_running
runner_token="$(write_token cache-runner)"
code="$(put_probe running "${runner_token}")"
[[ "${code}" == 403 ]]
docker exec "${CLUSTER}-control-plane" grep -q "Pod ${NS}/cache-runner is Running, not Pending" /tmp/probe.txt
k -n "${NS}" delete pod cache-runner
echo "go-cache turned away a token from a Pod without check-gotest's label, took it once the Pending Pod had the label, and turned it away once the Pod was gone. It turned away a token from a Running Pod with the label."
echo "::endgroup::"

echo "::group::A check can change only its own Pods"
gotest_token="$(k -n check-gotest create token check-gotest)"
# pod_request sends request $1 for the Pods path $2 under
# /api/v1/namespaces/, with body $3, as check-gotest, without changing
# anything.
pod_request() {
  local type=application/json
  [[ "$1" == PATCH ]] && type=application/merge-patch+json
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/pod.json" -w '%{http_code}' -X "$1" \
    -H "Authorization: Bearer ${gotest_token}" -H "Content-Type: ${type}" \
    --data "${3:-}" "${server}/api/v1/namespaces/$2?dryRun=All"
}
# gotest_pod prints a Pod named $3, or gotest-e2e if $3 is empty, that meets
# the restricted Pod Security Standard, with the gotest check's label, that
# runs as service account $1 on node $2, or on the node that the scheduler
# picks if $2 is empty.
gotest_pod() {
  cat <<EOF
{"apiVersion": "v1", "kind": "Pod",
 "metadata": {"name": "${3:-gotest-e2e}", "labels": {"kube.imjasonh.github.io/controller": "check-gotest"}},
 "spec": {"serviceAccountName": "$1", "nodeName": "${2:-}", "restartPolicy": "Never", "automountServiceAccountToken": false,
  "securityContext": {"runAsNonRoot": true, "runAsUser": 65532, "seccompProfile": {"type": "RuntimeDefault"}},
  "containers": [{"name": "test", "image": "${GO_IMAGE}", "command": ["go", "version"],
   "securityContext": {"allowPrivilegeEscalation": false, "capabilities": {"drop": ["ALL"]}}}]}}
EOF
}
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default)")"
[[ "${code}" == 201 ]]
code="$(pod_request POST check-gofmt/pods "$(gotest_pod check-gofmt)")"
cat "${WORKDIR}/pod.json"
echo
[[ "${code}" == 422 ]]
grep -q "the gotest check can't change Pods in the namespaces of git-k8s programs" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod rogue)")"
[[ "${code}" == 422 ]]
grep -q "the gotest check's Pods must run as their namespace's default service account" "${WORKDIR}/pod.json"
code="$(pod_request POST default/pods "$(gotest_pod default)")"
[[ "${code}" == 422 ]]
grep -q "can't create or change Pods in namespace default, which doesn't have the label git-k8s.imjasonh.com/check-pods=true" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default "${CLUSTER}-control-plane")")"
[[ "${code}" == 422 ]]
grep -q "the gotest check can't assign its Pods to a node" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default "" review-e2e)")"
[[ "${code}" == 422 ]]
grep -q "the gotest check's new Pods need a name of the form gotest-ID, where ID has no hyphens" "${WORKDIR}/pod.json"
k -n "${NS}" apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: other
spec:
  restartPolicy: Never
  automountServiceAccountToken: false
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: other
      image: ${GO_IMAGE}
      command: [go, version]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
EOF
code="$(pod_request PATCH "${NS}/pods/other" '{"metadata":{"labels":{"kube.imjasonh.github.io/controller":"check-gotest"}}}')"
cat "${WORKDIR}/pod.json"
echo
[[ "${code}" == 422 ]]
grep -q "the gotest check can change or delete only its own Pods" "${WORKDIR}/pod.json"
code="$(pod_request DELETE "${NS}/pods/other")"
[[ "${code}" == 422 ]]
grep -q "the gotest check can change or delete only its own Pods" "${WORKDIR}/pod.json"
k -n "${NS}" delete pod other
echo "check-gotest can't run Pods in a program's namespace, as another service account, in a namespace that doesn't opt in, on a node that it names, or under another check's Pod name, and can't change or delete a Pod that it didn't create."
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
