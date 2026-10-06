#!/usr/bin/env bash
# Start a kind cluster, a local registry, a git server, and a module proxy,
# and install git-k8s, its built-in checks, and go-cache with production
# settings, for the stress harness in this directory. The setup follows
# e2e/kind/run-kind.sh, but it keeps everything running when it exits and
# writes what the harness needs to STATE/env.
#
# Only the following differ from a production install: images come from a
# local registry and build for one platform, a git server on this machine
# plays GitHub, and go-cache's upstream is a module proxy on this machine
# that serves only example.com/greet, so test repositories can use only the
# standard library and that module.
#
# Environment variables:
#   GK_STRESS_STATE          directory for logs, binaries, and the env file
#                            (default /tmp/gk-stress)
#   GK_STRESS_CLUSTER        kind cluster name (default gk-stress)
#   GK_STRESS_REGISTRY       registry container name (default gk-stress-registry)
#   GK_STRESS_REGISTRY_PORT  registry port on 127.0.0.1 (default 5300)
#   GK_STRESS_GIT_PORT       git server port (default 18700)
#   GK_STRESS_CHAINGUARD     where Chainguard's images come from
#                            (default cgr.dev/chainguard; docker.io/chainguard
#                            is a mirror)
#   GK_STRESS_DOCKER_IMAGES  1 copies Chainguard's images into the registry
#                            through Docker, from its local cache when it has
#                            them, for a machine without internet access
#   GK_STRESS_NXDOMAIN       1 makes CoreDNS answer names outside the cluster
#                            with NXDOMAIN, for a machine without a DNS server
#                            that answers
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
STATE="${GK_STRESS_STATE:-/tmp/gk-stress}"
CLUSTER="${GK_STRESS_CLUSTER:-gk-stress}"
CONTEXT="kind-${CLUSTER}"
REGISTRY="${GK_STRESS_REGISTRY:-gk-stress-registry}"
PORT="${GK_STRESS_REGISTRY_PORT:-5300}"
GIT_PORT="${GK_STRESS_GIT_PORT:-18700}"
CHAINGUARD="${GK_STRESS_CHAINGUARD:-cgr.dev/chainguard}"
PLATFORM="linux/$(go env GOARCH)"
LOCAL="localhost:${PORT}"
GO_IMAGE="${LOCAL}/chainguard/go:latest"
GIT_IMAGE="${LOCAL}/chainguard/git:latest"
CHECKS=(check-base check-gofmt check-risk check-approval check-gotest)

mkdir -p "${STATE}/bin" "${STATE}/repos" "${STATE}/manifests"
# saved prints a value from the env file of an earlier run in the same state
# directory. A second run reuses only the password, the git server, and the
# module proxy; everything else comes from this run's environment and this
# checkout.
saved() {
  if [[ -f "${STATE}/env" ]]; then
    sed -n "s/^$1=//p" "${STATE}/env" | tail -n 1
  fi
}
PASSWORD="$(saved PASSWORD)"
PASSWORD="${PASSWORD:-$(od -An -N12 -tx1 /dev/urandom | tr -d ' \n')}"
GIT_SERVER_PID="$(saved GIT_SERVER_PID)"
MOD_PROXY_PID="$(saved MOD_PROXY_PID)"

k() { kubectl --context "${CONTEXT}" "$@"; }

eventually() {
  local timeout=$1
  shift
  local deadline=$((SECONDS + timeout))
  until "$@"; do
    if ((SECONDS >= deadline)); then
      echo "timed out after ${timeout}s: $*" >&2
      return 1
    fi
    sleep 0.5
  done
}

# running reports whether the process with PID $1 runs the command $2, so a
# PID that another process took after a reboot doesn't count.
running() { [[ -n "$1" && "$(ps -p "$1" -o comm= 2>/dev/null)" == "$2" ]]; }
# detach starts a server that outlives this script and logs to $1. The server
# gets only stdin, stdout, and stderr. If it kept another of this script's file
# descriptors, it would hold any lock that the caller took on that descriptor,
# such as flock's, until the server exits.
detach() {
  local log=$1 fd
  shift
  (
    for fd in /proc/"${BASHPID}"/fd/*; do
      fd=${fd##*/}
      if [[ ${fd} =~ ^[0-9]+$ ]] && ((fd > 2)); then
        exec {fd}>&-
      fi
    done
    exec setsid "$@" >>"${log}" 2>&1 </dev/null
  ) &
}

echo "--- Registry ${REGISTRY} on 127.0.0.1:${PORT}"
if [[ "$(docker inspect -f '{{.State.Running}}' "${REGISTRY}" 2>/dev/null || true)" != true ]]; then
  docker run -d --restart=always -p "127.0.0.1:${PORT}:5000" --name "${REGISTRY}" registry:2 >/dev/null
fi
# Test Pods run in the go and git images, so the registry gets copies that
# the node can pull. Programs' images build on the git image, and go-cache's
# on the static image.
if [[ "${GK_STRESS_DOCKER_IMAGES:-}" == 1 ]]; then
  # seed copies a Chainguard image into the registry, from the local Docker
  # cache when it has the image.
  seed() {
    local name=$1 src
    for src in "${CHAINGUARD}/${name}" "chainguard/${name}"; do
      if docker image inspect "${src}" >/dev/null 2>&1; then
        break
      fi
      src=""
    done
    if [[ -z "${src}" ]]; then
      src="${CHAINGUARD}/${name}"
      docker pull -q --platform "${PLATFORM}" "${src}" >/dev/null
    fi
    docker tag "${src}" "${LOCAL}/chainguard/${name}"
    docker push -q --platform "${PLATFORM}" "${LOCAL}/chainguard/${name}" >/dev/null
  }
  for image in git:latest go:latest static:latest; do
    seed "${image}"
  done
  BASE="${LOCAL}/chainguard"
else
  crane() { go run github.com/google/go-containerregistry/cmd/crane@v0.22.1 "$@"; }
  crane copy --platform "${PLATFORM}" "${CHAINGUARD}/go:latest" "${GO_IMAGE}"
  crane copy --platform "${PLATFORM}" "${CHAINGUARD}/git:latest" "${GIT_IMAGE}"
  BASE="${CHAINGUARD}"
fi

echo "--- kind cluster ${CLUSTER}"
if ! kind get clusters 2>/dev/null | grep -qx "${CLUSTER}"; then
  kind create cluster --name "${CLUSTER}" --wait 120s --config - <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
networking:
  kubeProxyMode: nftables
EOF
fi
if [[ "$(docker inspect -f '{{json .NetworkSettings.Networks.kind}}' "${REGISTRY}")" == null ]]; then
  docker network connect kind "${REGISTRY}"
fi
GATEWAY="$(docker network inspect kind -f '{{range .IPAM.Config}}{{.Gateway}} {{end}}' | tr ' ' '\n' |
  grep -E '^[0-9]+[.][0-9]+[.][0-9]+[.][0-9]+$' | head -n 1)"
for node in $(kind get nodes --name "${CLUSTER}"); do
  docker exec "${node}" mkdir -p "/etc/containerd/certs.d/${LOCAL}"
  printf '[host."http://%s:5000"]\n' "${REGISTRY}" |
    docker exec -i "${node}" cp /dev/stdin "/etc/containerd/certs.d/${LOCAL}/hosts.toml"
done
# git looks up the IPv6 address of the mirror's short Service name through
# the whole search list, and the last name, git-k8s.git-k8s.svc., goes to
# CoreDNS's upstream. If the upstream doesn't answer, that lookup times out,
# which adds 4 seconds to every git command that checks and test Pods run
# against the mirror. A working upstream answers NXDOMAIN at once, and with
# GK_STRESS_NXDOMAIN=1, so does CoreDNS. The cluster's zones need their own
# server block, because CoreDNS runs the template plugin before the
# kubernetes plugin.
if [[ "${GK_STRESS_NXDOMAIN:-}" == 1 ]] && ! k -n kube-system get configmap coredns -o jsonpath='{.data.Corefile}' | grep -q 'rcode NXDOMAIN'; then
  k -n kube-system create configmap coredns --dry-run=client -o yaml --from-file=Corefile=/dev/stdin <<'EOF' | k replace -f - >/dev/null
cluster.local:53 in-addr.arpa:53 ip6.arpa:53 {
    errors
    kubernetes cluster.local in-addr.arpa ip6.arpa {
       pods insecure
       fallthrough in-addr.arpa ip6.arpa
       ttl 30
    }
    loadbalance
}
.:53 {
    errors
    health {
       lameduck 5s
    }
    ready
    prometheus :9153
    template ANY ANY {
       rcode NXDOMAIN
    }
    reload
}
EOF
  k -n kube-system rollout restart deployment/coredns >/dev/null
  k -n kube-system rollout status deployment/coredns --timeout=120s
fi

echo "--- Git server on 0.0.0.0:${GIT_PORT}"
(cd "${ROOT}" && go build -o "${STATE}/bin/gitserver" ./e2e/gitserver && go build -o "${STATE}/bin/modproxy" ./e2e/modproxy)
if running "${GIT_SERVER_PID}" gitserver && [[ "$(saved GIT_PORT)" != "${GIT_PORT}" ]]; then
  kill "${GIT_SERVER_PID}"
  GIT_SERVER_PID=""
fi
if ! running "${GIT_SERVER_PID}" gitserver; then
  GITSERVER_PASSWORD="${PASSWORD}" detach "${STATE}/gitserver.log" "${STATE}/bin/gitserver" \
    -addr="0.0.0.0:${GIT_PORT}" -root="${STATE}/repos"
  GIT_SERVER_PID=$!
fi
listening() { (echo >"/dev/tcp/127.0.0.1/${GIT_PORT}") 2>/dev/null; }
eventually 30 listening

echo "--- Module proxy for go-cache"
# example.com/greet isn't on the internet, so test Pods can get it only
# through go-cache, whose upstream is this proxy.
GREET="${STATE}/modules/example.com/greet@v1.0.0"
mkdir -p "${GREET}"
printf 'module example.com/greet\n\ngo 1.24\n' >"${GREET}/go.mod"
printf 'package greet\n\nfunc Hello(name string) string { return "Hello, " + name }\n' >"${GREET}/greet.go"
mod_port() { sed -nE 's/.* serving .* on .*:([0-9]+)$/\1/p' "${STATE}/modproxy.log" | tail -n 1; }
if ! running "${MOD_PROXY_PID}" modproxy; then
  : >"${STATE}/modproxy.log"
  detach "${STATE}/modproxy.log" "${STATE}/bin/modproxy" -addr=0.0.0.0:0 -dir="${STATE}/modules"
  MOD_PROXY_PID=$!
fi
mod_proxy_listening() { [[ -n "$(mod_port)" ]]; }
eventually 30 mod_proxy_listening
MOD_PORT="$(mod_port)"

cat >"${STATE}/env" <<EOF
STATE=${STATE}
ROOT=${ROOT}
CLUSTER=${CLUSTER}
CONTEXT=${CONTEXT}
REGISTRY=${REGISTRY}
REGISTRY_PORT=${PORT}
GIT_PORT=${GIT_PORT}
PASSWORD=${PASSWORD}
GATEWAY=${GATEWAY}
CLUSTER_URL=http://${GATEWAY}:${GIT_PORT}
HOST_URL=http://git-k8s:${PASSWORD}@127.0.0.1:${GIT_PORT}
MOD_PORT=${MOD_PORT}
GIT_SERVER_PID=${GIT_SERVER_PID}
MOD_PROXY_PID=${MOD_PROXY_PID}
GO_IMAGE=${GO_IMAGE}
GIT_IMAGE=${GIT_IMAGE}
EOF

echo "--- Pull the test Pods' images onto the nodes"
for node in $(kind get nodes --name "${CLUSTER}"); do
  docker exec "${node}" crictl pull "${GO_IMAGE}" >/dev/null
  docker exec "${node}" crictl pull "${GIT_IMAGE}" >/dev/null
done

echo "--- Install git-k8s, the checks, and go-cache with generate"
cd "${ROOT}"
# generate builds a program, pushes its image, and writes its manifests.
# Unlike run-kind.sh, it keeps each program's default replicas.
generate() {
  local program=$1
  shift
  go run "./cmd/${program}" generate -registry="${LOCAL}/gk-stress" -base="${BASE}/git:latest" \
    -platform="${PLATFORM}" "$@" >"${STATE}/manifests/${program}.yaml"
}
generate git-k8s -- -go-cache-namespace=go-cache
k apply -f "${STATE}/manifests/git-k8s.yaml"
generate go-cache -base="${BASE}/static:latest" -replicas=1 -tmp-size=10Gi -- \
  -max-size=8Gi "-upstream=http://${GATEWAY}:${MOD_PORT}"
for program in "${CHECKS[@]}"; do
  case "${program}" in
    check-gotest)
      generate "${program}" -- "-go-image=${GO_IMAGE}" "-git-image=${GIT_IMAGE}" -go-cache=http://go-cache.go-cache
      ;;
    *) generate "${program}" ;;
  esac
done
k -n git-k8s rollout status deployment/git-k8s --timeout=300s
k apply -f "${STATE}/manifests/go-cache.yaml"
k apply -f "${ROOT}/config/go-cache.yaml"
for program in "${CHECKS[@]}"; do
  k apply -f "${STATE}/manifests/${program}.yaml"
done
for program in go-cache "${CHECKS[@]}"; do
  k -n "${program}" rollout status "deployment/${program}" --timeout=300s
done

echo "--- Ready"
k get nodes -o wide
k get pods -A -o wide | grep -E 'git-k8s|check-|go-cache' || true
echo "Built from ${ROOT}; the images:"
sed -n 's/^ *image: //p' "${STATE}"/manifests/*.yaml | sort -u
echo "Pods reach the git server at http://${GATEWAY}:${GIT_PORT}; go-cache's upstream is http://${GATEWAY}:${MOD_PORT}"
echo "The harness reads ${STATE}/env"
