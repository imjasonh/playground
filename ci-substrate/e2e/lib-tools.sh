# Shared by the kind e2e scripts. Source it, then call the install_ functions
# with a directory for the tools they download. Each one puts that directory
# first on PATH.

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

# kube-proxy and local-path-provisioner exit with "too many open files" when
# the host's inotify instance limit is low (Linux defaults to 128) and another
# kind cluster already holds most of them. Raise the limits when permitted;
# otherwise continue, since a single cluster on a CI runner stays under them.
# See https://kind.sigs.k8s.io/docs/user/known-issues/#pod-errors-due-to-too-many-open-files
raise_inotify_limits() {
  local instances watches
  instances="$(sysctl -n fs.inotify.max_user_instances 2>/dev/null || echo 0)"
  watches="$(sysctl -n fs.inotify.max_user_watches 2>/dev/null || echo 0)"
  if [[ "${instances}" -ge 512 && "${watches}" -ge 524288 ]]; then
    return
  fi
  local sudo=""
  if [[ "$(id -u)" -ne 0 ]]; then
    command -v sudo >/dev/null 2>&1 || return 0
    sudo="sudo -n"
  fi
  ${sudo} sysctl -q -w fs.inotify.max_user_instances=512 fs.inotify.max_user_watches=524288 2>/dev/null ||
    echo "could not raise inotify limits (instances=${instances}, watches=${watches}); continuing" >&2
}

go_arch() {
  case "$(uname -m)" in
    x86_64) echo amd64 ;;
    aarch64 | arm64) echo arm64 ;;
    *) uname -m ;;
  esac
}

# install_kind installs kind KIND_VERSION unless that version is already on
# PATH. Substrate's pod certificates need the Kubernetes version that kind's
# default node image brings, so an older kind on PATH does not count.
install_kind() {
  local dir=$1 ver="${KIND_VERSION:-v0.33.0}"
  if [[ "$(kind version 2>/dev/null | awk '{print $2}')" == "${ver}" ]]; then
    return
  fi
  echo "Installing kind ${ver}"
  mkdir -p "${dir}"
  curl -fsSL -o "${dir}/kind" \
    "https://kind.sigs.k8s.io/dl/${ver}/kind-$(uname -s | tr '[:upper:]' '[:lower:]')-$(go_arch)"
  chmod +x "${dir}/kind"
  export PATH="${dir}:${PATH}"
}

install_ko() {
  local dir=$1
  command -v ko >/dev/null 2>&1 && return
  echo "Installing ko"
  GOBIN="${dir}" go install github.com/google/ko@v0.17.1
  export PATH="${dir}:${PATH}"
}

install_kubectl() {
  local dir=$1 ver="${KUBECTL_VERSION:-v1.34.1}"
  command -v kubectl >/dev/null 2>&1 && return
  echo "Installing kubectl ${ver}"
  mkdir -p "${dir}"
  curl -fsSL -o "${dir}/kubectl" \
    "https://dl.k8s.io/release/${ver}/bin/$(uname -s | tr '[:upper:]' '[:lower:]')/$(go_arch)/kubectl"
  chmod +x "${dir}/kubectl"
  export PATH="${dir}:${PATH}"
}

install_crane() {
  local dir=$1
  command -v crane >/dev/null 2>&1 && return
  echo "Installing crane"
  GOBIN="${dir}" go install github.com/google/go-containerregistry/cmd/crane@v0.22.1
  export PATH="${dir}:${PATH}"
}
