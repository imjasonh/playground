# Shared by the e2e scripts that run stock Bazel. Source it, then call
# install_bazel <version>.

# install_bazel puts a pinned Bazel release in a cache directory, checked
# against the release's checksum, and prints its path.
install_bazel() {
  local version=$1 platform sum
  case "$(uname -s)-$(uname -m)" in
    Linux-x86_64) platform=linux-x86_64 sum=4dc8e99dfa802e252dac176d08201fd15c542ae78c448c8a89974b6f387c282c ;;
    Linux-aarch64) platform=linux-arm64 sum=58e6042fc54f3bf5704452b579f575ae935817d4b842a76123f05fae6b1f9a83 ;;
    Darwin-arm64) platform=darwin-arm64 sum=45e9388abf21d1107e146ea366ad080eb93cb6a5f3a4a3b048f78de0bc3faffa ;;
    Darwin-x86_64) platform=darwin-x86_64 sum=ce73346274c379f77880db8bd8b9c8569885fe56f19386173760949da9078df0 ;;
    *)
      echo "no pinned Bazel for $(uname -s)-$(uname -m)" >&2
      return 1
      ;;
  esac
  if [[ "${version}" != 8.4.2 ]]; then
    echo "update the checksums in lib-bazel.sh for Bazel ${version}" >&2
    return 1
  fi
  local dir="${CI_SUBSTRATE_BAZEL_CACHE:-${HOME}/.cache/ci-substrate}"
  local bin="${dir}/bazel-${version}-${platform}"
  if [[ ! -x "${bin}" ]]; then
    mkdir -p "${dir}"
    curl -fsSL -o "${bin}.tmp" "https://github.com/bazelbuild/bazel/releases/download/${version}/bazel-${version}-${platform}"
    if ! echo "${sum}  ${bin}.tmp" | sha256sum -c - >/dev/null; then
      echo "Bazel download does not match its checksum" >&2
      return 1
    fi
    chmod +x "${bin}.tmp"
    mv "${bin}.tmp" "${bin}"
  fi
  echo "${bin}"
}
