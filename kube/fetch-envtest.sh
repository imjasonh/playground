#!/usr/bin/env bash
# Download the etcd and kube-apiserver binaries that the end-to-end tests run,
# check them against the SHA-512 hashes that controller-tools publishes, and
# print the directory that holds them. The binaries are cached in .envtest/
# next to this script.
#
# Usage:
#   export KUBEBUILDER_ASSETS="$(bash fetch-envtest.sh)"
#   go test ./...
set -euo pipefail

version=v1.37.0

os=$(uname -s | tr '[:upper:]' '[:lower:]')
case "$(uname -m)" in
  x86_64 | amd64) arch=amd64 ;;
  aarch64 | arm64) arch=arm64 ;;
  *)
    echo "fetch-envtest.sh: unsupported architecture $(uname -m)" >&2
    exit 1
    ;;
esac

# From https://github.com/kubernetes-sigs/controller-tools/blob/main/envtest-releases.yaml
case "${os}-${arch}" in
  linux-amd64) hash=1d1c453633b72c161a5d5a886cde7ac850be1a2ac796a9e1d4ffacacc64868295bdd2d57aa66cd0c158f5ce510f5dfe3fbc61ac21bd3dcfb875bd70658aa663a ;;
  linux-arm64) hash=ae6a670502988200b0131c943758cfd3d3a58cf4e6247ef7f0e6a6467f1cd9a333c802e86101f0446b1b92a0e327387224e1e44fe1a4693da0929c6e529cfe9a ;;
  darwin-amd64) hash=19a2a5376a8aa57a7b25ec5198834db29bf2ba0d6ff572d7f45ba683b13fb14c3ebec8069e92db66c39f1c7a9cff1bc2be879e2aacdc9fa8b8a7e861959bdf7b ;;
  darwin-arm64) hash=fb38cfacdd71b5e97a4d4cceac861af5f55069cf783f0e49cf181bfc32eb3e557c2091a534dc5d38f1b92c5ba142bc1979f215a5385b3630ea6a661be6fa161b ;;
  *)
    echo "fetch-envtest.sh: no envtest release for ${os}-${arch}" >&2
    exit 1
    ;;
esac

name="envtest-${version}-${os}-${arch}"
dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/.envtest/${name}"
if [[ -x "${dir}/kube-apiserver" && -x "${dir}/etcd" ]]; then
  echo "${dir}"
  exit 0
fi

tmp=$(mktemp -d)
trap 'rm -rf "${tmp}"' EXIT
curl -fsSL --retry 4 -o "${tmp}/${name}.tar.gz" \
  "https://github.com/kubernetes-sigs/controller-tools/releases/download/envtest-${version}/${name}.tar.gz"
if command -v sha512sum >/dev/null 2>&1; then
  echo "${hash}  ${tmp}/${name}.tar.gz" | sha512sum -c - >/dev/null
else
  echo "${hash}  ${tmp}/${name}.tar.gz" | shasum -a 512 -c - >/dev/null
fi
tar -xzf "${tmp}/${name}.tar.gz" -C "${tmp}"
mkdir -p "$(dirname "${dir}")"
rm -rf "${dir}"
mv "${tmp}/controller-tools/envtest" "${dir}"
echo "${dir}"
