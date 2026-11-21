#!/usr/bin/env bash
# Build and unpack the Wolfi user-space environment defined in .agents/apko.yaml,
# patch ELF binaries to use Wolfi's dynamic loader and glibc in ~/.apko-root,
# configure a writable ~/.rustup with the repo's pinned toolchain + wasm32 target,
# and export the environment in ~/.bashrc for non-interactive agent commands.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
apko_cfg="${repo_root}/.agents/apko.yaml"
apko_root="${HOME}/.apko-root"
local_bin="${HOME}/.local/bin"

# Use host system paths while bootstrapping and patching so an in-progress
# unpack never invokes an unpatched ELF binary from ~/.apko-root/usr/bin.
export PATH="${local_bin}:/opt/antigravity/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

mkdir -p "$local_bin"

# 1. Bootstrap crane and apko into ~/.local/bin if not present.
if [ ! -x "${local_bin}/crane" ]; then
  echo "Bootstrapping crane into ${local_bin}..."
  curl -fsSL "https://github.com/google/go-containerregistry/releases/latest/download/go-containerregistry_Linux_x86_64.tar.gz" |
    /usr/bin/tar -C "$local_bin" -xzf - crane
fi

if [ ! -x "${local_bin}/apko" ]; then
  echo "Bootstrapping apko from cgr.dev/chainguard/apko:latest into ${local_bin}..."
  "${local_bin}/crane" export --platform linux/amd64 cgr.dev/chainguard/apko:latest - |
    /usr/bin/tar -C "$local_bin" --strip-components=2 -xf - usr/bin/apko
fi

# 2. Build and unpack .agents/apko.yaml into ~/.apko-root when the config hash changes.
cfg_sha=$(/usr/bin/sha256sum "$apko_cfg" | /usr/bin/awk '{print $1}')
current_sha=""
if [ -f "${apko_root}/.apko-config.sha256" ]; then
  current_sha=$(/usr/bin/cat "${apko_root}/.apko-config.sha256")
fi

if [ "$cfg_sha" != "$current_sha" ] || [ ! -x "${apko_root}/usr/bin/go" ]; then
  echo "Building Wolfi environment from ${apko_cfg} with apko..."
  tmp_dir=$(/usr/bin/mktemp -d)
  stage_root="${apko_root}.tmp.$$"
  rm -rf "$stage_root"
  mkdir -p "$stage_root"
  trap 'rm -rf "$tmp_dir" "$stage_root"' EXIT

  "${local_bin}/apko" build --sbom=false "$apko_cfg" playground-env:latest "${tmp_dir}/env.tar" --arch x86_64

  echo "Extracting Wolfi rootfs into ${stage_root}..."
  /usr/bin/tar -xOf "${tmp_dir}/env.tar" --wildcards '*.tar.gz' |
    /usr/bin/tar -C "$stage_root" --no-same-owner --exclude='dev/*' -xzf -

  # Trust the VM proxy's local CA certificate inside the Wolfi rootfs.
  if [ -f /etc/ssl/certs/ca-certificates.crt ]; then
    mkdir -p "${stage_root}/etc/ssl/certs"
    /usr/bin/cp -f /etc/ssl/certs/ca-certificates.crt "${stage_root}/etc/ssl/certs/ca-certificates.crt"
  fi

  # Rewrite absolute symlinks and patch ELF executables to use Wolfi's ld-linux and usr/lib.
  echo "Patching Wolfi ELF binaries and symlinks for user-space execution..."
  /usr/bin/cp "${stage_root}/usr/bin/patchelf" "${tmp_dir}/patchelf"
  loader="${stage_root}/usr/lib/ld-linux-x86-64.so.2"
  final_loader="${apko_root}/usr/lib/ld-linux-x86-64.so.2"
  final_rpath="${apko_root}/usr/lib"

  for f in "${stage_root}/usr/bin/"* "${stage_root}/usr/lib/go/bin/"* "${stage_root}/usr/lib/go/pkg/tool/linux_amd64/"*; do
    if [ ! -e "$f" ] && [ ! -L "$f" ]; then
      continue
    fi
    if [ -L "$f" ]; then
      target=$(/usr/bin/readlink "$f")
      case "$target" in
        /bin/*|/usr/bin/*|/sbin/*)
          /usr/bin/ln -snf "$(/usr/bin/basename "$target")" "$f"
          ;;
        /*)
          /usr/bin/ln -snf "${apko_root}${target}" "$f"
          ;;
      esac
    elif [ -f "$f" ] && [ -x "$f" ] && [ "$(/usr/bin/head -c 4 "$f" 2>/dev/null)" = "$(printf '\177ELF')" ]; then
      "$loader" --library-path "${stage_root}/usr/lib" "${tmp_dir}/patchelf" \
        --force-rpath \
        --set-interpreter "$final_loader" \
        --set-rpath "$final_rpath" \
        "$f" 2>/dev/null || true
    fi
  done

  printf '%s\n' "$cfg_sha" > "${stage_root}/.apko-config.sha256"
  rm -rf "$apko_root"
  /usr/bin/mv "$stage_root" "$apko_root"
  rm -rf "$tmp_dir"
  trap - EXIT
else
  echo "Wolfi environment in ${apko_root} is already up to date (${cfg_sha})."
fi

# 3. Configure a writable ~/.rustup that links the host's preinstalled stable
# toolchain to the pinned 1.100.0 channel and installs the wasm32 target.
rustup_home="${HOME}/.rustup"
if [ -d /usr/local/rustup/toolchains/stable-x86_64-unknown-linux-gnu ]; then
  mkdir -p "${rustup_home}/toolchains" "${rustup_home}/tmp" "${rustup_home}/update-hashes"
  /usr/bin/ln -snf /usr/local/rustup/settings.toml "${rustup_home}/settings.toml"
  if [ ! -d "${rustup_home}/toolchains/stable-x86_64-unknown-linux-gnu" ]; then
    /usr/bin/cp -as /usr/local/rustup/toolchains/stable-x86_64-unknown-linux-gnu \
      "${rustup_home}/toolchains/stable-x86_64-unknown-linux-gnu"
    for f in /usr/local/rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/*; do
      if [ -f "$f" ]; then
        /usr/bin/cp -f --remove-destination "$f" \
          "${rustup_home}/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/$(/usr/bin/basename "$f")"
      fi
    done
  fi
  /usr/bin/ln -snf stable-x86_64-unknown-linux-gnu "${rustup_home}/toolchains/1.100.0-x86_64-unknown-linux-gnu"
  export RUSTUP_HOME="$rustup_home"
  if ! /usr/local/bin/rustup target list --installed | /usr/bin/grep -qx 'wasm32-unknown-unknown'; then
    /usr/local/bin/rustup target add wasm32-unknown-unknown
  fi
fi

# 4. Persist environment variables in ~/.bashrc so every non-interactive agent
# command (via BASH_ENV=~/.bashrc) uses the Wolfi tools by default.
bashrc="${HOME}/.bashrc"
/usr/bin/touch "$bashrc"
/usr/bin/sed -i '/case \$- in/,/esac/d' "$bashrc" 2>/dev/null || true
/usr/bin/sed -i '/# --- begin wolfi-apko-env ---/,/# --- end wolfi-apko-env ---/d' "$bashrc" 2>/dev/null || true

icu_dir=$(echo "${apko_root}/usr/share/icu/"*)
cat <<EOF >> "$bashrc"
# --- begin wolfi-apko-env ---
export GOROOT="${apko_root}/usr/lib/go"
export ICU_DATA="${icu_dir}"
export SSL_CERT_FILE="/etc/ssl/certs/ca-certificates.crt"
export RUSTUP_HOME="${rustup_home}"
export PATH="/opt/antigravity/bin:${apko_root}/usr/bin:${local_bin}:\$PATH"
# --- end wolfi-apko-env ---
EOF
