#!/usr/bin/env bash
# Download and install Godot 4.7.2-stable Linux headless binary + Web export
# templates into ~/.cache/godot and ~/.local/share/godot/export_templates.
# Prints the path to the godot executable on stdout.
set -euo pipefail

GODOT_VERSION="${GODOT_VERSION:-4.7.2-stable}"
GODOT_TEMPLATE_DIR="${GODOT_VERSION/-/.}" # 4.7.2.stable

cache_dir="${HOME}/.cache/godot/${GODOT_VERSION}"
bin_name="Godot_v${GODOT_VERSION}_linux.x86_64"
bin_path="${cache_dir}/${bin_name}"
tpl_dir="${HOME}/.local/share/godot/export_templates/${GODOT_TEMPLATE_DIR}"

mkdir -p "$cache_dir" "$tpl_dir"

base_url="https://github.com/godotengine/godot/releases/download/${GODOT_VERSION}"

if [ ! -x "$bin_path" ]; then
  tmp_zip="$(mktemp)"
  trap 'rm -f "$tmp_zip"' EXIT
  echo "Downloading ${bin_name}.zip..." >&2
  curl -fsSL "${base_url}/${bin_name}.zip" -o "$tmp_zip"
  unzip -qo "$tmp_zip" -d "$cache_dir"
  chmod +x "$bin_path"
  rm -f "$tmp_zip"
  trap - EXIT
fi

if [ ! -f "${tpl_dir}/web_nothreads_release.zip" ] || [ ! -f "${tpl_dir}/version.txt" ]; then
  tmp_tpz="$(mktemp)"
  trap 'rm -f "$tmp_tpz"' EXIT
  echo "Downloading Godot_v${GODOT_VERSION}_export_templates.tpz..." >&2
  curl -fsSL "${base_url}/Godot_v${GODOT_VERSION}_export_templates.tpz" -o "$tmp_tpz"
  unzip -qjo "$tmp_tpz" 'templates/web_*' 'templates/version.txt' -d "$tpl_dir"
  rm -f "$tmp_tpz"
  trap - EXIT
fi

echo "$bin_path"
