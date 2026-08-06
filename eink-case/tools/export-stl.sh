#!/bin/bash
# Export OpenSCAD file to STL
# Usage: export-stl.sh input.scad output.stl [-D 'var=value' ...]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
source "$SCRIPT_DIR/common.sh"

check_openscad

if [ $# -lt 2 ]; then
    echo "Usage: $0 input.scad output.stl [-D 'var=value' ...]"
    echo ""
    echo "Examples:"
    echo "  $0 box.scad box.stl"
    echo "  $0 box.scad box_large.stl -D 'width=80' -D 'height=60'"
    exit 1
fi

INPUT="$1"
OUTPUT="$2"
shift 2

# Collect -D parameters
DEFINES=()
while [ $# -gt 0 ]; do
    case "$1" in
        -D)
            shift
            DEFINES+=("-D" "$1")
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
    shift
done

# Ensure output directory exists
mkdir -p "$(dirname "$OUTPUT")"

echo "Exporting STL: $INPUT -> $OUTPUT"
if [ ${#DEFINES[@]} -gt 0 ]; then
    echo "Parameters: ${DEFINES[*]}"
fi

# Binary STL: smaller, and GitHub treats it as a binary blob (not tens of
# thousands of ASCII facet lines in the PR diff). Slicers accept both; there
# is no practical reason to commit ASCII STLs here.
$OPENSCAD \
    "${DEFINES[@]}" \
    --export-format=binstl \
    -o "$OUTPUT" \
    "$INPUT"

# Show file info (binary headers may literally start with "solid …"; sniff facets)
SIZE=$(ls -lh "$OUTPUT" | awk '{print $5}')
if grep -a -q 'facet normal' "$OUTPUT"; then
    KIND="ascii"
else
    KIND="binary"
fi
echo "STL exported: $OUTPUT ($SIZE, $KIND)"
