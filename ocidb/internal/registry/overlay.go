package registry

// Overlay (squash / whiteout) semantics.
//
// An image's final filesystem is the result of stacking its layers in order and
// applying OCI whiteout rules:
//
//   - A normal entry at path P in a higher layer replaces the same path from a
//     lower layer (the lower copy is shadowed and never visible).
//   - A whiteout file named ".wh.<name>" in directory D deletes D/<name> (and
//     everything beneath it) from all lower layers.
//   - An opaque whiteout ".wh..wh..opq" in directory D deletes everything that
//     lower layers contributed *under* D (but keeps D itself and entries this
//     layer and higher add under D).
//
// Whiteout marker files are control entries: they are consumed to perform the
// deletion and never appear in the final filesystem themselves.

import (
	"path"
	"strings"
)

// Whiteout kinds, as reported by OverlayInfo.Whiteout.
const (
	WhiteoutNone   = ""
	WhiteoutFile   = "file"   // ".wh.<name>" deletes a single lower path
	WhiteoutOpaque = "opaque" // ".wh..wh..opq" clears a directory's lower contents
)

// overlayLoc identifies a specific entry (layer index + entry index).
type overlayLoc struct{ layer, entry int }

// OverlayInfo describes how a single tar entry fares in the squashed image.
type OverlayInfo struct {
	// Present is true when this exact entry is part of the final (squashed)
	// filesystem: it is the winning occurrence of its path and is not deleted by
	// any higher layer.
	Present bool
	// Whiteout classifies deletion control entries (WhiteoutNone for ordinary
	// files/dirs/symlinks).
	Whiteout string
}

// Overlay computes squash/whiteout semantics across per-layer tables of
// contents given in application order (index 0 is the lowest/base layer). The
// result is parallel to the input: result[i][j] describes layers[i][j].
func Overlay(layers [][]TarEntry) [][]OverlayInfo {
	out := make([][]OverlayInfo, len(layers))

	// winner maps a cleaned path to the layer/entry index that currently owns it
	// as we stack layers bottom-to-top.
	winner := map[string]overlayLoc{}

	for li, entries := range layers {
		out[li] = make([]OverlayInfo, len(entries))

		// 1) Classify and apply this layer's whiteouts to the lower state first;
		//    per the spec they affect only lower layers.
		for ei, ent := range entries {
			kind := whiteoutKind(ent.Path)
			out[li][ei].Whiteout = kind
			switch kind {
			case WhiteoutOpaque:
				dir := cleanPath(path.Dir(ent.Path))
				deleteSubtree(winner, dir, false)
			case WhiteoutFile:
				target := cleanPath(path.Join(path.Dir(ent.Path), strings.TrimPrefix(path.Base(ent.Path), ".wh.")))
				deleteSubtree(winner, target, true)
			}
		}

		// 2) Add this layer's ordinary entries, overwriting any lower winner.
		for ei, ent := range entries {
			if out[li][ei].Whiteout != WhiteoutNone {
				continue
			}
			winner[cleanPath(ent.Path)] = overlayLoc{li, ei}
		}
	}

	for _, w := range winner {
		out[w.layer][w.entry].Present = true
	}
	return out
}

// deleteSubtree removes path target from m. When inclusive is true, target
// itself is removed; entries strictly beneath target/ are always removed.
func deleteSubtree(m map[string]overlayLoc, target string, inclusive bool) {
	if inclusive {
		delete(m, target)
	}
	prefix := target + "/"
	if target == "/" {
		prefix = "/"
	}
	for k := range m {
		if k == target {
			continue
		}
		if strings.HasPrefix(k, prefix) {
			delete(m, k)
		}
	}
}

// whiteoutKind classifies a path's basename as a whiteout control entry.
func whiteoutKind(p string) string {
	base := path.Base(p)
	switch {
	case base == ".wh..wh..opq":
		return WhiteoutOpaque
	case strings.HasPrefix(base, ".wh."):
		return WhiteoutFile
	default:
		return WhiteoutNone
	}
}

// cleanPath drops a trailing slash so directory and file paths share a key
// space ("/etc/" and "/etc" are the same node); root stays "/".
func cleanPath(p string) string {
	if p == "" {
		return "/"
	}
	if p == "/" {
		return p
	}
	return strings.TrimSuffix(p, "/")
}
