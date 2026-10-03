// Package subset compares decoded JSON documents.
package subset

import (
	"encoding/json"
	"strconv"
)

// Contains reports whether every value set in want is present and equal in
// have. Objects compare key by key, so have may contain extra keys, for
// example fields that the API server defaulted. Arrays must have the same
// length and compare element by element. A null in want matches a missing or
// null value in have.
//
// Both arguments use the types that encoding/json decodes into an any:
// map[string]any, []any, string, bool, nil, and float64 or json.Number.
func Contains(have, want any) bool {
	switch w := want.(type) {
	case nil:
		return have == nil
	case map[string]any:
		h, ok := have.(map[string]any)
		if !ok {
			return false
		}
		for k, wv := range w {
			hv, present := h[k]
			if !present && wv != nil {
				return false
			}
			if !Contains(hv, wv) {
				return false
			}
		}
		return true
	case []any:
		h, ok := have.([]any)
		if !ok || len(h) != len(w) {
			return false
		}
		for i := range w {
			if !Contains(h[i], w[i]) {
				return false
			}
		}
		return true
	case json.Number:
		return numberEqual(have, string(w))
	case float64:
		return numberEqual(have, strconv.FormatFloat(w, 'g', -1, 64))
	default:
		return have == want
	}
}

func numberEqual(have any, want string) bool {
	var hs string
	switch h := have.(type) {
	case json.Number:
		hs = string(h)
	case float64:
		hs = strconv.FormatFloat(h, 'g', -1, 64)
	default:
		return false
	}
	if hs == want {
		return true
	}
	hf, err1 := strconv.ParseFloat(hs, 64)
	wf, err2 := strconv.ParseFloat(want, 64)
	return err1 == nil && err2 == nil && hf == wf
}
