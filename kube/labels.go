package kube

import (
	"fmt"
	"maps"
	"regexp"
	"slices"
	"strings"
)

// selector is a parsed label selector. Every requirement must match.
type selector []requirement

type requirement struct {
	key    string
	op     string // "=", "!=", "in", "notin", "exists", "!"
	values []string
}

var setRE = regexp.MustCompile(`^([^\s!=(),]+)\s+(in|notin)\s*\(([^()]*)\)$`)

// parseSelector parses the Kubernetes label selector syntax, for example
// "app=web,tier!=db,env in (prod,staging),!canary".
func parseSelector(s string) (selector, error) {
	var out selector
	depth, start := 0, 0
	var parts []string
	for i, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case ',':
			if depth == 0 {
				parts = append(parts, s[start:i])
				start = i + 1
			}
		}
	}
	parts = append(parts, s[start:])
	for _, p := range parts {
		p = strings.TrimSpace(p)
		if p == "" {
			continue
		}
		var r requirement
		switch {
		case setRE.MatchString(p):
			m := setRE.FindStringSubmatch(p)
			r = requirement{key: m[1], op: m[2]}
			for v := range strings.SplitSeq(m[3], ",") {
				if v = strings.TrimSpace(v); v != "" {
					r.values = append(r.values, v)
				}
			}
			slices.Sort(r.values)
		case strings.HasPrefix(p, "!"):
			r = requirement{key: strings.TrimSpace(p[1:]), op: "!"}
		case strings.Contains(p, "!="):
			k, v, _ := strings.Cut(p, "!=")
			r = requirement{key: strings.TrimSpace(k), op: "!=", values: []string{strings.TrimSpace(v)}}
		case strings.Contains(p, "=="):
			k, v, _ := strings.Cut(p, "==")
			r = requirement{key: strings.TrimSpace(k), op: "=", values: []string{strings.TrimSpace(v)}}
		case strings.Contains(p, "="):
			k, v, _ := strings.Cut(p, "=")
			r = requirement{key: strings.TrimSpace(k), op: "=", values: []string{strings.TrimSpace(v)}}
		default:
			r = requirement{key: p, op: "exists"}
		}
		if r.key == "" || strings.ContainsAny(r.key, " ()=!,") {
			return nil, fmt.Errorf("invalid label selector requirement %q", p)
		}
		out = append(out, r)
	}
	slices.SortFunc(out, func(a, b requirement) int { return strings.Compare(a.String(), b.String()) })
	return out, nil
}

// selectorFromMap returns a selector that requires each label to equal its
// value.
func selectorFromMap(m map[string]string) selector {
	var out selector
	for _, k := range slices.Sorted(maps.Keys(m)) {
		out = append(out, requirement{key: k, op: "=", values: []string{m[k]}})
	}
	return out
}

func (s selector) matches(labels map[string]string) bool {
	for _, r := range s {
		v, ok := labels[r.key]
		switch r.op {
		case "=":
			if !ok || v != r.values[0] {
				return false
			}
		case "!=":
			if ok && v == r.values[0] {
				return false
			}
		case "in":
			if !ok || !slices.Contains(r.values, v) {
				return false
			}
		case "notin":
			if ok && slices.Contains(r.values, v) {
				return false
			}
		case "exists":
			if !ok {
				return false
			}
		case "!":
			if ok {
				return false
			}
		}
	}
	return true
}

func (r requirement) String() string {
	switch r.op {
	case "=", "!=":
		return r.key + r.op + r.values[0]
	case "in", "notin":
		return r.key + " " + r.op + " (" + strings.Join(r.values, ",") + ")"
	case "!":
		return "!" + r.key
	default:
		return r.key
	}
}

// String returns the selector in canonical form, suitable for the
// labelSelector query parameter.
func (s selector) String() string {
	parts := make([]string, len(s))
	for i, r := range s {
		parts[i] = r.String()
	}
	return strings.Join(parts, ",")
}
