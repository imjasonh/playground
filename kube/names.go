package kube

import "strings"

// objectName makes s a valid name for a Namespace, Service, Lease, or other
// Kubernetes object: at most 63 lowercase letters, digits, and '-', which is
// also a valid label value.
func objectName(s string) string {
	s = strings.Map(func(r rune) rune {
		switch {
		case r >= 'a' && r <= 'z', r >= '0' && r <= '9':
			return r
		case r >= 'A' && r <= 'Z':
			return r + 'a' - 'A'
		}
		return '-'
	}, s)
	if len(s) > 63 {
		s = s[:63]
	}
	if s = strings.Trim(s, "-"); s == "" {
		return "controller"
	}
	return s
}
