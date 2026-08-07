// Package names validates owner and app identifiers and lists reserved SSH users.
package names

import (
	"fmt"
	"regexp"
)

// Charset for owner ids (from join) and app names: [a-z][a-z0-9-]{2,31}
var identRE = regexp.MustCompile(`^[a-z][a-z0-9-]{2,31}$`)

// Reserved SSH usernames that cannot be claimed as apps.
var reserved = map[string]struct{}{
	"join":   {},
	"deploy": {},
	"menu":   {},
	"help":   {},
	"status": {},
	"whoami": {},
	"root":   {},
	"admin":  {},
}

// IsReserved reports whether name is a platform SSH user.
func IsReserved(name string) bool {
	_, ok := reserved[name]
	return ok
}

// ValidateIdent checks an owner or app name.
func ValidateIdent(name string) error {
	if name == "" {
		return fmt.Errorf("name is empty")
	}
	if IsReserved(name) {
		return fmt.Errorf("%q is reserved", name)
	}
	if !identRE.MatchString(name) {
		return fmt.Errorf("%q must match %s", name, identRE.String())
	}
	return nil
}
