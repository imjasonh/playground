// Package platform defines the canonical RBE Platform.Properties keys used to
// route actions to pre-warmed Substrate Tag environments and clean-room
// isolation modes, and encodes them into Substrate actor names so actors
// forked from a memory snapshot know which queue to lease from via
// /system/name alone.
package platform

import (
	"fmt"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

const (
	// PropEnv names a published Substrate Tag in the tenant's atespace to
	// fork build actors from (e.g. "ci-substrate/env=warm-go").
	PropEnv = "ci-substrate/env"
	// PropIsolation selects per-action isolation: "clean" reverts actors to
	// their clean snapshot after each action; empty/"warm" reuses actors.
	PropIsolation = "ci-substrate/isolation"
	// IsolationClean requests clean-room per-action isolation via RevertActor.
	IsolationClean = "clean"
)

// Spec is the subset of RBE Platform.Properties that routes scheduling and
// Substrate actor creation.
type Spec struct {
	// Env is the Substrate Tag name to fork actors from, or empty for the
	// default ActorTemplate.
	Env string
	// Isolation is "clean" for per-action revert, or empty for warm reuse.
	Isolation string
}

// FromProperties extracts a Spec from RBE Platform.Properties.
func FromProperties(props []*repb.Platform_Property) Spec {
	var s Spec
	for _, p := range props {
		switch p.GetName() {
		case PropEnv:
			s.Env = strings.TrimSpace(p.GetValue())
		case PropIsolation:
			v := strings.TrimSpace(p.GetValue())
			if v == "warm" {
				v = ""
			}
			s.Isolation = v
		}
	}
	return s
}

// Validate reports an error if s carries an invalid tag name or unknown
// isolation mode.
func (s Spec) Validate() error {
	if s.Isolation != "" && s.Isolation != IsolationClean {
		return fmt.Errorf("unknown %s value %q (want %q or \"warm\")", PropIsolation, s.Isolation, IsolationClean)
	}
	if s.Env != "" {
		if len(s.Env) > 40 {
			return fmt.Errorf("%s tag %q exceeds 40 characters", PropEnv, s.Env)
		}
		if strings.Contains(s.Env, "--") {
			return fmt.Errorf("%s tag %q must not contain \"--\"", PropEnv, s.Env)
		}
		for i := 0; i < len(s.Env); i++ {
			c := s.Env[i]
			alnum := (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
			if !alnum && (c != '-' || i == 0 || i == len(s.Env)-1) {
				return fmt.Errorf("%s tag %q must be a lowercase DNS label", PropEnv, s.Env)
			}
		}
	}
	return nil
}

// FromAction extracts a Spec from Action.platform, falling back to
// Command.platform per REAPI v2.2.
func FromAction(action *repb.Action, command *repb.Command) Spec {
	if props := action.GetPlatform().GetProperties(); len(props) > 0 {
		return FromProperties(props)
	}
	return FromProperties(command.GetPlatform().GetProperties())
}

// Key returns the canonical queue key for s (empty for the default pool).
func (s Spec) Key() string {
	var parts []string
	if s.Env != "" {
		parts = append(parts, "env="+s.Env)
	}
	if s.Isolation == IsolationClean {
		parts = append(parts, "isolation="+IsolationClean)
	}
	return strings.Join(parts, ",")
}

// ParseKey parses a canonical queue key produced by Spec.Key.
func ParseKey(key string) Spec {
	if key == "" {
		return Spec{}
	}
	var s Spec
	for _, part := range strings.Split(key, ",") {
		k, v, ok := strings.Cut(part, "=")
		if !ok {
			continue
		}
		switch k {
		case "env":
			s.Env = v
		case "isolation":
			if v == IsolationClean {
				s.Isolation = IsolationClean
			}
		}
	}
	return s
}

// ActorName formats a Substrate actor name (valid k8s-short-name, <= 63 chars)
// encoding s after basePrefix, with id as the unique suffix.
func ActorName(basePrefix string, s Spec, id string) string {
	var name string
	switch {
	case s.Isolation == IsolationClean && s.Env != "":
		name = basePrefix + "clean-env-" + s.Env + "--" + id
	case s.Isolation == IsolationClean:
		name = basePrefix + "clean--" + id
	case s.Env != "":
		name = basePrefix + "env-" + s.Env + "--" + id
	default:
		name = basePrefix + id
	}
	if len(name) > 63 {
		name = strings.TrimRight(name[:63], "-")
	}
	return name
}

// ParseActorName decodes the Spec encoded into a Substrate actor name by
// ActorName. It reports false if name does not carry basePrefix.
func ParseActorName(basePrefix, name string) (Spec, bool) {
	if basePrefix == "" || !strings.HasPrefix(name, basePrefix) {
		return Spec{}, false
	}
	rest := strings.TrimPrefix(name, basePrefix)
	switch {
	case strings.HasPrefix(rest, "clean-env-"):
		tag, _, ok := strings.Cut(strings.TrimPrefix(rest, "clean-env-"), "--")
		if ok && tag != "" {
			return Spec{Env: tag, Isolation: IsolationClean}, true
		}
	case strings.HasPrefix(rest, "clean--"):
		return Spec{Isolation: IsolationClean}, true
	case strings.HasPrefix(rest, "env-"):
		tag, _, ok := strings.Cut(strings.TrimPrefix(rest, "env-"), "--")
		if ok && tag != "" {
			return Spec{Env: tag}, true
		}
	}
	return Spec{}, true
}
