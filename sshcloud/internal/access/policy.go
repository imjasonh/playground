// Package access loads and evaluates the gateway SSH-key admission policy.
package access

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"strings"

	"golang.org/x/crypto/ssh"
)

const (
	// JoinAllowlist admits only member and deployer keys.
	JoinAllowlist = "allowlist"
	// JoinOpen admits every valid SSH public key.
	JoinOpen = "open"

	// DeployAllowlist admits only deployer keys.
	DeployAllowlist = "allowlist"
	// DeployAllUsers admits every registered user.
	DeployAllUsers = "all-users"

	maxPolicyBytes = 1 << 20
)

// Policy is an immutable, parsed access policy.
type Policy struct {
	joinMode   string
	deployMode string
	members    map[string]struct{}
	deployers  map[string]struct{}
}

// Source returns the current policy. Implementations must return an error
// instead of a stale or permissive policy when the configured policy cannot be
// read or parsed.
type Source interface {
	Load() (Policy, error)
}

// StaticSource serves one immutable policy.
type StaticSource struct {
	Policy Policy
}

// Load implements Source.
func (s StaticSource) Load() (Policy, error) {
	return s.Policy, nil
}

// FileSource reloads a JSON policy from Path on every decision. This makes an
// atomic file replacement take effect without restarting the gateway.
type FileSource struct {
	Path string
}

// Load implements Source.
func (s FileSource) Load() (Policy, error) {
	if strings.TrimSpace(s.Path) == "" {
		return Policy{}, fmt.Errorf("access policy path is empty")
	}
	f, err := os.Open(s.Path)
	if err != nil {
		return Policy{}, fmt.Errorf("open access policy: %w", err)
	}
	defer f.Close()

	data, err := io.ReadAll(io.LimitReader(f, maxPolicyBytes+1))
	if err != nil {
		return Policy{}, fmt.Errorf("read access policy: %w", err)
	}
	if len(data) > maxPolicyBytes {
		return Policy{}, fmt.Errorf("access policy exceeds %d bytes", maxPolicyBytes)
	}
	policy, err := ParseJSON(data)
	if err != nil {
		return Policy{}, fmt.Errorf("parse access policy: %w", err)
	}
	return policy, nil
}

// LocalDevelopmentPolicy is deliberately permissive. The gateway uses it only
// when no access-policy file is configured.
func LocalDevelopmentPolicy() Policy {
	return Policy{
		joinMode:   JoinOpen,
		deployMode: DeployAllUsers,
		members:    map[string]struct{}{},
		deployers:  map[string]struct{}{},
	}
}

type policyJSON struct {
	Version               int      `json:"version"`
	JoinMode              string   `json:"join_mode"`
	DeployMode            string   `json:"deploy_mode"`
	MemberSSHPublicKeys   []string `json:"member_ssh_public_keys"`
	DeployerSSHPublicKeys []string `json:"deployer_ssh_public_keys"`
}

// ParseJSON validates a complete policy and converts configured OpenSSH public
// key lines to the same SHA256 fingerprints used by the SSH gateway.
func ParseJSON(data []byte) (Policy, error) {
	if len(data) == 0 {
		return Policy{}, fmt.Errorf("empty policy")
	}
	if len(data) > maxPolicyBytes {
		return Policy{}, fmt.Errorf("access policy exceeds %d bytes", maxPolicyBytes)
	}
	if err := rejectDuplicateFields(data); err != nil {
		return Policy{}, err
	}

	var raw policyJSON
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&raw); err != nil {
		return Policy{}, fmt.Errorf("invalid JSON: %w", err)
	}
	if err := requireJSONEOF(dec); err != nil {
		return Policy{}, err
	}
	if raw.Version != 1 {
		return Policy{}, fmt.Errorf("unsupported version %d", raw.Version)
	}
	if raw.JoinMode != JoinAllowlist && raw.JoinMode != JoinOpen {
		return Policy{}, fmt.Errorf("invalid join_mode %q", raw.JoinMode)
	}
	if raw.DeployMode != DeployAllowlist && raw.DeployMode != DeployAllUsers {
		return Policy{}, fmt.Errorf("invalid deploy_mode %q", raw.DeployMode)
	}

	members, err := fingerprints("member_ssh_public_keys", raw.MemberSSHPublicKeys)
	if err != nil {
		return Policy{}, err
	}
	deployers, err := fingerprints("deployer_ssh_public_keys", raw.DeployerSSHPublicKeys)
	if err != nil {
		return Policy{}, err
	}
	return Policy{
		joinMode:   raw.JoinMode,
		deployMode: raw.DeployMode,
		members:    members,
		deployers:  deployers,
	}, nil
}

// AllowsUse reports whether a key may join and use the platform. Deployer keys
// imply membership.
func (p Policy) AllowsUse(fingerprint string) bool {
	if p.joinMode == JoinOpen {
		return true
	}
	if p.joinMode != JoinAllowlist {
		return false
	}
	_, member := p.members[fingerprint]
	_, deployer := p.deployers[fingerprint]
	return member || deployer
}

// AllowsDeploy reports whether a registered user presenting fingerprint may
// deploy. Registration remains mandatory in both deploy modes.
func (p Policy) AllowsDeploy(fingerprint string, registered bool) bool {
	if !registered {
		return false
	}
	switch p.deployMode {
	case DeployAllUsers:
		return true
	case DeployAllowlist:
		_, ok := p.deployers[fingerprint]
		return ok
	default:
		return false
	}
}

func fingerprints(field string, lines []string) (map[string]struct{}, error) {
	result := make(map[string]struct{}, len(lines))
	for i, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			return nil, fmt.Errorf("%s[%d] is empty", field, i)
		}
		key, _, options, rest, err := ssh.ParseAuthorizedKey([]byte(line))
		if err != nil {
			return nil, fmt.Errorf("%s[%d] is not an OpenSSH public key: %w", field, i, err)
		}
		if len(options) != 0 {
			return nil, fmt.Errorf("%s[%d] must not contain authorized_keys options", field, i)
		}
		if len(bytes.TrimSpace(rest)) != 0 {
			return nil, fmt.Errorf("%s[%d] contains more than one public key", field, i)
		}
		result[ssh.FingerprintSHA256(key)] = struct{}{}
	}
	return result, nil
}

func rejectDuplicateFields(data []byte) error {
	dec := json.NewDecoder(bytes.NewReader(data))
	tok, err := dec.Token()
	if err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	if delim, ok := tok.(json.Delim); !ok || delim != '{' {
		return fmt.Errorf("policy must be a JSON object")
	}
	seen := map[string]struct{}{}
	for dec.More() {
		tok, err := dec.Token()
		if err != nil {
			return fmt.Errorf("invalid JSON: %w", err)
		}
		name, ok := tok.(string)
		if !ok {
			return fmt.Errorf("policy field name is not a string")
		}
		if _, duplicate := seen[name]; duplicate {
			return fmt.Errorf("duplicate policy field %q", name)
		}
		seen[name] = struct{}{}
		var value json.RawMessage
		if err := dec.Decode(&value); err != nil {
			return fmt.Errorf("invalid JSON field %q: %w", name, err)
		}
	}
	if _, err := dec.Token(); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	return requireJSONEOF(dec)
}

func requireJSONEOF(dec *json.Decoder) error {
	var extra any
	if err := dec.Decode(&extra); err != io.EOF {
		if err == nil {
			return fmt.Errorf("policy must contain exactly one JSON object")
		}
		return fmt.Errorf("invalid trailing JSON: %w", err)
	}
	return nil
}
