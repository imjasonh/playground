package access

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/crypto/ssh"
)

func TestPolicyStagesAndDeployerImpliesMember(t *testing.T) {
	t.Parallel()
	memberLine, memberFP := testPublicKey(t)
	deployerLine, deployerFP := testPublicKey(t)
	_, unknownFP := testPublicKey(t)

	tests := []struct {
		name       string
		joinMode   string
		deployMode string
		check      func(t *testing.T, policy Policy)
	}{
		{
			name:       "private allowlists",
			joinMode:   JoinAllowlist,
			deployMode: DeployAllowlist,
			check: func(t *testing.T, policy Policy) {
				if !policy.AllowsUse(memberFP) || policy.AllowsDeploy(memberFP, true) {
					t.Fatal("member must be able to use but not deploy")
				}
				if !policy.AllowsUse(deployerFP) || !policy.AllowsDeploy(deployerFP, true) {
					t.Fatal("deployer must imply membership and deploy permission")
				}
				if policy.AllowsUse(unknownFP) || policy.AllowsDeploy(unknownFP, true) {
					t.Fatal("unknown key must be denied")
				}
			},
		},
		{
			name:       "open join with allowlisted deploy",
			joinMode:   JoinOpen,
			deployMode: DeployAllowlist,
			check: func(t *testing.T, policy Policy) {
				if !policy.AllowsUse(unknownFP) {
					t.Fatal("open join must admit unknown key")
				}
				if policy.AllowsDeploy(unknownFP, true) {
					t.Fatal("open join must not open deploy")
				}
			},
		},
		{
			name:       "open self service",
			joinMode:   JoinOpen,
			deployMode: DeployAllUsers,
			check: func(t *testing.T, policy Policy) {
				if !policy.AllowsUse(unknownFP) || !policy.AllowsDeploy(unknownFP, true) {
					t.Fatal("registered user must be able to use and deploy")
				}
				if policy.AllowsDeploy(unknownFP, false) {
					t.Fatal("unregistered key must not deploy")
				}
			},
		},
	}

	for _, tc := range tests {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			policy := parseTestPolicy(t, tc.joinMode, tc.deployMode, []string{memberLine}, []string{deployerLine})
			tc.check(t, policy)
		})
	}
}

func TestParseJSONRejectsUnsafePolicy(t *testing.T) {
	t.Parallel()
	validKey, _ := testPublicKey(t)
	valid := `{"version":1,"join_mode":"allowlist","deploy_mode":"allowlist","member_ssh_public_keys":[],"deployer_ssh_public_keys":[]}`
	tests := map[string]string{
		"empty":              "",
		"missing modes":      `{"version":1}`,
		"unknown mode":       strings.Replace(valid, `"allowlist"`, `"invite"`, 1),
		"unknown field":      strings.TrimSuffix(valid, "}") + `,"permit":true}`,
		"duplicate field":    strings.Replace(valid, `"version":1`, `"version":1,"version":1`, 1),
		"multiple objects":   valid + valid,
		"malformed key":      strings.Replace(valid, `"member_ssh_public_keys":[]`, `"member_ssh_public_keys":["SHA256:not-a-key"]`, 1),
		"key options":        strings.Replace(valid, `"member_ssh_public_keys":[]`, `"member_ssh_public_keys":[`+mustJSON(t, `from="192.0.2.1" `+validKey)+`]`, 1),
		"multiple key lines": strings.Replace(valid, `"member_ssh_public_keys":[]`, `"member_ssh_public_keys":[`+mustJSON(t, validKey+"\n"+validKey)+`]`, 1),
	}
	for name, data := range tests {
		name, data := name, data
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			if _, err := ParseJSON([]byte(data)); err == nil {
				t.Fatalf("ParseJSON(%q) unexpectedly succeeded", data)
			}
		})
	}
}

func TestFileSourceReloadsAndFailsClosed(t *testing.T) {
	t.Parallel()
	memberLine, memberFP := testPublicKey(t)
	_, otherFP := testPublicKey(t)
	path := filepath.Join(t.TempDir(), "access-policy.json")
	writeTestPolicy(t, path, JoinAllowlist, DeployAllowlist, []string{memberLine}, nil)

	source := FileSource{Path: path}
	policy, err := source.Load()
	if err != nil {
		t.Fatal(err)
	}
	if !policy.AllowsUse(memberFP) || policy.AllowsUse(otherFP) {
		t.Fatal("initial file policy not enforced")
	}

	writeTestPolicy(t, path, JoinOpen, DeployAllUsers, nil, nil)
	policy, err = source.Load()
	if err != nil {
		t.Fatal(err)
	}
	if !policy.AllowsUse(otherFP) || !policy.AllowsDeploy(otherFP, true) {
		t.Fatal("replacement policy was not reloaded")
	}

	if err := os.WriteFile(path, []byte("{broken"), 0o600); err != nil {
		t.Fatal(err)
	}
	if _, err := source.Load(); err == nil {
		t.Fatal("corrupt configured policy must fail closed, not retain the prior policy")
	}
	if err := os.Remove(path); err != nil {
		t.Fatal(err)
	}
	if _, err := source.Load(); err == nil {
		t.Fatal("missing configured policy must fail closed")
	}
}

func parseTestPolicy(t *testing.T, joinMode, deployMode string, members, deployers []string) Policy {
	t.Helper()
	raw := policyJSON{
		Version:               1,
		JoinMode:              joinMode,
		DeployMode:            deployMode,
		MemberSSHPublicKeys:   members,
		DeployerSSHPublicKeys: deployers,
	}
	data, err := json.Marshal(raw)
	if err != nil {
		t.Fatal(err)
	}
	policy, err := ParseJSON(data)
	if err != nil {
		t.Fatal(err)
	}
	return policy
}

func writeTestPolicy(t *testing.T, path, joinMode, deployMode string, members, deployers []string) {
	t.Helper()
	raw := policyJSON{
		Version:               1,
		JoinMode:              joinMode,
		DeployMode:            deployMode,
		MemberSSHPublicKeys:   members,
		DeployerSSHPublicKeys: deployers,
	}
	data, err := json.Marshal(raw)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, data, 0o600); err != nil {
		t.Fatal(err)
	}
}

func testPublicKey(t *testing.T) (string, string) {
	t.Helper()
	_, privateKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	key, err := ssh.NewPublicKey(privateKey.Public())
	if err != nil {
		t.Fatal(err)
	}
	return strings.TrimSpace(string(ssh.MarshalAuthorizedKey(key))) + " test@example", ssh.FingerprintSHA256(key)
}

func mustJSON(t *testing.T, value string) string {
	t.Helper()
	data, err := json.Marshal(value)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}
