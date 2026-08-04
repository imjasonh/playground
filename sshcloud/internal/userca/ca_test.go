package userca

import (
	"testing"
	"time"

	"golang.org/x/crypto/ssh"
)

func TestMintAndVerify(t *testing.T) {
	t.Parallel()
	ca, _, err := Generate()
	if err != nil {
		t.Fatal(err)
	}
	cert, err := ca.Mint("alice", time.Minute)
	if err != nil {
		t.Fatal(err)
	}
	sshCert, ok := cert.Signer.PublicKey().(*ssh.Certificate)
	if !ok {
		t.Fatal("expected certificate public key")
	}
	checker := &ssh.CertChecker{
		IsUserAuthority: func(auth ssh.PublicKey) bool {
			return string(auth.Marshal()) == string(ca.PublicKey().Marshal())
		},
	}
	if err := checker.CheckCert("alice", sshCert); err != nil {
		t.Fatal(err)
	}
	if err := checker.CheckCert("bob", sshCert); err == nil {
		t.Fatal("expected principal mismatch")
	}
}
