package gateway

import (
	"fmt"
	"io"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

// DialFunc resolves a running app instance address.
type DialFunc func(user, app string) (addr string, err error)

// ProxySSH dials the app SSH server with a minted user cert and pipes the session.
func ProxySSH(client io.ReadWriter, ca *userca.CA, principal, addr string) error {
	cert, err := ca.Mint(principal, 5*time.Minute)
	if err != nil {
		return fmt.Errorf("mint cert: %w", err)
	}
	cfg := &ssh.ClientConfig{
		User:            principal,
		Auth:            []ssh.AuthMethod{ssh.PublicKeys(cert.Signer)},
		HostKeyCallback: ssh.InsecureIgnoreHostKey(), // app host keys are ephemeral pre-Firecracker
		Timeout:         10 * time.Second,
	}
	conn, err := ssh.Dial("tcp", addr, cfg)
	if err != nil {
		return fmt.Errorf("dial app: %w", err)
	}
	defer conn.Close()

	sess, err := conn.NewSession()
	if err != nil {
		return err
	}
	defer sess.Close()

	sess.Stdout = client
	sess.Stderr = client
	sess.Stdin = client

	modes := ssh.TerminalModes{ssh.ECHO: 0}
	_ = sess.RequestPty("xterm", 40, 80, modes)
	if err := sess.Shell(); err != nil {
		return err
	}
	return sess.Wait()
}
