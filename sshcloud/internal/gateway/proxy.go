package gateway

import (
	"context"
	"fmt"
	"io"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

// DialRequest is a backend wake/dial for one app generation.
type DialRequest struct {
	User  string
	App   string
	Gen   string
	Image string
}

// DialFunc resolves a running app instance address.
type DialFunc func(req DialRequest) (addr string, err error)

// ProxySSH dials the app SSH server with a minted user cert and pipes the session.
// ctx cancel (deploy kick) closes the hop and ends the proxy.
func ProxySSH(ctx context.Context, client io.ReadWriter, ca *userca.CA, principal, addr string) error {
	if ctx == nil {
		ctx = context.Background()
	}
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

	wait := make(chan error, 1)
	go func() { wait <- sess.Wait() }()
	select {
	case <-ctx.Done():
		_, _ = io.WriteString(client, "\r\n[sshcloud] session ended (deploy cutover)\r\n")
		_ = conn.Close()
		<-wait
		return ctx.Err()
	case err := <-wait:
		return err
	}
}
