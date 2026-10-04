package gitserver

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"

	"golang.org/x/crypto/ssh"
)

// SSHServer serves the bare repositories under Root over SSH, so the
// repository at Root/app.git is at ssh://HOST/app.git and HOST:app.git.
type SSHServer struct {
	// Root holds the repositories.
	Root string
	// HostKey is the key that the server identifies itself with.
	HostKey ssh.Signer
	// AuthorizedKeys are the keys that clients can authenticate with.
	AuthorizedKeys []ssh.PublicKey
}

// Serve serves the connections that l accepts, until l is closed.
func (s *SSHServer) Serve(l net.Listener) error {
	config := &ssh.ServerConfig{PublicKeyCallback: s.authorize}
	config.AddHostKey(s.HostKey)
	for {
		c, err := l.Accept()
		if err != nil {
			return err
		}
		go s.serve(c, config)
	}
}

func (s *SSHServer) authorize(_ ssh.ConnMetadata, key ssh.PublicKey) (*ssh.Permissions, error) {
	for _, k := range s.AuthorizedKeys {
		if bytes.Equal(k.Marshal(), key.Marshal()) {
			return nil, nil
		}
	}
	return nil, fmt.Errorf("unknown key %s", ssh.FingerprintSHA256(key))
}

func (s *SSHServer) serve(c net.Conn, config *ssh.ServerConfig) {
	defer c.Close()
	conn, chans, reqs, err := ssh.NewServerConn(c, config)
	if err != nil {
		fmt.Fprintf(os.Stderr, "gitserver: ssh from %s: %v\n", c.RemoteAddr(), err)
		return
	}
	defer conn.Close()
	go ssh.DiscardRequests(reqs)
	for nc := range chans {
		if nc.ChannelType() != "session" {
			nc.Reject(ssh.UnknownChannelType, "only sessions are supported")
			continue
		}
		ch, reqs, err := nc.Accept()
		if err != nil {
			continue
		}
		go s.session(ch, reqs)
	}
}

// git quotes the repository's path, and puts a slash before it for an
// ssh:// URL but not for an scp-like one.
var sshCommandRE = regexp.MustCompile(`^(git-upload-pack|git-receive-pack) '/?([A-Za-z0-9][-A-Za-z0-9_.]*\.git)'$`)

// session runs the git command that a session's exec request names, with
// the protocol version that its GIT_PROTOCOL variable asks for.
func (s *SSHServer) session(ch ssh.Channel, reqs <-chan *ssh.Request) {
	defer ch.Close()
	protocol := ""
	for req := range reqs {
		switch req.Type {
		case "env":
			var env struct{ Name, Value string }
			if ssh.Unmarshal(req.Payload, &env) == nil && env.Name == "GIT_PROTOCOL" {
				protocol = env.Value
			}
			req.Reply(true, nil)
		case "exec":
			var payload struct{ Command string }
			var m []string
			if ssh.Unmarshal(req.Payload, &payload) == nil {
				m = sshCommandRE.FindStringSubmatch(payload.Command)
			}
			if m == nil || strings.Contains(m[2], "..") {
				req.Reply(false, nil)
				return
			}
			req.Reply(true, nil)
			status := s.run(ch, m[1], filepath.Join(s.Root, m[2]), protocol)
			ch.CloseWrite()
			ch.SendRequest("exit-status", false, ssh.Marshal(struct{ Status uint32 }{status}))
			return
		default:
			req.Reply(false, nil)
		}
	}
}

// run runs a git service with the session's input and output, and returns
// its exit status.
func (s *SSHServer) run(ch ssh.Channel, service, dir, protocol string) uint32 {
	if err := ensure(dir, service == "git-receive-pack"); err != nil {
		fmt.Fprintln(ch.Stderr(), err)
		return 128
	}
	cmd := exec.Command("git", strings.TrimPrefix(service, "git-"), dir)
	cmd.Env = append(os.Environ(), "GIT_PROTOCOL="+protocol, "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
	cmd.Stdout, cmd.Stderr = ch, ch.Stderr()
	fail := func(err error) uint32 {
		fmt.Fprintf(os.Stderr, "gitserver: git %s %s: %v\n", service, filepath.Base(dir), err)
		var exit *exec.ExitError
		if errors.As(err, &exit) && exit.ExitCode() > 0 {
			return uint32(exit.ExitCode())
		}
		return 1
	}
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return fail(err)
	}
	if err := cmd.Start(); err != nil {
		return fail(err)
	}
	// The client can keep its side open until the session ends, so copying
	// its input mustn't hold up Wait.
	go func() {
		io.Copy(stdin, ch)
		stdin.Close()
	}()
	if err := cmd.Wait(); err != nil {
		return fail(err)
	}
	return 0
}
