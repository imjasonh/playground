// Package envtest runs a real etcd and kube-apiserver for end-to-end tests.
//
// It uses the binaries in a directory such as the one that
// controller-runtime's setup-envtest downloads, conventionally named by
// $KUBEBUILDER_ASSETS. There's no controller manager, so garbage collection
// and built-in controllers such as the Deployment controller don't run.
package envtest

import (
	"context"
	"crypto/rand"
	"crypto/rsa"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/pem"
	"errors"
	"fmt"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"syscall"
	"time"
)

// Env is a running control plane.
type Env struct {
	// URL is the API server's address.
	URL string
	// EtcdURL is etcd's client address, for tests that check what the API
	// server stores.
	EtcdURL string
	// Kubeconfig is the path of a kubeconfig file for an administrator.
	Kubeconfig string

	dir   string
	procs []proc
}

type proc struct {
	cmd    *exec.Cmd
	exited chan struct{}
}

// Start starts etcd and kube-apiserver from the binaries in assets.
func Start(ctx context.Context, assets string) (*Env, error) {
	for _, b := range []string{"etcd", "kube-apiserver"} {
		if _, err := os.Stat(filepath.Join(assets, b)); err != nil {
			return nil, fmt.Errorf("envtest: %w", err)
		}
	}
	dir, err := os.MkdirTemp("", "kube-envtest-")
	if err != nil {
		return nil, err
	}
	env := &Env{dir: dir}
	if err := env.boot(ctx, assets); err != nil {
		env.Stop()
		return nil, err
	}
	return env, nil
}

func (env *Env) boot(ctx context.Context, assets string) error {
	dir := env.dir
	ports, err := freePorts(3)
	if err != nil {
		return err
	}
	etcdURL := "http://127.0.0.1:" + strconv.Itoa(ports[0])
	env.EtcdURL = etcdURL
	if err := env.start(filepath.Join(assets, "etcd"), "etcd.log",
		"--data-dir="+filepath.Join(dir, "etcd"),
		"--listen-client-urls="+etcdURL,
		"--advertise-client-urls="+etcdURL,
		"--listen-peer-urls=http://127.0.0.1:"+strconv.Itoa(ports[1]),
		"--initial-advertise-peer-urls=http://127.0.0.1:"+strconv.Itoa(ports[1]),
		"--initial-cluster=default=http://127.0.0.1:"+strconv.Itoa(ports[1]),
		"--unsafe-no-fsync",
	); err != nil {
		return err
	}

	key, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		return err
	}
	keyFile := filepath.Join(dir, "sa.key")
	pubFile := filepath.Join(dir, "sa.pub")
	pub, err := x509.MarshalPKIXPublicKey(&key.PublicKey)
	if err != nil {
		return err
	}
	if err := os.WriteFile(keyFile, pem.EncodeToMemory(&pem.Block{Type: "RSA PRIVATE KEY", Bytes: x509.MarshalPKCS1PrivateKey(key)}), 0o600); err != nil {
		return err
	}
	if err := os.WriteFile(pubFile, pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: pub}), 0o600); err != nil {
		return err
	}
	tokenBytes := make([]byte, 16)
	if _, err := rand.Read(tokenBytes); err != nil {
		return err
	}
	token := hex.EncodeToString(tokenBytes)
	tokenFile := filepath.Join(dir, "tokens.csv")
	if err := os.WriteFile(tokenFile, []byte(token+",admin,admin,system:masters\n"), 0o600); err != nil {
		return err
	}
	certDir := filepath.Join(dir, "certs")
	env.URL = "https://127.0.0.1:" + strconv.Itoa(ports[2])
	if err := env.start(filepath.Join(assets, "kube-apiserver"), "apiserver.log",
		"--etcd-servers="+etcdURL,
		"--cert-dir="+certDir,
		"--secure-port="+strconv.Itoa(ports[2]),
		"--bind-address=127.0.0.1",
		"--endpoint-reconciler-type=none",
		"--service-cluster-ip-range=10.0.0.0/24",
		"--service-account-issuer=https://kubernetes.default.svc",
		"--service-account-key-file="+pubFile,
		"--service-account-signing-key-file="+keyFile,
		"--authorization-mode=RBAC",
		"--token-auth-file="+tokenFile,
		"--disable-admission-plugins=ServiceAccount",
		"--allow-privileged=true",
	); err != nil {
		return err
	}
	if err := env.waitReady(ctx, token); err != nil {
		return fmt.Errorf("%w\n%s", err, env.tail("apiserver.log"))
	}
	ca, err := os.ReadFile(filepath.Join(certDir, "apiserver.crt"))
	if err != nil {
		return err
	}
	env.Kubeconfig = filepath.Join(dir, "kubeconfig")
	kc := fmt.Sprintf(`apiVersion: v1
kind: Config
current-context: envtest
clusters:
- name: envtest
  cluster:
    server: %s
    certificate-authority-data: %s
contexts:
- name: envtest
  context:
    cluster: envtest
    user: admin
    namespace: default
users:
- name: admin
  user:
    token: %s
`, env.URL, base64.StdEncoding.EncodeToString(ca), token)
	if err := os.WriteFile(env.Kubeconfig, []byte(kc), 0o600); err != nil {
		return err
	}
	return nil
}

func (e *Env) start(bin, logName string, args ...string) error {
	log, err := os.Create(filepath.Join(e.dir, logName))
	if err != nil {
		return err
	}
	cmd := exec.Command(bin, args...) // #nosec G204 -- test binaries from a trusted directory.
	cmd.Stdout, cmd.Stderr = log, log
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	if err := cmd.Start(); err != nil {
		return err
	}
	p := proc{cmd: cmd, exited: make(chan struct{})}
	go func() {
		_ = cmd.Wait()
		log.Close()
		close(p.exited)
	}()
	e.procs = append(e.procs, p)
	return nil
}

func (e *Env) waitReady(ctx context.Context, token string) error {
	hc := &http.Client{
		Timeout:   2 * time.Second,
		Transport: &http.Transport{TLSClientConfig: &tls.Config{InsecureSkipVerify: true}}, // #nosec G402 -- readiness probe of a local test server.
	}
	deadline := time.Now().Add(time.Minute)
	for time.Now().Before(deadline) {
		req, _ := http.NewRequestWithContext(ctx, http.MethodGet, e.URL+"/readyz", nil)
		req.Header.Set("Authorization", "Bearer "+token)
		if resp, err := hc.Do(req); err == nil {
			resp.Body.Close()
			if resp.StatusCode == http.StatusOK {
				return nil
			}
		}
		for _, p := range e.procs {
			select {
			case <-p.exited:
				return fmt.Errorf("envtest: %s exited", filepath.Base(p.cmd.Path))
			default:
			}
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(200 * time.Millisecond):
		}
	}
	return errors.New("envtest: kube-apiserver wasn't ready after a minute")
}

func (e *Env) tail(name string) string {
	b, _ := os.ReadFile(filepath.Join(e.dir, name))
	if len(b) > 4000 {
		b = b[len(b)-4000:]
	}
	return string(b)
}

// Stop stops the control plane and deletes its files.
func (e *Env) Stop() {
	for i := len(e.procs) - 1; i >= 0; i-- {
		p := e.procs[i]
		_ = p.cmd.Process.Signal(syscall.SIGTERM)
		select {
		case <-p.exited:
		case <-time.After(10 * time.Second):
			_ = p.cmd.Process.Kill()
			<-p.exited
		}
	}
	_ = os.RemoveAll(e.dir)
}

func freePorts(n int) ([]int, error) {
	var ports []int
	var lns []net.Listener
	defer func() {
		for _, ln := range lns {
			ln.Close()
		}
	}()
	for range n {
		ln, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			return nil, err
		}
		lns = append(lns, ln)
		ports = append(ports, ln.Addr().(*net.TCPAddr).Port)
	}
	return ports, nil
}
