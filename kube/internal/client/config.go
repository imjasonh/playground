// Package client is a small Kubernetes API client built on net/http.
//
// It covers what a controller needs: loading kubeconfig and in-cluster
// credentials, JSON requests, server-side apply, discovery, paginated and
// streaming lists, and watches. It decodes list responses item by item so
// a large list never has to fit in memory as one document.
package client

import (
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"errors"
	"fmt"
	"net"
	"net/url"
	"os"
	"path/filepath"
	"strings"

	"github.com/imjasonh/playground/kube/internal/yaml"
)

// Config describes how to reach and authenticate to an API server.
type Config struct {
	// Host is the API server URL, for example https://10.0.0.1:443.
	Host string
	// Namespace is the default namespace from the kubeconfig context or the
	// pod's service account. It's empty when neither sets one.
	Namespace string
	// Source describes where the configuration came from, for logs.
	Source string

	tlsConfig *tls.Config
	proxyURL  *url.URL
	auth      authenticator
}

const (
	inClusterTokenFile     = "/var/run/secrets/kubernetes.io/serviceaccount/token"
	inClusterCAFile        = "/var/run/secrets/kubernetes.io/serviceaccount/ca.crt"
	inClusterNamespaceFile = "/var/run/secrets/kubernetes.io/serviceaccount/namespace"
)

// Load finds cluster configuration. It uses the first of these that exists:
// the kubeconfig file at path, the files listed in $KUBECONFIG, the pod's
// service account, and $HOME/.kube/config.
func Load(path string) (*Config, error) {
	if path != "" {
		return LoadKubeconfig([]string{path}, "")
	}
	if env := os.Getenv("KUBECONFIG"); env != "" {
		return LoadKubeconfig(filepath.SplitList(env), "")
	}
	if os.Getenv("KUBERNETES_SERVICE_HOST") != "" {
		return InCluster()
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return nil, fmt.Errorf("no kubeconfig found and not running in a cluster: %w", err)
	}
	p := filepath.Join(home, ".kube", "config")
	if _, err := os.Stat(p); err != nil {
		return nil, fmt.Errorf("no kubeconfig found ($KUBECONFIG is unset, %s is missing) and not running in a cluster", p)
	}
	return LoadKubeconfig([]string{p}, "")
}

// InCluster returns configuration for a pod, using its service account.
func InCluster() (*Config, error) {
	host, port := os.Getenv("KUBERNETES_SERVICE_HOST"), os.Getenv("KUBERNETES_SERVICE_PORT")
	if host == "" || port == "" {
		return nil, errors.New("KUBERNETES_SERVICE_HOST and KUBERNETES_SERVICE_PORT must be set")
	}
	return inCluster("https://"+net.JoinHostPort(host, port), inClusterTokenFile, inClusterCAFile, inClusterNamespaceFile)
}

func inCluster(host, tokenFile, caFile, nsFile string) (*Config, error) {
	pool, err := loadCAFile(caFile)
	if err != nil {
		return nil, err
	}
	ns, _ := os.ReadFile(nsFile)
	tf := &tokenFileAuth{path: tokenFile}
	if _, err := tf.token(); err != nil {
		return nil, err
	}
	return &Config{
		Host:      host,
		Namespace: strings.TrimSpace(string(ns)),
		Source:    "in-cluster service account",
		tlsConfig: &tls.Config{RootCAs: pool, MinVersion: tls.VersionTLS12},
		auth:      tf,
	}, nil
}

// kubeconfig mirrors the parts of the kubeconfig file format this package
// understands.
type kubeconfig struct {
	CurrentContext string `json:"current-context"`
	Clusters       []struct {
		Name    string  `json:"name"`
		Cluster cluster `json:"cluster"`
	} `json:"clusters"`
	Contexts []struct {
		Name    string      `json:"name"`
		Context kubecontext `json:"context"`
	} `json:"contexts"`
	Users []struct {
		Name string `json:"name"`
		User user   `json:"user"`
	} `json:"users"`
}

type cluster struct {
	Server                   string `json:"server"`
	TLSServerName            string `json:"tls-server-name"`
	InsecureSkipTLSVerify    bool   `json:"insecure-skip-tls-verify"`
	CertificateAuthority     string `json:"certificate-authority"`
	CertificateAuthorityData string `json:"certificate-authority-data"`
	ProxyURL                 string `json:"proxy-url"`
	dir                      string
}

type kubecontext struct {
	Cluster   string `json:"cluster"`
	User      string `json:"user"`
	Namespace string `json:"namespace"`
}

type user struct {
	ClientCertificate     string      `json:"client-certificate"`
	ClientCertificateData string      `json:"client-certificate-data"`
	ClientKey             string      `json:"client-key"`
	ClientKeyData         string      `json:"client-key-data"`
	Token                 string      `json:"token"`
	TokenFile             string      `json:"tokenFile"`
	Username              string      `json:"username"`
	Password              string      `json:"password"`
	Exec                  *execConfig `json:"exec"`
	AuthProvider          *struct {
		Name string `json:"name"`
	} `json:"auth-provider"`
	dir string
}

// LoadKubeconfig merges the kubeconfig files at paths and returns the
// configuration for contextName, or for the current context when
// contextName is empty. When files disagree, the first file to define a
// cluster, user, context, or current context wins, as with kubectl.
func LoadKubeconfig(paths []string, contextName string) (*Config, error) {
	clusters := map[string]cluster{}
	users := map[string]user{}
	contexts := map[string]kubecontext{}
	current := ""
	var loaded []string
	for _, p := range paths {
		if p == "" {
			continue
		}
		data, err := os.ReadFile(p)
		if errors.Is(err, os.ErrNotExist) && len(paths) > 1 {
			continue
		}
		if err != nil {
			return nil, err
		}
		var kc kubeconfig
		if err := yaml.Unmarshal(data, &kc); err != nil {
			return nil, fmt.Errorf("parsing %s: %w", p, err)
		}
		loaded = append(loaded, p)
		dir := filepath.Dir(p)
		if current == "" {
			current = kc.CurrentContext
		}
		for _, c := range kc.Clusters {
			if _, ok := clusters[c.Name]; !ok {
				c.Cluster.dir = dir
				clusters[c.Name] = c.Cluster
			}
		}
		for _, u := range kc.Users {
			if _, ok := users[u.Name]; !ok {
				u.User.dir = dir
				users[u.Name] = u.User
			}
		}
		for _, c := range kc.Contexts {
			if _, ok := contexts[c.Name]; !ok {
				contexts[c.Name] = c.Context
			}
		}
	}
	if len(loaded) == 0 {
		return nil, fmt.Errorf("no kubeconfig files found in %v", paths)
	}
	if contextName == "" {
		contextName = current
	}
	if contextName == "" {
		return nil, fmt.Errorf("kubeconfig %v has no current-context", loaded)
	}
	ctx, ok := contexts[contextName]
	if !ok {
		return nil, fmt.Errorf("kubeconfig %v has no context %q", loaded, contextName)
	}
	cl, ok := clusters[ctx.Cluster]
	if !ok {
		return nil, fmt.Errorf("context %q refers to unknown cluster %q", contextName, ctx.Cluster)
	}
	if cl.Server == "" {
		return nil, fmt.Errorf("cluster %q has no server", ctx.Cluster)
	}
	u := users[ctx.User]

	cfg := &Config{
		Host:      strings.TrimSuffix(cl.Server, "/"),
		Namespace: ctx.Namespace,
		Source:    fmt.Sprintf("kubeconfig %s (context %q)", strings.Join(loaded, string(filepath.ListSeparator)), contextName),
	}
	tc := &tls.Config{
		MinVersion:         tls.VersionTLS12,
		ServerName:         cl.TLSServerName,
		InsecureSkipVerify: cl.InsecureSkipTLSVerify, // #nosec G402 -- the kubeconfig asked for it.
	}
	switch {
	case cl.CertificateAuthorityData != "":
		pem, err := base64.StdEncoding.DecodeString(cl.CertificateAuthorityData)
		if err != nil {
			return nil, fmt.Errorf("cluster %q: decoding certificate-authority-data: %w", ctx.Cluster, err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(pem) {
			return nil, fmt.Errorf("cluster %q: certificate-authority-data has no certificates", ctx.Cluster)
		}
		tc.RootCAs = pool
	case cl.CertificateAuthority != "":
		pool, err := loadCAFile(resolve(cl.dir, cl.CertificateAuthority))
		if err != nil {
			return nil, fmt.Errorf("cluster %q: %w", ctx.Cluster, err)
		}
		tc.RootCAs = pool
	}
	if cl.ProxyURL != "" {
		pu, err := url.Parse(cl.ProxyURL)
		if err != nil {
			return nil, fmt.Errorf("cluster %q: proxy-url: %w", ctx.Cluster, err)
		}
		cfg.proxyURL = pu
	}

	certPEM, keyPEM, err := u.clientCert()
	if err != nil {
		return nil, fmt.Errorf("user %q: %w", ctx.User, err)
	}
	if certPEM != nil {
		cert, err := tls.X509KeyPair(certPEM, keyPEM)
		if err != nil {
			return nil, fmt.Errorf("user %q: client certificate: %w", ctx.User, err)
		}
		tc.Certificates = []tls.Certificate{cert}
	}
	cfg.tlsConfig = tc

	switch {
	case u.Exec != nil:
		if u.Exec.Command != "" && strings.ContainsRune(u.Exec.Command, filepath.Separator) && !filepath.IsAbs(u.Exec.Command) {
			u.Exec.Command = filepath.Join(u.dir, u.Exec.Command)
		}
		cfg.auth = &execAuth{cfg: *u.Exec, server: cl.Server, caData: cl.CertificateAuthorityData, insecure: cl.InsecureSkipTLSVerify}
	case u.Token != "":
		cfg.auth = staticAuth("Bearer " + u.Token)
	case u.TokenFile != "":
		cfg.auth = &tokenFileAuth{path: resolve(u.dir, u.TokenFile)}
	case u.Username != "":
		cfg.auth = staticAuth("Basic " + base64.StdEncoding.EncodeToString([]byte(u.Username+":"+u.Password)))
	case u.AuthProvider != nil:
		return nil, fmt.Errorf("user %q: auth-provider %q is not supported; use an exec credential plugin", ctx.User, u.AuthProvider.Name)
	}
	return cfg, nil
}

func (u user) clientCert() (certPEM, keyPEM []byte, err error) {
	switch {
	case u.ClientCertificateData != "":
		if certPEM, err = base64.StdEncoding.DecodeString(u.ClientCertificateData); err != nil {
			return nil, nil, fmt.Errorf("decoding client-certificate-data: %w", err)
		}
	case u.ClientCertificate != "":
		if certPEM, err = os.ReadFile(resolve(u.dir, u.ClientCertificate)); err != nil {
			return nil, nil, err
		}
	default:
		return nil, nil, nil
	}
	switch {
	case u.ClientKeyData != "":
		if keyPEM, err = base64.StdEncoding.DecodeString(u.ClientKeyData); err != nil {
			return nil, nil, fmt.Errorf("decoding client-key-data: %w", err)
		}
	case u.ClientKey != "":
		if keyPEM, err = os.ReadFile(resolve(u.dir, u.ClientKey)); err != nil {
			return nil, nil, err
		}
	default:
		return nil, nil, errors.New("client certificate has no key")
	}
	return certPEM, keyPEM, nil
}

func resolve(dir, p string) string {
	if p == "" || filepath.IsAbs(p) {
		return p
	}
	return filepath.Join(dir, p)
}

func loadCAFile(path string) (*x509.CertPool, error) {
	pem, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	pool := x509.NewCertPool()
	if !pool.AppendCertsFromPEM(pem) {
		return nil, fmt.Errorf("%s has no certificates", path)
	}
	return pool, nil
}
