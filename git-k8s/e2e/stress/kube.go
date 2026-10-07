package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os/exec"
	"strings"
	"time"
)

// kubeClient calls the API server of a kubectl context with the context's
// client certificate. It ignores proxy environment variables, because the
// API server of a kind cluster listens on 127.0.0.1.
type kubeClient struct {
	server string
	http   *http.Client
}

// statusError is an API server response with a status other than 2xx.
type statusError struct {
	code int
	body string
}

func (e *statusError) Error() string {
	return fmt.Sprintf("status %d: %s", e.code, strings.TrimSpace(e.body))
}

func isNotFound(err error) bool {
	var se *statusError
	return errors.As(err, &se) && se.code == http.StatusNotFound
}

func newKubeClient(kubeContext string) (*kubeClient, error) {
	out, err := exec.Command("kubectl", "config", "view", "--raw", "--minify", "--flatten", "-o", "json", "--context", kubeContext).Output()
	if err != nil {
		return nil, fmt.Errorf("reading kubectl context %s: %w", kubeContext, err)
	}
	var cfg struct {
		Clusters []struct {
			Cluster struct {
				Server string `json:"server"`
				CAData string `json:"certificate-authority-data"`
			} `json:"cluster"`
		} `json:"clusters"`
		Users []struct {
			User struct {
				CertData string `json:"client-certificate-data"`
				KeyData  string `json:"client-key-data"`
			} `json:"user"`
		} `json:"users"`
	}
	if err := json.Unmarshal(out, &cfg); err != nil {
		return nil, err
	}
	if len(cfg.Clusters) != 1 || len(cfg.Users) != 1 {
		return nil, fmt.Errorf("kubectl context %s has %d clusters and %d users, want 1 of each", kubeContext, len(cfg.Clusters), len(cfg.Users))
	}
	decode := func(s string) []byte {
		b, _ := base64.StdEncoding.DecodeString(s)
		return b
	}
	pool := x509.NewCertPool()
	if !pool.AppendCertsFromPEM(decode(cfg.Clusters[0].Cluster.CAData)) {
		return nil, errors.New("kubectl context has no certificate authority data")
	}
	pair, err := tls.X509KeyPair(decode(cfg.Users[0].User.CertData), decode(cfg.Users[0].User.KeyData))
	if err != nil {
		return nil, fmt.Errorf("kubectl context %s has no client certificate: %w", kubeContext, err)
	}
	tr := &http.Transport{
		TLSClientConfig:     &tls.Config{RootCAs: pool, Certificates: []tls.Certificate{pair}},
		MaxIdleConnsPerHost: 32,
		IdleConnTimeout:     90 * time.Second,
	}
	return &kubeClient{server: strings.TrimSuffix(cfg.Clusters[0].Cluster.Server, "/"), http: &http.Client{Transport: tr}}, nil
}

// do sends a request and returns the response body of a 2xx response.
func (k *kubeClient) do(ctx context.Context, method, path, contentType string, body []byte) ([]byte, error) {
	ctx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, method, k.server+path, bytes.NewReader(body))
	if err != nil {
		return nil, err
	}
	if contentType != "" {
		req.Header.Set("Content-Type", contentType)
	}
	req.Header.Set("Accept", "application/json")
	resp, err := k.http.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode/100 != 2 {
		return nil, &statusError{code: resp.StatusCode, body: string(b)}
	}
	return b, nil
}

func (k *kubeClient) get(ctx context.Context, path string, into any) error {
	b, err := k.do(ctx, http.MethodGet, path, "", nil)
	if err != nil {
		return err
	}
	if into == nil {
		return nil
	}
	return json.Unmarshal(b, into)
}

// apply applies obj with server-side apply as the field manager stress.
func (k *kubeClient) apply(ctx context.Context, path string, obj any) error {
	b, err := json.Marshal(obj)
	if err != nil {
		return err
	}
	_, err = k.do(ctx, http.MethodPatch, path+"?fieldManager=stress&force=true", "application/apply-patch+yaml", b)
	return err
}

// mergePatch sends a JSON merge patch.
func (k *kubeClient) mergePatch(ctx context.Context, path string, patch any) error {
	b, err := json.Marshal(patch)
	if err != nil {
		return err
	}
	_, err = k.do(ctx, http.MethodPatch, path, "application/merge-patch+json", b)
	return err
}

func (k *kubeClient) create(ctx context.Context, path string, obj any) error {
	b, err := json.Marshal(obj)
	if err != nil {
		return err
	}
	_, err = k.do(ctx, http.MethodPost, path, "application/json", b)
	return err
}

func (k *kubeClient) delete(ctx context.Context, path string) error {
	_, err := k.do(ctx, http.MethodDelete, path, "", nil)
	if isNotFound(err) {
		return nil
	}
	return err
}

// username returns the user that the client authenticates as, as
// kubectl auth whoami prints it.
func (k *kubeClient) username(ctx context.Context) (string, error) {
	b, err := k.do(ctx, http.MethodPost, "/apis/authentication.k8s.io/v1/selfsubjectreviews", "application/json",
		[]byte(`{"apiVersion":"authentication.k8s.io/v1","kind":"SelfSubjectReview"}`))
	if err != nil {
		return "", err
	}
	var r struct {
		Status struct {
			UserInfo struct {
				Username string `json:"username"`
			} `json:"userInfo"`
		} `json:"status"`
	}
	if err := json.Unmarshal(b, &r); err != nil {
		return "", err
	}
	return r.Status.UserInfo.Username, nil
}

// watch lists the objects at path, calls handle with ADDED for each, then
// watches for changes and calls handle for each event, with the time that
// the event arrived, until ctx is done. It lists again when the watch's
// resource version expires. path may have a query string.
func (k *kubeClient) watch(ctx context.Context, path string, handle func(typ string, obj json.RawMessage, at time.Time)) {
	sep := "?"
	if strings.Contains(path, "?") {
		sep = "&"
	}
	rv := ""
	for ctx.Err() == nil {
		if rv == "" {
			var list struct {
				Metadata struct {
					ResourceVersion string `json:"resourceVersion"`
				} `json:"metadata"`
				Items []json.RawMessage `json:"items"`
			}
			if err := k.get(ctx, path, &list); err != nil {
				logf("listing %s: %v", path, err)
				sleep(ctx, time.Second)
				continue
			}
			at := time.Now()
			for _, item := range list.Items {
				handle("ADDED", item, at)
			}
			rv = list.Metadata.ResourceVersion
		}
		var err error
		rv, err = k.watchOnce(ctx, path+sep+"watch=1&allowWatchBookmarks=true&timeoutSeconds=300&resourceVersion="+rv, rv, handle)
		if err != nil && ctx.Err() == nil {
			logf("watching %s: %v", path, err)
			sleep(ctx, 500*time.Millisecond)
		}
	}
}

// watchOnce reads one watch response and returns the resource version to
// watch from next, or "" to list again.
func (k *kubeClient) watchOnce(ctx context.Context, path, rv string, handle func(string, json.RawMessage, time.Time)) (string, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, k.server+path, nil)
	if err != nil {
		return rv, err
	}
	req.Header.Set("Accept", "application/json")
	resp, err := k.http.Do(req)
	if err != nil {
		return rv, err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusGone {
		return "", nil
	}
	if resp.StatusCode != http.StatusOK {
		b, _ := io.ReadAll(resp.Body)
		return rv, &statusError{code: resp.StatusCode, body: string(b)}
	}
	dec := json.NewDecoder(resp.Body)
	for {
		var ev struct {
			Type   string          `json:"type"`
			Object json.RawMessage `json:"object"`
		}
		if err := dec.Decode(&ev); err != nil {
			if errors.Is(err, io.EOF) || ctx.Err() != nil {
				return rv, nil
			}
			return rv, err
		}
		at := time.Now()
		var meta struct {
			Code     int `json:"code"`
			Metadata struct {
				ResourceVersion string `json:"resourceVersion"`
			} `json:"metadata"`
		}
		_ = json.Unmarshal(ev.Object, &meta)
		switch ev.Type {
		case "ERROR":
			if meta.Code == http.StatusGone {
				return "", nil
			}
			return rv, fmt.Errorf("watch error: %s", ev.Object)
		case "BOOKMARK":
		default:
			handle(ev.Type, ev.Object, at)
		}
		if meta.Metadata.ResourceVersion != "" {
			rv = meta.Metadata.ResourceVersion
		}
	}
}

func sleep(ctx context.Context, d time.Duration) {
	t := time.NewTimer(d)
	defer t.Stop()
	select {
	case <-ctx.Done():
	case <-t.C:
	}
}
