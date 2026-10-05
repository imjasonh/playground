package client

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube/internal/protobuf"
)

// Client sends requests to one API server.
type Client struct {
	// Namespace is the default namespace from the client's configuration.
	Namespace string

	host  string
	hc    *http.Client
	disco discovery
}

// DefaultTimeout bounds non-streaming requests whose context has no deadline.
const DefaultTimeout = 30 * time.Second

// New returns a client for cfg. userAgent identifies the program to the API
// server in request logs and audit events.
func New(cfg *Config, userAgent string) (*Client, error) {
	u, err := url.Parse(cfg.Host)
	if err != nil {
		return nil, fmt.Errorf("parsing host %q: %w", cfg.Host, err)
	}
	if u.Scheme != "https" && u.Scheme != "http" {
		return nil, fmt.Errorf("host %q must be an http or https URL", cfg.Host)
	}
	tr := &http.Transport{
		Proxy:                 http.ProxyFromEnvironment,
		DialContext:           (&net.Dialer{Timeout: 30 * time.Second, KeepAlive: 30 * time.Second}).DialContext,
		TLSHandshakeTimeout:   10 * time.Second,
		ForceAttemptHTTP2:     true,
		DisableCompression:    !cfg.Compression,
		MaxIdleConnsPerHost:   25,
		IdleConnTimeout:       90 * time.Second,
		ExpectContinueTimeout: time.Second,
		// Watches are long-lived streams. Without pings, a connection that
		// dies without a FIN or RST leaves every watch on it hanging.
		HTTP2: &http.HTTP2Config{SendPingTimeout: 30 * time.Second, PingTimeout: 15 * time.Second},
	}
	if cfg.proxyURL != nil {
		tr.Proxy = http.ProxyURL(cfg.proxyURL)
	}
	if u.Scheme == "https" {
		tc := &tls.Config{MinVersion: tls.VersionTLS12}
		if cfg.tlsConfig != nil {
			tc = cfg.tlsConfig.Clone()
		}
		if a := cfg.auth; a != nil {
			if _, ok := a.(*execAuth); ok {
				tc.GetClientCertificate = func(*tls.CertificateRequestInfo) (*tls.Certificate, error) {
					cert, err := a.certificate(context.Background())
					if err != nil || cert == nil {
						return &tls.Certificate{}, err
					}
					return cert, nil
				}
			}
		}
		tr.TLSClientConfig = tc
	}
	return &Client{
		Namespace: cfg.Namespace,
		host:      strings.TrimSuffix(u.String(), "/"),
		hc:        &http.Client{Transport: &authTransport{base: tr, auth: cfg.auth, userAgent: userAgent}},
	}, nil
}

// Request describes one API call.
type Request struct {
	Method      string
	Path        string
	Query       url.Values
	Body        []byte
	ContentType string
	Accept      string
	// Stream disables DefaultTimeout, for watches and large lists.
	Stream bool
}

// Do sends r. On success the caller must close the response body. A non-2xx
// response is returned as an *APIError.
func (c *Client) Do(ctx context.Context, r Request) (*http.Response, error) {
	u := c.host + r.Path
	if len(r.Query) > 0 {
		u += "?" + r.Query.Encode()
	}
	var cancel context.CancelFunc = func() {}
	if _, ok := ctx.Deadline(); !ok && !r.Stream {
		ctx, cancel = context.WithTimeout(ctx, DefaultTimeout)
	}
	var body io.Reader
	if r.Body != nil {
		body = bytes.NewReader(r.Body)
	}
	req, err := http.NewRequestWithContext(ctx, r.Method, u, body)
	if err != nil {
		cancel()
		return nil, err
	}
	if r.ContentType != "" {
		req.Header.Set("Content-Type", r.ContentType)
	}
	accept := r.Accept
	if accept == "" {
		accept = "application/json"
	}
	req.Header.Set("Accept", accept)
	resp, err := c.hc.Do(req)
	if err != nil {
		cancel()
		return nil, err
	}
	if resp.StatusCode < 200 || resp.StatusCode > 299 {
		defer cancel()
		defer resp.Body.Close()
		return nil, decodeError(resp)
	}
	resp.Body = &cancelOnClose{ReadCloser: resp.Body, cancel: cancel}
	return resp, nil
}

type cancelOnClose struct {
	io.ReadCloser
	cancel context.CancelFunc
}

func (c *cancelOnClose) Close() error {
	err := c.ReadCloser.Close()
	c.cancel()
	return err
}

// Call sends r and decodes a JSON response into out, unless out is nil.
func (c *Client) Call(ctx context.Context, r Request, out any) error {
	resp, err := c.Do(ctx, r)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if out == nil {
		_, err := io.Copy(io.Discard, resp.Body)
		return err
	}
	return json.NewDecoder(resp.Body).Decode(out)
}

// Get decodes the object at path into out.
func (c *Client) Get(ctx context.Context, path string, out any) error {
	return c.Call(ctx, Request{Method: http.MethodGet, Path: path}, out)
}

// Create posts obj to the collection at path.
func (c *Client) Create(ctx context.Context, path string, obj, out any) error {
	b, err := json.Marshal(obj)
	if err != nil {
		return err
	}
	return c.Call(ctx, Request{Method: http.MethodPost, Path: path, Body: b, ContentType: "application/json"}, out)
}

// Update replaces the object at path with obj. Set metadata.resourceVersion
// in obj to make the update conditional.
func (c *Client) Update(ctx context.Context, path string, obj, out any) error {
	b, err := json.Marshal(obj)
	if err != nil {
		return err
	}
	return c.Call(ctx, Request{Method: http.MethodPut, Path: path, Body: b, ContentType: "application/json"}, out)
}

// Patch types accepted by Patch.
const (
	ApplyPatch     = "application/apply-patch+yaml"
	MergePatch     = "application/merge-patch+json"
	JSONPatch      = "application/json-patch+json"
	StrategicPatch = "application/strategic-merge-patch+json"
)

// Patch sends a patch of the given type to path.
func (c *Client) Patch(ctx context.Context, path, patchType string, query url.Values, body []byte, out any) error {
	return c.Call(ctx, Request{Method: http.MethodPatch, Path: path, Query: query, Body: body, ContentType: patchType}, out)
}

// Apply sends obj as a server-side apply patch owned by fieldManager. JSON
// is valid YAML, so obj is sent as JSON. With force set, the apply takes
// ownership of fields that other managers own instead of failing with a
// conflict.
func (c *Client) Apply(ctx context.Context, path, fieldManager string, force bool, obj, out any) error {
	b, err := json.Marshal(obj)
	if err != nil {
		return err
	}
	q := url.Values{"fieldManager": {fieldManager}}
	if force {
		q.Set("force", "true")
	}
	return c.Patch(ctx, path, ApplyPatch, q, b, out)
}

// DeleteOptions controls a delete request.
type DeleteOptions struct {
	// UID, if set, makes the delete conditional on the object's UID, so a
	// newer object with the same name isn't deleted by mistake.
	UID string
	// Propagation is Background, Foreground, or Orphan. Empty means the
	// server default.
	Propagation string
}

// Delete deletes the object at path. Deleting an object that doesn't exist
// returns an error that satisfies IsNotFound.
func (c *Client) Delete(ctx context.Context, path string, opts DeleteOptions) error {
	return c.DeleteInto(ctx, path, opts, nil)
}

// DeleteInto is like Delete, and decodes the response into out unless out
// is nil. Depending on the type and the object, the response is a Status,
// the object as it was deleted, or the object as it waits for finalizers.
func (c *Client) DeleteInto(ctx context.Context, path string, opts DeleteOptions, out any) error {
	body := map[string]any{"kind": "DeleteOptions", "apiVersion": "v1"}
	if opts.Propagation != "" {
		body["propagationPolicy"] = opts.Propagation
	}
	if opts.UID != "" {
		body["preconditions"] = map[string]string{"uid": opts.UID}
	}
	b, err := json.Marshal(body)
	if err != nil {
		return err
	}
	return c.Call(ctx, Request{Method: http.MethodDelete, Path: path, Body: b, ContentType: "application/json"}, out)
}

// Path returns the URL path of a resource collection, object, or subresource.
// apiVersion is "v1" for the core group or "group/version" otherwise; name
// and namespace may be empty.
func Path(apiVersion, plural, namespace, name string, subresource ...string) string {
	var b strings.Builder
	if strings.Contains(apiVersion, "/") {
		b.WriteString("/apis/")
	} else {
		b.WriteString("/api/")
	}
	b.WriteString(apiVersion)
	if namespace != "" {
		b.WriteString("/namespaces/")
		b.WriteString(url.PathEscape(namespace))
	}
	b.WriteString("/")
	b.WriteString(plural)
	if name != "" {
		b.WriteString("/")
		b.WriteString(url.PathEscape(name))
	}
	for _, s := range subresource {
		b.WriteString("/")
		b.WriteString(s)
	}
	return b.String()
}

// APIError is a non-2xx response from the API server.
type APIError struct {
	// Code is the HTTP status code.
	Code int
	// Reason is the machine-readable reason from the Status object, for
	// example NotFound, AlreadyExists, Conflict, or Expired.
	Reason string
	// Message is the human-readable description from the server.
	Message string
}

func (e *APIError) Error() string {
	if e.Message == "" {
		return fmt.Sprintf("API server returned %d %s", e.Code, http.StatusText(e.Code))
	}
	return fmt.Sprintf("%s (%d %s)", e.Message, e.Code, e.Reason)
}

// status is the API server's error body.
type status struct {
	Kind    string `json:"kind"`
	Status  string `json:"status"`
	Message string `json:"message"`
	Reason  string `json:"reason"`
	Code    int    `json:"code"`
}

func decodeError(resp *http.Response) error {
	b, _ := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	e := &APIError{Code: resp.StatusCode}
	var s status
	switch {
	case bytes.HasPrefix(b, protobuf.Magic):
		if _, kind, raw, err := protobuf.Unwrap(b); err == nil && kind == "Status" {
			_, e.Reason, e.Message, _ = protobuf.Status(raw)
		}
	case json.Unmarshal(b, &s) == nil && s.Kind == "Status":
		e.Reason, e.Message = s.Reason, s.Message
	default:
		e.Message = strings.TrimSpace(string(b))
	}
	if e.Reason == "" {
		e.Reason = strings.ReplaceAll(http.StatusText(resp.StatusCode), " ", "")
	}
	return e
}

func apiError(err error) *APIError {
	var e *APIError
	if errors.As(err, &e) {
		return e
	}
	return nil
}

// IsNotFound reports whether err is a 404 from the API server.
func IsNotFound(err error) bool {
	e := apiError(err)
	return e != nil && e.Code == http.StatusNotFound
}

// IsConflict reports whether err is a 409 Conflict (but not AlreadyExists).
func IsConflict(err error) bool {
	e := apiError(err)
	return e != nil && e.Code == http.StatusConflict && e.Reason != "AlreadyExists"
}

// IsAlreadyExists reports whether err says the object already exists.
func IsAlreadyExists(err error) bool {
	e := apiError(err)
	return e != nil && e.Reason == "AlreadyExists"
}

// IsGone reports whether err is a 410, which the server returns when a
// watch or list asks for a resource version it no longer has.
func IsGone(err error) bool {
	e := apiError(err)
	return e != nil && (e.Code == http.StatusGone || e.Reason == "Expired" || e.Reason == "Gone")
}

// IsInvalid reports whether err is a 422 validation failure.
func IsInvalid(err error) bool {
	e := apiError(err)
	return e != nil && e.Code == http.StatusUnprocessableEntity
}

// IsForbidden reports whether err is a 403.
func IsForbidden(err error) bool {
	e := apiError(err)
	return e != nil && e.Code == http.StatusForbidden
}

// IsBadRequest reports whether err is a 400.
func IsBadRequest(err error) bool {
	e := apiError(err)
	return e != nil && e.Code == http.StatusBadRequest
}
