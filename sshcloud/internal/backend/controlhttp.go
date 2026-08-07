package backend

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

const (
	maxControlJSONBytes  = 1 << 20
	maxControlErrorBytes = 4 << 10
)

type controlHTTPKernel struct {
	baseURL          string
	controlClient    *controlauth.Client
	httpClient       *http.Client
	insecureLoopback bool
	timeout          time.Duration
}

type controlHTTPStatusError struct {
	Operation  string
	Status     string
	StatusCode int
	Body       string
}

func (e *controlHTTPStatusError) Error() string {
	if e.Body == "" {
		return fmt.Sprintf("%s: %s", e.Operation, e.Status)
	}
	return fmt.Sprintf("%s: %s: %s", e.Operation, e.Status, e.Body)
}

func statusError(err error) (*controlHTTPStatusError, bool) {
	var statusErr *controlHTTPStatusError
	ok := errors.As(err, &statusErr)
	return statusErr, ok
}

func (k controlHTTPKernel) json(
	ctx context.Context,
	method, requestPath, operation string,
	in, out any,
	headers http.Header,
) error {
	endpoint, err := k.endpoint(requestPath)
	if err != nil {
		return err
	}
	var body io.Reader
	if in != nil {
		payload, marshalErr := json.Marshal(in)
		if marshalErr != nil {
			return fmt.Errorf("%s request JSON: %w", operation, marshalErr)
		}
		if len(payload) > maxControlJSONBytes {
			return fmt.Errorf("%s request JSON exceeds %d bytes", operation, maxControlJSONBytes)
		}
		body = bytes.NewReader(payload)
	}
	req, err := http.NewRequestWithContext(ctx, method, endpoint, body)
	if err != nil {
		return fmt.Errorf("%s request: %w", operation, err)
	}
	if in != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	if out != nil {
		req.Header.Set("Accept", "application/json")
	}
	for name, values := range headers {
		for _, value := range values {
			req.Header.Add(name, value)
		}
	}
	res, err := k.do(req)
	if err != nil {
		return fmt.Errorf("%s: %w", operation, err)
	}
	defer res.Body.Close()
	if res.StatusCode < http.StatusOK || res.StatusCode >= http.StatusMultipleChoices {
		message, readErr := readControlBody(res.Body, maxControlErrorBytes)
		if readErr != nil {
			message = []byte(readErr.Error())
		}
		return &controlHTTPStatusError{
			Operation: operation, Status: res.Status, StatusCode: res.StatusCode,
			Body: strings.TrimSpace(string(message)),
		}
	}
	if out == nil {
		if _, err := readControlBody(res.Body, maxControlJSONBytes); err != nil {
			return fmt.Errorf("%s response: %w", operation, err)
		}
		return nil
	}
	data, err := readControlBody(res.Body, maxControlJSONBytes)
	if err != nil {
		return fmt.Errorf("%s response: %w", operation, err)
	}
	decoder := json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(out); err != nil {
		return fmt.Errorf("%s response JSON: %w", operation, err)
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		if err == nil {
			return fmt.Errorf("%s response JSON contains a trailing value", operation)
		}
		return fmt.Errorf("%s response JSON contains trailing data: %w", operation, err)
	}
	return nil
}

func (k controlHTTPKernel) endpoint(requestPath string) (string, error) {
	base, err := url.Parse(strings.TrimRight(k.baseURL, "/"))
	if err != nil || base.Scheme == "" || base.Host == "" || base.User != nil ||
		base.RawQuery != "" || base.Fragment != "" {
		return "", fmt.Errorf("invalid control base URL %q", k.baseURL)
	}
	if !strings.HasPrefix(requestPath, "/") || strings.HasPrefix(requestPath, "//") {
		return "", fmt.Errorf("invalid control request path %q", requestPath)
	}
	relative, err := url.ParseRequestURI(requestPath)
	if err != nil || relative.IsAbs() || relative.Host != "" {
		return "", fmt.Errorf("invalid control request path %q", requestPath)
	}
	base.Path = strings.TrimRight(base.Path, "/") + relative.Path
	base.RawPath = ""
	base.RawQuery = relative.RawQuery
	return base.String(), nil
}

func (k controlHTTPKernel) do(req *http.Request) (*http.Response, error) {
	if k.controlClient != nil {
		return k.controlClient.Do(req)
	}
	if err := controlauth.PrepareRequest(req, nil, k.insecureLoopback); err != nil {
		return nil, err
	}
	client := k.httpClient
	if client == nil {
		client = &http.Client{Timeout: k.timeout}
	}
	copy := *client
	copy.CheckRedirect = func(*http.Request, []*http.Request) error {
		return http.ErrUseLastResponse
	}
	return copy.Do(req)
}

func readControlBody(r io.Reader, limit int64) ([]byte, error) {
	data, err := io.ReadAll(io.LimitReader(r, limit+1))
	if err != nil {
		return nil, err
	}
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("body exceeds %d bytes", limit)
	}
	return data, nil
}
