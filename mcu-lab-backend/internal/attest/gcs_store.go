package attest

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
	"time"

	"golang.org/x/oauth2"
)

const defaultGCSBaseURL = "https://storage.googleapis.com"

// GCSStore persists App Attest challenges and device records in a Google Cloud
// Storage bucket using the JSON API and object-generation preconditions so
// multiple Cloud Run instances share durable state without counter replay.
type GCSStore struct {
	Bucket      string
	Prefix      string
	BaseURL     string
	TokenSource oauth2.TokenSource
	HTTPClient  *http.Client
}

type storedChallenge struct {
	ExpiresAt time.Time `json:"expiresAt"`
}

func (s *GCSStore) client() *http.Client {
	if s.HTTPClient != nil {
		return s.HTTPClient
	}
	return &http.Client{Timeout: 8 * time.Second}
}

func (s *GCSStore) baseURL() string {
	if s.BaseURL != "" {
		return strings.TrimRight(s.BaseURL, "/")
	}
	return defaultGCSBaseURL
}

func (s *GCSStore) objectName(kind, rawKey string) string {
	sum := sha256.Sum256([]byte(rawKey))
	name := kind + "/" + hex.EncodeToString(sum[:]) + ".json"
	if s.Prefix != "" {
		return strings.TrimRight(s.Prefix, "/") + "/" + name
	}
	return name
}

func (s *GCSStore) authorize(req *http.Request) error {
	if s.TokenSource == nil {
		return nil
	}
	tok, err := s.TokenSource.Token()
	if err != nil {
		return fmt.Errorf("gcs token: %w", err)
	}
	req.Header.Set("Authorization", "Bearer "+tok.AccessToken)
	return nil
}

func (s *GCSStore) putObject(ctx context.Context, objName string, body []byte) error {
	u := fmt.Sprintf("%s/upload/storage/v1/b/%s/o?uploadType=media&name=%s",
		s.baseURL(),
		url.PathEscape(s.Bucket),
		url.QueryEscape(objName),
	)
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, u, bytes.NewReader(body))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	if err := s.authorize(req); err != nil {
		return err
	}
	resp, err := s.client().Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 512))
		return fmt.Errorf("gcs put %s: status %d: %s", objName, resp.StatusCode, strings.TrimSpace(string(msg)))
	}
	return nil
}

func (s *GCSStore) getObject(ctx context.Context, objName string) ([]byte, string, error) {
	u := fmt.Sprintf("%s/storage/v1/b/%s/o/%s?alt=media",
		s.baseURL(),
		url.PathEscape(s.Bucket),
		url.PathEscape(objName),
	)
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, "", err
	}
	if err := s.authorize(req); err != nil {
		return nil, "", err
	}
	resp, err := s.client().Do(req)
	if err != nil {
		return nil, "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusNotFound {
		return nil, "", nil
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 512))
		return nil, "", fmt.Errorf("gcs get %s: status %d: %s", objName, resp.StatusCode, strings.TrimSpace(string(msg)))
	}
	data, err := io.ReadAll(io.LimitReader(resp.Body, 64*1024))
	if err != nil {
		return nil, "", err
	}
	return data, resp.Header.Get("X-Goog-Generation"), nil
}

func (s *GCSStore) deleteObject(ctx context.Context, objName, generation string) error {
	u := fmt.Sprintf("%s/storage/v1/b/%s/o/%s",
		s.baseURL(),
		url.PathEscape(s.Bucket),
		url.PathEscape(objName),
	)
	if generation != "" {
		u += "?ifGenerationMatch=" + url.QueryEscape(generation)
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodDelete, u, nil)
	if err != nil {
		return err
	}
	if err := s.authorize(req); err != nil {
		return err
	}
	resp, err := s.client().Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusNotFound || resp.StatusCode == http.StatusPreconditionFailed {
		return errors.New("unknown or already used challenge")
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 512))
		return fmt.Errorf("gcs delete %s: status %d: %s", objName, resp.StatusCode, strings.TrimSpace(string(msg)))
	}
	return nil
}

// PutChallenge stores a one-time challenge nonce with its expiration time.
func (s *GCSStore) PutChallenge(challenge string, expiresAt time.Time) error {
	raw, err := json.Marshal(storedChallenge{ExpiresAt: expiresAt})
	if err != nil {
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	return s.putObject(ctx, s.objectName("challenges", challenge), raw)
}

// ConsumeChallenge atomically verifies and deletes a challenge nonce using its
// GCS object generation so concurrent replays fail with HTTP 412.
func (s *GCSStore) ConsumeChallenge(challenge string, now time.Time) error {
	ctx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	objName := s.objectName("challenges", challenge)
	raw, gen, err := s.getObject(ctx, objName)
	if err != nil {
		return err
	}
	if len(raw) == 0 {
		return errors.New("unknown or already used challenge")
	}
	if err := s.deleteObject(ctx, objName, gen); err != nil {
		return err
	}
	var c storedChallenge
	if err := json.Unmarshal(raw, &c); err != nil {
		return errors.New("corrupt challenge record")
	}
	if now.After(c.ExpiresAt) {
		return errors.New("challenge expired")
	}
	return nil
}

// GetDevice looks up a registered device by keyID.
func (s *GCSStore) GetDevice(keyID string) (*DeviceRecord, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	raw, _, err := s.getObject(ctx, s.objectName("devices", keyID))
	if err != nil {
		return nil, err
	}
	if len(raw) == 0 {
		return nil, nil
	}
	var rec DeviceRecord
	if err := json.Unmarshal(raw, &rec); err != nil {
		return nil, err
	}
	return &rec, nil
}

// PutDevice persists or updates an attested device record.
func (s *GCSStore) PutDevice(rec *DeviceRecord) error {
	if rec == nil {
		return errors.New("nil device record")
	}
	raw, err := json.Marshal(rec)
	if err != nil {
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	return s.putObject(ctx, s.objectName("devices", rec.KeyID), raw)
}
