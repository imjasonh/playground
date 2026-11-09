package objstore

import (
	"context"
	"encoding/json/v2"
	"errors"
	"fmt"
	"io"
	"math/rand/v2"
	"net/http"
	"net/url"
	"os"
	"strings"
	"sync"
	"time"
)

// GCS is a bucket in Cloud Storage, through the JSON API. On Cloud Run it
// authenticates with the service account's token from the metadata server.
// Elsewhere, set GOOGLE_OAUTH_ACCESS_TOKEN (for example, to the output of
// gcloud auth print-access-token), or point it at an emulator, which needs
// no token.
type GCS struct {
	client   *http.Client
	endpoint string
	bucket   string
	prefix   string
	tokens   *tokenSource
}

// NewGCS returns the bucket. An empty endpoint means STORAGE_EMULATOR_HOST
// if that is set, and Cloud Storage otherwise.
func NewGCS(ctx context.Context, bucket, prefix, endpoint string) (*GCS, error) {
	if endpoint == "" {
		endpoint = os.Getenv("STORAGE_EMULATOR_HOST")
	}
	emulator := endpoint != ""
	if !emulator {
		endpoint = "https://storage.googleapis.com"
	}
	if !strings.Contains(endpoint, "://") {
		endpoint = "http://" + endpoint
	}
	g := &GCS{
		client:   &http.Client{Transport: &http.Transport{MaxIdleConnsPerHost: 64, ForceAttemptHTTP2: true, IdleConnTimeout: 90 * time.Second}},
		endpoint: strings.TrimRight(endpoint, "/"),
		bucket:   bucket,
		prefix:   prefix,
	}
	if !emulator {
		g.tokens = &tokenSource{client: g.client, static: os.Getenv("GOOGLE_OAUTH_ACCESS_TOKEN")}
	}
	return g, nil
}

func (g *GCS) name(key string) string {
	if g.prefix == "" {
		return key
	}
	return g.prefix + "/" + key
}

func (g *GCS) objectURL(key string) string {
	return g.endpoint + "/storage/v1/b/" + url.PathEscape(g.bucket) + "/o/" + url.PathEscape(g.name(key))
}

// Get implements Bucket.
func (g *GCS) Get(ctx context.Context, key string) (io.ReadCloser, error) {
	resp, err := g.do(ctx, http.MethodGet, g.objectURL(key)+"?alt=media", nil, 0)
	if err != nil {
		return nil, err
	}
	switch resp.StatusCode {
	case http.StatusOK:
		return resp.Body, nil
	case http.StatusNotFound:
		resp.Body.Close()
		return nil, ErrNotFound
	default:
		return nil, statusError("get "+key, resp)
	}
}

// Create implements Bucket with ifGenerationMatch=0, which Cloud Storage
// rejects with 412 when the object exists. When r is an io.Seeker, a failed
// attempt is retried; if the first attempt landed without its response
// arriving, the retry reports ErrExists for this caller's own object, and
// the caller must check the contents to tell.
func (g *GCS) Create(ctx context.Context, key string, r io.Reader, size int64) error {
	q := url.Values{"uploadType": {"media"}, "name": {g.name(key)}, "ifGenerationMatch": {"0"}}
	u := g.endpoint + "/upload/storage/v1/b/" + url.PathEscape(g.bucket) + "/o?" + q.Encode()
	resp, err := g.do(ctx, http.MethodPost, u, r, size)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	switch resp.StatusCode {
	case http.StatusOK, http.StatusCreated:
		io.Copy(io.Discard, resp.Body)
		return nil
	case http.StatusPreconditionFailed:
		return ErrExists
	default:
		return statusError("create "+key, resp)
	}
}

type listPage struct {
	NextPageToken string `json:"nextPageToken"`
	Items         []struct {
		Name        string    `json:"name"`
		Size        int64     `json:"size,string"`
		TimeCreated time.Time `json:"timeCreated"`
	} `json:"items"`
}

// List implements Bucket. Cloud Storage's startOffset is inclusive, so List
// drops an object named startAfter itself.
func (g *GCS) List(ctx context.Context, prefix, startAfter string) ([]Object, error) {
	var out []Object
	token := ""
	for {
		q := url.Values{"prefix": {g.name(prefix)}, "fields": {"nextPageToken,items(name,size,timeCreated)"}}
		if startAfter != "" {
			q.Set("startOffset", g.name(startAfter))
		}
		if token != "" {
			q.Set("pageToken", token)
		}
		resp, err := g.do(ctx, http.MethodGet, g.endpoint+"/storage/v1/b/"+url.PathEscape(g.bucket)+"/o?"+q.Encode(), nil, 0)
		if err != nil {
			return nil, err
		}
		if resp.StatusCode != http.StatusOK {
			return nil, statusError("list "+prefix, resp)
		}
		var page listPage
		err = json.UnmarshalRead(resp.Body, &page)
		resp.Body.Close()
		if err != nil {
			return nil, fmt.Errorf("list %s: %w", prefix, err)
		}
		for _, it := range page.Items {
			key := strings.TrimPrefix(it.Name, g.name(""))
			if key <= startAfter {
				continue
			}
			out = append(out, Object{Key: key, Size: it.Size, Created: it.TimeCreated})
		}
		if page.NextPageToken == "" {
			return out, nil
		}
		token = page.NextPageToken
	}
}

// Delete implements Bucket.
func (g *GCS) Delete(ctx context.Context, key string) error {
	resp, err := g.do(ctx, http.MethodDelete, g.objectURL(key), nil, 0)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	switch resp.StatusCode {
	case http.StatusOK, http.StatusNoContent, http.StatusNotFound:
		return nil
	default:
		return statusError("delete "+key, resp)
	}
}

// do sends a request, retrying network errors, 429s, and 5xx responses with
// backoff. A body is retried only if it can seek back to its start.
func (g *GCS) do(ctx context.Context, method, u string, body io.Reader, size int64) (*http.Response, error) {
	seeker, _ := body.(io.Seeker)
	var start int64
	if seeker != nil {
		start, _ = seeker.Seek(0, io.SeekCurrent)
	}
	const attempts = 5
	for attempt := 1; ; attempt++ {
		req, err := http.NewRequestWithContext(ctx, method, u, body)
		if err != nil {
			return nil, err
		}
		if body != nil {
			req.ContentLength = size
			req.Header.Set("Content-Type", "application/octet-stream")
		}
		if g.tokens != nil {
			tok, err := g.tokens.token(ctx)
			if err != nil {
				return nil, err
			}
			req.Header.Set("Authorization", "Bearer "+tok)
		}
		resp, err := g.client.Do(req)
		retryable := err != nil || resp.StatusCode == http.StatusTooManyRequests || resp.StatusCode >= 500
		if !retryable || attempt == attempts || (body != nil && seeker == nil) {
			return resp, err
		}
		if resp != nil {
			io.Copy(io.Discard, resp.Body)
			resp.Body.Close()
		}
		if seeker != nil {
			if _, err := seeker.Seek(start, io.SeekStart); err != nil {
				return nil, err
			}
		}
		backoff := time.Duration(50<<attempt)*time.Millisecond + rand.N(50*time.Millisecond)
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		case <-time.After(backoff):
		}
	}
}

func statusError(op string, resp *http.Response) error {
	b, _ := io.ReadAll(io.LimitReader(resp.Body, 1<<10))
	resp.Body.Close()
	return fmt.Errorf("gcs %s: %s: %s", op, resp.Status, strings.TrimSpace(string(b)))
}

// tokenSource caches an access token from the metadata server.
type tokenSource struct {
	client *http.Client
	static string

	mu      sync.Mutex
	tok     string
	expires time.Time
}

func (t *tokenSource) token(ctx context.Context) (string, error) {
	if t.static != "" {
		return t.static, nil
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.tok != "" && time.Until(t.expires) > time.Minute {
		return t.tok, nil
	}
	host := os.Getenv("GCE_METADATA_HOST")
	if host == "" {
		host = "metadata.google.internal"
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, "http://"+host+"/computeMetadata/v1/instance/service-accounts/default/token", nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("Metadata-Flavor", "Google")
	resp, err := t.client.Do(req)
	if err != nil {
		return "", fmt.Errorf("metadata token: %w (off Google Cloud, set GOOGLE_OAUTH_ACCESS_TOKEN)", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", statusError("metadata token", resp)
	}
	var body struct {
		AccessToken string `json:"access_token"`
		ExpiresIn   int64  `json:"expires_in"`
	}
	if err := json.UnmarshalRead(resp.Body, &body); err != nil {
		return "", fmt.Errorf("metadata token: %w", err)
	}
	if body.AccessToken == "" {
		return "", errors.New("metadata token: empty access_token")
	}
	t.tok = body.AccessToken
	t.expires = time.Now().Add(time.Duration(body.ExpiresIn) * time.Second)
	return t.tok, nil
}
