// Package gocache shares Go build outputs between check-gotest's test Pods
// through a go-cache server.
//
// Prog is a GOCACHEPROG program: the go command starts it and asks it for
// build outputs by action ID. Prog keeps outputs in a local directory, and
// asks a repository's build cache on the go-cache server for those that the
// directory doesn't have. It never writes to the server. Upload sends the
// outputs that the go command built while Prog shared them to the server
// later, so a Pod can upload them from a container that never reads the
// branch's files. Build decides which outputs a Pod can share.
package gocache

import (
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// OutputIDHeader is the HTTP header that holds a build output's ID, in hex,
// when go-cache sends or receives the output.
const OutputIDHeader = "Go-Output-Id"

// MaxOutputSize is the size of the largest build output that go-cache
// stores.
const MaxOutputSize = 256 << 20

const audiencePrefix = "git-k8s.imjasonh.com/go-cache/"

// Path is the URL path of a repository's build cache on a go-cache server.
func Path(namespace, repository string) string {
	return "/cache/" + namespace + "/" + repository
}

// ReadAudience is the audience of the service account tokens that read a
// repository's build cache.
func ReadAudience(namespace, repository string) string {
	return audiencePrefix + "read/" + namespace + "/" + repository
}

// WriteAudience is the audience of the service account tokens that write a
// repository's build cache.
func WriteAudience(namespace, repository string) string {
	return audiencePrefix + "write/" + namespace + "/" + repository
}

// IsID reports whether s is an action ID or output ID in hex.
func IsID(s string) bool {
	if len(s) != 2*sha256.Size {
		return false
	}
	for _, c := range s {
		if (c < '0' || c > '9') && (c < 'a' || c > 'f') {
			return false
		}
	}
	return true
}

// request and response are the messages of the GOCACHEPROG protocol, which
// cmd/go/internal/cacheprog defines.
type request struct {
	ID       int64
	Command  string
	ActionID []byte `json:",omitempty"`
	OutputID []byte `json:",omitempty"`
	BodySize int64  `json:",omitempty"`
}

type response struct {
	ID            int64
	Err           string     `json:",omitempty"`
	KnownCommands []string   `json:",omitempty"`
	Miss          bool       `json:",omitempty"`
	OutputID      []byte     `json:",omitempty"`
	Size          int64      `json:",omitempty"`
	Time          *time.Time `json:",omitempty"`
	DiskPath      string     `json:",omitempty"`
}

// Prog is a GOCACHEPROG program. It stores the outputs in Dir:
//
//	a/ACTION    the output ID and size of the output for an action ID
//	o/OUTPUT    an output, by output ID
//	p/ACTION    present when the go command built the output for ACTION
//	            while Share was set
type Prog struct {
	// Dir holds the outputs.
	Dir string
	// Remote, when set, is the URL of a repository's build cache on a
	// go-cache server, which Prog reads the outputs that Dir lacks from.
	Remote string
	// TokenFile holds the service account token that reads Remote.
	TokenFile string
	// Share makes Prog record the outputs that the go command builds, for
	// Upload to send.
	Share bool
	// Client makes the requests to Remote. It defaults to a client with a
	// timeout.
	Client *http.Client
	// Log, when set, gets a message when a request to Remote fails. Prog
	// stops using Remote after that, so a broken server can't slow every
	// build step down.
	Log io.Writer

	failed atomic.Bool
}

// Run answers the go command's requests from in, writing responses to out,
// until the go command sends close or closes in.
func (p *Prog) Run(ctx context.Context, in io.Reader, out io.Writer) error {
	dir, err := filepath.Abs(p.Dir)
	if err != nil {
		return err
	}
	p.Dir = dir
	for _, sub := range []string{"a", "o", "p", "tmp"} {
		if err := os.MkdirAll(filepath.Join(dir, sub), 0o755); err != nil {
			return err
		}
	}
	var mu sync.Mutex
	enc := json.NewEncoder(out)
	respond := func(r *response) {
		mu.Lock()
		defer mu.Unlock()
		// If the go command stops reading, it closes in too, which ends Run.
		_ = enc.Encode(r)
	}
	respond(&response{KnownCommands: []string{"get", "put", "close"}})
	dec := json.NewDecoder(bufio.NewReader(in))
	var wg sync.WaitGroup
	defer wg.Wait()
	for {
		var req request
		if err := dec.Decode(&req); err != nil {
			if errors.Is(err, io.EOF) {
				return nil
			}
			return err
		}
		var body []byte
		if req.Command == "put" && req.BodySize > 0 {
			if err := dec.Decode(&body); err != nil {
				return fmt.Errorf("reading the body of put %d: %w", req.ID, err)
			}
		}
		if req.Command == "close" {
			wg.Wait()
			respond(&response{ID: req.ID})
			return nil
		}
		wg.Go(func() {
			var res *response
			switch req.Command {
			case "get":
				res = p.get(ctx, req.ActionID)
			case "put":
				res = p.put(&req, body)
			default:
				res = &response{Err: fmt.Sprintf("unknown command %q", req.Command)}
			}
			res.ID = req.ID
			respond(res)
		})
	}
}

func (p *Prog) get(ctx context.Context, action []byte) *response {
	if len(action) == 0 {
		return &response{Err: "get needs an action ID"}
	}
	id := hex.EncodeToString(action)
	if res := p.lookup(id); res != nil {
		return res
	}
	if p.Remote == "" || p.failed.Load() {
		return &response{Miss: true}
	}
	if err := p.fetch(ctx, id); err != nil {
		if !errors.Is(err, errNotFound) && p.failed.CompareAndSwap(false, true) && p.Log != nil {
			fmt.Fprintf(p.Log, "go-cache: %v; building without it\n", err)
		}
		return &response{Miss: true}
	}
	if res := p.lookup(id); res != nil {
		return res
	}
	return &response{Miss: true}
}

func (p *Prog) put(req *request, body []byte) *response {
	if len(req.ActionID) == 0 || len(req.OutputID) != sha256.Size || int64(len(body)) != req.BodySize {
		return &response{Err: "put needs an action ID, an output ID, and a body of BodySize bytes"}
	}
	id, output := hex.EncodeToString(req.ActionID), hex.EncodeToString(req.OutputID)
	if err := p.writeOutput(output, bytes.NewReader(body), req.BodySize); err != nil {
		return &response{Err: err.Error()}
	}
	if err := p.writeIndex(id, output, req.BodySize); err != nil {
		return &response{Err: err.Error()}
	}
	if p.Share {
		if err := os.WriteFile(filepath.Join(p.Dir, "p", id), nil, 0o644); err != nil {
			return &response{Err: err.Error()}
		}
	}
	return &response{DiskPath: filepath.Join(p.Dir, "o", output)}
}

// lookup returns a hit for action ID id from Dir, or nil.
func (p *Prog) lookup(id string) *response {
	b, err := os.ReadFile(filepath.Join(p.Dir, "a", id))
	if err != nil {
		return nil
	}
	output, size, err := parseIndex(b)
	if err != nil {
		return nil
	}
	path := filepath.Join(p.Dir, "o", output)
	fi, err := os.Stat(path)
	if err != nil || fi.Size() != size {
		return nil
	}
	sum, _ := hex.DecodeString(output)
	t := fi.ModTime()
	return &response{OutputID: sum, Size: size, Time: &t, DiskPath: path}
}

var errNotFound = errors.New("not found")

// fetch copies the output for action ID id from Remote to Dir.
func (p *Prog) fetch(ctx context.Context, id string) error {
	token, err := os.ReadFile(p.TokenFile)
	if err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, p.Remote+"/"+id, nil)
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+strings.TrimSpace(string(token)))
	client := p.Client
	if client == nil {
		client = defaultClient
	}
	resp, err := client.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	switch resp.StatusCode {
	case http.StatusOK:
	case http.StatusNotFound:
		return errNotFound
	default:
		return statusError(resp)
	}
	output := resp.Header.Get(OutputIDHeader)
	if !IsID(output) {
		return fmt.Errorf("GET %s: %s %q isn't an output ID", req.URL, OutputIDHeader, output)
	}
	if resp.ContentLength < 0 || resp.ContentLength > MaxOutputSize {
		return fmt.Errorf("GET %s: unexpected Content-Length %d", req.URL, resp.ContentLength)
	}
	if err := p.writeOutput(output, resp.Body, resp.ContentLength); err != nil {
		return fmt.Errorf("GET %s: %w", req.URL, err)
	}
	return p.writeIndex(id, output, resp.ContentLength)
}

var defaultClient = &http.Client{Timeout: 2 * time.Minute}

// writeOutput stores size bytes from r as output ID output, after checking
// that they're the output with that ID.
func (p *Prog) writeOutput(output string, r io.Reader, size int64) error {
	path := filepath.Join(p.Dir, "o", output)
	if fi, err := os.Stat(path); err == nil && fi.Size() == size {
		return nil
	}
	f, err := os.CreateTemp(filepath.Join(p.Dir, "tmp"), "o-")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	h := sha256.New()
	n, err := io.Copy(io.MultiWriter(f, h), io.LimitReader(r, size+1))
	if cerr := f.Close(); err == nil {
		err = cerr
	}
	switch {
	case err != nil:
		return err
	case n != size:
		return fmt.Errorf("output %s has %d bytes, want %d", output, n, size)
	case hex.EncodeToString(h.Sum(nil)) != output:
		return fmt.Errorf("output %s doesn't match its ID", output)
	}
	return os.Rename(f.Name(), path)
}

func (p *Prog) writeIndex(id, output string, size int64) error {
	f, err := os.CreateTemp(filepath.Join(p.Dir, "tmp"), "a-")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	_, err = fmt.Fprintf(f, "%s %d\n", output, size)
	if cerr := f.Close(); err == nil {
		err = cerr
	}
	if err != nil {
		return err
	}
	return os.Rename(f.Name(), filepath.Join(p.Dir, "a", id))
}

func parseIndex(b []byte) (output string, size int64, err error) {
	f := strings.Fields(string(b))
	if len(f) == 2 && IsID(f[0]) {
		size, err = strconv.ParseInt(f[1], 10, 64)
		if err == nil && size >= 0 {
			return f[0], size, nil
		}
	}
	return "", 0, fmt.Errorf("bad index entry %q", b)
}

func statusError(resp *http.Response) error {
	msg, _ := io.ReadAll(io.LimitReader(resp.Body, 512))
	return fmt.Errorf("%s %s: %s: %s", resp.Request.Method, resp.Request.URL, resp.Status, bytes.TrimSpace(msg))
}

// Upload sends the outputs that the go command built in a Prog's dir while
// Prog shared them to remote, a repository's build cache on a go-cache
// server, with the service account token in tokenFile. It returns how many
// outputs the server stored, and how many it already had. Upload stops
// sending outputs once the server answers 503 Service Unavailable, as
// go-cache does when its store can't take writes.
func Upload(ctx context.Context, client *http.Client, dir, remote, tokenFile string) (stored, had int, err error) {
	root, err := os.OpenRoot(dir)
	if err != nil {
		return 0, 0, err
	}
	defer root.Close()
	token, err := os.ReadFile(tokenFile)
	if err != nil {
		return 0, 0, err
	}
	built, err := fs.ReadDir(root.FS(), "p")
	if errors.Is(err, fs.ErrNotExist) {
		return 0, 0, nil
	} else if err != nil {
		return 0, 0, err
	}
	var (
		mu      sync.Mutex
		failed  int
		first   error
		stopped atomic.Bool
		wg      sync.WaitGroup
		ids     = make(chan string)
	)
	for range 8 {
		wg.Go(func() {
			for id := range ids {
				if stopped.Load() {
					continue
				}
				status, err := upload(ctx, client, root, remote, strings.TrimSpace(string(token)), id)
				if status == http.StatusServiceUnavailable {
					// The rest would fail too, each after waiting up to 30
					// seconds for a write slot.
					stopped.Store(true)
				}
				mu.Lock()
				switch {
				case err != nil:
					failed++
					if first == nil {
						first = err
					}
				case status == http.StatusCreated:
					stored++
				default:
					had++
				}
				mu.Unlock()
			}
		})
	}
	total := 0
	for _, e := range built {
		if IsID(e.Name()) {
			total++
			if !stopped.Load() {
				ids <- e.Name()
			}
		}
	}
	close(ids)
	wg.Wait()
	if failed > 0 {
		sent := failed + stored + had
		err := fmt.Errorf("%d of %d uploads failed, the first with: %w", failed, sent, first)
		if sent < total {
			err = fmt.Errorf("%w; %d more weren't sent", err, total-sent)
		}
		return stored, had, err
	}
	return stored, had, nil
}

// upload sends the output for id, and returns the server's status code if
// it answered.
func upload(ctx context.Context, client *http.Client, root *os.Root, remote, token, id string) (int, error) {
	b, err := root.ReadFile("a/" + id)
	if err != nil {
		return 0, err
	}
	output, size, err := parseIndex(b)
	if err != nil {
		return 0, err
	}
	f, err := root.Open("o/" + output)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	if fi, err := f.Stat(); err != nil || !fi.Mode().IsRegular() || fi.Size() != size {
		return 0, fmt.Errorf("output %s isn't a file of %d bytes", output, size)
	}
	var body io.Reader = http.NoBody
	if size > 0 {
		body = f
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPut, remote+"/"+id, body)
	if err != nil {
		return 0, err
	}
	req.ContentLength = size
	req.Header.Set(OutputIDHeader, output)
	req.Header.Set("Authorization", "Bearer "+token)
	req.Header.Set("Content-Type", "application/octet-stream")
	if size > 0 {
		// go-cache answers without reading the body when it has the output.
		req.Header.Set("Expect", "100-continue")
	}
	if client == nil {
		client = defaultClient
	}
	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusCreated && resp.StatusCode != http.StatusOK {
		return resp.StatusCode, statusError(resp)
	}
	return resp.StatusCode, nil
}
