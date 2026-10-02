package client

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/url"
	"strconv"
)

// Watch event types.
const (
	Added    = "ADDED"
	Modified = "MODIFIED"
	Deleted  = "DELETED"
	Bookmark = "BOOKMARK"
	Error    = "ERROR"
)

// InitialEventsEndAnnotation marks the bookmark that ends the initial state
// of a streaming list (a watch with sendInitialEvents=true).
const InitialEventsEndAnnotation = "k8s.io/initial-events-end"

// Event is one watch event. Object holds the raw JSON so callers can decode
// it into their own types.
type Event struct {
	Type   string          `json:"type"`
	Object json.RawMessage `json:"object"`
}

// Err converts an ERROR event into an *APIError.
func (e Event) Err() error {
	var s status
	if err := json.Unmarshal(e.Object, &s); err != nil {
		return fmt.Errorf("watch error event: %s", e.Object)
	}
	return &APIError{Code: s.Code, Reason: s.Reason, Message: s.Message}
}

// Watcher reads events from one watch stream.
type Watcher struct {
	body   io.ReadCloser
	frames *frameReader
	cancel context.CancelFunc
}

// Watch opens a watch stream on the collection at path.
func (c *Client) Watch(ctx context.Context, path string, query url.Values, accept string) (*Watcher, error) {
	q := maps.Clone(query)
	if q == nil {
		q = url.Values{}
	}
	q.Set("watch", "1")
	ctx, cancel := context.WithCancel(ctx)
	resp, err := c.Do(ctx, Request{Method: http.MethodGet, Path: path, Query: q, Accept: accept, Stream: true})
	if err != nil {
		cancel()
		return nil, err
	}
	return &Watcher{body: resp.Body, frames: newFrameReader(resp.Body), cancel: cancel}, nil
}

// Next blocks until the next event. It returns io.EOF when the server ends
// the stream, which it does after the request's timeoutSeconds.
func (w *Watcher) Next() (Event, error) {
	frame, err := w.frames.next()
	if err != nil {
		return Event{}, err
	}
	var e Event
	return e, json.Unmarshal(frame, &e)
}

// NextFrame blocks until the next event and returns its type and its raw
// JSON, undecoded, so the caller can decode the object straight into its
// final type, on another goroutine if it likes. It returns io.EOF when the
// server ends the stream.
func (w *Watcher) NextFrame() (typ string, frame []byte, err error) {
	if frame, err = w.frames.next(); err != nil {
		return "", nil, err
	}
	if typ = eventType(frame); typ == "" {
		var e struct {
			Type string `json:"type"`
		}
		if err := json.Unmarshal(frame, &e); err != nil {
			return "", nil, err
		}
		typ = e.Type
	}
	return typ, frame, nil
}

// FrameError decodes the Status in an ERROR event frame into an *APIError.
func FrameError(frame []byte) error {
	var e struct {
		Object status `json:"object"`
	}
	if err := json.Unmarshal(frame, &e); err != nil {
		return fmt.Errorf("decoding watch error event: %w", err)
	}
	return &APIError{Code: e.Object.Code, Reason: e.Object.Reason, Message: e.Object.Message}
}

// Close stops the watch.
func (w *Watcher) Close() error {
	w.cancel()
	return w.body.Close()
}

// ListMeta is the metadata of a list response.
type ListMeta struct {
	ResourceVersion string `json:"resourceVersion"`
	Continue        string `json:"continue"`
}

// List sends one list request and calls item once for each element of the
// response's items array, with dec positioned at that element. item must
// consume exactly one JSON value, usually with dec.Decode. List never holds
// the whole response in memory.
func (c *Client) List(ctx context.Context, path string, query url.Values, accept string, item func(dec *json.Decoder) error) (ListMeta, error) {
	var meta ListMeta
	resp, err := c.Do(ctx, Request{Method: http.MethodGet, Path: path, Query: query, Accept: accept, Stream: true})
	if err != nil {
		return meta, err
	}
	defer resp.Body.Close()
	dec := json.NewDecoder(resp.Body)
	if err := expectDelim(dec, '{'); err != nil {
		return meta, err
	}
	for dec.More() {
		tok, err := dec.Token()
		if err != nil {
			return meta, err
		}
		switch tok {
		case "metadata":
			if err := dec.Decode(&meta); err != nil {
				return meta, fmt.Errorf("decoding list metadata: %w", err)
			}
		case "items":
			if !dec.More() {
				continue
			}
			tok, err := dec.Token()
			if err != nil {
				return meta, err
			}
			if tok == nil {
				continue
			}
			if d, ok := tok.(json.Delim); !ok || d != '[' {
				return meta, fmt.Errorf("list items: expected '[', got %v", tok)
			}
			for dec.More() {
				if err := item(dec); err != nil {
					return meta, err
				}
			}
			if err := expectDelim(dec, ']'); err != nil {
				return meta, err
			}
		default:
			var skip json.RawMessage
			if err := dec.Decode(&skip); err != nil {
				return meta, err
			}
		}
	}
	return meta, expectDelim(dec, '}')
}

// ListAll lists every page of the collection at path, pageSize items at a
// time, and returns the list's resource version. A pageSize of zero asks for
// everything in one response.
func (c *Client) ListAll(ctx context.Context, path string, query url.Values, accept string, pageSize int, item func(dec *json.Decoder) error) (string, error) {
	q := maps.Clone(query)
	if q == nil {
		q = url.Values{}
	}
	if pageSize > 0 {
		q.Set("limit", strconv.Itoa(pageSize))
	}
	for {
		meta, err := c.List(ctx, path, q, accept, item)
		if err != nil {
			return "", err
		}
		if meta.Continue == "" {
			return meta.ResourceVersion, nil
		}
		q.Set("continue", meta.Continue)
		q.Del("resourceVersion")
		q.Del("resourceVersionMatch")
	}
}

func expectDelim(dec *json.Decoder, want json.Delim) error {
	tok, err := dec.Token()
	if err != nil {
		return err
	}
	if d, ok := tok.(json.Delim); !ok || d != want {
		return fmt.Errorf("expected %q, got %v", want, tok)
	}
	return nil
}
