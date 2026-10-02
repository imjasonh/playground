package client

import (
	"bufio"
	"bytes"
	"context"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/url"
	"strconv"
	"strings"

	"github.com/imjasonh/playground/kube/internal/protobuf"
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
	frames *frameReader  // JSON events
	pb     *bufio.Reader // protobuf events, each after its length
	cancel context.CancelFunc
	// Proto reports that the server sent protobuf, so frames from NextFrame
	// are protobuf objects for protobuf.Unwrap instead of JSON events.
	Proto bool
}

// maxFrame bounds one protobuf watch event. Objects are at most a few
// megabytes, the limit of the API server's storage.
const maxFrame = 64 << 20

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
	w := &Watcher{body: resp.Body, cancel: cancel}
	if isProtobuf(resp) {
		w.Proto, w.pb = true, bufio.NewReaderSize(resp.Body, 64<<10)
	} else {
		w.frames = newFrameReader(resp.Body)
	}
	return w, nil
}

func isProtobuf(resp *http.Response) bool {
	return strings.HasPrefix(resp.Header.Get("Content-Type"), "application/vnd.kubernetes.protobuf")
}

// Next blocks until the next event of a JSON watch. It returns io.EOF when
// the server ends the stream, which it does after the request's
// timeoutSeconds.
func (w *Watcher) Next() (Event, error) {
	if w.Proto {
		return Event{}, errors.New("watch: Next reads JSON watches; this one is protobuf")
	}
	frame, err := w.frames.next()
	if err != nil {
		return Event{}, err
	}
	var e Event
	return e, json.Unmarshal(frame, &e)
}

// NextFrame blocks until the next event and returns its type and its
// object, undecoded, so the caller can decode the object straight into its
// final type. For a JSON watch, frame is the whole JSON event; for a
// protobuf watch, it's the encoded object. It returns io.EOF when the
// server ends the stream.
func (w *Watcher) NextFrame() (typ string, frame []byte, err error) {
	if w.Proto {
		var n [4]byte
		if _, err := io.ReadFull(w.pb, n[:]); err != nil {
			return "", nil, err
		}
		size := binary.BigEndian.Uint32(n[:])
		if size > maxFrame {
			return "", nil, fmt.Errorf("watch: a %d-byte event is too large", size)
		}
		event := make([]byte, size)
		if _, err := io.ReadFull(w.pb, event); err != nil {
			if errors.Is(err, io.EOF) {
				err = io.ErrUnexpectedEOF
			}
			return "", nil, err
		}
		return protobuf.Event(event)
	}
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
	if bytes.HasPrefix(frame, protobuf.Magic) {
		_, _, raw, err := protobuf.Unwrap(frame)
		if err != nil {
			return fmt.Errorf("decoding watch error event: %w", err)
		}
		code, reason, message, err := protobuf.Status(raw)
		if err != nil {
			return fmt.Errorf("decoding watch error event: %w", err)
		}
		return &APIError{Code: int(code), Reason: reason, Message: message}
	}
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

// Items receives the items of list responses, whichever encoding the server
// chose.
type Items struct {
	// JSON is called for each item of a JSON list, with dec positioned at
	// it. It must consume exactly one JSON value, usually with dec.Decode.
	JSON func(dec *json.Decoder) error
	// Proto is called with each encoded item of a protobuf list.
	Proto func(raw []byte) error
}

// List sends one list request and calls item once for each element of the
// response's items array, with dec positioned at that element. item must
// consume exactly one JSON value, usually with dec.Decode. List never holds
// the whole response in memory.
func (c *Client) List(ctx context.Context, path string, query url.Values, accept string, item func(dec *json.Decoder) error) (ListMeta, error) {
	return c.listPage(ctx, path, query, accept, Items{JSON: item})
}

func (c *Client) listPage(ctx context.Context, path string, query url.Values, accept string, items Items) (ListMeta, error) {
	var meta ListMeta
	resp, err := c.Do(ctx, Request{Method: http.MethodGet, Path: path, Query: query, Accept: accept, Stream: true})
	if err != nil {
		return meta, err
	}
	defer resp.Body.Close()
	if isProtobuf(resp) {
		if items.Proto == nil {
			return meta, errors.New("list: the server sent protobuf, which this caller can't read")
		}
		b, err := io.ReadAll(resp.Body)
		if err != nil {
			return meta, err
		}
		_, _, raw, err := protobuf.Unwrap(b)
		if err != nil {
			return meta, err
		}
		meta.ResourceVersion, meta.Continue, err = protobuf.List(raw, items.Proto)
		return meta, err
	}
	if items.JSON == nil {
		return meta, errors.New("list: the server sent JSON, which this caller can't read")
	}
	item := items.JSON
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
	return c.ListItems(ctx, path, query, accept, pageSize, Items{JSON: item})
}

// ListItems is ListAll for callers that read protobuf lists too.
func (c *Client) ListItems(ctx context.Context, path string, query url.Values, accept string, pageSize int, items Items) (string, error) {
	q := maps.Clone(query)
	if q == nil {
		q = url.Values{}
	}
	if pageSize > 0 {
		q.Set("limit", strconv.Itoa(pageSize))
	}
	for {
		meta, err := c.listPage(ctx, path, q, accept, items)
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
