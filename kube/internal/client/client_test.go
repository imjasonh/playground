package client

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync/atomic"
	"testing"
)

func newTestClient(t *testing.T, h http.HandlerFunc) *Client {
	t.Helper()
	s := httptest.NewServer(h)
	t.Cleanup(s.Close)
	c, err := New(&Config{Host: s.URL}, "kube-test/1")
	if err != nil {
		t.Fatal(err)
	}
	return c
}

func TestPath(t *testing.T) {
	for _, tc := range []struct {
		got, want string
	}{
		{Path("v1", "pods", "", ""), "/api/v1/pods"},
		{Path("v1", "pods", "default", "web"), "/api/v1/namespaces/default/pods/web"},
		{Path("apps/v1", "deployments", "ns", "d", "status"), "/apis/apps/v1/namespaces/ns/deployments/d/status"},
		{Path("example.dev/v1", "websites", "", "w"), "/apis/example.dev/v1/websites/w"},
	} {
		if tc.got != tc.want {
			t.Errorf("got %q, want %q", tc.got, tc.want)
		}
	}
}

func TestErrors(t *testing.T) {
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/notfound":
			w.WriteHeader(404)
			fmt.Fprint(w, `{"kind":"Status","apiVersion":"v1","status":"Failure","message":"pods \"x\" not found","reason":"NotFound","code":404}`)
		case "/conflict":
			w.WriteHeader(409)
			fmt.Fprint(w, `{"kind":"Status","status":"Failure","message":"the object has been modified","reason":"Conflict","code":409}`)
		case "/exists":
			w.WriteHeader(409)
			fmt.Fprint(w, `{"kind":"Status","status":"Failure","message":"already exists","reason":"AlreadyExists","code":409}`)
		default:
			w.WriteHeader(500)
			fmt.Fprint(w, "boom")
		}
	})
	err := c.Get(t.Context(), "/notfound", nil)
	if !IsNotFound(err) || !strings.Contains(err.Error(), `pods "x" not found`) {
		t.Errorf("not found: %v", err)
	}
	if err := c.Get(t.Context(), "/conflict", nil); !IsConflict(err) || IsAlreadyExists(err) {
		t.Errorf("conflict: %v", err)
	}
	if err := c.Get(t.Context(), "/exists", nil); !IsAlreadyExists(err) || IsConflict(err) {
		t.Errorf("already exists: %v", err)
	}
	err = c.Get(t.Context(), "/other", nil)
	var ae *APIError
	if !errors.As(err, &ae) || ae.Code != 500 || ae.Message != "boom" {
		t.Errorf("500: %#v", err)
	}
}

func TestApplyAndDelete(t *testing.T) {
	var gotQuery, gotType, gotBody, gotUA atomic.Value
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		b, _ := io.ReadAll(r.Body)
		gotQuery.Store(r.URL.RawQuery)
		gotType.Store(r.Method + " " + r.Header.Get("Content-Type"))
		gotBody.Store(string(b))
		gotUA.Store(r.UserAgent())
		fmt.Fprint(w, `{"metadata":{"name":"x","resourceVersion":"7"}}`)
	})
	var out struct {
		Metadata struct {
			ResourceVersion string `json:"resourceVersion"`
		} `json:"metadata"`
	}
	obj := map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "x"}}
	if err := c.Apply(t.Context(), "/api/v1/namespaces/d/configmaps/x", "my-ctrl", true, obj, &out); err != nil {
		t.Fatal(err)
	}
	if out.Metadata.ResourceVersion != "7" {
		t.Errorf("decoded %+v", out)
	}
	if q := gotQuery.Load(); q != "fieldManager=my-ctrl&force=true" {
		t.Errorf("query = %q", q)
	}
	if ct := gotType.Load(); ct != "PATCH application/apply-patch+yaml" {
		t.Errorf("content type = %q", ct)
	}
	if ua := gotUA.Load(); ua != "kube-test/1" {
		t.Errorf("User-Agent = %q", ua)
	}
	if err := c.Delete(t.Context(), "/api/v1/namespaces/d/configmaps/x", DeleteOptions{UID: "u-1", Propagation: "Background"}); err != nil {
		t.Fatal(err)
	}
	var del map[string]any
	if err := json.Unmarshal([]byte(gotBody.Load().(string)), &del); err != nil {
		t.Fatal(err)
	}
	if del["propagationPolicy"] != "Background" || del["preconditions"].(map[string]any)["uid"] != "u-1" {
		t.Errorf("delete body = %v", del)
	}
}

type item struct {
	Metadata struct {
		Name string `json:"name"`
	} `json:"metadata"`
}

func collect(names *[]string) func(*json.Decoder) error {
	return func(dec *json.Decoder) error {
		var it item
		if err := dec.Decode(&it); err != nil {
			return err
		}
		*names = append(*names, it.Metadata.Name)
		return nil
	}
}

func TestListStreamsItemsInAnyKeyOrder(t *testing.T) {
	for name, body := range map[string]string{
		"metadata first": `{"kind":"PodList","apiVersion":"v1","metadata":{"resourceVersion":"42"},"items":[{"metadata":{"name":"a"}},{"metadata":{"name":"b"}}]}`,
		"items first":    `{"apiVersion":"example.dev/v1","items":[{"metadata":{"name":"a"}},{"metadata":{"name":"b"}}],"kind":"WebsiteList","metadata":{"resourceVersion":"42"}}`,
	} {
		t.Run(name, func(t *testing.T) {
			c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) { fmt.Fprint(w, body) })
			var names []string
			meta, err := c.List(t.Context(), "/x", nil, "", collect(&names))
			if err != nil {
				t.Fatal(err)
			}
			if meta.ResourceVersion != "42" || strings.Join(names, ",") != "a,b" {
				t.Errorf("meta=%+v names=%v", meta, names)
			}
		})
	}
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprint(w, `{"metadata":{"resourceVersion":"1"},"items":null}`)
	})
	var names []string
	if _, err := c.List(t.Context(), "/x", nil, "", collect(&names)); err != nil || len(names) != 0 {
		t.Errorf("null items: %v %v", names, err)
	}
}

func TestListAllPaginates(t *testing.T) {
	var queries []string
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		queries = append(queries, r.URL.RawQuery)
		switch r.URL.Query().Get("continue") {
		case "":
			fmt.Fprint(w, `{"metadata":{"resourceVersion":"9","continue":"p2"},"items":[{"metadata":{"name":"a"}}]}`)
		case "p2":
			fmt.Fprint(w, `{"metadata":{"resourceVersion":"9"},"items":[{"metadata":{"name":"b"}}]}`)
		}
	})
	var names []string
	rv, err := c.ListAll(t.Context(), "/x", map[string][]string{"labelSelector": {"app=web"}}, "", 1, collect(&names))
	if err != nil {
		t.Fatal(err)
	}
	if rv != "9" || strings.Join(names, ",") != "a,b" {
		t.Errorf("rv=%q names=%v", rv, names)
	}
	if len(queries) != 2 || queries[0] != "labelSelector=app%3Dweb&limit=1" || queries[1] != "continue=p2&labelSelector=app%3Dweb&limit=1" {
		t.Errorf("queries = %q", queries)
	}
}

func TestWatch(t *testing.T) {
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Query().Get("watch") != "1" {
			t.Errorf("watch not set: %s", r.URL.RawQuery)
		}
		fmt.Fprintln(w, `{"type":"ADDED","object":{"metadata":{"name":"a","resourceVersion":"2"}}}`)
		fmt.Fprintln(w, `{"type":"BOOKMARK","object":{"metadata":{"resourceVersion":"3"}}}`)
		fmt.Fprintln(w, `{"type":"ERROR","object":{"kind":"Status","status":"Failure","message":"too old resource version: 1 (3)","reason":"Expired","code":410}}`)
	})
	w, err := c.Watch(t.Context(), "/api/v1/pods", nil, "")
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()
	var types []string
	for {
		e, err := w.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		types = append(types, e.Type)
		if e.Type == Error && !IsGone(e.Err()) {
			t.Errorf("error event: %v", e.Err())
		}
	}
	if strings.Join(types, ",") != "ADDED,BOOKMARK,ERROR" {
		t.Errorf("types = %v", types)
	}
}

func memWatcher(stream string) *Watcher {
	r := strings.NewReader(stream)
	return &Watcher{body: io.NopCloser(r), frames: newFrameReader(r), cancel: func() {}}
}

func TestWatcherNextFrame(t *testing.T) {
	w := memWatcher(`{"type":"ADDED","object":{"metadata":{"name":"a"}}}
{"object":{"metadata":{"name":"b"}},"type":"MODIFIED","extra":[1,2]}
{"type":"ERROR","object":{"kind":"Status","code":410,"reason":"Expired","message":"too old"}}
`)
	var got []string
	for {
		typ, frame, err := w.NextFrame()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		if typ == Error {
			if err := FrameError(frame); !IsGone(err) {
				t.Errorf("error event = %v", err)
			}
			got = append(got, typ)
			continue
		}
		var e struct {
			Object item `json:"object"`
		}
		if err := json.Unmarshal(frame, &e); err != nil {
			t.Fatal(err)
		}
		got = append(got, typ+" "+e.Object.Metadata.Name)
	}
	if want := "ADDED a,MODIFIED b,ERROR"; strings.Join(got, ",") != want {
		t.Errorf("events = %v, want %s", got, want)
	}
}

func BenchmarkWatchDecode(b *testing.B) {
	type pod struct {
		Metadata struct {
			Name   string            `json:"name"`
			Labels map[string]string `json:"labels"`
		} `json:"metadata"`
		Spec struct {
			NodeName string `json:"nodeName"`
		} `json:"spec"`
	}
	event := `{"type":"MODIFIED","object":{"metadata":{"name":"web-1","labels":{"app":"web","tier":"frontend"},"managedFields":[{"manager":"kubelet","fieldsV1":{"f:status":{"f:phase":{},"f:conditions":{}}}}]},"spec":{"nodeName":"node-7","containers":[{"name":"app","image":"nginx"}]},"status":{"phase":"Running"}}}` + "\n"
	stream := strings.Repeat(event, 1000)
	b.Run("envelope-then-object", func(b *testing.B) {
		b.SetBytes(int64(len(stream)))
		for b.Loop() {
			w := memWatcher(stream)
			for {
				e, err := w.Next()
				if err != nil {
					break
				}
				var p pod
				_ = json.Unmarshal(e.Object, &p)
			}
		}
	})
	b.Run("frame-then-typed-event", func(b *testing.B) {
		b.SetBytes(int64(len(stream)))
		for b.Loop() {
			w := memWatcher(stream)
			for {
				_, frame, err := w.NextFrame()
				if err != nil {
					break
				}
				var e struct {
					Object pod `json:"object"`
				}
				_ = json.Unmarshal(frame, &e)
			}
		}
	})
}

func TestDiscoveryRefetchesOnMiss(t *testing.T) {
	var calls atomic.Int32
	c := newTestClient(t, func(w http.ResponseWriter, r *http.Request) {
		n := calls.Add(1)
		switch r.URL.Path {
		case "/apis/example.dev/v1":
			if n == 1 {
				fmt.Fprint(w, `{"resources":[]}`)
				return
			}
			fmt.Fprint(w, `{"resources":[{"name":"websites","singularName":"website","namespaced":true,"kind":"Website","verbs":["get","list"]},{"name":"websites/status","namespaced":true,"kind":"Website"}]}`)
		case "/api/v1":
			fmt.Fprint(w, `{"resources":[{"name":"namespaces","namespaced":false,"kind":"Namespace"}]}`)
		default:
			http.NotFound(w, r)
		}
	})
	var nk *NoKindError
	if _, err := c.Resource(t.Context(), "example.dev/v1", "Website"); !errors.As(err, &nk) || calls.Load() != 1 {
		t.Errorf("Resource before Website is served = %v with %d calls, want a NoKindError after one call", err, calls.Load())
	}
	r, err := c.Resource(t.Context(), "example.dev/v1", "Website")
	if err != nil {
		t.Fatal(err)
	}
	if r.Name != "websites" || !r.Namespaced || calls.Load() != 2 {
		t.Errorf("resource = %+v after %d calls, want websites after one refetch", r, calls.Load())
	}
	before := calls.Load()
	if _, err := c.Resource(t.Context(), "example.dev/v1", "Website"); err != nil || calls.Load() != before {
		t.Errorf("cached lookup made %d calls, err %v", calls.Load()-before, err)
	}
	if r, err := c.Resource(t.Context(), "v1", "Namespace"); err != nil || r.Namespaced {
		t.Errorf("namespace: %+v %v", r, err)
	}
	before = calls.Load()
	if _, err := c.Resource(t.Context(), "nope.dev/v1", "Thing"); !errors.As(err, &nk) || calls.Load() != before+1 {
		t.Errorf("unknown group: %v with %d calls, want a NoKindError after one call", err, calls.Load()-before)
	}

	before = calls.Load()
	if ok, err := c.Serves(t.Context(), "example.dev/v1", "websites/status"); !ok || err != nil || calls.Load() != before {
		t.Errorf("Serves(websites/status) = %v, %v with %d calls, want true from the cache", ok, err, calls.Load()-before)
	}
	if ok, err := c.Serves(t.Context(), "v1", "namespaces/status"); ok || err != nil || calls.Load() != before+1 {
		t.Errorf("Serves(namespaces/status) = %v, %v with %d calls, want false after one refetch", ok, err, calls.Load()-before)
	}
	before = calls.Load()
	if ok, err := c.Serves(t.Context(), "other.dev/v1", "things"); ok || err != nil || calls.Load() != before+1 {
		t.Errorf("Serves(things) in an unknown group = %v, %v with %d calls, want false after one call", ok, err, calls.Load()-before)
	}
	c.Forget("example.dev/v1")
	before = calls.Load()
	if ok, err := c.Serves(t.Context(), "example.dev/v1", "websites/status"); !ok || err != nil || calls.Load() != before+1 {
		t.Errorf("Serves(websites/status) after Forget = %v, %v with %d calls, want true after one call", ok, err, calls.Load()-before)
	}
}
