package client

import (
	"encoding/json"
	"io"
	"strings"
	"testing"
	"testing/iotest"
)

func TestFrameReader(t *testing.T) {
	frames := []string{
		`{"type":"ADDED","object":{"metadata":{"name":"a"},"data":{"k":"brace } in a string","q":"escaped \" quote","b":"backslash \\"}}}`,
		`{"type":"MODIFIED","object":{"list":[{"x":[1,2,{"y":"]"}]}],"empty":{}}}`,
		`{"object":{},"type":"BOOKMARK"}`,
	}
	stream := "  " + strings.Join(frames, "\n") + "\n\t\r\n"
	for name, r := range map[string]io.Reader{
		"whole":    strings.NewReader(stream),
		"one byte": iotest.OneByteReader(strings.NewReader(stream)),
	} {
		t.Run(name, func(t *testing.T) {
			fr := newFrameReader(r)
			for i, want := range frames {
				got, err := fr.next()
				if err != nil {
					t.Fatalf("frame %d: %v", i, err)
				}
				if string(got) != want {
					t.Errorf("frame %d = %s, want %s", i, got, want)
				}
				if !json.Valid(got) {
					t.Errorf("frame %d isn't valid JSON", i)
				}
			}
			if _, err := fr.next(); err != io.EOF {
				t.Errorf("after the last frame, err = %v, want io.EOF", err)
			}
		})
	}
	if _, err := newFrameReader(strings.NewReader(`{"type":"ADDED","object":{`)).next(); err != io.ErrUnexpectedEOF {
		t.Errorf("truncated frame: err = %v", err)
	}
	if _, err := newFrameReader(strings.NewReader(`[1]`)).next(); err == nil {
		t.Error("non-object: want error")
	}
}

func TestEventType(t *testing.T) {
	for frame, want := range map[string]string{
		`{"type":"ADDED","object":{}}`:    "ADDED",
		`{"type":"BOOKMARK","object":{}}`: "BOOKMARK",
		`{"object":{},"type":"ADDED"}`:    "",
		`{ "type": "ADDED" }`:             "",
		`{"type":"AD\"DED"}`:              "",
	} {
		if got := eventType([]byte(frame)); got != want {
			t.Errorf("eventType(%s) = %q, want %q", frame, got, want)
		}
	}
}

func BenchmarkFrameReader(b *testing.B) {
	event := `{"type":"MODIFIED","object":{"metadata":{"name":"web-1","labels":{"app":"web","tier":"frontend"},"managedFields":[{"manager":"kubelet","fieldsV1":{"f:status":{"f:phase":{},"f:conditions":{}}}}]},"spec":{"nodeName":"node-7","containers":[{"name":"app","image":"nginx"}]},"status":{"phase":"Running"}}}` + "\n"
	stream := strings.Repeat(event, 1000)
	b.SetBytes(int64(len(stream)))
	for b.Loop() {
		fr := newFrameReader(strings.NewReader(stream))
		for {
			if _, err := fr.next(); err != nil {
				break
			}
		}
	}
}
