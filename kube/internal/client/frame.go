package client

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
)

// frameReader splits a stream of JSON objects, such as a watch response,
// into one byte slice per object without decoding them. It only tracks
// nesting, strings, and escapes, so it's much cheaper than a JSON decoder;
// callers can then decode frames concurrently.
type frameReader struct {
	r *bufio.Reader
}

func newFrameReader(r io.Reader) *frameReader {
	return &frameReader{r: bufio.NewReaderSize(r, 64<<10)}
}

// next returns the next object. The slice is newly allocated, so callers
// may keep it. At the end of the stream it returns io.EOF.
func (f *frameReader) next() ([]byte, error) {
	for {
		c, err := f.r.ReadByte()
		if err != nil {
			return nil, err
		}
		if c == ' ' || c == '\n' || c == '\r' || c == '\t' {
			continue
		}
		if c != '{' {
			return nil, fmt.Errorf("watch stream: expected '{', got %q", c)
		}
		break
	}
	frame := []byte{'{'}
	depth, inString, escaped := 1, false, false
	for {
		chunk, err := f.r.Peek(max(f.r.Buffered(), 1))
		if err != nil && len(chunk) == 0 {
			if errors.Is(err, io.EOF) {
				return nil, io.ErrUnexpectedEOF
			}
			return nil, err
		}
		end := -1
	scan:
		for i, c := range chunk {
			switch {
			case escaped:
				escaped = false
			case inString:
				switch c {
				case '\\':
					escaped = true
				case '"':
					inString = false
				}
			case c == '"':
				inString = true
			case c == '{' || c == '[':
				depth++
			case c == '}' || c == ']':
				depth--
				if depth == 0 {
					end = i + 1
					break scan
				}
			}
		}
		if end >= 0 {
			frame = append(frame, chunk[:end]...)
			_, _ = f.r.Discard(end)
			return frame, nil
		}
		frame = append(frame, chunk...)
		_, _ = f.r.Discard(len(chunk))
	}
}

var typePrefix = []byte(`{"type":"`)

// eventType returns the type of a watch event frame by reading its prefix,
// which the API server always writes first. It returns "" when the frame
// doesn't start that way, and the caller must decode the type instead.
func eventType(frame []byte) string {
	rest, ok := bytes.CutPrefix(frame, typePrefix)
	if !ok {
		return ""
	}
	i := bytes.IndexByte(rest, '"')
	if i < 0 || bytes.IndexByte(rest[:i], '\\') >= 0 {
		return ""
	}
	return string(rest[:i])
}
