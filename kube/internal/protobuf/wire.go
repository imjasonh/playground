package protobuf

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
)

// Wire types.
const (
	wireVarint  = 0
	wireFixed64 = 1
	wireBytes   = 2
	wireFixed32 = 5
)

var errTruncated = errors.New("protobuf: truncated message")

// Magic starts every protobuf-encoded Kubernetes object, before its
// runtime.Unknown envelope.
var Magic = []byte("k8s\x00")

func varint(b []byte) (uint64, int) {
	var v uint64
	for i := 0; i < len(b) && i < 10; i++ {
		c := b[i]
		v |= uint64(c&0x7f) << (7 * i)
		if c < 0x80 {
			return v, i + 1
		}
	}
	return 0, 0
}

// field is one decoded field: its number, wire type, and value, which is in
// v for varint and fixed wire types and in data for the bytes wire type.
type field struct {
	num  int
	wt   int
	v    uint64
	data []byte
}

// next decodes the field at the start of b and returns it with the number
// of bytes it took.
func next(b []byte) (field, int, error) {
	tag, n := varint(b)
	if n == 0 {
		return field{}, 0, errTruncated
	}
	f := field{num: int(tag >> 3), wt: int(tag & 7)}
	if f.num <= 0 {
		return field{}, 0, fmt.Errorf("protobuf: bad field number %d", f.num)
	}
	b = b[n:]
	switch f.wt {
	case wireVarint:
		v, m := varint(b)
		if m == 0 {
			return field{}, 0, errTruncated
		}
		f.v = v
		return f, n + m, nil
	case wireFixed64:
		if len(b) < 8 {
			return field{}, 0, errTruncated
		}
		f.v = binary.LittleEndian.Uint64(b)
		return f, n + 8, nil
	case wireFixed32:
		if len(b) < 4 {
			return field{}, 0, errTruncated
		}
		f.v = uint64(binary.LittleEndian.Uint32(b))
		return f, n + 4, nil
	case wireBytes:
		l, m := varint(b)
		if m == 0 || l > uint64(len(b)-m) {
			return field{}, 0, errTruncated
		}
		f.data = b[m : m+int(l)]
		return f, n + m + int(l), nil
	default:
		return field{}, 0, fmt.Errorf("protobuf: unsupported wire type %d", f.wt)
	}
}

// each calls fn for every field in b, in order.
func each(b []byte, fn func(field) error) error {
	for len(b) > 0 {
		f, n, err := next(b)
		if err != nil {
			return err
		}
		if err := fn(f); err != nil {
			return err
		}
		b = b[n:]
	}
	return nil
}

// Unwrap returns the type and the encoded object of a protobuf-encoded
// Kubernetes object: Magic followed by a runtime.Unknown.
func Unwrap(b []byte) (apiVersion, kind string, raw []byte, err error) {
	rest, ok := bytes.CutPrefix(b, Magic)
	if !ok {
		return "", "", nil, errors.New("protobuf: missing the k8s magic prefix")
	}
	err = each(rest, func(f field) error {
		switch {
		case f.num == 1 && f.wt == wireBytes:
			return each(f.data, func(t field) error {
				switch {
				case t.num == 1 && t.wt == wireBytes:
					apiVersion = string(t.data)
				case t.num == 2 && t.wt == wireBytes:
					kind = string(t.data)
				}
				return nil
			})
		case f.num == 2 && f.wt == wireBytes:
			raw = f.data
		case f.num == 3 && f.wt == wireBytes && len(f.data) > 0:
			return fmt.Errorf("protobuf: content encoding %q isn't supported", f.data)
		}
		return nil
	})
	return apiVersion, kind, raw, err
}

// Event decodes a watch event frame, a metav1.WatchEvent, into its type and
// its object, still wrapped as Unwrap expects.
func Event(frame []byte) (typ string, object []byte, err error) {
	err = each(frame, func(f field) error {
		switch {
		case f.num == 1 && f.wt == wireBytes:
			typ = string(f.data)
		case f.num == 2 && f.wt == wireBytes:
			return each(f.data, func(r field) error {
				if r.num == 1 && r.wt == wireBytes {
					object = r.data
				}
				return nil
			})
		}
		return nil
	})
	return typ, object, err
}

// List calls item with each item of a list message, encoded, and returns
// the list's resource version and continue token.
func List(raw []byte, item func(raw []byte) error) (resourceVersion, cont string, err error) {
	err = each(raw, func(f field) error {
		switch {
		case f.num == 1 && f.wt == wireBytes:
			return each(f.data, func(m field) error {
				switch {
				case m.num == 2 && m.wt == wireBytes:
					resourceVersion = string(m.data)
				case m.num == 3 && m.wt == wireBytes:
					cont = string(m.data)
				}
				return nil
			})
		case f.num == 2 && f.wt == wireBytes:
			return item(f.data)
		}
		return nil
	})
	return resourceVersion, cont, err
}

// Status decodes a metav1.Status message.
func Status(raw []byte) (code int32, reason, message string, err error) {
	err = each(raw, func(f field) error {
		switch {
		case f.num == 3 && f.wt == wireBytes:
			message = string(f.data)
		case f.num == 4 && f.wt == wireBytes:
			reason = string(f.data)
		case f.num == 6 && f.wt == wireVarint:
			code = int32(f.v)
		}
		return nil
	})
	return code, reason, message, err
}

// Meta returns the resource version and annotations of an object message,
// whose metadata, a metav1.ObjectMeta, is field 1.
func Meta(raw []byte) (resourceVersion string, annotations map[string]string, err error) {
	err = each(raw, func(f field) error {
		if f.num != 1 || f.wt != wireBytes {
			return nil
		}
		return each(f.data, func(m field) error {
			switch {
			case m.num == 6 && m.wt == wireBytes:
				resourceVersion = string(m.data)
			case m.num == 12 && m.wt == wireBytes:
				var k, v string
				if err := each(m.data, func(e field) error {
					switch e.num {
					case 1:
						k = string(e.data)
					case 2:
						v = string(e.data)
					}
					return nil
				}); err != nil {
					return err
				}
				if annotations == nil {
					annotations = map[string]string{}
				}
				annotations[k] = v
			}
			return nil
		})
	})
	return resourceVersion, annotations, err
}
