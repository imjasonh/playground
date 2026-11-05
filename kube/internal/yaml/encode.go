package yaml

import (
	"bytes"
	"encoding/json/jsontext"
	"encoding/json/v2"
	"fmt"
	"strings"

	"github.com/imjasonh/playground/kube/internal/jsonnum"
)

// FromJSON converts one JSON value to a YAML document in block style,
// keeping the order of object keys.
//
// Strings stay plain only when every YAML 1.1 and 1.2 parser reads them as
// the same string, so kubectl's parser never turns a string such as "on",
// "1:20", or "2026-10-02" into another type. Other strings use JSON's
// double-quoted form, which YAML accepts.
func FromJSON(data []byte) ([]byte, error) {
	dec := jsontext.NewDecoder(bytes.NewReader(data))
	v, err := decodeOrdered(dec)
	if err != nil {
		return nil, err
	}
	if dec.PeekKind() != 0 {
		return nil, fmt.Errorf("yaml: more than one JSON value")
	}
	var b strings.Builder
	switch v := v.(type) {
	case ordered:
		if len(v) == 0 {
			b.WriteString("{}\n")
		}
		writeMap(&b, v, 0)
	case []any:
		if len(v) == 0 {
			b.WriteString("[]\n")
		}
		writeList(&b, v, 0)
	default:
		b.WriteString(scalar(v))
		b.WriteByte('\n')
	}
	return []byte(b.String()), nil
}

// ordered is a JSON object with its keys in their original order.
type ordered []member

type member struct {
	key   string
	value any
}

func decodeOrdered(dec *jsontext.Decoder) (any, error) {
	tok, err := dec.ReadToken()
	if err != nil {
		return nil, err
	}
	switch tok.Kind() {
	case '{':
		obj := ordered{}
		for dec.PeekKind() != '}' {
			k, err := dec.ReadToken()
			if err != nil {
				return nil, err
			}
			key := k.String()
			v, err := decodeOrdered(dec)
			if err != nil {
				return nil, err
			}
			obj = append(obj, member{key, v})
		}
		_, err := dec.ReadToken()
		return obj, err
	case '[':
		list := []any{}
		for dec.PeekKind() != ']' {
			v, err := decodeOrdered(dec)
			if err != nil {
				return nil, err
			}
			list = append(list, v)
		}
		_, err := dec.ReadToken()
		return list, err
	case 'n':
		return nil, nil
	case 't', 'f':
		return tok.Bool(), nil
	case '0':
		return jsonnum.Number(tok.String()), nil
	}
	return tok.String(), nil
}

func writeMap(b *strings.Builder, m ordered, indent int) {
	for _, kv := range m {
		b.WriteString(strings.Repeat(" ", indent))
		b.WriteString(scalar(kv.key))
		b.WriteByte(':')
		writeValue(b, kv.value, indent, indent+2)
	}
}

// writeValue writes v after a key or a list dash. Nested maps go at
// mapIndent, and nested lists at the key's own indent, as kubectl writes
// them.
func writeValue(b *strings.Builder, v any, listIndent, mapIndent int) {
	switch v := v.(type) {
	case ordered:
		if len(v) == 0 {
			b.WriteString(" {}\n")
			return
		}
		b.WriteByte('\n')
		writeMap(b, v, mapIndent)
	case []any:
		if len(v) == 0 {
			b.WriteString(" []\n")
			return
		}
		b.WriteByte('\n')
		writeList(b, v, listIndent)
	default:
		b.WriteByte(' ')
		b.WriteString(scalar(v))
		b.WriteByte('\n')
	}
}

func writeList(b *strings.Builder, list []any, indent int) {
	pad := strings.Repeat(" ", indent)
	for _, item := range list {
		b.WriteString(pad)
		b.WriteByte('-')
		switch item := item.(type) {
		case ordered:
			if len(item) == 0 {
				b.WriteString(" {}\n")
				continue
			}
			// The first key shares the dash's line; the rest line up with it.
			b.WriteByte(' ')
			b.WriteString(scalar(item[0].key))
			b.WriteByte(':')
			writeValue(b, item[0].value, indent+2, indent+4)
			writeMap(b, item[1:], indent+2)
		case []any:
			if len(item) == 0 {
				b.WriteString(" []\n")
				continue
			}
			b.WriteByte('\n')
			writeList(b, item, indent+2)
		default:
			b.WriteByte(' ')
			b.WriteString(scalar(item))
			b.WriteByte('\n')
		}
	}
}

func scalar(v any) string {
	switch v := v.(type) {
	case nil:
		return "null"
	case bool:
		if v {
			return "true"
		}
		return "false"
	case jsonnum.Number:
		return v.String()
	case string:
		if plain(v) {
			return v
		}
		q, _ := json.Marshal(v, json.Deterministic(true))
		return string(q)
	}
	return fmt.Sprint(v)
}

// plain reports whether s can be written without quotes. It allows only
// names, paths, and image references that start with a letter, '/', or
// '_', and rejects words that YAML 1.1 reads as booleans or null.
func plain(s string) bool {
	if s == "" {
		return false
	}
	switch strings.ToLower(s) {
	case "y", "n", "yes", "no", "on", "off", "true", "false", "null":
		return false
	}
	c := s[0]
	if !(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '/' || c == '_') {
		return false
	}
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z', c >= '0' && c <= '9':
		case strings.IndexByte("._/-@=+", c) >= 0:
		case c == ':' && i+1 < len(s) && s[i+1] != ' ':
		default:
			return false
		}
	}
	return true
}
