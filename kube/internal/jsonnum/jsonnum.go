// Package jsonnum decodes JSON into map[string]any and friends with
// numbers kept as written, which encoding/json/v2 has no option for.
package jsonnum

import (
	"encoding/json/jsontext"
	"encoding/json/v2"
	"fmt"
	"io"
)

// A Number is a JSON number as written in the document.
type Number string

func (n Number) String() string { return string(n) }

// MarshalJSON encodes n as a JSON number. A Number that isn't one is an error.
func (n Number) MarshalJSON() ([]byte, error) {
	if n == "" {
		return []byte("0"), nil
	}
	v := jsontext.Value(n)
	if !v.IsValid() || v.Kind() != '0' {
		return nil, fmt.Errorf("jsonnum: %q is not a JSON number", string(n))
	}
	return []byte(n), nil
}

// Unmarshal decodes data into v. Wherever v holds an any, a JSON number
// becomes a Number, an object a map[string]any, and an array a []any.
func Unmarshal(data []byte, v any) error {
	return json.Unmarshal(data, v, json.WithUnmarshalers(unmarshalAny))
}

// UnmarshalRead is Unmarshal for a reader, which it reads to EOF.
func UnmarshalRead(r io.Reader, v any) error {
	return json.UnmarshalRead(r, v, json.WithUnmarshalers(unmarshalAny))
}

var unmarshalAny = json.UnmarshalFromFunc(func(dec *jsontext.Decoder, v *any) error {
	x, err := value(dec)
	if err != nil {
		return err
	}
	*v = x
	return nil
})

func value(dec *jsontext.Decoder) (any, error) {
	switch dec.PeekKind() {
	case '0':
		raw, err := dec.ReadValue()
		return Number(raw), err
	case '{':
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		m := map[string]any{}
		for dec.PeekKind() != '}' {
			k, err := dec.ReadToken()
			if err != nil {
				return nil, err
			}
			key := k.String()
			x, err := value(dec)
			if err != nil {
				return nil, err
			}
			m[key] = x
		}
		_, err := dec.ReadToken()
		return m, err
	case '[':
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		list := []any{}
		for dec.PeekKind() != ']' {
			x, err := value(dec)
			if err != nil {
				return nil, err
			}
			list = append(list, x)
		}
		_, err := dec.ReadToken()
		return list, err
	}
	tok, err := dec.ReadToken()
	if err != nil {
		return nil, err
	}
	switch tok.Kind() {
	case 'n':
		return nil, nil
	case 't', 'f':
		return tok.Bool(), nil
	}
	return tok.String(), nil
}
