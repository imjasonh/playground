// Package protobuf decodes the protobuf encoding of built-in Kubernetes
// objects into Go structs that declare any subset of an object's fields by
// their JSON names, without generated code. schema.txt, generated from
// k8s.io/api by the gen command, maps each kind's fields to protobuf field
// numbers.
package protobuf

import (
	_ "embed"
	"fmt"
	"strconv"
	"strings"
	"sync"
)

//go:embed schema.txt
var schemaText string

type kind int

const (
	kString kind = iota + 1
	kBytes
	kBool
	kInt32
	kInt64
	kUint32
	kUint64
	kDouble
	kFloat
	kMessage
	kRepeated
	kMap
)

// Type is the type of a protobuf field.
type Type struct {
	kind kind
	msg  *Message // kMessage
	elem *Type    // kRepeated
	key  *Type    // kMap
	val  *Type    // kMap
}

// Field is a field of a message.
type Field struct {
	// JSON is the field's JSON name, or "" for a message field whose own
	// fields appear in the parent's JSON object.
	JSON string
	Num  int
	Type *Type
}

// Message is a protobuf message.
type Message struct {
	Name string
	// Wrapper messages hold a repeated field 1 and are arrays in JSON.
	Wrapper bool
	Fields  []*Field
	byJSON  map[string]*Field
	byNum   map[int]*Field
	inline  []*Field
}

type schema struct {
	kinds map[string]*Message
	msgs  map[string]*Message
}

var loadSchema = sync.OnceValues(func() (*schema, error) { return parseSchema(schemaText) })

// ForKind returns the message for objects of a kind, or nil if the schema
// doesn't have it.
func ForKind(apiVersion, kind string) *Message {
	s, err := loadSchema()
	if err != nil {
		panic(err)
	}
	return s.kinds[apiVersion+" "+kind]
}

func parseSchema(text string) (*schema, error) {
	s := &schema{kinds: map[string]*Message{}, msgs: map[string]*Message{}}
	msg := func(name string) *Message {
		m := s.msgs[name]
		if m == nil {
			m = &Message{Name: name, byJSON: map[string]*Field{}, byNum: map[int]*Field{}}
			s.msgs[name] = m
		}
		return m
	}
	var cur *Message
	for i, line := range strings.Split(text, "\n") {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		bad := func() (*schema, error) { return nil, fmt.Errorf("protobuf schema line %d: %q", i+1, line) }
		parts := strings.Fields(line)
		switch {
		case strings.HasPrefix(line, "\t"):
			if cur == nil || len(parts) != 3 {
				return bad()
			}
			num, err := strconv.Atoi(parts[1])
			if err != nil {
				return bad()
			}
			t, err := parseType(parts[2], msg)
			if err != nil {
				return bad()
			}
			f := &Field{JSON: parts[0], Num: num, Type: t}
			if f.JSON == "-" {
				f.JSON = ""
				cur.inline = append(cur.inline, f)
			} else {
				cur.byJSON[f.JSON] = f
			}
			cur.byNum[num] = f
			cur.Fields = append(cur.Fields, f)
		case parts[0] == "kind" && len(parts) == 4:
			s.kinds[parts[1]+" "+parts[2]] = msg(parts[3])
		case parts[0] == "message" && (len(parts) == 2 || len(parts) == 3 && parts[2] == "wrapper"):
			cur = msg(parts[1])
			cur.Wrapper = len(parts) == 3
		default:
			return bad()
		}
	}
	return s, nil
}

func parseType(s string, msg func(string) *Message) (*Type, error) {
	switch {
	case strings.HasPrefix(s, "[]"):
		elem, err := parseType(s[2:], msg)
		return &Type{kind: kRepeated, elem: elem}, err
	case strings.HasPrefix(s, "map:"):
		k, v, ok := strings.Cut(s[4:], ":")
		if !ok {
			return nil, fmt.Errorf("bad map type %q", s)
		}
		key, err := parseType(k, msg)
		if err != nil {
			return nil, err
		}
		val, err := parseType(v, msg)
		return &Type{kind: kMap, key: key, val: val}, err
	case strings.HasPrefix(s, "msg:"):
		return &Type{kind: kMessage, msg: msg(s[4:])}, nil
	}
	k, ok := map[string]kind{
		"string": kString, "bytes": kBytes, "bool": kBool, "int32": kInt32, "int64": kInt64,
		"uint32": kUint32, "uint64": kUint64, "double": kDouble, "float": kFloat,
	}[s]
	if !ok {
		return nil, fmt.Errorf("unknown type %q", s)
	}
	return &Type{kind: k}, nil
}
