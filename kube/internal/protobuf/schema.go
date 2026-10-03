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

// schema parses messages from its text on first use, so a program pays only
// for the kinds it reads and the messages they contain.
type schema struct {
	kinds map[string]string // "apiVersion kind" -> message name

	mu     sync.Mutex
	blocks map[string]string // message name -> its lines, unparsed
	msgs   map[string]*Message
}

var loadSchema = sync.OnceValues(func() (*schema, error) { return newSchema(schemaText) })

// ForKind returns the message for objects of a kind, or nil if the schema
// doesn't have it.
func ForKind(apiVersion, kind string) *Message {
	s, err := loadSchema()
	if err != nil {
		return nil
	}
	m, err := s.kind(apiVersion, kind)
	if err != nil {
		return nil
	}
	return m
}

// newSchema indexes text by kind and by message without parsing fields.
func newSchema(text string) (*schema, error) {
	s := &schema{kinds: map[string]string{}, blocks: map[string]string{}, msgs: map[string]*Message{}}
	name, start := "", 0
	end := func(at int) {
		if name != "" {
			s.blocks[name] = text[start:at]
		}
	}
	for pos, n := 0, 0; pos < len(text); n++ {
		line, _, _ := strings.Cut(text[pos:], "\n")
		at := pos
		pos += len(line) + 1
		switch parts := strings.Fields(line); {
		case len(parts) == 0 || strings.HasPrefix(line, "#") || strings.HasPrefix(line, "\t"):
		case parts[0] == "kind" && len(parts) == 4:
			s.kinds[parts[1]+" "+parts[2]] = parts[3]
		case parts[0] == "message" && (len(parts) == 2 || len(parts) == 3 && parts[2] == "wrapper"):
			end(at)
			name, start = parts[1], at
		default:
			return nil, fmt.Errorf("protobuf schema line %d: %q", n+1, line)
		}
	}
	end(len(text))
	return s, nil
}

func (s *schema) kind(apiVersion, kind string) (*Message, error) {
	name, ok := s.kinds[apiVersion+" "+kind]
	if !ok {
		return nil, fmt.Errorf("protobuf: no schema for %s %s", apiVersion, kind)
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.message(name)
}

// message parses a message and the messages its fields refer to. The caller
// holds s.mu.
func (s *schema) message(name string) (m *Message, err error) {
	if m := s.msgs[name]; m != nil {
		return m, nil
	}
	defer func() {
		if err != nil {
			delete(s.msgs, name)
		}
	}()
	block, ok := s.blocks[name]
	if !ok {
		return nil, fmt.Errorf("protobuf: the schema has no message %s", name)
	}
	header, fields, _ := strings.Cut(block, "\n")
	m = &Message{Name: name, Wrapper: strings.HasSuffix(header, " wrapper"), byJSON: map[string]*Field{}, byNum: map[int]*Field{}}
	s.msgs[name] = m
	for line := range strings.Lines(fields) {
		parts := strings.Fields(line)
		if len(parts) == 0 {
			continue
		}
		bad := fmt.Errorf("protobuf schema, message %s: %q", name, strings.TrimSpace(line))
		if len(parts) != 3 {
			return nil, bad
		}
		num, err := strconv.Atoi(parts[1])
		if err != nil {
			return nil, bad
		}
		t, err := s.parseType(parts[2])
		if err != nil {
			return nil, fmt.Errorf("%w: %v", bad, err)
		}
		f := &Field{JSON: parts[0], Num: num, Type: t}
		if f.JSON == "-" {
			f.JSON = ""
			m.inline = append(m.inline, f)
		} else {
			m.byJSON[f.JSON] = f
		}
		m.byNum[num] = f
		m.Fields = append(m.Fields, f)
	}
	return m, nil
}

func (s *schema) parseType(t string) (*Type, error) {
	switch {
	case strings.HasPrefix(t, "[]"):
		elem, err := s.parseType(t[2:])
		return &Type{kind: kRepeated, elem: elem}, err
	case strings.HasPrefix(t, "map:"):
		k, v, ok := strings.Cut(t[4:], ":")
		if !ok {
			return nil, fmt.Errorf("bad map type %q", t)
		}
		key, err := s.parseType(k)
		if err != nil {
			return nil, err
		}
		val, err := s.parseType(v)
		return &Type{kind: kMap, key: key, val: val}, err
	case strings.HasPrefix(t, "msg:"):
		m, err := s.message(t[4:])
		return &Type{kind: kMessage, msg: m}, err
	}
	k, ok := map[string]kind{
		"string": kString, "bytes": kBytes, "bool": kBool, "int32": kInt32, "int64": kInt64,
		"uint32": kUint32, "uint64": kUint64, "double": kDouble, "float": kFloat,
	}[t]
	if !ok {
		return nil, fmt.Errorf("unknown type %q", t)
	}
	return &Type{kind: k}, nil
}
