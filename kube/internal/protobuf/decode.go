package protobuf

import (
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"reflect"
	"slices"
	"strings"
	"sync"
	"time"
)

// Plan decodes one message into values of one Go struct type. It decodes
// the fields that the struct declares, found by their JSON names the way
// encoding/json finds them, and skips the rest.
type Plan struct {
	t      reflect.Type
	msg    *Message
	fields []*fieldPlan // by field number
}

type op int

const (
	opString op = iota + 1
	opBytes
	opBool
	opInt
	opUint
	opFloat
	opMessage  // a struct
	opPointer  // a pointer: allocate, then decode with elem
	opInline   // a message whose fields belong to the same struct
	opRepeated // a slice
	opMap      // a map with string keys
	opWrapper  // a slice, from a wrapper message
	opTime     // time.Time, from meta.v1.Time or MicroTime
	opTimePtr  // *time.Time
	opQuantity // a string, from resource.Quantity
	opJSON     // anything else: convert to JSON and use encoding/json
)

type fieldPlan struct {
	op    op
	index []int // the Go field, from the struct; nil for opInline
	pt    *Type
	gt    reflect.Type
	sub   *Plan      // opMessage, opInline
	elem  *fieldPlan // opPointer, opRepeated, opMap values, opWrapper
}

var (
	timeType        = reflect.TypeFor[time.Time]()
	unmarshalerType = reflect.TypeFor[json.Unmarshaler]()
	plans           sync.Map // planKey -> *Plan or error
)

type planKey struct {
	t   reflect.Type
	msg *Message
}

// For returns a plan to decode objects of a kind into struct type t. It
// returns an error if the schema doesn't have the kind, or if t declares a
// field that the kind doesn't have, such as one that a newer version of
// Kubernetes added; read those types as JSON.
func For(t reflect.Type, apiVersion, kind string) (*Plan, error) {
	msg := ForKind(apiVersion, kind)
	if msg == nil {
		return nil, fmt.Errorf("protobuf: no schema for %s %s", apiVersion, kind)
	}
	key := planKey{t, msg}
	if v, ok := plans.Load(key); ok {
		if err, ok := v.(error); ok {
			return nil, err
		}
		return v.(*Plan), nil
	}
	b := &builder{plans: map[planKey]*Plan{}}
	p, err := b.plan(t, msg, true)
	if err != nil {
		plans.Store(key, err)
		return nil, err
	}
	plans.Store(key, p)
	return p, nil
}

// Unmarshal decodes the message raw into v, a pointer to the plan's type.
// Fields that raw doesn't set keep their values.
func (p *Plan) Unmarshal(raw []byte, v any) error {
	rv := reflect.ValueOf(v)
	if rv.Kind() != reflect.Pointer || rv.Elem().Type() != p.t {
		return fmt.Errorf("protobuf: Unmarshal into %T, want *%v", v, p.t)
	}
	return p.decode(rv.Elem(), raw)
}

func (p *Plan) decode(sv reflect.Value, b []byte) error {
	for len(b) > 0 {
		f, n, err := next(b)
		if err != nil {
			return err
		}
		b = b[n:]
		if f.num >= len(p.fields) || p.fields[f.num] == nil {
			continue
		}
		fp := p.fields[f.num]
		if fp.op == opInline {
			if f.wt == wireBytes {
				if err := fp.sub.decode(sv, f.data); err != nil {
					return err
				}
			}
			continue
		}
		if err := fp.set(fieldByIndex(sv, fp.index), f); err != nil {
			return err
		}
	}
	return nil
}

func fieldByIndex(v reflect.Value, index []int) reflect.Value {
	for i, x := range index {
		if i > 0 && v.Kind() == reflect.Pointer {
			if v.IsNil() {
				v.Set(reflect.New(v.Type().Elem()))
			}
			v = v.Elem()
		}
		v = v.Field(x)
	}
	return v
}

// set decodes one occurrence of a field into dst. A value whose wire type
// doesn't match the schema is ignored, as encoding/json leaves a field with
// the wrong JSON type empty.
func (fp *fieldPlan) set(dst reflect.Value, f field) error {
	switch fp.op {
	case opString:
		if f.wt == wireBytes {
			dst.SetString(string(f.data))
		}
	case opBytes:
		if f.wt == wireBytes {
			dst.SetBytes(append(make([]byte, 0, len(f.data)), f.data...))
		}
	case opBool:
		if f.wt == wireVarint {
			dst.SetBool(f.v != 0)
		}
	case opInt:
		if x, ok := signed(fp.pt.kind, f); ok && !dst.OverflowInt(x) {
			dst.SetInt(x)
		}
	case opUint:
		if x, ok := signed(fp.pt.kind, f); ok && x >= 0 && !dst.OverflowUint(uint64(x)) {
			dst.SetUint(uint64(x))
		} else if fp.pt.kind == kUint64 && f.wt == wireVarint && !dst.OverflowUint(f.v) {
			dst.SetUint(f.v)
		}
	case opFloat:
		if x, ok := float(fp.pt.kind, f); ok && !dst.OverflowFloat(x) {
			dst.SetFloat(x)
		}
	case opMessage:
		if f.wt == wireBytes {
			return fp.sub.decode(dst, f.data)
		}
	case opPointer:
		if dst.IsNil() {
			dst.Set(reflect.New(dst.Type().Elem()))
		}
		return fp.elem.set(dst.Elem(), f)
	case opRepeated:
		if f.wt == wireBytes && packable(fp.pt.elem.kind) {
			return packed(fp.pt.elem.kind, f.data, func(e field) error { return fp.appendTo(dst, e) })
		}
		return fp.appendTo(dst, f)
	case opWrapper:
		if f.wt != wireBytes {
			return nil
		}
		items := fp.pt.msg.byNum[1].Type.elem
		return each(f.data, func(e field) error {
			if e.num != 1 {
				return nil
			}
			if e.wt == wireBytes && packable(items.kind) {
				return packed(items.kind, e.data, func(p field) error { return fp.appendTo(dst, p) })
			}
			return fp.appendTo(dst, e)
		})
	case opMap:
		if f.wt != wireBytes {
			return nil
		}
		if dst.IsNil() {
			dst.Set(reflect.MakeMap(dst.Type()))
		}
		k := reflect.New(dst.Type().Key()).Elem()
		v := reflect.New(dst.Type().Elem()).Elem()
		if err := each(f.data, func(e field) error {
			switch e.num {
			case 1:
				if e.wt == wireBytes {
					k.SetString(string(e.data))
				}
			case 2:
				return fp.elem.set(v, e)
			}
			return nil
		}); err != nil {
			return err
		}
		dst.SetMapIndex(k, v)
	case opTime, opTimePtr:
		if f.wt != wireBytes {
			return nil
		}
		t, err := timeOf(fp.pt.msg, f.data)
		if err != nil {
			return err
		}
		if fp.op == opTimePtr {
			dst.Set(reflect.New(timeType))
			dst = dst.Elem()
		}
		dst.Set(reflect.ValueOf(t))
	case opQuantity:
		if f.wt == wireBytes {
			return each(f.data, func(q field) error {
				if q.num == 1 && q.wt == wireBytes {
					dst.SetString(string(q.data))
				}
				return nil
			})
		}
	case opJSON:
		v, err := toJSON(fp.pt, f)
		if err != nil {
			return err
		}
		b, err := json.Marshal(v)
		if err != nil {
			return err
		}
		var te *json.UnmarshalTypeError
		if err := json.Unmarshal(b, dst.Addr().Interface()); err != nil && !errors.As(err, &te) {
			return err
		}
	}
	return nil
}

// appendTo decodes one element and appends it to the slice dst.
func (fp *fieldPlan) appendTo(dst reflect.Value, f field) error {
	e := reflect.New(dst.Type().Elem()).Elem()
	if err := fp.elem.set(e, f); err != nil {
		return err
	}
	dst.Set(reflect.Append(dst, e))
	return nil
}

func signed(k kind, f field) (int64, bool) {
	if f.wt != wireVarint {
		return 0, false
	}
	switch k {
	case kInt32:
		return int64(int32(f.v)), true
	case kUint32:
		return int64(uint32(f.v)), true
	case kInt64, kUint64:
		return int64(f.v), k == kInt64 || f.v <= math.MaxInt64
	}
	return 0, false
}

func float(k kind, f field) (float64, bool) {
	switch {
	case k == kDouble && f.wt == wireFixed64:
		return math.Float64frombits(f.v), true
	case k == kFloat && f.wt == wireFixed32:
		return float64(math.Float32frombits(uint32(f.v))), true
	}
	if x, ok := signed(k, f); ok {
		return float64(x), true
	}
	return 0, false
}

func packable(k kind) bool {
	switch k {
	case kBool, kInt32, kInt64, kUint32, kUint64, kDouble, kFloat:
		return true
	}
	return false
}

// packed calls fn for each value in a packed repeated scalar field.
func packed(k kind, b []byte, fn func(field) error) error {
	for len(b) > 0 {
		f := field{num: 1}
		switch k {
		case kDouble:
			if len(b) < 8 {
				return errTruncated
			}
			f.wt, f.v, b = wireFixed64, leUint64(b), b[8:]
		case kFloat:
			if len(b) < 4 {
				return errTruncated
			}
			f.wt, f.v, b = wireFixed32, uint64(leUint32(b)), b[4:]
		default:
			v, n := varint(b)
			if n == 0 {
				return errTruncated
			}
			f.wt, f.v, b = wireVarint, v, b[n:]
		}
		if err := fn(f); err != nil {
			return err
		}
	}
	return nil
}

func leUint64(b []byte) uint64 {
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}

func leUint32(b []byte) uint32 {
	return uint32(b[0]) | uint32(b[1])<<8 | uint32(b[2])<<16 | uint32(b[3])<<24
}

// timeOf decodes a meta.v1.Time or MicroTime. Time has whole seconds in
// JSON, so it drops fractions here too.
func timeOf(m *Message, b []byte) (time.Time, error) {
	var sec, nanos int64
	err := each(b, func(f field) error {
		switch {
		case f.num == 1 && f.wt == wireVarint:
			sec = int64(f.v)
		case f.num == 2 && f.wt == wireVarint:
			nanos = int64(int32(f.v))
		}
		return nil
	})
	if m.Name == "meta.v1.Time" {
		nanos = 0
	}
	return time.Unix(sec, nanos).UTC(), err
}

// toJSON converts a field's value to what encoding/json would decode from
// the field's JSON form.
func toJSON(t *Type, f field) (any, error) {
	switch t.kind {
	case kString:
		return string(f.data), nil
	case kBytes:
		return append([]byte{}, f.data...), nil
	case kBool:
		return f.v != 0, nil
	case kInt32, kInt64, kUint32:
		x, _ := signed(t.kind, f)
		return x, nil
	case kUint64:
		return f.v, nil
	case kDouble, kFloat:
		x, _ := float(t.kind, f)
		return x, nil
	case kMessage:
		return messageJSON(t.msg, f.data)
	case kRepeated:
		var out []any
		if f.wt == wireBytes && packable(t.elem.kind) {
			err := packed(t.elem.kind, f.data, func(e field) error {
				v, err := toJSON(t.elem, e)
				out = append(out, v)
				return err
			})
			return out, err
		}
		v, err := toJSON(t.elem, f)
		return []any{v}, err
	}
	return nil, fmt.Errorf("protobuf: can't convert %v to JSON", t.kind)
}

func messageJSON(m *Message, b []byte) (any, error) {
	switch m.Name {
	case "meta.v1.Time", "meta.v1.MicroTime":
		t, err := timeOf(m, b)
		if m.Name == "meta.v1.Time" {
			return t.Format(time.RFC3339), err
		}
		return t.Format("2006-01-02T15:04:05.000000Z07:00"), err
	case "meta.v1.Duration":
		var d int64
		err := each(b, func(f field) error {
			if f.num == 1 {
				d = int64(f.v)
			}
			return nil
		})
		return time.Duration(d).String(), err
	case "resource.Quantity":
		var s string
		err := each(b, func(f field) error {
			if f.num == 1 {
				s = string(f.data)
			}
			return nil
		})
		return s, err
	case "intstr.IntOrString":
		var typ, i int64
		var s string
		err := each(b, func(f field) error {
			switch f.num {
			case 1:
				typ = int64(f.v)
			case 2:
				i = int64(int32(f.v))
			case 3:
				s = string(f.data)
			}
			return nil
		})
		if typ == 1 {
			return s, err
		}
		return i, err
	case "runtime.RawExtension", "meta.v1.FieldsV1":
		var raw json.RawMessage
		err := each(b, func(f field) error {
			if f.num == 1 && f.wt == wireBytes && json.Valid(f.data) {
				raw = append(json.RawMessage{}, f.data...)
			}
			return nil
		})
		return raw, err
	}
	obj := map[string]any{}
	err := each(b, func(f field) error {
		pf := m.byNum[f.num]
		if pf == nil {
			return nil
		}
		if pf.JSON == "" {
			if f.wt != wireBytes {
				return nil
			}
			inner, err := messageJSON(pf.Type.msg, f.data)
			if err != nil {
				return err
			}
			if o, ok := inner.(map[string]any); ok {
				for k, v := range o {
					obj[k] = v
				}
			}
			return nil
		}
		switch pf.Type.kind {
		case kRepeated:
			v, err := toJSON(pf.Type, f)
			if err != nil {
				return err
			}
			prev, _ := obj[pf.JSON].([]any)
			obj[pf.JSON] = append(prev, v.([]any)...)
		case kMap:
			if f.wt != wireBytes {
				return nil
			}
			mm, _ := obj[pf.JSON].(map[string]any)
			if mm == nil {
				mm = map[string]any{}
				obj[pf.JSON] = mm
			}
			var key string
			var val any
			if pf.Type.val.kind == kMessage {
				val = map[string]any{}
			}
			if err := each(f.data, func(e field) error {
				switch e.num {
				case 1:
					key = string(e.data)
				case 2:
					v, err := toJSON(pf.Type.val, e)
					val = v
					return err
				}
				return nil
			}); err != nil {
				return err
			}
			mm[key] = val
		default:
			v, err := toJSON(pf.Type, f)
			if err != nil {
				return err
			}
			obj[pf.JSON] = v
		}
		return nil
	})
	if m.Wrapper {
		items, _ := obj["items"].([]any)
		return items, err
	}
	return obj, err
}

// builder makes plans, sharing the plans of struct types that appear more
// than once, including in themselves.
type builder struct {
	plans map[planKey]*Plan
}

func (b *builder) plan(t reflect.Type, msg *Message, top bool) (*Plan, error) {
	key := planKey{t, msg}
	if p := b.plans[key]; p != nil {
		return p, nil
	}
	p := &Plan{t: t, msg: msg}
	b.plans[key] = p
	if err := b.fill(p, jsonFields(t), top); err != nil {
		return nil, err
	}
	return p, nil
}

// fill assigns each of the Go fields gfs to a field of p's message, or to a
// field of one of its inline messages.
func (b *builder) fill(p *Plan, gfs []goField, top bool) error {
	direct := map[*Field]goField{}
	inline := map[*Field][]goField{}
	for _, gf := range gfs {
		if pf := p.msg.lookup(gf.name); pf != nil {
			direct[pf] = gf
			continue
		}
		if pf := p.msg.inlineFor(gf.name); pf != nil {
			inline[pf] = append(inline[pf], gf)
			continue
		}
		if top && (gf.name == "apiVersion" || gf.name == "kind") {
			continue // in the envelope, not the object
		}
		return fmt.Errorf("protobuf: %v has field %q, which %s doesn't have", p.t, gf.name, p.msg.Name)
	}
	n := 0
	for _, f := range p.msg.Fields {
		n = max(n, f.Num+1)
	}
	p.fields = make([]*fieldPlan, n)
	for pf, gf := range direct {
		fp, err := b.fieldPlan(gf.typ, pf.Type)
		if err != nil {
			return err
		}
		fp.index = gf.index
		p.fields[pf.Num] = fp
	}
	for pf, gfs := range inline {
		sub := &Plan{t: p.t, msg: pf.Type.msg}
		if err := b.fill(sub, gfs, false); err != nil {
			return err
		}
		p.fields[pf.Num] = &fieldPlan{op: opInline, pt: pf.Type, sub: sub}
	}
	return nil
}

func (b *builder) fieldPlan(gt reflect.Type, pt *Type) (*fieldPlan, error) {
	fp := &fieldPlan{op: opJSON, pt: pt, gt: gt}
	if pt.kind == kMessage {
		switch pt.msg.Name {
		case "meta.v1.Time", "meta.v1.MicroTime":
			switch gt {
			case timeType:
				fp.op = opTime
			case reflect.PointerTo(timeType):
				fp.op = opTimePtr
			}
			return fp, nil
		case "resource.Quantity":
			switch {
			case gt.Kind() == reflect.String && !unmarshals(gt):
				fp.op = opQuantity
			case gt.Kind() == reflect.Pointer && gt.Elem().Kind() == reflect.String && !unmarshals(gt.Elem()):
				fp.op, fp.elem = opPointer, &fieldPlan{op: opQuantity, pt: pt, gt: gt.Elem()}
			}
			return fp, nil
		case "meta.v1.Duration", "intstr.IntOrString", "runtime.RawExtension", "meta.v1.FieldsV1":
			return fp, nil
		}
	}
	if unmarshals(gt) {
		return fp, nil
	}
	gk := gt.Kind()
	if gk == reflect.Pointer {
		elem, err := b.fieldPlan(gt.Elem(), pt)
		if err != nil || elem.op == opJSON {
			return fp, err
		}
		fp.op, fp.elem = opPointer, elem
		return fp, nil
	}
	switch pt.kind {
	case kString:
		if gk == reflect.String {
			fp.op = opString
		}
	case kBytes:
		if gk == reflect.Slice && gt.Elem().Kind() == reflect.Uint8 {
			fp.op = opBytes
		}
	case kBool:
		if gk == reflect.Bool {
			fp.op = opBool
		}
	case kInt32, kInt64, kUint32, kUint64, kDouble, kFloat:
		switch {
		case gk >= reflect.Int && gk <= reflect.Int64 && pt.kind != kDouble && pt.kind != kFloat:
			fp.op = opInt
		case gk >= reflect.Uint && gk <= reflect.Uint64 && pt.kind != kDouble && pt.kind != kFloat:
			fp.op = opUint
		case gk == reflect.Float32 || gk == reflect.Float64:
			fp.op = opFloat
		}
	case kMessage:
		switch {
		case pt.msg.Wrapper && gk == reflect.Slice:
			elem, err := b.fieldPlan(gt.Elem(), pt.msg.byNum[1].Type.elem)
			if err != nil {
				return nil, err
			}
			fp.op, fp.elem = opWrapper, elem
		case !pt.msg.Wrapper && gk == reflect.Struct:
			sub, err := b.plan(gt, pt.msg, false)
			if err != nil {
				return nil, err
			}
			fp.op, fp.sub = opMessage, sub
		}
	case kRepeated:
		if gk == reflect.Slice && !(gt.Elem().Kind() == reflect.Uint8 && pt.elem.kind != kBytes) {
			elem, err := b.fieldPlan(gt.Elem(), pt.elem)
			if err != nil {
				return nil, err
			}
			fp.op, fp.elem = opRepeated, elem
		}
	case kMap:
		if gk == reflect.Map && gt.Key().Kind() == reflect.String && !unmarshals(gt.Key()) {
			elem, err := b.fieldPlan(gt.Elem(), pt.val)
			if err != nil {
				return nil, err
			}
			fp.op, fp.elem = opMap, elem
		}
	}
	return fp, nil
}

func unmarshals(t reflect.Type) bool {
	return t.Implements(unmarshalerType) || reflect.PointerTo(t).Implements(unmarshalerType)
}

// lookup finds a field by JSON name, exactly or, as encoding/json does,
// ignoring case.
func (m *Message) lookup(name string) *Field {
	if f := m.byJSON[name]; f != nil {
		return f
	}
	for json, f := range m.byJSON {
		if strings.EqualFold(json, name) {
			return f
		}
	}
	return nil
}

// inlineFor returns the inline field of m whose message, or one of its own
// inline messages, has a field with this JSON name.
func (m *Message) inlineFor(name string) *Field {
	for _, f := range m.inline {
		if f.Type.msg.lookup(name) != nil || f.Type.msg.inlineFor(name) != nil {
			return f
		}
	}
	return nil
}

type goField struct {
	name  string
	index []int
	typ   reflect.Type
}

// jsonFields returns the fields of struct type t that encoding/json encodes,
// with their JSON names, including fields of embedded structs. Where two
// fields have one name, the shallower wins; at one depth, a tagged field
// beats untagged ones, and otherwise neither is used.
func jsonFields(t reflect.Type) []goField {
	type level struct {
		t     reflect.Type
		index []int
	}
	var out []goField
	taken := map[string]bool{}
	visited := map[reflect.Type]bool{}
	for cur := []level{{t, nil}}; len(cur) > 0; {
		var nextLevel []level
		type cand struct {
			goField
			tagged bool
		}
		byName := map[string][]cand{}
		var order []string
		for _, l := range cur {
			if visited[l.t] {
				continue
			}
			visited[l.t] = true
			for i := range l.t.NumField() {
				sf := l.t.Field(i)
				tag := sf.Tag.Get("json")
				if tag == "-" {
					continue
				}
				name, _, _ := strings.Cut(tag, ",")
				index := append(slices.Clone(l.index), i)
				ft := sf.Type
				if ft.Kind() == reflect.Pointer {
					ft = ft.Elem()
				}
				if sf.Anonymous && name == "" && ft.Kind() == reflect.Struct {
					nextLevel = append(nextLevel, level{ft, index})
					continue
				}
				if !sf.IsExported() {
					continue
				}
				tagged := name != ""
				if !tagged {
					name = sf.Name
				}
				if _, seen := byName[name]; !seen {
					order = append(order, name)
				}
				byName[name] = append(byName[name], cand{goField{name, index, sf.Type}, tagged})
			}
		}
		for _, name := range order {
			if taken[name] {
				continue
			}
			taken[name] = true
			cs := byName[name]
			var tagged []cand
			for _, c := range cs {
				if c.tagged {
					tagged = append(tagged, c)
				}
			}
			switch {
			case len(cs) == 1:
				out = append(out, cs[0].goField)
			case len(tagged) == 1:
				out = append(out, tagged[0].goField)
			}
		}
		cur = nextLevel
	}
	return out
}
