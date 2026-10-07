package protobuf

import (
	"encoding/json"
	"errors"
	"math"
	"reflect"
	"strconv"
	"strings"
	"testing"
	"time"
)

// enc builds protobuf messages for tests.
type enc []byte

func (e enc) varint(v uint64) enc {
	for v >= 0x80 {
		e = append(e, byte(v)|0x80)
		v >>= 7
	}
	return append(e, byte(v))
}

func (e enc) uint(num int, v uint64) enc { return e.varint(uint64(num)<<3 | wireVarint).varint(v) }
func (e enc) str(num int, s string) enc {
	return append(e.varint(uint64(num)<<3|wireBytes).varint(uint64(len(s))), s...)
}
func (e enc) msg(num int, m enc) enc { return e.str(num, string(m)) }
func (e enc) double(num int, f float64) enc {
	e = e.varint(uint64(num)<<3 | wireFixed64)
	b := math.Float64bits(f)
	for i := range 8 {
		e = append(e, byte(b>>(8*i)))
	}
	return e
}

const testSchema = `
kind t/v1 Obj t.Obj
message t.Obj
	name 1 string
	count 2 int32
	ratio 3 double
	tags 4 []string
	nums 5 []int64
	labels 6 map:string:string
	when 7 msg:meta.v1.Time
	size 8 msg:resource.Quantity
	port 9 msg:intstr.IntOrString
	- 10 msg:t.Source
	extra 11 map:string:msg:t.Extra
	child 12 msg:t.Child
	children 13 []msg:t.Child
	data 14 bytes
	flag 15 bool
	limits 16 map:string:msg:resource.Quantity
	micro 17 msg:meta.v1.MicroTime
	timeout 18 msg:meta.v1.Duration
message t.Source
	configMap 1 msg:t.Child
	- 2 msg:t.Deeper
message t.Deeper
	hostPath 1 string
message t.Child
	name 1 string
	next 2 msg:t.Child
message t.Extra wrapper
	items 1 []string
message meta.v1.Time
	seconds 1 int64
	nanos 2 int32
message meta.v1.MicroTime
	seconds 1 int64
	nanos 2 int32
message meta.v1.Duration
	duration 1 int64
message resource.Quantity
	string 1 string
message intstr.IntOrString
	type 1 int64
	intVal 2 int32
	strVal 3 string
`

type child struct {
	Name string `json:"name"`
	Next *child `json:"next,omitempty"`
}

type intOrString struct {
	Int   int
	Str   string
	IsStr bool
}

func (v *intOrString) UnmarshalJSON(b []byte) error {
	if len(b) > 0 && b[0] == '"' {
		v.IsStr = true
		return json.Unmarshal(b, &v.Str)
	}
	return json.Unmarshal(b, &v.Int)
}

type quantity string

type base struct {
	Name string `json:"name"`
}

type obj struct {
	base
	Count     *int32              `json:"count,omitempty"`
	Ratio     float64             `json:"ratio"`
	Tags      []string            `json:"tags"`
	Nums      []int64             `json:"nums"`
	Labels    map[string]string   `json:"labels"`
	When      time.Time           `json:"when"`
	Size      quantity            `json:"size"`
	Port      intOrString         `json:"port"`
	ConfigMap *child              `json:"configMap,omitempty"`
	HostPath  string              `json:"hostPath"`
	Extra     map[string][]string `json:"extra"`
	Child     child               `json:"child"`
	Children  []child             `json:"children"`
	Data      []byte              `json:"data"`
	Flag      *bool               `json:"flag"`
	Limits    map[string]quantity `json:"limits"`
	Micro     *time.Time          `json:"micro"`
	Timeout   string              `json:"timeout"`
}

func testMessage(t *testing.T) *Message {
	t.Helper()
	s, err := newSchema(testSchema)
	if err != nil {
		t.Fatal(err)
	}
	m, err := s.kind("t/v1", "Obj")
	if err != nil {
		t.Fatal(err)
	}
	return m
}

func testPlan[T any](t *testing.T) *Plan {
	t.Helper()
	msg := testMessage(t)
	b := &builder{plans: map[planKey]*Plan{}}
	p, err := b.plan(reflect.TypeFor[T](), msg, true)
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func TestDecode(t *testing.T) {
	when := time.Date(2026, 10, 2, 20, 41, 7, 0, time.UTC)
	var m enc
	m = m.str(1, "web").
		uint(2, uint64(math.MaxUint64)). // -1 as an int32 varint
		double(3, 0.25).
		str(4, "a").str(4, "b").
		msg(5, enc{}.varint(1).varint(1<<40)). // packed
		uint(5, 7).                            // and not packed
		msg(6, enc{}.str(1, "app").str(2, "web")).
		msg(6, enc{}.str(1, "empty").str(2, "")).
		msg(7, enc{}.uint(1, uint64(when.Unix())).uint(2, 999)).
		msg(8, enc{}.str(1, "250m")).
		msg(9, enc{}.uint(1, 1).str(3, "http")).
		msg(10, enc{}.msg(1, enc{}.str(1, "settings")).msg(2, enc{}.str(1, "/var"))).
		msg(11, enc{}.str(1, "groups").msg(2, enc{}.str(1, "x").str(1, "y"))).
		msg(12, enc{}.str(1, "parent").msg(2, enc{}.str(1, "grandchild"))).
		msg(13, enc{}.str(1, "c1")).msg(13, enc{}.str(1, "c2")).
		str(14, "\x00\xff").
		uint(15, 1).
		msg(16, enc{}.str(1, "cpu").msg(2, enc{}.str(1, "2"))).
		msg(17, enc{}.uint(1, uint64(when.Unix())).uint(2, 123456000)).
		msg(18, enc{}.uint(1, uint64(90*time.Second))).
		uint(99, 5).              // unknown to the schema: skipped
		str(2, "wrong wire type") // ignored, as JSON leaves mismatched fields
	var got obj
	if err := testPlan[obj](t).Unmarshal(m, &got); err != nil {
		t.Fatal(err)
	}
	minusOne := int32(-1)
	yes := true
	micro := time.Date(2026, 10, 2, 20, 41, 7, 123456000, time.UTC)
	want := obj{
		base:  base{Name: "web"},
		Count: &minusOne, Ratio: 0.25, Tags: []string{"a", "b"}, Nums: []int64{1, 1 << 40, 7},
		Labels: map[string]string{"app": "web", "empty": ""}, When: when, Size: "250m",
		Port:      intOrString{Str: "http", IsStr: true},
		ConfigMap: &child{Name: "settings"}, HostPath: "/var",
		Extra:    map[string][]string{"groups": {"x", "y"}},
		Child:    child{Name: "parent", Next: &child{Name: "grandchild"}},
		Children: []child{{Name: "c1"}, {Name: "c2"}}, Data: []byte{0, 0xff}, Flag: &yes,
		Limits: map[string]quantity{"cpu": "2"}, Micro: &micro, Timeout: "1m30s",
	}
	if !reflect.DeepEqual(got, want) {
		gb, _ := json.Marshal(got)
		wb, _ := json.Marshal(want)
		t.Errorf("got  %s\nwant %s", gb, wb)
	}
}

func TestTimesDecodeLikeJSON(t *testing.T) {
	type asTime struct {
		When  time.Time `json:"when"`
		Micro time.Time `json:"micro"`
	}
	type asPointer struct {
		When  *time.Time `json:"when"`
		Micro *time.Time `json:"micro"`
	}
	type asJSON struct {
		When  json.RawMessage `json:"when"`
		Micro json.RawMessage `json:"micro"`
	}
	types := []struct {
		name string
		plan *Plan
		new  func() any
	}{
		{"time.Time", testPlan[asTime](t), func() any { return new(asTime) }},
		{"*time.Time", testPlan[asPointer](t), func() any { return new(asPointer) }},
		{"json.RawMessage", testPlan[asJSON](t), func() any { return new(asJSON) }},
	}
	later := uint64(time.Date(2026, 10, 2, 20, 41, 7, 0, time.UTC).Unix())
	// The API server sends the zero time as an empty message, and as null in
	// JSON. It writes both fields of any other time, so the epoch's message
	// isn't empty.
	for _, tc := range []struct {
		name        string
		when, micro enc
		js          string
	}{
		{"zero", enc{}, enc{}, `{"when":null,"micro":null}`},
		{"epoch", enc{}.uint(1, 0).uint(2, 0), enc{}.uint(1, 0).uint(2, 0),
			`{"when":"1970-01-01T00:00:00Z","micro":"1970-01-01T00:00:00.000000Z"}`},
		{"later", enc{}.uint(1, later).uint(2, 0), enc{}.uint(1, later).uint(2, 123456000),
			`{"when":"2026-10-02T20:41:07Z","micro":"2026-10-02T20:41:07.123456Z"}`},
	} {
		raw := enc{}.msg(7, tc.when).msg(17, tc.micro)
		for _, ty := range types {
			fromJSON, fromProto := ty.new(), ty.new()
			if err := json.Unmarshal([]byte(tc.js), fromJSON); err != nil {
				t.Fatal(err)
			}
			if err := ty.plan.Unmarshal(raw, fromProto); err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(fromJSON, fromProto) {
				jb, _ := json.Marshal(fromJSON)
				pb, _ := json.Marshal(fromProto)
				t.Errorf("%s time into %s: JSON %s, protobuf %s", tc.name, ty.name, jb, pb)
			}
		}
	}
	// A field sent twice keeps its last value, so the empty message has to
	// clear the time decoded before it.
	var p asPointer
	dup := enc{}.msg(7, enc{}.uint(1, later).uint(2, 0)).msg(7, enc{})
	if err := testPlan[asPointer](t).Unmarshal(dup, &p); err != nil || p.When != nil {
		t.Errorf("a time, then an empty message: When = %v, %v; want nil", p.When, err)
	}
}

func TestPlanRejectsFieldsTheSchemaLacks(t *testing.T) {
	type future struct {
		Name string `json:"name"`
		Warp int    `json:"warpDrive"`
	}
	msg := testMessage(t)
	b := &builder{plans: map[planKey]*Plan{}}
	if _, err := b.plan(reflect.TypeFor[future](), msg, true); err == nil || !strings.Contains(err.Error(), "warpDrive") {
		t.Errorf("err = %v", err)
	}
	type top struct {
		APIVersion string `json:"apiVersion"`
		Kind       string `json:"kind"`
		Name       string `json:"name"`
	}
	if _, err := b.plan(reflect.TypeFor[top](), msg, true); err != nil {
		t.Errorf("apiVersion and kind are in the envelope, not the object: %v", err)
	}
}

func TestFieldNamesMatchLikeEncodingJSON(t *testing.T) {
	type named struct {
		NAME  string // no tag: matches "name" ignoring case
		Count int32  `json:"count"`
		Skip  string `json:"-"`
	}
	var got named
	if err := testPlan[named](t).Unmarshal(enc{}.str(1, "x").uint(2, 3), &got); err != nil {
		t.Fatal(err)
	}
	if got.NAME != "x" || got.Count != 3 {
		t.Errorf("got %+v", got)
	}
}

type numberOnly int

func (n *numberOnly) UnmarshalJSON(b []byte) error { return json.Unmarshal(b, (*int)(n)) }

func TestJSONFieldErrorsFailTheMessage(t *testing.T) {
	type numbers struct {
		Name string     `json:"name"`
		Port numberOnly `json:"port"`
	}
	var got numbers
	err := testPlan[numbers](t).Unmarshal(enc{}.str(1, "web").msg(9, enc{}.uint(1, 1).str(3, "http")), &got)
	if te := (*json.UnmarshalTypeError)(nil); !errors.As(err, &te) {
		t.Errorf("Unmarshal = %v, want a *json.UnmarshalTypeError", err)
	}
}

func TestEnvelopes(t *testing.T) {
	object := append(append([]byte{}, Magic...), enc{}.
		msg(1, enc{}.str(1, "v1").str(2, "Pod")).
		msg(2, enc{}.msg(1, enc{}.str(1, "web").str(3, "shop").str(5, "uid-1").str(6, "42").uint(7, 3).msg(12, enc{}.str(1, "k8s.io/initial-events-end").str(2, "true"))))...)
	apiVersion, kind, raw, err := Unwrap(object)
	if err != nil || apiVersion != "v1" || kind != "Pod" {
		t.Fatalf("Unwrap = %q %q %v", apiVersion, kind, err)
	}
	om, err := Meta(raw)
	if err != nil || om.Name != "web" || om.Namespace != "shop" || om.UID != "uid-1" || om.ResourceVersion != "42" || om.Annotations["k8s.io/initial-events-end"] != "true" {
		t.Errorf("Meta = %+v %v", om, err)
	}
	if _, _, _, err := Unwrap([]byte("{}")); err == nil {
		t.Error("Unwrap accepted JSON")
	}

	event := enc{}.str(1, "BOOKMARK").msg(2, enc{}.str(1, string(object)))
	typ, obj, err := Event(event)
	if err != nil || typ != "BOOKMARK" || string(obj) != string(object) {
		t.Errorf("Event = %q %q %v", typ, obj, err)
	}

	list := enc{}.msg(1, enc{}.str(2, "99").str(3, "next-page")).msg(2, enc{}.str(1, "a")).msg(2, enc{}.str(1, "b"))
	var names []string
	rv, cont, err := List(list, func(item []byte) error {
		names = append(names, strconv.Quote(string(item)))
		return nil
	})
	if err != nil || rv != "99" || cont != "next-page" || len(names) != 2 {
		t.Errorf("List = %q %q %v %v", rv, cont, names, err)
	}

	code, reason, message, err := Status(enc{}.str(2, "Failure").str(3, "pods \"x\" not found").str(4, "NotFound").uint(6, 404))
	if err != nil || code != 404 || reason != "NotFound" || message != `pods "x" not found` {
		t.Errorf("Status = %d %q %q %v", code, reason, message, err)
	}
}

func TestTruncatedMessages(t *testing.T) {
	var got obj
	p := testPlan[obj](t)
	for _, b := range []enc{{0x0a}, {0x0a, 0x05, 'a'}, {0x10}, {0x19, 1, 2}, {0x0b}} {
		if err := p.Unmarshal(b, &got); err == nil {
			t.Errorf("Unmarshal(%x) succeeded", []byte(b))
		}
	}
}

func TestEveryKindParses(t *testing.T) {
	s, err := newSchema(schemaText)
	if err != nil {
		t.Fatal(err)
	}
	for k := range s.kinds {
		apiVersion, kind, _ := strings.Cut(k, " ")
		if _, err := s.kind(apiVersion, kind); err != nil {
			t.Error(err)
		}
	}
	if len(s.msgs) != len(s.blocks) {
		t.Errorf("parsed %d of %d messages; some aren't reachable from any kind", len(s.msgs), len(s.blocks))
	}
}

func TestSchemaParsesOnlyWhatAKindUses(t *testing.T) {
	s, err := newSchema(schemaText)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := s.kind("v1", "ConfigMap"); err != nil {
		t.Fatal(err)
	}
	if len(s.msgs) > 10 {
		t.Errorf("reading ConfigMaps parsed %d messages", len(s.msgs))
	}
	if _, err := newSchema("message a\n\tname 1 nope\n"); err != nil {
		t.Fatal(err)
	}
	bad, _ := newSchema("kind v1 A a\nmessage a\n\tname 1 nope\n")
	if _, err := bad.kind("v1", "A"); err == nil {
		t.Error("a field with an unknown type parsed")
	}
	if _, err := bad.kind("v1", "A"); err == nil {
		t.Error("a message that failed to parse was cached")
	}
	if _, err := newSchema("bogus line"); err == nil {
		t.Error("a bogus line parsed")
	}
}

func TestSchemaHasCommonKinds(t *testing.T) {
	for _, k := range [][2]string{
		{"v1", "Pod"}, {"v1", "PodList"}, {"v1", "Secret"}, {"apps/v1", "Deployment"}, {"batch/v1", "Job"},
		{"networking.k8s.io/v1", "Ingress"}, {"coordination.k8s.io/v1", "Lease"}, {"discovery.k8s.io/v1", "EndpointSlice"},
		{"meta.k8s.io/v1", "PartialObjectMetadata"}, {"meta.k8s.io/v1", "Status"},
	} {
		if ForKind(k[0], k[1]) == nil {
			t.Errorf("the schema doesn't have %s %s", k[0], k[1])
		}
	}
	if ForKind("example.dev/v1", "Widget") != nil {
		t.Error("the schema has a custom kind")
	}
}
