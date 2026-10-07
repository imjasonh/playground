package main

import (
	"fmt"
	"go/format"
	"strconv"
	"strings"
)

// The test repositories are Go modules that use only the standard library,
// except for a high-risk branch that requires example.com/greet, which
// go-cache gets from the module proxy that setup.sh starts.

const conflictPairs = 8

func baseFiles() map[string]string {
	files := map[string]string{
		"go.mod":    "module example.com/app\n\ngo 1.24\n",
		"README.md": "# app\n\nA test repository for the git-k8s stress harness.\n",
		"main.go": `// Command app prints a few values.
package main

import (
	"fmt"

	"example.com/app/calc"
	"example.com/app/text"
)

func main() {
	fmt.Println(calc.Fib(10), text.Reverse("stress"))
}
`,
		"calc/calc.go": `// Package calc does arithmetic.
package calc

// Add returns a + b.
func Add(a, b int) int { return a + b }

// Fib returns the nth Fibonacci number.
func Fib(n int) int {
	a, b := 0, 1
	for range n {
		a, b = b, a+b
	}
	return a
}
`,
		"calc/calc_test.go": `package calc

import "testing"

func TestAdd(t *testing.T) {
	if got := Add(2, 3); got != 5 {
		t.Fatalf("Add(2, 3) = %d, want 5", got)
	}
}

func TestFib(t *testing.T) {
	for n, want := range []int{0, 1, 1, 2, 3, 5, 8, 13} {
		if got := Fib(n); got != want {
			t.Errorf("Fib(%d) = %d, want %d", n, got, want)
		}
	}
}
`,
		"text/text.go": `// Package text transforms strings.
package text

import "strings"

// Reverse returns s with its runes in reverse order.
func Reverse(s string) string {
	r := []rune(s)
	for i, j := 0, len(r)-1; i < j; i, j = i+1, j-1 {
		r[i], r[j] = r[j], r[i]
	}
	return string(r)
}

// Words splits s into words.
func Words(s string) []string { return strings.Fields(s) }
`,
		"text/text_test.go": `package text

import (
	"slices"
	"testing"
)

func TestReverse(t *testing.T) {
	if got := Reverse("abc"); got != "cba" {
		t.Fatalf("Reverse(abc) = %q, want cba", got)
	}
}

func TestWords(t *testing.T) {
	if got := Words(" a b  c "); !slices.Equal(got, []string{"a", "b", "c"}) {
		t.Fatalf("Words = %q", got)
	}
}
`,
		"store/store.go": `// Package store keeps values in memory.
package store

import "sync"

// Store maps keys to values. Its methods are safe for concurrent use.
type Store struct {
	mu sync.Mutex
	m  map[string]string
}

// Set sets key to value.
func (s *Store) Set(key, value string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.m == nil {
		s.m = map[string]string{}
	}
	s.m[key] = value
}

// Get returns the value of key.
func (s *Store) Get(key string) (string, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	v, ok := s.m[key]
	return v, ok
}
`,
		"store/store_test.go": `package store

import (
	"fmt"
	"sync"
	"testing"
)

func TestStore(t *testing.T) {
	var s Store
	var wg sync.WaitGroup
	for i := range 100 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			s.Set(fmt.Sprint(i), fmt.Sprint(i*i))
		}()
	}
	wg.Wait()
	if v, ok := s.Get("7"); !ok || v != "49" {
		t.Fatalf("Get(7) = %q, %v", v, ok)
	}
}
`,
		"conflict/conflict.go": "// Package conflict has one line for each pair of branches that change the same line.\npackage conflict\n",
	}
	var owners []string
	for k := 1; k <= conflictPairs; k++ {
		files[conflictFile(k)] = conflictSource(k, "base")
		owners = append(owners, fmt.Sprintf("Owner%d", k))
	}
	files["conflict/conflict_test.go"] = fmt.Sprintf(`package conflict

import "testing"

func TestOwners(t *testing.T) {
	for i, owner := range []string{%s} {
		if owner == "" {
			t.Errorf("Owner%%d is empty", i+1)
		}
	}
}
`, strings.Join(owners, ", "))
	return files
}

func conflictFile(k int) string { return fmt.Sprintf("conflict/p%d.go", k) }

func conflictSource(k int, owner string) string {
	return fmt.Sprintf("package conflict\n\n// Owner%d names the branches that changed this line.\nconst Owner%d = %q\n", k, k, owner)
}

// featureNumber returns the number in a feature id such as f007.
func featureNumber(id string) int {
	n, _ := strconv.Atoi(strings.TrimLeft(id, "fw"))
	return n
}

func featureSource(id string) string {
	return gofmt(fmt.Sprintf(`// Package %[1]s is feature %[2]d.
package %[1]s

// Value returns the feature's number.
func Value() int { return %[2]d }

// Sum returns Value() + 2*Value() + ... + n*Value().
func Sum(n int) int {
	s := 0
	for i := 1; i <= n; i++ {
		s += i * Value()
	}
	return s
}
`, id, featureNumber(id)))
}

// unformattedSource is featureSource as gofmt wouldn't write it.
func unformattedSource(id string) string {
	return fmt.Sprintf(`// Package %[1]s is feature %[2]d.
package %[1]s
// Value returns the feature's number.
func Value()  int {return %[2]d}
// Sum returns Value() + 2*Value() + ... + n*Value().
func Sum(n int) int {
s := 0
for i := 1; i <= n; i++ { s += i*Value() }
return s
}
`, id, featureNumber(id))
}

// featureTest tests featureSource, and fails when want isn't the feature's
// number.
func featureTest(id string, want int) string {
	return gofmt(fmt.Sprintf(`package %[1]s

import "testing"

func TestValue(t *testing.T) {
	if got := Value(); got != %[2]d {
		t.Fatalf("Value() = %%d, want %[2]d", got)
	}
}

func TestSum(t *testing.T) {
	if got, want := Sum(3), 6*Value(); got != want {
		t.Fatalf("Sum(3) = %%d, want %%d", got, want)
	}
}
`, id, want))
}

// bigTable adds more than 200 lines, which makes the change high risk.
func bigTable(id string) (string, string) {
	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n// table holds the first 240 squares.\nvar table = [...]int{\n", id)
	for i := range 240 {
		fmt.Fprintf(&b, "\t%d,\n", i*i)
	}
	b.WriteString("}\n\n// Square returns i*i for i below 240.\nfunc Square(i int) int { return table[i] }\n")
	test := fmt.Sprintf(`package %s

import "testing"

func TestSquare(t *testing.T) {
	for i := range 240 {
		if got := Square(i); got != i*i {
			t.Fatalf("Square(%%d) = %%d", i, got)
		}
	}
}
`, id)
	return gofmt(b.String()), gofmt(test)
}

func greetSource(id string) (string, string) {
	src := fmt.Sprintf("package %[1]s\n\nimport \"example.com/greet\"\n\n// Greeting greets the feature.\nfunc Greeting() string { return greet.Hello(%[1]q) }\n", id)
	test := fmt.Sprintf(`package %[1]s

import "testing"

func TestGreeting(t *testing.T) {
	if got := Greeting(); got != "Hello, %[1]s" {
		t.Fatalf("Greeting() = %%q", got)
	}
}
`, id)
	return gofmt(src), gofmt(test)
}

func gofmt(src string) string {
	b, err := format.Source([]byte(src))
	if err != nil {
		panic(fmt.Sprintf("formatting generated source: %v\n%s", err, src))
	}
	return string(b)
}

// commitPlan is one commit that a branch's developer makes.
type commitPlan struct {
	message string
	files   map[string]string
}

// branchCommits returns the commits that the developer of b pushes first.
// greetSum is the go.sum line for example.com/greet.
func branchCommits(b branchPlan, greetSum string) []commitPlan {
	dir := "feat/" + b.ID + "/"
	src, test := featureSource(b.ID), featureTest(b.ID, featureNumber(b.ID))
	files := map[string]string{dir + b.ID + ".go": src, dir + b.ID + "_test.go": test}
	msg := "Add " + b.ID
	switch b.Kind {
	case kindUnformatted:
		files[dir+b.ID+".go"] = unformattedSource(b.ID)
	case kindFailing:
		files[dir+b.ID+"_test.go"] = featureTest(b.ID, featureNumber(b.ID)+1)
	case kindConflict:
		files[conflictFile(b.Pair)] = conflictSource(b.Pair, b.Name)
		msg = fmt.Sprintf("Add %s and claim conflict line %d", b.ID, b.Pair)
	case kindBigRisk:
		table, tableTest := bigTable(b.ID)
		files[dir+"table.go"], files[dir+"table_test.go"] = table, tableTest
		msg = "Add " + b.ID + " with a table of squares"
	case kindModRisk:
		greet, greetTest := greetSource(b.ID)
		files[dir+"greet.go"], files[dir+"greet_test.go"] = greet, greetTest
		files["go.mod"] = "module example.com/app\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n"
		files["go.sum"] = greetSum
		msg = "Add " + b.ID + ", which greets with example.com/greet"
	case kindMulti:
		return []commitPlan{
			{"Add " + b.ID, map[string]string{dir + b.ID + ".go": src}},
			{"Test " + b.ID, map[string]string{dir + b.ID + "_test.go": test}},
			{"Document " + b.ID, map[string]string{dir + "README.md": fmt.Sprintf("# %s\n\nFeature %d.\n", b.ID, featureNumber(b.ID))}},
		}
	}
	return []commitPlan{{msg, files}}
}

// expectedFiles returns files that main must have, with their contents,
// once b lands.
func expectedFiles(b branchPlan) map[string]string {
	dir := "feat/" + b.ID + "/"
	files := map[string]string{dir + b.ID + ".go": featureSource(b.ID), dir + b.ID + "_test.go": featureTest(b.ID, featureNumber(b.ID))}
	switch b.Kind {
	case kindUnformatted:
		files[dir+b.ID+".go"] = gofmt(unformattedSource(b.ID))
	case kindBigRisk:
		files[dir+"table.go"], files[dir+"table_test.go"] = bigTable(b.ID)
	case kindModRisk:
		files[dir+"greet.go"], files[dir+"greet_test.go"] = greetSource(b.ID)
	case kindMulti:
		files[dir+"README.md"] = fmt.Sprintf("# %s\n\nFeature %d.\n", b.ID, featureNumber(b.ID))
	}
	return files
}
