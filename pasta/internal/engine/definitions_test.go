package engine

import (
	"slices"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/lang"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// TestDefinitionTypes checks that every node type a language lists in
// definition_types occurs in a sample and has a `name` field holding an
// identifier the fact store indexes.
func TestDefinitionTypes(t *testing.T) {
	samples := map[string]string{
		"go":         "package p\n\nfunc f() {}\n\nfunc (r R) m() {}\n",
		"python":     "def f():\n    pass\n",
		"javascript": "function f() {}\nfunction* g() {}\nclass C { m() {} }\n",
		"typescript": "function f(): void {}\nfunction* g() {}\nclass C { m(): void {} }\n",
		"tsx":        "function f(): void {}\nfunction* g() {}\nclass C { m(): void {} }\n",
		"rust":       "fn f() {}\n",
		"java":       "class C { void m() {} }\n",
		"ruby":       "def f\nend\n\ndef self.g\nend\n",
	}
	identifiers := []string{"identifier", "field_identifier", "property_identifier"}
	for name, l := range lang.All {
		if len(l.DefinitionTypes) == 0 {
			continue
		}
		t.Run(name, func(t *testing.T) {
			src, ok := samples[name]
			if !ok {
				t.Fatalf("no sample for %s, which declares definition_types %v", name, l.DefinitionTypes)
			}
			tree, root, err := tsutil.Parse(t.Context(), l.GetLanguage(), []byte(src), name)
			if err != nil {
				t.Fatal(err)
			}
			defer tree.Release()
			seen := map[string]bool{}
			tsutil.Walk(root, func(n tsutil.Node) bool {
				if !slices.Contains(l.DefinitionTypes, n.Type()) {
					return true
				}
				seen[n.Type()] = true
				id := n.ChildByFieldName("name")
				if !id.IsValid() || !slices.Contains(identifiers, id.Type()) {
					t.Errorf("%s %q: name field is %q, want one of %v", n.Type(), n.Text(), id.Type(), identifiers)
				}
				return true
			})
			for _, typ := range l.DefinitionTypes {
				if !seen[typ] {
					t.Errorf("the sample has no %s", typ)
				}
			}
		})
	}
}
