package tsutil

import (
	"testing"

	"github.com/odvcencio/gotreesitter/grammars"
)

func TestErrorHeavy(t *testing.T) {
	cases := []struct {
		name  string
		src   string
		heavy bool
	}{
		{"clean", "const x = 1;\n", false},
		{"trailing brace (degraded, not heavy)", "const x = 1;\n}\n", false},
		{"broken object literal", "const x = {{{{\n", true},
		{"garbage", "{{{{{{\n{{{{{{\n", true},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			tree, root, err := Parse(t.Context(), grammars.JavascriptLanguage(), []byte(tc.src), "")
			if err != nil {
				t.Fatal(err)
			}
			defer tree.Release()
			if got := ErrorHeavy(root); got != tc.heavy {
				t.Fatalf("ErrorHeavy=%v want %v (HasError=%v root.IsError=%v)",
					got, tc.heavy, root.HasError(), root.IsError())
			}
		})
	}
}
