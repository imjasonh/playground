package tsutil

import (
	"testing"

	"github.com/imjasonh/playground/pasta/internal/tswasm"
)

func TestErrorHeavy(t *testing.T) {
	cases := []struct {
		name  string
		src   string
		heavy bool
	}{
		{"clean", "const x = 1;\n", false},
		// Official C tree-sitter recovers trailing glitches with a
		// single ERROR — degraded, not heavy (same as gotreesitter).
		{"trailing brace (degraded, not heavy)", "const x = 1;\n}\n", false},
		// C tree-sitter recovers nested `{` more cleanly than the
		// pure-Go port (often one ERROR). Use denser garbage for heavy.
		{"broken object literal (recovered)", "const x = {{{{\n", false},
		{"brace garbage", "{{{{{{\n{{{{{{\n", true},
		{"mixed garbage", "!!!!!!!\n@@@@@@@\n#######\n", true},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			tree, root, err := Parse(t.Context(), &tswasm.Language{Grammar: "javascript"}, []byte(tc.src), "")
			if err != nil {
				t.Fatal(err)
			}
			defer tree.Release()
			if got := ErrorHeavy(root); got != tc.heavy {
				t.Fatalf("ErrorHeavy=%v want %v (HasError=%v root.IsError=%v type=%q)",
					got, tc.heavy, root.HasError(), root.IsError(), root.Type())
			}
		})
	}
}
