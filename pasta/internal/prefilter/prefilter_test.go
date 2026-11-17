package prefilter

import (
	"reflect"
	"regexp"
	"slices"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
)

func TestForRule_eqAndRequireSubstring(t *testing.T) {
	rule := &dsl.Rule{
		Name: "prefer_shorthand",
		Match: dsl.Pattern{
			Node: []string{"generic_type"},
			Where: []dsl.Predicate{
				{Op: "eq", Args: []dsl.Arg{{Str: "@outer"}, {Str: "Array"}}},
			},
		},
		RequireSubstring: []string{"ReadonlyArray"},
		// within tokens must NOT be inferred — diagnose can fire without them.
		Rewrite: &dsl.Rewrite{Edits: []dsl.Edit{
			{Within: "_root", Token: "var", ReplaceWith: "let"},
		}},
	}
	f := ForRule(rule)
	wantAll := []string{"ReadonlyArray", "Array"}
	if !reflect.DeepEqual(f.AllOf, wantAll) {
		t.Fatalf("AllOf = %v, want %v", f.AllOf, wantAll)
	}
	if len(f.AnyOf) != 0 {
		t.Fatalf("AnyOf = %v, want empty", f.AnyOf)
	}
}

func TestForRule_withinTokenNotRequired(t *testing.T) {
	rule := &dsl.Rule{
		Match:    dsl.Pattern{Node: []string{"variable_declaration"}},
		Diagnose: &dsl.Diagnostic{Message: "use let"},
		Rewrite: &dsl.Rewrite{Edits: []dsl.Edit{
			{Within: "_root", Token: "var", ReplaceWith: "let"},
		}},
	}
	f := ForRule(rule)
	if len(f.AllOf) != 0 || len(f.AnyOf) != 0 {
		t.Fatalf("within-only rewrite must leave filter empty, got %+v", f)
	}
	if !f.Match([]byte("const x = 1")) {
		t.Fatal("diagnose-capable rule without substring constraints must match")
	}
}

func TestForRule_matches(t *testing.T) {
	rule := &dsl.Rule{
		Match: dsl.Pattern{
			Where: []dsl.Predicate{
				{Op: "matches", Args: []dsl.Arg{{Str: "@a"}, {Str: "^(foo|bar)$"}}},
				{Op: "matches", Args: []dsl.Arg{{Str: "@b"}, {Str: "(^|::)Command::new$"}}},
				{Op: "eq", Args: []dsl.Arg{{Str: "@a"}, {Str: "@b"}}},
			},
		},
	}
	f := ForRule(rule)
	if want := []string{"Command::new"}; !reflect.DeepEqual(f.AllOf, want) {
		t.Errorf("AllOf = %v, want %v", f.AllOf, want)
	}
	if want := [][]string{{"foo", "bar"}}; !reflect.DeepEqual(f.AnyOf, want) {
		t.Errorf("AnyOf = %v, want %v", f.AnyOf, want)
	}
	for src, want := range map[string]bool{
		"foo(); Command::new(x)": true,
		"bar Command::new":       true,
		"Command::new":           false,
		"foo bar":                false,
	} {
		if got := f.Match([]byte(src)); got != want {
			t.Errorf("Match(%q) = %v, want %v", src, got, want)
		}
	}
}

func TestRegexLiterals(t *testing.T) {
	for _, tc := range []struct {
		pat  string
		want [][]string
	}{
		{"==|!=", [][]string{{"!=", "=="}}},
		{"gets", [][]string{{"gets"}}},
		{"(^|::)Command::new$", [][]string{{"Command::new"}}},
		{"^(Atoi|ParseBool)$", [][]string{{"Atoi", "ParseBool"}}},
		{"^Add(Int32|Int64)$", [][]string{{"AddInt32", "AddInt64"}}},
		{"^Parse(InLocation)?$", [][]string{{"Parse"}}},
		{"^\\*?(slog|clog)\\.Logger$", [][]string{{"slog.Logger", "clog.Logger"}}},
		{"\\bextends\\b", [][]string{{"extends"}}},
		{"foo.*bar", [][]string{{"foo"}, {"bar"}}},
		{"(?s)^curl\\b.*(-k|--insecure)\\b", [][]string{{"curl"}, {"-k", "--insecure"}}},
		{"(a+bc|de)x", [][]string{{"bc", "de"}, {"x"}}},
		{"x{2,}", [][]string{{"x"}}},
		{"", nil},
		{"^_|_$", [][]string{{"_"}}},
		{"(?i)^html$", nil},
		{"[a-z]+", nil},
		{"foo|.*", nil},
		{"a?", nil},
		{"x*y?", nil},
		{"(", nil},
	} {
		got := regexLiterals(tc.pat)
		for _, g := range got {
			slices.Sort(g)
		}
		for _, g := range tc.want {
			slices.Sort(g)
		}
		if !reflect.DeepEqual(got, tc.want) {
			t.Errorf("regexLiterals(%q) = %q, want %q", tc.pat, got, tc.want)
		}
	}
}

// TestRegexLiteralsSound checks, for strings each regex matches, that
// every group has a literal in the string.
func TestRegexLiteralsSound(t *testing.T) {
	for pat, matches := range map[string][]string{
		"^(===|!==|==|!=)$":             {"===", "!==", "==", "!="},
		"^Parse(InLocation)?$":          {"Parse", "ParseInLocation"},
		"(^|\\s)\\*?context\\.Context$": {"context.Context", "x *context.Context"},
		"[!=]=+x?":                      {"==", "!===x"},
		"\\s(-k|--insecure)\\b":         {" -k", "\t--insecure"},
	} {
		re := regexp.MustCompile(pat)
		groups := regexLiterals(pat)
		if len(groups) == 0 {
			t.Errorf("regexLiterals(%q) = none", pat)
		}
		for _, m := range matches {
			if !re.MatchString(m) {
				t.Fatalf("%q doesn't match %q", pat, m)
			}
			if !(Filter{AnyOf: groups}).Match([]byte(m)) {
				t.Errorf("groups %q of %q reject %q", groups, pat, m)
			}
		}
	}
}

func TestFilterMatch_allOf(t *testing.T) {
	f := Filter{AllOf: []string{"Object", "assign"}}
	if f.Match([]byte("Object.keys(x)")) {
		t.Fatal("expected miss without assign")
	}
	if !f.Match([]byte("Object.assign({}, x)")) {
		t.Fatal("expected hit for Object.assign")
	}
}

func TestFilterMatch_anyOf(t *testing.T) {
	f := Filter{AnyOf: [][]string{{"==", "!="}}}
	if f.Match([]byte("a + b")) {
		t.Fatal("expected miss")
	}
	if !f.Match([]byte("a == b")) {
		t.Fatal("expected hit on ==")
	}
	if !f.Match([]byte("a != b")) {
		t.Fatal("expected hit on !=")
	}
}
