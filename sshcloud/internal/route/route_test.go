package route

import "testing"

func TestResolveUnknownKeyAlwaysJoin(t *testing.T) {
	t.Parallel()
	for _, user := range []string{"", "alice", "fortune", "join", "deploy", "menu"} {
		d := Resolve(Input{SSHUser: user, KeyKnown: false})
		if d.Kind != Join {
			t.Fatalf("user %q: got %v, want join", user, d.Kind)
		}
	}
}

func TestResolveKnownKey(t *testing.T) {
	t.Parallel()
	has := func(app string) bool { return app == "fortune" || app == "myapp" }

	cases := []struct {
		user string
		kind Kind
		app  string
	}{
		{"join", Join, ""},
		{"deploy", Deploy, ""},
		{"menu", Menu, ""},
		{"", Menu, ""},
		{"fortune", App, "fortune"},
		{"myapp", App, "myapp"},
		{"laptop-user", Menu, ""}, // bare ssh foo.com footgun path → menu
		{"help", Menu, ""},
		{"root", Menu, ""},
	}
	for _, tc := range cases {
		t.Run(tc.user+"_"+tc.kind.String(), func(t *testing.T) {
			t.Parallel()
			d := Resolve(Input{SSHUser: tc.user, KeyKnown: true, HasApp: has})
			if d.Kind != tc.kind || d.App != tc.app {
				t.Fatalf("got kind=%v app=%q, want kind=%v app=%q", d.Kind, d.App, tc.kind, tc.app)
			}
		})
	}
}
