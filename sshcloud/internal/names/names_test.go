package names

import "testing"

func TestValidateIdent(t *testing.T) {
	t.Parallel()
	cases := []struct {
		name    string
		wantErr bool
	}{
		{"alice", false},
		{"fortune", false},
		{"my-app", false},
		{"ab", true},
		{"", true},
		{"Join", true},
		{"join", true},
		{"deploy", true},
		{"menu", true},
		{"-bad", true},
		{"has_underscore", true},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			err := ValidateIdent(tc.name)
			if tc.wantErr && err == nil {
				t.Fatalf("expected error")
			}
			if !tc.wantErr && err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
		})
	}
}

func TestIsReserved(t *testing.T) {
	t.Parallel()
	if !IsReserved("join") || !IsReserved("menu") {
		t.Fatal("expected join/menu reserved")
	}
	if IsReserved("fortune") {
		t.Fatal("fortune should not be reserved")
	}
}
