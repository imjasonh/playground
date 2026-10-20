package observe

import "testing"

func TestParseCloudTrace(t *testing.T) {
	traceID, spanID, sampled, ok := parseCloudTrace("0123456789abcdef0123456789abcdef/17;o=1")
	if !ok || !sampled {
		t.Fatalf("parsed ok=%v sampled=%v", ok, sampled)
	}
	if traceID.String() != "0123456789abcdef0123456789abcdef" {
		t.Fatalf("trace = %s", traceID)
	}
	if spanID.String() != "0000000000000011" {
		t.Fatalf("span = %s", spanID)
	}
	if _, _, _, ok := parseCloudTrace("not-a-header"); ok {
		t.Fatal("accepted a bad header")
	}
}
