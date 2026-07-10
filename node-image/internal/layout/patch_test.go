package layout_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layout"
)

func TestApplyPatchAddsMarker(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "index.js"), []byte("module.exports=1;\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	patch := filepath.Join(dir, "x.patch")
	body := `diff --git a/index.js b/index.js
--- a/index.js
+++ b/index.js
@@ -1 +1,2 @@
 module.exports=1;
+
+// patched
`
	if err := os.WriteFile(patch, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := layout.ApplyPatch(dir, patch); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dir, "index.js"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(b), "patched") {
		t.Fatalf("patch not applied: %s", b)
	}
}
