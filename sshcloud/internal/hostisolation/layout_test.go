package hostisolation

import "testing"

func TestFixedIdentifierValidation(t *testing.T) {
	t.Parallel()
	const id = "0123abcdef89"
	if err := ValidateVMID(id); err != nil {
		t.Fatal(err)
	}
	if got, err := VMIDFromWorkDir("/var/lib/sshcloud/agent/vm-" + id); err != nil || got != id {
		t.Fatalf("VMIDFromWorkDir = %q, %v", got, err)
	}
	if got, err := TapName(id); err != nil || got != "fc-"+id {
		t.Fatalf("TapName = %q, %v", got, err)
	}
	if got, err := VMIDFromTapName("fc-" + id); err != nil || got != id {
		t.Fatalf("VMIDFromTapName = %q, %v", got, err)
	}

	for _, bad := range []string{"", "../0123abcdef89", "0123ABCDEF89", "0123abcdef8", "0123abcdef890"} {
		if err := ValidateVMID(bad); err == nil {
			t.Errorf("ValidateVMID(%q) succeeded", bad)
		}
	}
	for _, bad := range []string{"../rootfs.ext4", "/rootfs.ext4", ""} {
		if _, err := WorkRelativePath(id, bad); err == nil {
			t.Errorf("WorkRelativePath accepted segment %q", bad)
		}
	}
}

func TestSandboxIDIsStableAndSeparated(t *testing.T) {
	t.Parallel()
	first, err := SandboxID("0123abcdef89")
	if err != nil {
		t.Fatal(err)
	}
	again, _ := SandboxID("0123abcdef89")
	second, _ := SandboxID("1123abcdef89")
	if first != again {
		t.Fatalf("sandbox ID changed: %d != %d", first, again)
	}
	if first == second {
		t.Fatalf("test VM IDs collided at sandbox ID %d", first)
	}
	if first < sandboxIDBase {
		t.Fatalf("sandbox ID %d is below base", first)
	}
}

func TestValidateHostIP(t *testing.T) {
	t.Parallel()
	if err := ValidateHostIP("172.16.200.1", "172.16"); err != nil {
		t.Fatal(err)
	}
	for _, bad := range []string{"172.16.0.1", "172.16.201.1", "172.16.2.2", "172.17.2.1", "0172.16.2.1"} {
		if err := ValidateHostIP(bad, "172.16"); err == nil {
			t.Errorf("ValidateHostIP(%q) succeeded", bad)
		}
	}
}
