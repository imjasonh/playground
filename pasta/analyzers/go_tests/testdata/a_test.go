package a

import "testing"

func TestMissing() { // want "wrong signature for Test function"
}

func TestOk(t *testing.T) {
	_ = t
}

func Testfoo(t *testing.T) { // want "malformed name"
	_ = t
}

func BenchmarkMissing() { // want "wrong signature for Benchmark function"
}

func BenchmarkOk(b *testing.B) {
	_ = b
}

func FuzzMissing() { // want "wrong signature for Fuzz function"
}

func FuzzOk(f *testing.F) {
	_ = f
}

func TestMain(m *testing.M) {
	m.Run()
}

func helper() {}
