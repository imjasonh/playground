package a

func bad(x int) int {
	a := x << 64 // want "shift count 64 is too large"
	b := x >> 100 // want "shift count 100 is too large"
	return a + b
}

func ok(x int) int {
	return x << 3
}

func ok63(x int64) int64 {
	return x << 63
}
