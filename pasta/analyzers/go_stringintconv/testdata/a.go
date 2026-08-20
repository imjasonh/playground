package a

func bad() string {
	return string(123) // want "conversion from integer to string yields a string of one rune"
}

func okRune() string {
	return string(rune(123))
}

func okIdent(b []byte) string {
	return string(b)
}
