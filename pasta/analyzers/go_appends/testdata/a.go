package a

func bad(s []int) []int {
	return append(s) // want "append with no values"
}

func ok(s []int) []int {
	return append(s, 1)
}

func okSpread(s, t []int) []int {
	return append(s, t...)
}
