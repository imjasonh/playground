package a

func redundant(x, y bool) bool {
	a := x || x // want "redundant or"
	b := x && x // want "redundant and"
	c := x || y
	d := x && y
	return a && b && c && d
}

func suspect(x int) bool {
	a := x != 1 || x != 2 // want "suspect or"
	b := x == 1 && x == 2 // want "suspect and"
	c := x != 1 || x == 2
	d := x == 1 && x == 1
	return a && b && c && d
}
