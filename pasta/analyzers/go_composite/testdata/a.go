package a

import "go/token"

func bad() token.Position {
	return token.Position{1, 2, 3, 4} // want "unkeyed composite literal"
}

func okKeyed() token.Position {
	return token.Position{Line: 1}
}

func okLocal() T {
	return T{1, 2}
}

func okSlice() []int {
	return []int{1, 2}
}

type T struct{ A, B int }
