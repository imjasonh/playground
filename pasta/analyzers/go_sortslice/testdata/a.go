package a

import "sort"

func badZero(s []int) {
	sort.Slice(s, func() bool { // want "comparison function must have two parameters"
		return false
	})
}

func badOne(s []int) {
	sort.Slice(s, func(i int) bool { // want "comparison function must have two parameters"
		return s[i] < s[0]
	})
}

func badUnnamed(s []int) {
	sort.Slice(s, func(int) bool { // want "comparison function must have two parameters"
		return false
	})
}

func ok(s []int) {
	sort.Slice(s, func(i, j int) bool {
		return s[i] < s[j]
	})
}

func okUnnamed(s []int) {
	sort.Slice(s, func(int, int) bool {
		return false
	})
}
