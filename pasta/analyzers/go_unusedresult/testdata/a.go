package a

import (
	"context"
	"errors"
	"fmt"
	"slices"
	"sort"
)

func bad() {
	fmt.Sprintf("x") // want "result of fmt call not used"
	errors.New("x")  // want "result of errors call not used"
	context.WithCancel(context.Background()) // want "result of context call not used"
	slices.Clone([]int{1})                   // want "result of slices call not used"
	sort.Reverse(sort.IntSlice{})            // want "result of sort call not used"
}

func ok() {
	_ = fmt.Sprintf("x")
	err := errors.New("x")
	_ = err
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	_ = ctx
	s := slices.Clone([]int{1})
	_ = s
	_ = sort.Reverse(sort.IntSlice{})
	fmt.Println("used")
}
