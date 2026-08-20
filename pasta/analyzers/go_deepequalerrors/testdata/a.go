package a

import (
	"errors"
	"fmt"
	"reflect"
)

func badNew() bool {
	return reflect.DeepEqual(errors.New("x"), nil) // want "avoid using reflect.DeepEqual with error values"
}

func badNewSecond() bool {
	return reflect.DeepEqual(nil, errors.New("x")) // want "avoid using reflect.DeepEqual with error values"
}

func badErrorf() bool {
	return reflect.DeepEqual(fmt.Errorf("x"), nil) // want "avoid using reflect.DeepEqual with error values"
}

func ok() bool {
	return reflect.DeepEqual(1, 1)
}
