package a

type T struct{}

func (this T) A() {} // want "not this or self"

func (self *T) B() {} // want "not this or self"

func (_ T) C() {} // want "omit an unused receiver"

func (t T) D() {}

func (t *T) E() {}

func F() {}
