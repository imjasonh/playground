package a

type T struct{}

func (T) String() { // want "method String() should have signature String() string"
}

func (T) Error() { // want "method Error() should have signature Error() string"
}

func (T) ReadByte() byte { // want "method ReadByte() should have signature ReadByte() (byte, error)"
	return 0
}

func (T) OkString() string {
	return "ok"
}

func (T) StringInt() int { return 0 }

type W struct{}

func (W) String() int { // want "method String() should have signature String() string"
	return 0
}

type U struct{}

func (U) String() string { return "u" }

func (U) Error() string { return "u" }

func (U) ReadByte() (byte, error) { return 0, nil }
