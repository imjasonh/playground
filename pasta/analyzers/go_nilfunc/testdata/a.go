package a

func helper() {}

func bad() {
	if helper == nil { // want "comparison of function helper to nil"
		return
	}
	if nil != helper { // want "comparison of function helper to nil"
		return
	}
}

func okVar() {
	var f func()
	if f == nil {
		return
	}
}
