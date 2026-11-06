package app

import "example.com/pkg"

func use() {
	pkg.Old() // want `Old is deprecated`
	pkg.New() // OK

	var c pkg.Client
	c.Post() // want `Post is deprecated`
	c.Send() // OK
}
