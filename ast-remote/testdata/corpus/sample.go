package main

func greet(name string) string {
	return "hello, " + name
}

func main() {
	println(greet("world"))
	for i := 0; i < 3; i++ {
		println(i, greet("world"))
	}
}
