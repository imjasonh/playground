package client

func run() {
	cleanup() // OK: binds to the cleanup in this directory, which returns nothing
}
