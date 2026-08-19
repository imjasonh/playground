package a

import "fmt"

func bad(host string, port int) string {
	return fmt.Sprintf("%s:%d", host, port) // want "does not work with IPv6"
}

func badString(host, port string) string {
	return fmt.Sprintf("%s:%s", host, port) // want "does not work with IPv6"
}

func ok(host string, port int) string {
	return fmt.Sprintf("%s is on %d", host, port)
}
