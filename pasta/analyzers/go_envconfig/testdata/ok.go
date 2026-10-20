package ok

import (
	"os"
	"strconv"
	"time"
)

func ok(spec string, header string) {
	v := os.Getenv("NAME")
	println(v)
	n, _ := strconv.Atoi(header)
	d, _ := time.ParseDuration(spec)
	_, _ = strconv.ParseBool("true")
	_, _ = strconv.Atoi(os.Args[1])

	if v := os.Getenv("NAME"); v != "" {
		println(v)
	}
	if v := os.Getenv("LATE"); v != "" {
		println(v)
		n, _ = strconv.Atoi(v)
	}

	port := os.Getenv("PORT")
	println(port)
	n, _ = strconv.Atoi(header)
	_ = n
	_ = d
}
