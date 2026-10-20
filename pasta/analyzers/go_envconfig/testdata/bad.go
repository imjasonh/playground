package bad

import (
	"os"
	"strconv"
	"time"
)

func calls() {
	_, _ = time.ParseDuration(os.Getenv("T"))           // want "go-envconfig"
	_, _ = strconv.Atoi(os.Getenv("N"))                 // want "go-envconfig"
	_, _ = strconv.ParseBool(os.Getenv("B"))            // want "go-envconfig"
	_, _ = strconv.ParseInt(os.Getenv("I"), 10, 64)     // want "go-envconfig"
	_, _ = strconv.ParseUint(os.Getenv("U"), 10, 64)    // want "go-envconfig"
	_, _ = strconv.ParseFloat(os.Getenv("F"), 64)       // want "go-envconfig"
	_, _ = time.ParseDuration(os.LookupEnv("LOOKCALL")) // want "go-envconfig"
}

func next() {
	v := os.Getenv("NEXT") // want "go-envconfig"
	n, err := strconv.Atoi(v)
	_, _ = n, err
}

func nextLookup() {
	v, ok := os.LookupEnv("LOOK2") // want "go-envconfig"
	f, err := strconv.ParseFloat(v, 64)
	_, _, _ = f, err, ok
}

func ifGet() {
	if v := os.Getenv("IF"); v != "" { // want "go-envconfig"
		d, err := time.ParseDuration(v)
		if err != nil {
			return
		}
		_ = d
	}
}

func ifLookup() {
	if v, ok := os.LookupEnv("LOOK"); ok { // want "go-envconfig"
		n, err := strconv.Atoi(v)
		_, _ = n, err
	}
}
