package app

func writeFile(name string) error { return nil }

func cleanup() error { return nil }

func save() {
	// want:+1 `error return value of writeFile is discarded`
	writeFile("out")
}
