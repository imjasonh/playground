package a

import (
	"os"
	"os/signal"
)

func bad() {
	signal.Notify(make(chan os.Signal), os.Interrupt) // want "misuse of unbuffered os.Signal channel"
}

func ok() {
	signal.Notify(make(chan os.Signal, 1), os.Interrupt)
}

func okVar() {
	ch := make(chan os.Signal, 1)
	signal.Notify(ch, os.Interrupt)
}
