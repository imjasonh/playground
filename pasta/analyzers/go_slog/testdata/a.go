package a

import "log/slog"

func bad() {
	slog.Info("msg", "key") // want "missing key or value"
}

func okMsg() {
	slog.Info("msg")
}

func okKV() {
	slog.Info("msg", "key", "value")
}

func okAttr() {
	slog.Info("msg", slog.String("key", "value"))
}
