package a

import "net/http"

func bad(url string) {
	resp, err := http.Get(url) // want "using resp before checking for errors"
	defer resp.Body.Close()
	if err != nil {
		return
	}
	_ = resp
}

func ok(url string) {
	resp, err := http.Get(url)
	if err != nil {
		return
	}
	defer resp.Body.Close()
	_ = resp
}

func okPost(url string) {
	resp, err := http.Post(url, "", nil)
	if err != nil {
		return
	}
	defer resp.Body.Close()
	_ = resp
}
