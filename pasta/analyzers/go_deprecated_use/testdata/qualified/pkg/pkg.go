package pkg

// Deprecated: use New.
func Old() {}

func New() {}

type Client struct{}

// Deprecated: use Send.
func (Client) Post() {}

func (Client) Send() {}
