package sshtea

import (
	"testing"

	tea "charm.land/bubbletea/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
)

func TestMiddlewareIsWishMiddleware(t *testing.T) {
	var _ wish.Middleware = Middleware(func(ssh.Session) (tea.Model, []tea.ProgramOption) {
		return nil, nil
	})
}
