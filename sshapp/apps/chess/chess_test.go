package main

import (
	"testing"
	"time"
)

func TestCloneIsolatesBoards(t *testing.T) {
	g := NewGame()
	c := g.Clone()
	from := Position{1, 4} // e2
	to := Position{3, 4}   // e4
	if !g.MakeMove(from, to) {
		t.Fatal("e2e4")
	}
	if c.Board.At(from).Type != Pawn || c.Board.At(to).Type != Empty {
		t.Fatalf("clone mutated: from=%v to=%v", c.Board.At(from), c.Board.At(to))
	}
	if c.CurrentTurn != White {
		t.Fatalf("clone turn = %v", c.CurrentTurn)
	}
}

func TestMakeMovePawnAndTurn(t *testing.T) {
	g := NewGame()
	if !g.MakeMove(Position{1, 4}, Position{3, 4}) {
		t.Fatal("white e2e4")
	}
	if g.CurrentTurn != Black {
		t.Fatalf("turn = %v", g.CurrentTurn)
	}
	if !g.MakeMove(Position{6, 4}, Position{4, 4}) {
		t.Fatal("black e7e5")
	}
	if g.CurrentTurn != White {
		t.Fatalf("turn = %v", g.CurrentTurn)
	}
}

func TestRejectsMovingOpponentPiece(t *testing.T) {
	g := NewGame()
	if g.MakeMove(Position{6, 4}, Position{4, 4}) {
		t.Fatal("white must not move black pawn")
	}
}

func TestMatchmakingPairsTwoPlayers(t *testing.T) {
	gm := &GameManager{
		playerQueue:  make([]*Player, 0),
		activeGames:  make(map[string]*GameSession),
		playerToGame: make(map[string]string),
	}
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 2)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 2)}
	gm.AddPlayer(a)
	if len(gm.activeGames) != 0 {
		t.Fatal("single player should wait")
	}
	gm.AddPlayer(b)
	if len(gm.activeGames) != 1 {
		t.Fatalf("games=%d", len(gm.activeGames))
	}
	select {
	case u := <-a.UpdateChan:
		if u.Type != "matched" {
			t.Fatalf("alice got %q", u.Type)
		}
	case <-time.After(time.Second):
		t.Fatal("alice matched timeout")
	}
	select {
	case u := <-b.UpdateChan:
		if u.Type != "matched" {
			t.Fatalf("bob got %q", u.Type)
		}
	case <-time.After(time.Second):
		t.Fatal("bob matched timeout")
	}
}

func TestRemovePlayerNotifiesOpponent(t *testing.T) {
	gm := &GameManager{
		playerQueue:  make([]*Player, 0),
		activeGames:  make(map[string]*GameSession),
		playerToGame: make(map[string]string),
	}
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	gm.AddPlayer(a)
	gm.AddPlayer(b)
	<-a.UpdateChan // matched
	<-b.UpdateChan

	gm.RemovePlayer(a.ID)
	select {
	case u := <-b.UpdateChan:
		if u.Type != "opponent_disconnected" {
			t.Fatalf("got %q", u.Type)
		}
	case <-time.After(time.Second):
		t.Fatal("disconnect notify timeout")
	}
}

func TestBroadcastAfterCleanupDoesNotPanic(t *testing.T) {
	gm := &GameManager{
		playerQueue:  make([]*Player, 0),
		activeGames:  make(map[string]*GameSession),
		playerToGame: make(map[string]string),
	}
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	gm.AddPlayer(a)
	gm.AddPlayer(b)
	<-a.UpdateChan
	<-b.UpdateChan
	gm.RemovePlayer(a.ID)
	gm.RemovePlayer(b.ID)
	// Must not panic on closed Updates channel.
	gm.BroadcastUpdate(a.ID, GameUpdate{Type: "move"})
}
