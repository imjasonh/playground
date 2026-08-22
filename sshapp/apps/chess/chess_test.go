package main

import (
	"testing"
	"time"
)

func testGM() *GameManager {
	return &GameManager{
		activeGames:  make(map[string]*GameSession),
		playerToGame: make(map[string]string),
	}
}

func TestCloneIsolatesBoards(t *testing.T) {
	g := NewGame()
	c := g.Clone()
	if !g.MakeMove(Position{1, 4}, Position{3, 4}) {
		t.Fatal("e2e4")
	}
	if c.Board.At(Position{1, 4}).Type != Pawn || c.Board.At(Position{3, 4}).Type != Empty {
		t.Fatal("clone mutated")
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
}

func TestRejectsMovingOpponentPiece(t *testing.T) {
	g := NewGame()
	if g.MakeMove(Position{6, 4}, Position{4, 4}) {
		t.Fatal("white moved black pawn")
	}
}

func TestMatchmakingPairsTwoPlayers(t *testing.T) {
	gm := testGM()
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 2)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 2)}
	gm.AddPlayer(a)
	if len(gm.activeGames) != 0 {
		t.Fatal("single player matched")
	}
	gm.AddPlayer(b)
	if len(gm.activeGames) != 1 {
		t.Fatalf("games=%d", len(gm.activeGames))
	}
	for _, ch := range []chan GameUpdate{a.UpdateChan, b.UpdateChan} {
		select {
		case u := <-ch:
			if u.Type != "matched" {
				t.Fatalf("got %q", u.Type)
			}
		case <-time.After(time.Second):
			t.Fatal("matched timeout")
		}
	}
}

func TestRemovePlayerNotifiesOpponent(t *testing.T) {
	gm := testGM()
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	gm.AddPlayer(a)
	gm.AddPlayer(b)
	<-a.UpdateChan
	<-b.UpdateChan

	gm.RemovePlayer(a.ID)
	select {
	case u := <-b.UpdateChan:
		if u.Type != "opponent_disconnected" {
			t.Fatalf("got %q", u.Type)
		}
	case <-time.After(time.Second):
		t.Fatal("disconnect timeout")
	}
}

func TestBroadcastAfterCleanupDoesNotPanic(t *testing.T) {
	gm := testGM()
	a := &Player{ID: "a", Name: "alice", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	b := &Player{ID: "b", Name: "bob", Connected: true, UpdateChan: make(chan GameUpdate, 4)}
	gm.AddPlayer(a)
	gm.AddPlayer(b)
	<-a.UpdateChan
	<-b.UpdateChan
	gm.RemovePlayer(a.ID)
	gm.RemovePlayer(b.ID)
	gm.BroadcastUpdate(a.ID, GameUpdate{Type: "move"})
}
