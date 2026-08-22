package main

import (
	"context"
	"fmt"
	"sync"
	"time"

	"charm.land/ssh"
)

type Player struct {
	ID         string
	Session    ssh.Session
	Color      Color
	Name       string
	GameID     string
	Connected  bool
	UpdateChan chan GameUpdate
}

type GameUpdate struct {
	Type       string
	Data       any
	FromPlayer string
}

type GameSession struct {
	ID      string
	Game    *Game
	White   *Player
	Black   *Player
	Updates chan GameUpdate
	ctx     context.Context
	cancel  context.CancelFunc
	mu      sync.RWMutex
}

func NewGameSession(id string, white, black *Player) *GameSession {
	ctx, cancel := context.WithCancel(context.Background())
	gs := &GameSession{
		ID:      id,
		Game:    NewGame(),
		White:   white,
		Black:   black,
		Updates: make(chan GameUpdate, 10),
		ctx:     ctx,
		cancel:  cancel,
	}
	white.Color = White
	white.GameID = id
	black.Color = Black
	black.GameID = id
	go gs.fanOut()
	return gs
}

func (gs *GameSession) fanOut() {
	for {
		select {
		case <-gs.ctx.Done():
			return
		case update := <-gs.Updates:
			gs.mu.RLock()
			trySend(gs.White, update)
			trySend(gs.Black, update)
			gs.mu.RUnlock()
		}
	}
}

func trySend(p *Player, update GameUpdate) {
	if p == nil || !p.Connected || p.UpdateChan == nil {
		return
	}
	select {
	case p.UpdateChan <- update:
	default:
	}
}

func (gs *GameSession) GetOpponent(playerID string) *Player {
	gs.mu.RLock()
	defer gs.mu.RUnlock()
	if gs.White != nil && gs.White.ID == playerID {
		return gs.Black
	}
	if gs.Black != nil && gs.Black.ID == playerID {
		return gs.White
	}
	return nil
}

func (gs *GameSession) Disconnect(playerID string) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	var left *Player
	switch {
	case gs.White != nil && gs.White.ID == playerID:
		gs.White.Connected = false
		left = gs.Black
	case gs.Black != nil && gs.Black.ID == playerID:
		gs.Black.Connected = false
		left = gs.White
	}
	if left != nil && left.Connected {
		trySend(left, GameUpdate{Type: "opponent_disconnected"})
	}
	if !playerConnected(gs.White) && !playerConnected(gs.Black) {
		gs.cancel()
	}
}

func playerConnected(p *Player) bool {
	return p != nil && p.Connected
}

type GameManager struct {
	mu           sync.RWMutex
	playerQueue  []*Player
	activeGames  map[string]*GameSession
	playerToGame map[string]string
	gameCounter  int
}

var (
	gameManager     *GameManager
	gameManagerOnce sync.Once
)

func GetGameManager() *GameManager {
	gameManagerOnce.Do(func() {
		gameManager = &GameManager{
			activeGames:  make(map[string]*GameSession),
			playerToGame: make(map[string]string),
		}
	})
	return gameManager
}

func (gm *GameManager) AddPlayer(player *Player) {
	gm.mu.Lock()
	defer gm.mu.Unlock()

	gm.playerQueue = append(gm.playerQueue, player)
	if len(gm.playerQueue) < 2 {
		return
	}
	white, black := gm.playerQueue[0], gm.playerQueue[1]
	gm.playerQueue = gm.playerQueue[2:]

	gm.gameCounter++
	gameID := fmt.Sprintf("game_%d", gm.gameCounter)
	session := NewGameSession(gameID, white, black)
	gm.activeGames[gameID] = session
	gm.playerToGame[white.ID] = gameID
	gm.playerToGame[black.ID] = gameID

	matched := GameUpdate{Type: "matched"}
	trySend(white, matched)
	trySend(black, matched)
}

func (gm *GameManager) RemovePlayer(playerID string) {
	gm.mu.Lock()
	defer gm.mu.Unlock()

	for i, p := range gm.playerQueue {
		if p.ID == playerID {
			gm.playerQueue = append(gm.playerQueue[:i], gm.playerQueue[i+1:]...)
			break
		}
	}

	gameID, ok := gm.playerToGame[playerID]
	if !ok {
		return
	}
	session := gm.activeGames[gameID]
	if session == nil {
		delete(gm.playerToGame, playerID)
		return
	}
	session.Disconnect(playerID)
	if !playerConnected(session.White) && !playerConnected(session.Black) {
		delete(gm.activeGames, gameID)
		if session.White != nil {
			delete(gm.playerToGame, session.White.ID)
		}
		if session.Black != nil {
			delete(gm.playerToGame, session.Black.ID)
		}
	}
	delete(gm.playerToGame, playerID)
}

func (gm *GameManager) GetGameSession(playerID string) *GameSession {
	gm.mu.RLock()
	defer gm.mu.RUnlock()
	return gm.activeGames[gm.playerToGame[playerID]]
}

func (gm *GameManager) BroadcastUpdate(playerID string, update GameUpdate) {
	session := gm.GetGameSession(playerID)
	if session == nil {
		return
	}
	update.FromPlayer = playerID
	select {
	case <-session.ctx.Done():
	case session.Updates <- update:
	case <-time.After(100 * time.Millisecond):
	}
}

func (gm *GameManager) GetQueuePosition(playerID string) int {
	gm.mu.RLock()
	defer gm.mu.RUnlock()
	for i, p := range gm.playerQueue {
		if p.ID == playerID {
			return i + 1
		}
	}
	return -1
}
