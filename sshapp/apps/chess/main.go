// Command chess is a multiplayer chess game over SSH (Wish + Bubble Tea).
package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"slices"
	"strings"
	"syscall"
	"time"

	tea "charm.land/bubbletea/v2"
	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/activeterm"
	"charm.land/wish/v2/logging"
	"github.com/imjasonh/playground/sshapp/internal/sshtea"
)

type model struct {
	game       *Game
	cursorRow  int
	cursorCol  int
	selected   *Position
	validMoves []Position

	player      *Player
	opponent    *Player
	gameSession *GameSession
	gameState   string // "waiting", "playing", "finished", "opponent_disconnected"
	isMyTurn    bool
}

type sessionEndedMsg struct{}

func initialModel() model {
	return model{
		game:       NewGame(),
		cursorRow:  0,
		cursorCol:  0,
		selected:   nil,
		validMoves: make([]Position, 0),
		gameState:  "waiting",
		isMyTurn:   false,
	}
}

func initialModelWithPlayer(player *Player) model {
	m := initialModel()
	m.player = player
	m.gameState = "waiting"
	return m
}

func (m model) Init() tea.Cmd {
	if m.player != nil && m.player.UpdateChan != nil {
		return m.listenForUpdates()
	}
	return nil
}

func (m model) listenForUpdates() tea.Cmd {
	return func() tea.Msg {
		if m.player == nil || m.player.UpdateChan == nil {
			return sessionEndedMsg{}
		}
		update, ok := <-m.player.UpdateChan
		if !ok {
			return sessionEndedMsg{}
		}
		return update
	}
}

func (m model) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	switch msg := msg.(type) {
	case sessionEndedMsg:
		return m, tea.Quit
	case tea.KeyMsg:
		key := msg.String()
		if key == "ctrl+c" || key == "q" {
			return m, tea.Quit
		}
		if key == "esc" || key == "escape" {
			if m.gameState == "playing" && m.isMyTurn {
				m.selected = nil
				m.validMoves = nil
			}
			return m, nil
		}

		playing := m.gameState == "playing" && m.isMyTurn
		waiting := m.gameState == "waiting" || m.gameState == "opponent_disconnected"
		if !playing && !waiting {
			return m, nil
		}

		switch key {
		case "up", "k":
			if m.cursorRow < 7 {
				m.cursorRow++
			}
		case "down", "j":
			if m.cursorRow > 0 {
				m.cursorRow--
			}
		case "left", "h":
			if m.cursorCol > 0 {
				m.cursorCol--
			}
		case "right", "l":
			if m.cursorCol < 7 {
				m.cursorCol++
			}
		case "enter", " ":
			if playing {
				m = m.handleSelect()
			}
		}
		return m, nil

	case GameUpdate:
		return m.handleGameUpdate(msg)
	}
	return m, nil
}

func (m model) handleSelect() model {
	pos := Position{m.cursorRow, m.cursorCol}
	if m.selected == nil {
		piece := m.game.Board.At(pos)
		if piece.Type != Empty && piece.Color == m.player.Color {
			m.selected = &pos
			m.validMoves = m.getValidMoves(pos)
		}
		return m
	}
	if *m.selected == pos {
		m.selected = nil
		m.validMoves = nil
		return m
	}
	if !m.game.MakeMove(*m.selected, pos) {
		return m
	}
	GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
		Type: "move",
		Data: map[string]any{"gameState": m.game.Clone()},
	})
	m.selected = nil
	m.validMoves = nil
	m.isMyTurn = false
	return m
}

func (m model) handleGameUpdate(update GameUpdate) (tea.Model, tea.Cmd) {
	if m.player != nil && update.FromPlayer == m.player.ID {
		return m, m.listenForUpdates()
	}

	switch update.Type {
	case "matched":
		m.gameState = "playing"
		m.gameSession = GetGameManager().GetGameSession(m.player.ID)
		if m.gameSession != nil {
			m.game = m.gameSession.Game.Clone()
			m.opponent = m.gameSession.GetOpponent(m.player.ID)
			m.isMyTurn = m.player.Color == White
		}
	case "move":
		if data, ok := update.Data.(map[string]any); ok {
			if g, ok := data["gameState"].(*Game); ok {
				m.game = g.Clone()
				m.isMyTurn = true
				m.selected = nil
				m.validMoves = nil
			}
		}
	case "opponent_disconnected":
		m.gameState = "opponent_disconnected"
		m.isMyTurn = false
	}

	return m, m.listenForUpdates()
}

func (m model) getValidMoves(from Position) []Position {
	var moves []Position
	for row := range 8 {
		for col := range 8 {
			to := Position{row, col}
			if m.game.IsValidMove(from, to) {
				moves = append(moves, to)
			}
		}
	}
	return moves
}

func (m model) View() tea.View {
	var s strings.Builder
	s.WriteString("Chess\n")

	switch m.gameState {
	case "waiting":
		s.WriteString("Waiting for an opponent...\n")
		if m.player != nil {
			if n := GetGameManager().GetQueuePosition(m.player.ID); n > 0 {
				fmt.Fprintf(&s, "Queue position: %d\n", n)
			}
		}
		s.WriteString("Arrows move cursor, q quits\n\n")
	case "opponent_disconnected":
		s.WriteString("*** OPPONENT DISCONNECTED; YOU WIN ***\n")
		s.WriteString("q to quit\n\n")
	default:
		if m.player != nil && m.opponent != nil {
			fmt.Fprintf(&s, "You: %s (%s) vs %s (%s)\n",
				m.player.Name, m.player.Color, m.opponent.Name, m.opponent.Color)
		}
		if m.isMyTurn {
			s.WriteString("YOUR TURN - arrows, space select, esc clear, q quit\n\n")
		} else {
			s.WriteString("OPPONENT'S TURN\n\n")
		}
		if status := m.game.GameStatus(); status != "" {
			fmt.Fprintf(&s, "*** %s ***\n\n", status)
		}
	}
	s.WriteString(m.renderBoardWithInfo())

	return tea.NewView(s.String())
}

func (m model) renderBoardWithInfo() string {
	boardLines := m.getBoardLines()
	infoLines := m.getInfoLines()

	var s strings.Builder
	maxLines := len(boardLines)
	if len(infoLines) > maxLines {
		maxLines = len(infoLines)
	}

	for i := 0; i < maxLines; i++ {
		if i < len(boardLines) {
			s.WriteString(boardLines[i])
		} else {
			s.WriteString(strings.Repeat(" ", 26))
		}
		s.WriteString("   ")
		if i < len(infoLines) {
			s.WriteString(infoLines[i])
		}
		s.WriteString("\n")
	}
	return s.String()
}

func (m model) getBoardLines() []string {
	var lines []string
	lines = append(lines, "  a  b  c  d  e  f  g  h  ")

	for row := 7; row >= 0; row-- {
		var line strings.Builder
		line.WriteString(fmt.Sprintf("%d", row+1))

		for col := range 8 {
			pos := Position{row, col}
			piece := m.game.Board.At(pos)

			cellChar := piece.String()
			if piece.Type == Empty {
				cellChar = " "
			}

			var bgColor string
			if m.cursorRow == row && m.cursorCol == col {
				bgColor = "\033[41m"
			} else if m.selected != nil && m.selected.Row == row && m.selected.Col == col {
				bgColor = "\033[43m"
			} else if slices.Contains(m.validMoves, pos) {
				bgColor = "\033[42m"
			} else if (row+col)%2 == 0 {
				bgColor = "\033[100m"
			} else {
				bgColor = "\033[40m"
			}

			line.WriteString(fmt.Sprintf("%s %s \033[0m", bgColor, cellChar))
		}
		line.WriteString(fmt.Sprintf("%d", row+1))
		lines = append(lines, line.String())
	}

	lines = append(lines, "  a  b  c  d  e  f  g  h  ")
	return lines
}

func (m model) getInfoLines() []string {
	var lines []string
	lines = append(lines, "┌─────────────────────┐")
	lines = append(lines, "│ GAME INFO           │")
	lines = append(lines, "├─────────────────────┤")
	lines = append(lines, fmt.Sprintf("│ Turn: %-13s │", m.game.CurrentTurn))
	lines = append(lines, "│                     │")

	cursorPos := Position{m.cursorRow, m.cursorCol}
	piece := m.game.Board.At(cursorPos)
	lines = append(lines, fmt.Sprintf("│ Cursor: %-11s │", cursorPos.String()))

	if piece.Type == Empty {
		lines = append(lines, "│ Piece: Empty        │")
	} else {
		lines = append(lines, fmt.Sprintf("│ Piece: %-12s │", m.getPieceName(piece)))
	}

	lines = append(lines, "│                     │")
	lines = append(lines, "└─────────────────────┘")

	if len(m.game.MoveHistory) > 0 {
		lastMove := m.game.MoveHistory[len(m.game.MoveHistory)-1]
		lines = append(lines, fmt.Sprintf("Last move: %s -> %-12s", lastMove.From.String(), lastMove.To.String()))
	}
	return lines
}

func (m model) getPieceName(piece Piece) string {
	if piece.Type == Empty {
		return "Empty"
	}

	color := "White"
	if piece.Color == Black {
		color = "Black"
	}

	pieceType := ""
	switch piece.Type {
	case Pawn:
		pieceType = "Pawn"
	case Rook:
		pieceType = "Rook"
	case Knight:
		pieceType = "Knight"
	case Bishop:
		pieceType = "Bishop"
	case Queen:
		pieceType = "Queen"
	case King:
		pieceType = "King"
	}
	return fmt.Sprintf("%s %s", color, pieceType)
}

func main() {
	addr := envOr("SSHAPP_ADDR", ":2222")
	srv, err := newServer(addr, os.Getenv("SSHAPP_HOST_KEY"), envOr("SSHAPP_HOST_KEY_PATH", ".ssh/host_ed25519"))
	if err != nil {
		log.Fatal("create server", "error", err)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	log.Info("starting SSH chess server", "addr", addr)
	go func() {
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
			log.Error("listen", "error", err)
			stop()
		}
	}()

	<-ctx.Done()
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	if err := srv.Shutdown(shutdownCtx); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
		log.Error("shutdown", "error", err)
		os.Exit(1)
	}
}

func newServer(addr, hostKeyPEM, hostKeyPath string) (*ssh.Server, error) {
	opts := []ssh.Option{
		wish.WithAddress(addr),
		wish.WithPublicKeyAuth(func(_ ssh.Context, _ ssh.PublicKey) bool {
			return true
		}),
		wish.WithMiddleware(
			sshtea.Middleware(teaHandler),
			activeterm.Middleware(),
			logging.Middleware(),
		),
	}
	if hostKeyPEM != "" {
		opts = append(opts, wish.WithHostKeyPEM([]byte(hostKeyPEM)))
	} else {
		opts = append(opts, wish.WithHostKeyPath(hostKeyPath))
	}
	return wish.NewServer(opts...)
}

func teaHandler(s ssh.Session) (tea.Model, []tea.ProgramOption) {
	player := &Player{
		ID:         fmt.Sprintf("player_%d", time.Now().UnixNano()),
		Session:    s,
		Name:       s.User(),
		Connected:  true,
		UpdateChan: make(chan GameUpdate, 10),
	}
	GetGameManager().AddPlayer(player)
	go func() {
		<-s.Context().Done()
		GetGameManager().RemovePlayer(player.ID)
	}()
	return initialModelWithPlayer(player), nil
}

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}
