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
	wishtea "charm.land/wish/v2/bubbletea"
	"charm.land/wish/v2/logging"
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
		if m.player != nil && m.player.UpdateChan != nil {
			return <-m.player.UpdateChan
		}
		return nil
	}
}

func (m model) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	switch msg := msg.(type) {
	case tea.KeyMsg:
		switch msg.String() {
		case "ctrl+c", "q":
			return m, tea.Quit
		case "esc", "escape":
			if m.gameState == "playing" && m.isMyTurn {
				m.selected = nil
				m.validMoves = make([]Position, 0)
				if m.gameSession != nil {
					GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
						Type: "deselect",
						Data: nil,
					})
				}
			}
		}

		if m.gameState == "playing" && m.isMyTurn {
			switch msg.String() {
			case "up", "k":
				if m.cursorRow < 7 {
					m.cursorRow++
					m.broadcastCursorUpdate()
				}
			case "down", "j":
				if m.cursorRow > 0 {
					m.cursorRow--
					m.broadcastCursorUpdate()
				}
			case "left", "h":
				if m.cursorCol > 0 {
					m.cursorCol--
					m.broadcastCursorUpdate()
				}
			case "right", "l":
				if m.cursorCol < 7 {
					m.cursorCol++
					m.broadcastCursorUpdate()
				}
			case "enter", " ":
				currentPos := Position{m.cursorRow, m.cursorCol}

				if m.selected == nil {
					piece := m.game.Board.At(currentPos)
					if piece.Type != Empty && piece.Color == m.player.Color {
						m.selected = &currentPos
						m.validMoves = m.getValidMoves(currentPos)
						GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
							Type: "select",
							Data: map[string]interface{}{
								"position":   currentPos,
								"validMoves": m.validMoves,
							},
						})
					}
				} else if *m.selected == currentPos {
					m.selected = nil
					m.validMoves = make([]Position, 0)
					GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
						Type: "deselect",
						Data: nil,
					})
				} else if m.game.MakeMove(*m.selected, currentPos) {
					GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
						Type: "move",
						Data: map[string]interface{}{
							"from":      *m.selected,
							"to":        currentPos,
							"gameState": m.game,
						},
					})
					m.selected = nil
					m.validMoves = make([]Position, 0)
					m.isMyTurn = false
				}
			}
		} else if m.gameState == "waiting" || m.gameState == "opponent_disconnected" {
			switch msg.String() {
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
			}
		}

	case GameUpdate:
		return m.handleGameUpdate(msg)
	}
	return m, nil
}

func (m model) broadcastCursorUpdate() {
	if m.gameSession != nil {
		GetGameManager().BroadcastUpdate(m.player.ID, GameUpdate{
			Type: "cursor",
			Data: map[string]interface{}{
				"row": m.cursorRow,
				"col": m.cursorCol,
			},
		})
	}
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
			m.game = m.gameSession.Game
			m.opponent = m.gameSession.GetOpponent(m.player.ID)
			m.isMyTurn = m.player.Color == White
		}

	case "move":
		if data, ok := update.Data.(map[string]interface{}); ok {
			if gameState, ok := data["gameState"].(*Game); ok {
				m.game = gameState
				m.isMyTurn = true
				m.selected = nil
				m.validMoves = make([]Position, 0)
			}
		}

	case "cursor":
		// Opponent cursor is not shown; ignore.

	case "select":
		// Opponent selection is not shown; ignore.

	case "deselect":
		// Opponent deselection is not shown; ignore.

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

	switch m.gameState {
	case "waiting":
		s.WriteString("CheSSH\n")
		s.WriteString("Waiting for an opponent to connect...\n\n")
		if m.player != nil {
			if position := GetGameManager().GetQueuePosition(m.player.ID); position > 0 {
				s.WriteString(fmt.Sprintf("Position in queue: %d\n", position))
			}
		}
		s.WriteString("You can explore the board while waiting:\n")
		s.WriteString("Use arrow keys to move cursor, Q to quit\n\n")
		s.WriteString(m.renderBoardWithInfo())
	case "opponent_disconnected":
		s.WriteString("CheSSH\n")
		s.WriteString("*** OPPONENT DISCONNECTED; YOU WIN ***\n\n")
		s.WriteString("Your opponent has left the game.\n")
		s.WriteString("You can continue exploring the board or press Q to quit.\n\n")
		s.WriteString(m.renderBoardWithInfo())
	default:
		s.WriteString("CheSSH\n")
		if m.player != nil && m.opponent != nil {
			s.WriteString(fmt.Sprintf("You: %s (%s) vs %s (%s)\n",
				m.player.Name, m.player.Color, m.opponent.Name, m.opponent.Color))
		}
		if m.isMyTurn {
			s.WriteString("YOUR TURN - Use arrow keys to move cursor\n")
			s.WriteString("SPACE to select, ESC to deselect, Q to quit\n\n")
		} else {
			s.WriteString("OPPONENT'S TURN - Please wait\n\n\n")
		}
		if status := m.game.GameStatus(); status != "" {
			s.WriteString(fmt.Sprintf("*** %s ***\n\n", status))
		}
		s.WriteString(m.renderBoardWithInfo())
	}

	v := tea.NewView(s.String())
	v.AltScreen = true
	return v
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

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGINT, syscall.SIGTERM)
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
			wishtea.Middleware(teaHandler),
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
	m := initialModelWithPlayer(player)
	GetGameManager().AddPlayer(player)

	go func() {
		<-s.Context().Done()
		GetGameManager().RemovePlayer(player.ID)
		if player.UpdateChan != nil {
			close(player.UpdateChan)
		}
	}()

	return m, wishtea.MakeOptions(s)
}

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}
