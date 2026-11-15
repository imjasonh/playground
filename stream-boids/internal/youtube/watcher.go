package youtube

import (
	"cmp"
	"context"
	"slices"
	"sync"
	"time"

	"github.com/chainguard-dev/clog"
)

// WatcherConfig says what to watch and how often to poll.
type WatcherConfig struct {
	// VideoID is the broadcast to watch. When empty, the watcher searches
	// ChannelID for a live broadcast.
	VideoID   string
	ChannelID string
	// ViewerPoll is how often to read the viewer count (1 unit each).
	ViewerPoll time.Duration
	// ChatPoll is the shortest wait between chat reads (5 units each).
	// YouTube's own polling interval wins when it is longer.
	ChatPoll time.Duration
	// SearchInterval is how often to search for a live broadcast (100
	// units each) while none is known.
	SearchInterval time.Duration
	// MemberWindow is how long a member counts as watching after their
	// last chat message.
	MemberWindow time.Duration
	// QuotaPause is how long to stop calling the API after a quota error.
	QuotaPause time.Duration
}

// State is what the watcher knows about the broadcast.
type State struct {
	Live         bool
	Viewers      int
	ViewersKnown bool
	// Members are the display names of members who chatted within the
	// member window, most recent first. YouTube doesn't say who is
	// watching, so chat activity stands in for it.
	Members []string
}

type member struct {
	name string
	seen time.Time
}

// Watcher polls the API for a broadcast's state and chat events.
type Watcher struct {
	client *Client
	cfg    WatcherConfig
	events chan Message
	start  time.Time

	mu      sync.Mutex
	live    bool
	viewers int
	known   bool
	members map[string]member
}

// NewWatcher returns a Watcher. Run starts it.
func NewWatcher(client *Client, cfg WatcherConfig) *Watcher {
	return &Watcher{
		client:  client,
		cfg:     cfg,
		events:  make(chan Message, 64),
		start:   time.Now(),
		members: map[string]member{},
	}
}

// Events delivers Super Chats, Super Stickers, and membership events
// published after the watcher started. Events that arrive while the
// channel is full are dropped.
func (w *Watcher) Events() <-chan Message { return w.events }

// State returns the current state.
func (w *Watcher) State() State {
	w.mu.Lock()
	defer w.mu.Unlock()
	s := State{Live: w.live, Viewers: w.viewers, ViewersKnown: w.known}
	cutoff := time.Now().Add(-w.cfg.MemberWindow)
	ms := make([]member, 0, len(w.members))
	for id, m := range w.members {
		if m.seen.Before(cutoff) {
			delete(w.members, id)
			continue
		}
		ms = append(ms, m)
	}
	slices.SortFunc(ms, func(a, b member) int {
		return cmp.Or(b.seen.Compare(a.seen), cmp.Compare(a.name, b.name))
	})
	for _, m := range ms {
		s.Members = append(s.Members, m.name)
	}
	return s
}

// Run polls until ctx is done.
func (w *Watcher) Run(ctx context.Context) error {
	log := clog.FromContext(ctx)
	videoID := w.cfg.VideoID
	// chatID is the chat being polled; lastChat and pageToken stay set
	// after it stops, so a chat that comes back resumes without replaying.
	var chatID, lastChat, pageToken string
	var nextVideo, nextChat, nextSearch, pausedUntil time.Time

	// failed reports whether err stopped this round, pausing after a
	// quota error.
	failed := func(what string, err error) bool {
		if err == nil {
			return false
		}
		if IsQuota(err) {
			pausedUntil = time.Now().Add(w.cfg.QuotaPause)
			log.Warn("YouTube quota exhausted; pausing", "call", what, "until", pausedUntil.Format(time.RFC3339))
		} else if ctx.Err() == nil {
			log.Warn("YouTube call failed", "call", what, "error", err)
		}
		return true
	}

	for {
		now := time.Now()
		if now.Before(pausedUntil) {
			if !sleep(ctx, pausedUntil.Sub(now)) {
				return nil
			}
			continue
		}

		if videoID == "" && w.cfg.ChannelID != "" && !now.Before(nextSearch) {
			nextSearch = now.Add(w.cfg.SearchInterval)
			id, err := w.client.LiveVideo(ctx, w.cfg.ChannelID)
			if !failed("search", err) && id != "" {
				log.Info("found live broadcast", "video", id)
				videoID, nextVideo = id, now
			}
		}

		if videoID != "" && !now.Before(nextVideo) {
			nextVideo = now.Add(w.cfg.ViewerPoll)
			v, err := w.client.Video(ctx, videoID)
			if !failed("videos", err) {
				w.setVideo(v)
				switch {
				case v.Live && v.ChatID != chatID:
					if v.ChatID != lastChat {
						lastChat, pageToken = v.ChatID, ""
					}
					chatID, nextChat = v.ChatID, now
				case !v.Live:
					chatID = ""
					if w.cfg.VideoID == "" {
						// Search again for the next broadcast.
						videoID = ""
					}
				}
			}
		}

		if chatID != "" && !now.Before(nextChat) {
			page, err := w.client.Chat(ctx, chatID, pageToken)
			nextChat = now.Add(max(w.cfg.ChatPoll, page.Interval))
			switch {
			case IsChatGone(err):
				log.Info("live chat ended", "chat", chatID)
				chatID = ""
			case failed("liveChatMessages", err):
			default:
				pageToken = page.Next
				w.addMessages(ctx, page.Messages)
				if page.Offline {
					chatID = ""
				}
			}
		}

		if pausedUntil.After(now) {
			continue
		}
		wake := nextVideo
		if videoID == "" {
			wake = nextSearch
			if w.cfg.ChannelID == "" {
				wake = now.Add(time.Hour)
			}
		}
		if chatID != "" && nextChat.Before(wake) {
			wake = nextChat
		}
		if !sleep(ctx, time.Until(wake)) {
			return nil
		}
	}
}

func (w *Watcher) setVideo(v Video) {
	w.mu.Lock()
	defer w.mu.Unlock()
	w.live, w.viewers, w.known = v.Live, v.Viewers, v.ViewersKnown
}

func (w *Watcher) addMessages(ctx context.Context, msgs []Message) {
	now := time.Now()
	w.mu.Lock()
	for _, m := range msgs {
		isMember := m.Author.Member
		switch m.Type {
		case NewSponsor, MemberMilestone, GiftMembershipReceived:
			isMember = true
		}
		if !isMember || m.Author.ChannelID == "" {
			continue
		}
		seen := m.Published
		if seen.IsZero() || seen.After(now) {
			seen = now
		}
		if old, ok := w.members[m.Author.ChannelID]; !ok || seen.After(old.seen) {
			w.members[m.Author.ChannelID] = member{name: m.Author.Name, seen: seen}
		}
	}
	w.mu.Unlock()

	for _, m := range msgs {
		switch m.Type {
		case SuperChat, SuperSticker, NewSponsor, MemberMilestone, MembershipGifting:
		default:
			continue
		}
		// The first page holds history from before a restart.
		if !m.Published.After(w.start) {
			continue
		}
		select {
		case w.events <- m:
		default:
			clog.FromContext(ctx).Warn("dropped chat event; queue full", "type", m.Type)
		}
	}
}

// sleep waits for d or until ctx is done, and reports whether ctx is
// still live.
func sleep(ctx context.Context, d time.Duration) bool {
	t := time.NewTimer(max(d, 0))
	defer t.Stop()
	select {
	case <-ctx.Done():
		return false
	case <-t.C:
		return true
	}
}
