package youtube

import (
	"context"
	"net/http/httptest"
	"slices"
	"testing"
	"time"

	"github.com/imjasonh/playground/stream-boids/internal/fakeyt"
)

const apiKey = "AIzaFakeKey"

func fake(t *testing.T) (*fakeyt.Server, *Client) {
	t.Helper()
	fs := fakeyt.New()
	fs.Key = apiKey
	fs.PollInterval = 0
	srv := httptest.NewServer(fs)
	t.Cleanup(srv.Close)
	return fs, &Client{
		Base: srv.URL + "/youtube/v3",
		Key:  func(context.Context) (string, error) { return apiKey, nil },
	}
}

func TestVideo(t *testing.T) {
	fs, c := fake(t)
	fs.SetViewers(1234)
	v, err := c.Video(t.Context(), fakeyt.VideoID)
	if err != nil {
		t.Fatal(err)
	}
	want := Video{ID: fakeyt.VideoID, Live: true, Viewers: 1234, ViewersKnown: true, ChatID: fakeyt.ChatID}
	if v != want {
		t.Errorf("Video = %+v, want %+v", v, want)
	}

	fs.SetLive(false)
	v, err = c.Video(t.Context(), fakeyt.VideoID)
	if err != nil {
		t.Fatal(err)
	}
	if v.Live || v.ViewersKnown || v.ChatID != "" {
		t.Errorf("ended Video = %+v", v)
	}

	if _, err := c.Video(t.Context(), "nope"); err == nil {
		t.Error("unknown video returned no error")
	}
}

func TestKeyRequired(t *testing.T) {
	_, c := fake(t)
	c.Key = nil
	_, err := c.Video(t.Context(), fakeyt.VideoID)
	if ae, ok := err.(*APIError); !ok || ae.Reason != "keyInvalid" {
		t.Errorf("err = %v, want keyInvalid", err)
	}
}

func TestChat(t *testing.T) {
	fs, c := fake(t)
	fs.Chat("Ann", false, "hello")
	fs.SuperChat("Bea", true, 25, "great flock")
	fs.SuperSticker("Cy", false, 2)
	fs.Gift("Dee", false, "Ed", "Flo")
	page, err := c.Chat(t.Context(), fakeyt.ChatID, "")
	if err != nil {
		t.Fatal(err)
	}
	type row struct {
		Type, Name string
		Member     bool
		Tier       int
		Amount     string
		Text       string
		Gifts      int
	}
	var got []row
	for _, m := range page.Messages {
		got = append(got, row{m.Type, m.Author.Name, m.Author.Member, m.Tier, m.Amount, m.Text, m.Gifts})
		if m.Published.IsZero() || m.ID == "" || m.Author.ChannelID == "" {
			t.Errorf("message missing fields: %+v", m)
		}
	}
	want := []row{
		{TextMessage, "Ann", false, 0, "", "hello", 0},
		{SuperChat, "Bea", true, 5, "$25.00", "great flock", 0},
		{SuperSticker, "Cy", false, 2, "$2.00", "Super Sticker from Cy", 0},
		{MembershipGifting, "Dee", false, 0, "", "Dee gifted 2 memberships", 2},
		{GiftMembershipReceived, "Ed", true, 0, "", "Ed received a gift membership", 0},
		{GiftMembershipReceived, "Flo", true, 0, "", "Flo received a gift membership", 0},
	}
	if !slices.Equal(got, want) {
		t.Errorf("messages:\n got %+v\nwant %+v", got, want)
	}

	fs.Chat("Gus", false, "later")
	page, err = c.Chat(t.Context(), fakeyt.ChatID, page.Next)
	if err != nil {
		t.Fatal(err)
	}
	if len(page.Messages) != 1 || page.Messages[0].Author.Name != "Gus" {
		t.Errorf("second page = %+v, want only Gus", page.Messages)
	}

	fs.SetLive(false)
	if _, err := c.Chat(t.Context(), fakeyt.ChatID, page.Next); !IsChatGone(err) {
		t.Errorf("err = %v, want chat gone", err)
	}
}

func TestQuotaError(t *testing.T) {
	fs, c := fake(t)
	fs.SetQuotaExceeded(true)
	if _, err := c.Video(t.Context(), fakeyt.VideoID); !IsQuota(err) {
		t.Errorf("err = %v, want a quota error", err)
	}
}

func TestLiveVideo(t *testing.T) {
	fs, c := fake(t)
	id, err := c.LiveVideo(t.Context(), fakeyt.ChannelID)
	if err != nil || id != fakeyt.VideoID {
		t.Errorf("LiveVideo = %q, %v", id, err)
	}
	fs.SetLive(false)
	id, err = c.LiveVideo(t.Context(), fakeyt.ChannelID)
	if err != nil || id != "" {
		t.Errorf("LiveVideo after end = %q, %v", id, err)
	}
}

var fast = WatcherConfig{
	VideoID:        fakeyt.VideoID,
	ViewerPoll:     10 * time.Millisecond,
	ChatPoll:       10 * time.Millisecond,
	SearchInterval: 10 * time.Millisecond,
	MemberWindow:   time.Hour,
	QuotaPause:     time.Hour,
}

func watch(t *testing.T, c *Client, cfg WatcherConfig) *Watcher {
	t.Helper()
	w := NewWatcher(c, cfg)
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error)
	go func() { done <- w.Run(ctx) }()
	t.Cleanup(func() {
		cancel()
		if err := <-done; err != nil {
			t.Errorf("Run = %v", err)
		}
	})
	return w
}

func eventually(t *testing.T, what string, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(5 * time.Millisecond)
	}
}

func next(t *testing.T, w *Watcher) Message {
	t.Helper()
	select {
	case m := <-w.Events():
		return m
	case <-time.After(5 * time.Second):
		t.Fatal("no event")
		return Message{}
	}
}

func TestWatcherViewersMembersAndEvents(t *testing.T) {
	fs, c := fake(t)
	// History from before the watcher started: counts for membership but
	// must not replay as events.
	fs.SuperChat("Old", true, 100, "before restart")
	time.Sleep(2 * time.Millisecond)

	fs.SetViewers(42)
	w := watch(t, c, fast)
	eventually(t, "viewers", func() bool { s := w.State(); return s.Live && s.Viewers == 42 && s.ViewersKnown })

	fs.Chat("Ann", true, "hi")
	fs.Chat("Bob", false, "hi")
	fs.SuperChat("Cat", false, 7, "yay")
	fs.NewMember("Dan")
	fs.SetViewers(43)

	if m := next(t, w); m.Type != SuperChat || m.Author.Name != "Cat" || m.Tier != 3 {
		t.Errorf("first event = %+v, want Cat's tier 3 Super Chat", m)
	}
	if m := next(t, w); m.Type != NewSponsor || m.Author.Name != "Dan" {
		t.Errorf("second event = %+v, want Dan joining", m)
	}
	eventually(t, "members and viewers", func() bool {
		s := w.State()
		return s.Viewers == 43 && slices.Equal(s.Members, []string{"Dan", "Ann", "Old"})
	})
	select {
	case m := <-w.Events():
		t.Errorf("unexpected event %+v", m)
	default:
	}

	fs.SetLive(false)
	eventually(t, "broadcast end", func() bool { s := w.State(); return !s.Live && !s.ViewersKnown })
	chats := fs.Calls("liveChatMessages")
	time.Sleep(50 * time.Millisecond)
	if n := fs.Calls("liveChatMessages"); n > chats+1 {
		t.Errorf("chat polled %d more times after the broadcast ended", n-chats)
	}
	fs.SetLive(true)
	fs.SuperChat("Eve", false, 1, "back")
	if m := next(t, w); m.Author.Name != "Eve" {
		t.Errorf("event after restart = %+v, want Eve", m)
	}
}

func TestWatcherMembersExpire(t *testing.T) {
	fs, c := fake(t)
	cfg := fast
	cfg.MemberWindow = 150 * time.Millisecond
	w := watch(t, c, cfg)
	fs.Chat("Ann", true, "hi")
	eventually(t, "member", func() bool { return len(w.State().Members) == 1 })
	eventually(t, "member to expire", func() bool { return len(w.State().Members) == 0 })
}

func TestWatcherSearchesChannel(t *testing.T) {
	fs, c := fake(t)
	fs.SetViewers(7)
	cfg := fast
	cfg.VideoID, cfg.ChannelID = "", fakeyt.ChannelID
	w := watch(t, c, cfg)
	eventually(t, "viewers via search", func() bool { return w.State().Viewers == 7 })
	searches := fs.Calls("search")
	time.Sleep(50 * time.Millisecond)
	if n := fs.Calls("search"); n != searches {
		t.Errorf("searched %d more times while the broadcast was known", n-searches)
	}
	fs.SetLive(false)
	eventually(t, "searching again", func() bool { return fs.Calls("search") > searches+2 })
	fs.SetLive(true)
	eventually(t, "live again", func() bool { return w.State().Live })
}

func TestWatcherPausesOnQuota(t *testing.T) {
	fs, c := fake(t)
	fs.SetQuotaExceeded(true)
	w := watch(t, c, fast)
	eventually(t, "a call", func() bool { return fs.Calls("videos") > 0 })
	time.Sleep(100 * time.Millisecond)
	if n := fs.Calls("videos"); n != 1 {
		t.Errorf("called videos %d times during the quota pause, want 1", n)
	}
	if w.State().Live {
		t.Error("state says live without a successful call")
	}
}
