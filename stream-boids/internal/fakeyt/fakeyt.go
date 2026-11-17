// Package fakeyt serves the parts of the YouTube Data API that
// stream-boids reads, backed by state that tests and a control page set.
package fakeyt

import (
	"encoding/json"
	"fmt"
	"hash/fnv"
	"html/template"
	"math"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"time"
)

// IDs the fake serves.
const (
	VideoID   = "fakeVideo01"
	ChannelID = "UCfakeChannel0000000000"
	ChatID    = "fakeChat01"
)

// Server is a fake YouTube Data API. Its zero value is not usable; call
// New.
type Server struct {
	// Key, when set, is the API key every API request must send in the
	// X-Goog-Api-Key header.
	Key string
	// PollInterval is the pollingIntervalMillis that chat responses carry.
	PollInterval time.Duration

	mux *http.ServeMux

	mu      sync.Mutex
	live    bool
	viewers int
	quota   bool
	msgs    []map[string]any
	calls   map[string]int
}

// New returns a Server whose broadcast is live with no viewers.
func New() *Server {
	s := &Server{live: true, calls: map[string]int{}, PollInterval: 2 * time.Second, mux: http.NewServeMux()}
	s.mux.HandleFunc("GET /youtube/v3/videos", s.api("videos", s.videos))
	s.mux.HandleFunc("GET /youtube/v3/search", s.api("search", s.search))
	s.mux.HandleFunc("GET /youtube/v3/liveChat/messages", s.api("liveChatMessages", s.chat))
	s.mux.HandleFunc("GET /{$}", s.page)
	s.mux.HandleFunc("GET /control/state", s.state)
	s.mux.HandleFunc("POST /control/{action}", s.control)
	return s
}

func (s *Server) ServeHTTP(w http.ResponseWriter, r *http.Request) { s.mux.ServeHTTP(w, r) }

// SetLive starts or ends the broadcast.
func (s *Server) SetLive(live bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.live = live
}

// SetViewers sets the concurrent viewer count.
func (s *Server) SetViewers(n int) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.viewers = max(n, 0)
}

// SetQuotaExceeded makes every API call fail with quotaExceeded.
func (s *Server) SetQuotaExceeded(on bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.quota = on
}

// Calls returns how many times an endpoint ("videos", "search", or
// "liveChatMessages") was called.
func (s *Server) Calls(endpoint string) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.calls[endpoint]
}

// Chat posts a text message.
func (s *Server) Chat(name string, member bool, text string) {
	s.add(name, member, "textMessageEvent", text, nil)
}

// SuperChat posts a Super Chat for dollars, with YouTube's tier for that
// amount in US dollars.
func (s *Server) SuperChat(name string, member bool, dollars float64, text string) {
	amount := fmt.Sprintf("$%.2f", dollars)
	s.add(name, member, "superChatEvent", amount+" from "+name+": "+text, map[string]any{
		"superChatDetails": map[string]any{
			"amountMicros": strconv.FormatInt(int64(math.Round(dollars*1e6)), 10), "currency": "USD",
			"amountDisplayString": amount, "userComment": text, "tier": Tier(dollars),
		},
	})
}

// SuperSticker posts a Super Sticker for dollars.
func (s *Server) SuperSticker(name string, member bool, dollars float64) {
	amount := fmt.Sprintf("$%.2f", dollars)
	s.add(name, member, "superStickerEvent", "Super Sticker from "+name, map[string]any{
		"superStickerDetails": map[string]any{
			"amountMicros": strconv.FormatInt(int64(math.Round(dollars*1e6)), 10), "currency": "USD",
			"amountDisplayString": amount, "tier": Tier(dollars),
		},
	})
}

// NewMember posts a new membership.
func (s *Server) NewMember(name string) {
	s.add(name, true, "newSponsorEvent", "Welcome to the channel, "+name+"!", map[string]any{
		"newSponsorDetails": map[string]any{"memberLevelName": "Member"},
	})
}

// Gift posts a membership gifting event from name, followed by a
// received event for each recipient.
func (s *Server) Gift(name string, member bool, recipients ...string) {
	s.add(name, member, "membershipGiftingEvent", fmt.Sprintf("%s gifted %d memberships", name, len(recipients)), map[string]any{
		"membershipGiftingDetails": map[string]any{"giftMembershipsCount": len(recipients), "giftMembershipsLevelName": "Member"},
	})
	for _, r := range recipients {
		s.add(r, true, "giftMembershipReceivedEvent", r+" received a gift membership", map[string]any{
			"giftMembershipReceivedDetails": map[string]any{"memberLevelName": "Member", "gifterChannelId": channelID(name)},
		})
	}
}

// Tier returns YouTube's Super Chat tier for an amount in US dollars.
func Tier(dollars float64) int {
	for i, floor := range []float64{100, 50, 20, 10, 5, 2} {
		if dollars >= floor {
			return 7 - i
		}
	}
	return 1
}

func channelID(name string) string {
	h := fnv.New64a()
	h.Write([]byte(name))
	return fmt.Sprintf("UC%022x", h.Sum64())
}

func (s *Server) add(name string, member bool, typ, text string, details map[string]any) {
	s.mu.Lock()
	defer s.mu.Unlock()
	snippet := map[string]any{
		"type": typ, "liveChatId": ChatID, "authorChannelId": channelID(name),
		"publishedAt": time.Now().UTC().Format(time.RFC3339Nano), "hasDisplayContent": true,
		"displayMessage": text,
	}
	if typ == "textMessageEvent" {
		snippet["textMessageDetails"] = map[string]any{"messageText": text}
	}
	for k, v := range details {
		snippet[k] = v
	}
	s.msgs = append(s.msgs, map[string]any{
		"kind": "youtube#liveChatMessage", "id": fmt.Sprintf("msg%08d", len(s.msgs)+1),
		"snippet": snippet,
		"authorDetails": map[string]any{
			"channelId": channelID(name), "displayName": name, "isChatSponsor": member,
			"isChatOwner": false, "isChatModerator": false, "isVerified": false,
		},
	})
}

func (s *Server) api(name string, h func(*http.Request) (any, int, string)) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		s.mu.Lock()
		s.calls[name]++
		quota := s.quota
		s.mu.Unlock()
		var body any
		status := http.StatusOK
		reason := ""
		switch {
		case s.Key != "" && r.Header.Get("X-Goog-Api-Key") != s.Key:
			status, reason = http.StatusBadRequest, "keyInvalid"
		case r.URL.Query().Has("key"):
			// The client must keep the key out of URLs.
			status, reason = http.StatusBadRequest, "keyInURL"
		case quota:
			status, reason = http.StatusForbidden, "quotaExceeded"
		default:
			body, status, reason = h(r)
		}
		w.Header().Set("Content-Type", "application/json; charset=UTF-8")
		if status != http.StatusOK {
			body = map[string]any{"error": map[string]any{
				"code": status, "message": "fake: " + reason,
				"errors": []map[string]string{{"reason": reason, "domain": "youtube.fake", "message": "fake: " + reason}},
			}}
		}
		w.WriteHeader(status)
		json.NewEncoder(w).Encode(body)
	}
}

func (s *Server) videos(r *http.Request) (any, int, string) {
	items := []any{}
	if r.URL.Query().Get("id") == VideoID {
		s.mu.Lock()
		defer s.mu.Unlock()
		details := map[string]any{"actualStartTime": "2026-01-01T00:00:00Z"}
		content := "none"
		if s.live {
			content = "live"
			details["concurrentViewers"] = strconv.Itoa(s.viewers)
			details["activeLiveChatId"] = ChatID
		} else {
			details["actualEndTime"] = "2026-01-01T01:00:00Z"
		}
		items = append(items, map[string]any{
			"kind": "youtube#video", "id": VideoID,
			"snippet":              map[string]any{"title": "boids", "channelId": ChannelID, "liveBroadcastContent": content},
			"liveStreamingDetails": details,
		})
	}
	return map[string]any{"kind": "youtube#videoListResponse", "items": items}, http.StatusOK, ""
}

func (s *Server) search(r *http.Request) (any, int, string) {
	q := r.URL.Query()
	items := []any{}
	s.mu.Lock()
	live := s.live
	s.mu.Unlock()
	if live && q.Get("channelId") == ChannelID && q.Get("eventType") == "live" {
		items = append(items, map[string]any{"kind": "youtube#searchResult", "id": map[string]any{"kind": "youtube#video", "videoId": VideoID}})
	}
	return map[string]any{"kind": "youtube#searchListResponse", "items": items}, http.StatusOK, ""
}

func (s *Server) chat(r *http.Request) (any, int, string) {
	q := r.URL.Query()
	if q.Get("liveChatId") != ChatID {
		return nil, http.StatusNotFound, "liveChatNotFound"
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.live {
		return nil, http.StatusForbidden, "liveChatEnded"
	}
	from, _ := strconv.Atoi(q.Get("pageToken"))
	from = min(max(from, 0), len(s.msgs))
	return map[string]any{
		"kind": "youtube#liveChatMessageListResponse", "nextPageToken": strconv.Itoa(len(s.msgs)),
		"pollingIntervalMillis": s.PollInterval.Milliseconds(),
		"items":                 s.msgs[from:],
	}, http.StatusOK, ""
}

func (s *Server) state(w http.ResponseWriter, _ *http.Request) {
	s.mu.Lock()
	defer s.mu.Unlock()
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]any{
		"live": s.live, "viewers": s.viewers, "quotaExceeded": s.quota, "messages": len(s.msgs), "calls": s.calls,
	})
}

func (s *Server) control(w http.ResponseWriter, r *http.Request) {
	name := strings.TrimSpace(r.FormValue("name"))
	if name == "" {
		name = "Viewer"
	}
	member := r.FormValue("member") != ""
	on := r.FormValue("on") == "1"
	dollars, _ := strconv.ParseFloat(r.FormValue("amount"), 64)
	n, _ := strconv.Atoi(r.FormValue("n"))
	switch r.PathValue("action") {
	case "viewers":
		s.SetViewers(n)
	case "live":
		s.SetLive(on)
	case "quota":
		s.SetQuotaExceeded(on)
	case "chat":
		s.Chat(name, member, r.FormValue("text"))
	case "superchat":
		s.SuperChat(name, member, max(dollars, 1), r.FormValue("text"))
	case "supersticker":
		s.SuperSticker(name, member, max(dollars, 1))
	case "member":
		s.NewMember(name)
	case "gift":
		var rs []string
		for i := range min(max(n, 1), 50) {
			rs = append(rs, fmt.Sprintf("%s's friend %d", name, i+1))
		}
		s.Gift(name, member, rs...)
	case "members":
		for i := range min(max(n, 1), 5000) {
			s.Chat(fmt.Sprintf("Member %d", i+1), true, "hi")
		}
	default:
		http.NotFound(w, r)
		return
	}
	if r.Header.Get("Accept") == "application/json" {
		s.state(w, r)
		return
	}
	http.Redirect(w, r, "/", http.StatusSeeOther)
}

func (s *Server) page(w http.ResponseWriter, _ *http.Request) {
	s.mu.Lock()
	data := map[string]any{"Live": s.live, "Viewers": s.viewers, "Quota": s.quota, "Messages": len(s.msgs), "Calls": s.calls, "VideoID": VideoID, "ChannelID": ChannelID}
	s.mu.Unlock()
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	pageTmpl.Execute(w, data)
}

var pageTmpl = template.Must(template.New("page").Parse(`<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Fake YouTube</title>
<style>
  :root { color-scheme: light dark; font: 16px/1.5 system-ui, sans-serif; }
  body { max-width: 40rem; margin: 2rem auto; padding: 0 1rem; }
  h1 { font-size: 1.5rem; margin-bottom: 0.25rem; }
  h2 { font-size: 1rem; margin: 1.5rem 0 0.5rem; }
  form { display: flex; flex-wrap: wrap; gap: 0.5rem; align-items: center; margin: 0 0 0.5rem; }
  input[type=text], input[type=number] { padding: 0.25rem 0.5rem; font: inherit; }
  input[type=number] { width: 7rem; }
  button { font: inherit; padding: 0.25rem 0.75rem; }
  dl { display: grid; grid-template-columns: max-content 1fr; gap: 0.25rem 1rem; }
  dt { font-weight: 600; }
  dd { margin: 0; font-variant-numeric: tabular-nums; }
  code { font-family: ui-monospace, monospace; }
</style>
<h1>Fake YouTube</h1>
<dl>
  <dt>Broadcast</dt><dd>{{if .Live}}Live{{else}}Ended{{end}} (video <code>{{.VideoID}}</code>, channel <code>{{.ChannelID}}</code>)</dd>
  <dt>Viewers</dt><dd>{{.Viewers}}</dd>
  <dt>Chat messages</dt><dd>{{.Messages}}</dd>
  <dt>Quota</dt><dd>{{if .Quota}}Exceeded{{else}}OK{{end}}</dd>
  <dt>API calls</dt><dd>{{range $k, $v := .Calls}}{{$k}} {{$v}}; {{end}}</dd>
</dl>

<h2>Broadcast</h2>
<form method="post" action="/control/viewers">
  <label>Viewers <input type="number" name="n" min="0" value="{{.Viewers}}"></label>
  <button>Set viewers</button>
</form>
<form method="post" action="/control/live">
  <input type="hidden" name="on" value="{{if .Live}}0{{else}}1{{end}}">
  <button>{{if .Live}}End broadcast{{else}}Start broadcast{{end}}</button>
</form>
<form method="post" action="/control/quota">
  <input type="hidden" name="on" value="{{if .Quota}}0{{else}}1{{end}}">
  <button>{{if .Quota}}Restore quota{{else}}Exhaust quota{{end}}</button>
</form>

<h2>Chat</h2>
<form method="post" action="/control/chat">
  <input type="text" name="name" placeholder="Name" required>
  <input type="text" name="text" placeholder="Message">
  <label><input type="checkbox" name="member"> Member</label>
  <button>Send</button>
</form>
<form method="post" action="/control/members">
  <label>Members <input type="number" name="n" min="1" max="5000" value="25"></label>
  <button>Add chatting members</button>
</form>

<h2>Super Chat</h2>
<form method="post" action="/control/superchat">
  <input type="text" name="name" placeholder="Name" required>
  <label>$ <input type="number" name="amount" min="1" step="0.01" value="5"></label>
  <input type="text" name="text" placeholder="Message">
  <label><input type="checkbox" name="member"> Member</label>
  <button>Send Super Chat</button>
</form>
<form method="post" action="/control/supersticker">
  <input type="text" name="name" placeholder="Name" required>
  <label>$ <input type="number" name="amount" min="1" step="0.01" value="2"></label>
  <button>Send Super Sticker</button>
</form>

<h2>Memberships</h2>
<form method="post" action="/control/member">
  <input type="text" name="name" placeholder="Name" required>
  <button>Join</button>
</form>
<form method="post" action="/control/gift">
  <input type="text" name="name" placeholder="Gifter" required>
  <label>Gifts <input type="number" name="n" min="1" max="50" value="5"></label>
  <button>Gift memberships</button>
</form>
</html>
`))
