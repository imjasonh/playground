// Package youtube reads a live broadcast's viewer count and chat from the
// YouTube Data API.
package youtube

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strconv"
	"strings"
	"time"

	"github.com/imjasonh/playground/stream-boids/internal/secret"
)

// DefaultBase is the YouTube Data API v3 endpoint.
const DefaultBase = "https://www.googleapis.com/youtube/v3"

// Client calls the YouTube Data API.
type Client struct {
	// Base is the API endpoint. Empty means DefaultBase.
	Base string
	// Key returns the API key. Nil sends requests without one, which only
	// a fake server accepts.
	Key secret.Func
	// HTTP sends requests. Nil means a client with a 15-second timeout.
	HTTP *http.Client
}

// Video is a broadcast's live state.
type Video struct {
	ID string
	// Live is true while the broadcast is on the air.
	Live bool
	// Viewers is the concurrent viewer count. ViewersKnown is false when
	// YouTube didn't report one, as when the channel hides it.
	Viewers      int
	ViewersKnown bool
	// ChatID is the live chat's ID, or empty when chat is off.
	ChatID string
}

// Author is a chat message's sender.
type Author struct {
	ChannelID string
	Name      string
	// Member is true when the sender is a channel member.
	Member bool
}

// Message types this package reads. YouTube sends others, which carry
// only the author.
const (
	TextMessage            = "textMessageEvent"
	SuperChat              = "superChatEvent"
	SuperSticker           = "superStickerEvent"
	NewSponsor             = "newSponsorEvent"
	MemberMilestone        = "memberMilestoneChatEvent"
	MembershipGifting      = "membershipGiftingEvent"
	GiftMembershipReceived = "giftMembershipReceivedEvent"
)

// Message is one live chat message or event.
type Message struct {
	ID        string
	Type      string
	Published time.Time
	Author    Author
	Text      string
	// Tier is a Super Chat or Super Sticker's tier, from 1 up.
	Tier int
	// Amount is a Super Chat or Super Sticker's price as YouTube formats
	// it, such as "$5.00".
	Amount string
	// Gifts is the number of memberships a membership gifting event gave.
	Gifts int
}

// ChatPage is one response from liveChatMessages.list.
type ChatPage struct {
	Messages []Message
	// Next is the token for the next request.
	Next string
	// Interval is how long YouTube asks the caller to wait before the next
	// request.
	Interval time.Duration
	// Offline is true when the chat has gone offline.
	Offline bool
}

// APIError is an error response from the API.
type APIError struct {
	Status  int
	Reason  string
	Message string
}

func (e *APIError) Error() string {
	return fmt.Sprintf("youtube: %d %s: %s", e.Status, e.Reason, e.Message)
}

// Quota reports whether the error means the project ran out of quota.
func (e *APIError) Quota() bool {
	switch e.Reason {
	case "quotaExceeded", "dailyLimitExceeded", "rateLimitExceeded", "userRateLimitExceeded":
		return true
	}
	return false
}

// ChatGone reports whether the error means the chat no longer exists.
func (e *APIError) ChatGone() bool {
	switch e.Reason {
	case "liveChatEnded", "liveChatDisabled", "liveChatNotFound":
		return true
	}
	return false
}

// IsQuota reports whether err is an APIError for exhausted quota.
func IsQuota(err error) bool {
	var ae *APIError
	return errors.As(err, &ae) && ae.Quota()
}

// IsChatGone reports whether err is an APIError for a chat that ended.
func IsChatGone(err error) bool {
	var ae *APIError
	return errors.As(err, &ae) && ae.ChatGone()
}

// Video reads a video's live state. It costs 1 quota unit.
func (c *Client) Video(ctx context.Context, id string) (Video, error) {
	var resp struct {
		Items []struct {
			ID      string `json:"id"`
			Snippet struct {
				LiveBroadcastContent string `json:"liveBroadcastContent"`
			} `json:"snippet"`
			LiveStreamingDetails struct {
				ActualStartTime   string `json:"actualStartTime"`
				ActualEndTime     string `json:"actualEndTime"`
				ConcurrentViewers string `json:"concurrentViewers"`
				ActiveLiveChatID  string `json:"activeLiveChatId"`
			} `json:"liveStreamingDetails"`
		} `json:"items"`
	}
	err := c.get(ctx, "videos", url.Values{"part": {"snippet,liveStreamingDetails"}, "id": {id}}, &resp)
	if err != nil {
		return Video{}, err
	}
	if len(resp.Items) == 0 {
		return Video{}, fmt.Errorf("youtube: video %s not found", id)
	}
	it := resp.Items[0]
	d := it.LiveStreamingDetails
	v := Video{
		ID:     it.ID,
		Live:   it.Snippet.LiveBroadcastContent == "live" && d.ActualStartTime != "" && d.ActualEndTime == "",
		ChatID: d.ActiveLiveChatID,
	}
	if n, err := strconv.Atoi(d.ConcurrentViewers); err == nil && v.Live {
		v.Viewers, v.ViewersKnown = n, true
	}
	return v, nil
}

// LiveVideo returns the ID of the channel's current live broadcast, or ""
// when none is live. It costs 100 quota units.
func (c *Client) LiveVideo(ctx context.Context, channelID string) (string, error) {
	var resp struct {
		Items []struct {
			ID struct {
				VideoID string `json:"videoId"`
			} `json:"id"`
		} `json:"items"`
	}
	err := c.get(ctx, "search", url.Values{
		"part": {"id"}, "channelId": {channelID}, "eventType": {"live"}, "type": {"video"}, "maxResults": {"1"},
	}, &resp)
	if err != nil || len(resp.Items) == 0 {
		return "", err
	}
	return resp.Items[0].ID.VideoID, nil
}

// Chat reads the chat messages after the page token. An empty token
// returns recent history. It costs 5 quota units.
func (c *Client) Chat(ctx context.Context, chatID, pageToken string) (ChatPage, error) {
	var resp struct {
		NextPageToken         string `json:"nextPageToken"`
		PollingIntervalMillis int    `json:"pollingIntervalMillis"`
		OfflineAt             string `json:"offlineAt"`
		Items                 []struct {
			ID      string `json:"id"`
			Snippet struct {
				Type             string `json:"type"`
				PublishedAt      string `json:"publishedAt"`
				DisplayMessage   string `json:"displayMessage"`
				SuperChatDetails *struct {
					AmountDisplayString string `json:"amountDisplayString"`
					UserComment         string `json:"userComment"`
					Tier                int    `json:"tier"`
				} `json:"superChatDetails"`
				SuperStickerDetails *struct {
					AmountDisplayString string `json:"amountDisplayString"`
					Tier                int    `json:"tier"`
				} `json:"superStickerDetails"`
				MembershipGiftingDetails *struct {
					GiftMembershipsCount int `json:"giftMembershipsCount"`
				} `json:"membershipGiftingDetails"`
			} `json:"snippet"`
			AuthorDetails struct {
				ChannelID     string `json:"channelId"`
				DisplayName   string `json:"displayName"`
				IsChatSponsor bool   `json:"isChatSponsor"`
			} `json:"authorDetails"`
		} `json:"items"`
	}
	q := url.Values{"liveChatId": {chatID}, "part": {"snippet,authorDetails"}, "maxResults": {"2000"}}
	if pageToken != "" {
		q.Set("pageToken", pageToken)
	}
	if err := c.get(ctx, "liveChat/messages", q, &resp); err != nil {
		return ChatPage{}, err
	}
	page := ChatPage{
		Next:     resp.NextPageToken,
		Interval: time.Duration(resp.PollingIntervalMillis) * time.Millisecond,
		Offline:  resp.OfflineAt != "",
	}
	for _, it := range resp.Items {
		s := it.Snippet
		m := Message{
			ID:   it.ID,
			Type: s.Type,
			Text: s.DisplayMessage,
			Author: Author{
				ChannelID: it.AuthorDetails.ChannelID,
				Name:      it.AuthorDetails.DisplayName,
				Member:    it.AuthorDetails.IsChatSponsor,
			},
		}
		m.Published, _ = time.Parse(time.RFC3339Nano, s.PublishedAt)
		switch {
		case s.SuperChatDetails != nil:
			m.Tier, m.Amount, m.Text = s.SuperChatDetails.Tier, s.SuperChatDetails.AmountDisplayString, s.SuperChatDetails.UserComment
		case s.SuperStickerDetails != nil:
			m.Tier, m.Amount = s.SuperStickerDetails.Tier, s.SuperStickerDetails.AmountDisplayString
		case s.MembershipGiftingDetails != nil:
			m.Gifts = s.MembershipGiftingDetails.GiftMembershipsCount
		}
		page.Messages = append(page.Messages, m)
	}
	return page, nil
}

func (c *Client) get(ctx context.Context, path string, q url.Values, out any) error {
	base := c.Base
	if base == "" {
		base = DefaultBase
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, strings.TrimSuffix(base, "/")+"/"+path+"?"+q.Encode(), nil)
	if err != nil {
		return err
	}
	if c.Key != nil {
		key, err := c.Key(ctx)
		if err != nil {
			return fmt.Errorf("youtube: reading API key: %w", err)
		}
		// A header keeps the key out of URLs, which errors and proxies log.
		req.Header.Set("X-Goog-Api-Key", key)
	}
	hc := c.HTTP
	if hc == nil {
		hc = &http.Client{Timeout: 15 * time.Second}
	}
	resp, err := hc.Do(req)
	if err != nil {
		// The error names the URL, which holds IDs but not the key.
		return fmt.Errorf("youtube: %w", err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(io.LimitReader(resp.Body, 8<<20))
	if err != nil {
		return fmt.Errorf("youtube: reading %s: %w", path, err)
	}
	if resp.StatusCode != http.StatusOK {
		return parseError(resp.StatusCode, body)
	}
	if err := json.Unmarshal(body, out); err != nil {
		return fmt.Errorf("youtube: decoding %s: %w", path, err)
	}
	return nil
}

func parseError(status int, body []byte) error {
	var e struct {
		Error struct {
			Message string `json:"message"`
			Errors  []struct {
				Reason string `json:"reason"`
			} `json:"errors"`
		} `json:"error"`
	}
	ae := &APIError{Status: status}
	if json.Unmarshal(body, &e) == nil {
		ae.Message = e.Error.Message
		if len(e.Error.Errors) > 0 {
			ae.Reason = e.Error.Errors[0].Reason
		}
	}
	if ae.Message == "" {
		ae.Message = http.StatusText(status)
	}
	return ae
}
