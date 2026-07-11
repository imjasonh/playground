# Spotify Play

A static browser app that signs you into Spotify with **Authorization Code +
PKCE**, searches the catalog via the Web API, and streams tracks in-tab with
the [Web Playback SDK](https://developer.spotify.com/documentation/web-playback-sdk).

Playback requires a **Spotify Premium** account. Free accounts can log in and
search, but the SDK will report an account error when you try to play.

## Setup

1. Open the [Spotify Developer Dashboard](https://developer.spotify.com/dashboard)
   and create an app.
2. Under **Redirect URIs**, add the exact URI shown on the login screen (also
   printed below for local use):
   - Local: `http://localhost:3000/`
   - Production Pages: `https://<owner>.github.io/playground/spotify/`
   - PR preview: `https://<owner>.github.io/playground/preview/pr-<N>/spotify/`
3. Copy the app’s **Client ID** into the login form (it is stored only in
   `localStorage` — no client secret is used).

## Run locally

```bash
npm start
```

Open <http://localhost:3000>, paste your Client ID, and log in.

## Tests

Pure helpers (PKCE, token storage, search mapping, play request shaping) are
covered with Node’s built-in test runner:

```bash
npm test
```

## How it works

1. **Login** — generates a PKCE verifier/challenge, redirects to
   `accounts.spotify.com/authorize`, then exchanges the returned `code` for
   tokens at `/api/token` (no client secret).
2. **Search** — `GET /v1/search?type=track` with the access token.
3. **Play** — loads `https://sdk.scdn.co/spotify-player.js`, connects a
   `Spotify.Player` (a Connect device in this tab), then
   `PUT /v1/me/player/play?device_id=…` with the track URI.

Access tokens refresh automatically via the stored refresh token until Spotify
revokes consent or the refresh token expires.
