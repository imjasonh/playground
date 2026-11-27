use crate::engine::ai::play_ai_turn;
use crate::engine::ebm::build_default_ebm_map;
use crate::engine::map::{MapIndex, PlayerId};
use crate::engine::protocol::{ClientMsg, DraftPreview, RoomLobby, SeatInfo, ServerMsg};
use crate::engine::rules::{apply_action, new_game, PlayerSpec};
use crate::engine::state::{GameConfig, GameState, TurnPhase, PLAYER_COLORS};
use serde::{Deserialize, Serialize};
use worker::{
    durable_object, event, Context, DurableObject, Env, Headers, Method, Request, Response, Result,
    State, WebSocket, WebSocketIncomingMessage, WebSocketPair,
};

const DO_BINDING: &str = "GAME_ROOMS";
const ROOM_KEY: &str = "room_doc";

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SeatRecord {
    slot: PlayerId,
    name: String,
    color: String,
    is_bot: bool,
    token: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct RoomDoc {
    code: String,
    config: GameConfig,
    seats: Vec<SeatRecord>,
    seq: u64,
    game: Option<GameState>,
}

impl RoomDoc {
    fn new(code: String) -> Self {
        Self {
            code,
            config: GameConfig::standard(),
            seats: Vec::new(),
            seq: 0,
            game: None,
        }
    }

    fn lobby(&self, connected_slots: &[PlayerId]) -> RoomLobby {
        RoomLobby {
            code: self.code.clone(),
            config: self.config.clone(),
            seats: self
                .seats
                .iter()
                .map(|s| SeatInfo {
                    slot: s.slot,
                    name: s.name.clone(),
                    color: s.color.clone(),
                    is_bot: s.is_bot,
                    connected: s.is_bot || connected_slots.contains(&s.slot),
                })
                .collect(),
            started: self.game.is_some(),
        }
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct WsAttachment {
    slot: Option<PlayerId>,
}

fn cors_headers() -> Headers {
    let h = Headers::new();
    let _ = h.set("Access-Control-Allow-Origin", "*");
    let _ = h.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    let _ = h.set("Access-Control-Allow-Headers", "Content-Type");
    h
}

fn with_cors(resp: Response) -> Response {
    resp.with_headers(cors_headers())
}

fn random_u64() -> u64 {
    let f = js_sys::Math::random();
    let t = js_sys::Date::now() as u64;
    t.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (f.to_bits())
}

fn random_room_code() -> String {
    const ALPHABET: &[u8] = b"ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
    let mut seed = random_u64();
    let mut out = String::with_capacity(4);
    for _ in 0..4 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let idx = ((seed >> 32) as usize) % ALPHABET.len();
        out.push(ALPHABET[idx] as char);
    }
    out
}

fn random_token() -> String {
    format!("{:016x}{:016x}", random_u64(), random_u64())
}

#[event(fetch)]
pub async fn main(req: Request, env: Env, _ctx: Context) -> Result<Response> {
    if req.method() == Method::Options {
        return Ok(with_cors(Response::empty()?.with_status(204)));
    }

    let url = req.url()?;
    let path = url.path();

    if path == "/health" {
        return Ok(with_cors(Response::ok("ok")?));
    }

    if path == "/api/rooms" && req.method() == Method::Post {
        let code = random_room_code();
        let ns = env.durable_object(DO_BINDING)?;
        let stub = ns.id_from_name(&code)?.get_stub()?;
        let init_req = Request::new(
            &format!("https://do.internal/init?code={code}"),
            Method::Post,
        )?;
        let _ = stub.fetch_with_request(init_req).await?;
        let body = serde_json::json!({ "code": code }).to_string();
        return Ok(with_cors(Response::ok(body)?));
    }

    // Routes: /api/rooms/<CODE>/ws or /api/rooms/<CODE>
    if let Some(rest) = path.strip_prefix("/api/rooms/") {
        let mut parts = rest.split('/');
        let code = parts.next().unwrap_or("").to_uppercase();
        if code.len() < 3 || code.len() > 8 || !code.chars().all(|c| c.is_ascii_alphanumeric()) {
            return Ok(with_cors(Response::error("Invalid room code", 400)?));
        }
        let ns = env.durable_object(DO_BINDING)?;
        let stub = ns.id_from_name(&code)?.get_stub()?;
        let resp = stub.fetch_with_request(req).await?;
        return Ok(resp);
    }

    Ok(with_cors(Response::error("Not found", 404)?))
}

#[durable_object]
pub struct GameRoomDo {
    state: State,
    #[allow(dead_code)]
    env: Env,
}

impl GameRoomDo {
    async fn load_room(&self, fallback_code: &str) -> Result<RoomDoc> {
        let storage = self.state.storage();
        if let Some(doc) = storage.get::<RoomDoc>(ROOM_KEY).await? {
            Ok(doc)
        } else {
            Ok(RoomDoc::new(fallback_code.to_string()))
        }
    }

    async fn save_room(&self, doc: &RoomDoc) -> Result<()> {
        self.state.storage().put(ROOM_KEY, doc).await
    }

    fn connected_slots(&self) -> Vec<PlayerId> {
        self.state
            .get_websockets()
            .into_iter()
            .filter_map(|ws| {
                ws.deserialize_attachment::<WsAttachment>()
                    .ok()
                    .flatten()
                    .and_then(|a| a.slot)
            })
            .collect()
    }

    fn send_msg(ws: &WebSocket, msg: &ServerMsg) {
        if let Ok(json) = serde_json::to_string(msg) {
            let _ = ws.send_with_str(json);
        }
    }

    fn broadcast(&self, msg: &ServerMsg) {
        if let Ok(json) = serde_json::to_string(msg) {
            for ws in self.state.get_websockets() {
                let _ = ws.send_with_str(&json);
            }
        }
    }

    fn broadcast_except(&self, sender: &WebSocket, msg: &ServerMsg) {
        let sender_slot = sender
            .deserialize_attachment::<WsAttachment>()
            .ok()
            .flatten()
            .and_then(|a| a.slot);
        if let Ok(json) = serde_json::to_string(msg) {
            for ws in self.state.get_websockets() {
                let ws_slot = ws
                    .deserialize_attachment::<WsAttachment>()
                    .ok()
                    .flatten()
                    .and_then(|a| a.slot);
                if sender_slot.is_some() && ws_slot == sender_slot {
                    continue;
                }
                let _ = ws.send_with_str(&json);
            }
        }
    }

    fn run_bot_turns_if_needed(&self, map: &MapIndex, doc: &mut RoomDoc) {
        let Some(game) = doc.game.as_mut() else {
            return;
        };
        let mut guard = 0;
        while game.phase != TurnPhase::Finished && guard < 12 {
            let cur = game.current_player as usize;
            if cur >= game.players.len() || !game.players[cur].is_bot {
                break;
            }
            guard += 1;
            if play_ai_turn(map, game).is_err() {
                break;
            }
            doc.seq += 1;
        }
    }
}

impl DurableObject for GameRoomDo {
    fn new(state: State, env: Env) -> Self {
        Self { state, env }
    }

    async fn fetch(&self, req: Request) -> Result<Response> {
        let url = req.url()?;
        let path = url.path();

        if path == "/init" {
            let code = url
                .query_pairs()
                .find(|(k, _)| k == "code")
                .map(|(_, v)| v.to_uppercase())
                .unwrap_or_else(|| "ROOM".to_string());
            let doc = RoomDoc::new(code);
            self.save_room(&doc).await?;
            return Ok(with_cors(Response::ok("initialized")?));
        }

        if path.ends_with("/ws") {
            let code = path
                .strip_prefix("/api/rooms/")
                .and_then(|r| r.split('/').next())
                .unwrap_or("ROOM")
                .to_uppercase();
            // Ensure room exists in storage.
            if self
                .state
                .storage()
                .get::<RoomDoc>(ROOM_KEY)
                .await?
                .is_none()
            {
                self.save_room(&RoomDoc::new(code)).await?;
            }

            let pair = WebSocketPair::new()?;
            self.state.accept_web_socket(&pair.server);
            let _ = pair
                .server
                .serialize_attachment(WsAttachment { slot: None });
            return Response::from_websocket(pair.client);
        }

        let code = path
            .strip_prefix("/api/rooms/")
            .and_then(|r| r.split('/').next())
            .unwrap_or("ROOM")
            .to_uppercase();
        let doc = self.load_room(&code).await?;
        let lobby = doc.lobby(&self.connected_slots());
        let body = serde_json::to_string(&lobby).unwrap_or_else(|_| "{}".to_string());
        Ok(with_cors(Response::ok(body)?))
    }

    async fn websocket_message(
        &self,
        ws: WebSocket,
        message: WebSocketIncomingMessage,
    ) -> Result<()> {
        let text = match message {
            WebSocketIncomingMessage::String(s) => s,
            WebSocketIncomingMessage::Binary(b) => String::from_utf8_lossy(&b).to_string(),
        };

        let msg: ClientMsg = match serde_json::from_str(&text) {
            Ok(m) => m,
            Err(e) => {
                Self::send_msg(
                    &ws,
                    &ServerMsg::Error {
                        message: format!("Malformed message: {e}"),
                    },
                );
                return Ok(());
            }
        };

        if matches!(msg, ClientMsg::Ping) {
            Self::send_msg(&ws, &ServerMsg::Pong);
            return Ok(());
        }

        let mut doc = self.load_room("ROOM").await?;
        let attachment = ws
            .deserialize_attachment::<WsAttachment>()
            .ok()
            .flatten()
            .unwrap_or_default();

        match msg {
            ClientMsg::Join { name, color, token } => {
                let clean_name = name.trim();
                let clean_name = if clean_name.is_empty() {
                    "Conductor".to_string()
                } else {
                    clean_name.chars().take(24).collect()
                };

                // Reclaim seat by token if provided.
                if let Some(tok) = token {
                    if let Some(seat) = doc.seats.iter().find(|s| !s.is_bot && s.token == tok) {
                        let slot = seat.slot;
                        let tok_copy = seat.token.clone();
                        let _ = ws.serialize_attachment(WsAttachment { slot: Some(slot) });
                        let lobby = doc.lobby(&self.connected_slots());
                        Self::send_msg(
                            &ws,
                            &ServerMsg::Welcome {
                                code: doc.code.clone(),
                                slot: Some(slot),
                                token: Some(tok_copy),
                                lobby: lobby.clone(),
                                state: doc.game.as_ref().map(|g| g.to_public()),
                            },
                        );
                        self.broadcast(&ServerMsg::LobbyUpdate { lobby });
                        return Ok(());
                    }
                }

                // If game already started or room full, join as spectator.
                if doc.game.is_some() || doc.seats.len() >= 6 {
                    let lobby = doc.lobby(&self.connected_slots());
                    Self::send_msg(
                        &ws,
                        &ServerMsg::Welcome {
                            code: doc.code.clone(),
                            slot: None,
                            token: None,
                            lobby,
                            state: doc.game.as_ref().map(|g| g.to_public()),
                        },
                    );
                    return Ok(());
                }

                // Assign new seat.
                let slot = doc.seats.len() as PlayerId;
                let used_colors: Vec<&str> = doc.seats.iter().map(|s| s.color.as_str()).collect();
                let picked_color = color
                    .filter(|c| !used_colors.contains(&c.as_str()))
                    .unwrap_or_else(|| {
                        PLAYER_COLORS
                            .iter()
                            .find(|c| !used_colors.contains(*c))
                            .copied()
                            .unwrap_or(PLAYER_COLORS[slot as usize % PLAYER_COLORS.len()])
                            .to_string()
                    });
                let new_token = random_token();
                doc.seats.push(SeatRecord {
                    slot,
                    name: clean_name,
                    color: picked_color,
                    is_bot: false,
                    token: new_token.clone(),
                });
                self.save_room(&doc).await?;
                let _ = ws.serialize_attachment(WsAttachment { slot: Some(slot) });

                let lobby = doc.lobby(&self.connected_slots());
                Self::send_msg(
                    &ws,
                    &ServerMsg::Welcome {
                        code: doc.code.clone(),
                        slot: Some(slot),
                        token: Some(new_token),
                        lobby: lobby.clone(),
                        state: None,
                    },
                );
                self.broadcast(&ServerMsg::LobbyUpdate { lobby });
            }

            ClientMsg::UpdateConfig { config } => {
                if doc.game.is_some() {
                    Self::send_msg(
                        &ws,
                        &ServerMsg::Error {
                            message: "Cannot change config after game starts".into(),
                        },
                    );
                    return Ok(());
                }
                doc.config = config;
                self.save_room(&doc).await?;
                let lobby = doc.lobby(&self.connected_slots());
                self.broadcast(&ServerMsg::LobbyUpdate { lobby });
            }

            ClientMsg::AddBot { name } => {
                if doc.game.is_some() || doc.seats.len() >= 6 {
                    Self::send_msg(
                        &ws,
                        &ServerMsg::Error {
                            message: "Cannot add bot right now".into(),
                        },
                    );
                    return Ok(());
                }
                let slot = doc.seats.len() as PlayerId;
                let used_colors: Vec<&str> = doc.seats.iter().map(|s| s.color.as_str()).collect();
                let color = PLAYER_COLORS
                    .iter()
                    .find(|c| !used_colors.contains(*c))
                    .copied()
                    .unwrap_or(PLAYER_COLORS[slot as usize % PLAYER_COLORS.len()])
                    .to_string();
                let bot_name = name.unwrap_or_else(|| format!("RailBot {}", slot + 1));
                doc.seats.push(SeatRecord {
                    slot,
                    name: bot_name,
                    color,
                    is_bot: true,
                    token: String::new(),
                });
                self.save_room(&doc).await?;
                let lobby = doc.lobby(&self.connected_slots());
                self.broadcast(&ServerMsg::LobbyUpdate { lobby });
            }

            ClientMsg::RemoveBot { slot } => {
                if doc.game.is_some() {
                    return Ok(());
                }
                if let Some(pos) = doc.seats.iter().position(|s| s.slot == slot && s.is_bot) {
                    doc.seats.remove(pos);
                    for (i, s) in doc.seats.iter_mut().enumerate() {
                        s.slot = i as PlayerId;
                    }
                    self.save_room(&doc).await?;
                    let lobby = doc.lobby(&self.connected_slots());
                    self.broadcast(&ServerMsg::LobbyUpdate { lobby });
                }
            }

            ClientMsg::StartGame => {
                if doc.game.is_some() {
                    return Ok(());
                }
                if doc.seats.len() < 2 {
                    Self::send_msg(
                        &ws,
                        &ServerMsg::Error {
                            message: "Need at least 2 players (or add a RailBot) to start".into(),
                        },
                    );
                    return Ok(());
                }
                let map = MapIndex::new(build_default_ebm_map());
                let specs: Vec<PlayerSpec> = doc
                    .seats
                    .iter()
                    .map(|s| PlayerSpec {
                        name: s.name.clone(),
                        color: Some(s.color.clone()),
                        is_bot: s.is_bot,
                    })
                    .collect();
                match new_game(&map, doc.config.clone(), &specs, random_u64()) {
                    Ok(g) => {
                        doc.game = Some(g);
                        doc.seq = 1;
                        self.run_bot_turns_if_needed(&map, &mut doc);
                        self.save_room(&doc).await?;
                        let lobby = doc.lobby(&self.connected_slots());
                        self.broadcast(&ServerMsg::LobbyUpdate { lobby });
                        if let Some(g) = &doc.game {
                            self.broadcast(&ServerMsg::StateUpdate {
                                seq: doc.seq,
                                state: g.to_public(),
                            });
                        }
                    }
                    Err(e) => {
                        Self::send_msg(&ws, &ServerMsg::Error { message: e.message });
                    }
                }
            }

            ClientMsg::GameAction { action } => {
                let Some(slot) = attachment.slot else {
                    Self::send_msg(
                        &ws,
                        &ServerMsg::Error {
                            message: "Spectators cannot perform actions".into(),
                        },
                    );
                    return Ok(());
                };
                let map = MapIndex::new(build_default_ebm_map());
                let res = match doc.game.as_mut() {
                    Some(g) => apply_action(&map, g, slot, action),
                    None => Err(crate::engine::state::RuleError::new("Game has not started")),
                };
                match res {
                    Ok(()) => {
                        doc.seq += 1;
                        self.run_bot_turns_if_needed(&map, &mut doc);
                        self.save_room(&doc).await?;
                        if let Some(g) = &doc.game {
                            self.broadcast(&ServerMsg::StateUpdate {
                                seq: doc.seq,
                                state: g.to_public(),
                            });
                        }
                    }
                    Err(e) => {
                        Self::send_msg(&ws, &ServerMsg::Error { message: e.message });
                    }
                }
            }

            ClientMsg::Draft {
                build_edges,
                move_path,
            } => {
                if let Some(slot) = attachment.slot {
                    self.broadcast_except(
                        &ws,
                        &ServerMsg::DraftBroadcast {
                            draft: DraftPreview {
                                player_id: slot,
                                build_edges,
                                move_path,
                            },
                        },
                    );
                }
            }

            ClientMsg::Ping => {}
        }

        Ok(())
    }

    async fn websocket_close(
        &self,
        _ws: WebSocket,
        _code: usize,
        _reason: String,
        _was_clean: bool,
    ) -> Result<()> {
        if let Ok(doc) = self.load_room("ROOM").await {
            let lobby = doc.lobby(&self.connected_slots());
            self.broadcast(&ServerMsg::LobbyUpdate { lobby });
        }
        Ok(())
    }
}
