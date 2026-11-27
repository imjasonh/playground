use crate::engine::map::{MilepostId, PlayerId};
use crate::engine::state::{Action, GameConfig, PublicGameState};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SeatInfo {
    pub slot: PlayerId,
    pub name: String,
    pub color: String,
    pub is_bot: bool,
    pub connected: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoomLobby {
    pub code: String,
    pub config: GameConfig,
    pub seats: Vec<SeatInfo>,
    pub started: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DraftPreview {
    pub player_id: PlayerId,
    #[serde(default)]
    pub build_edges: Vec<(MilepostId, MilepostId)>,
    #[serde(default)]
    pub move_path: Vec<MilepostId>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ClientMsg {
    /// Join or reconnect to a room (pass saved `token` to reclaim your seat).
    Join {
        name: String,
        #[serde(default)]
        color: Option<String>,
        #[serde(default)]
        token: Option<String>,
    },
    /// Update room ruleset before the game starts.
    UpdateConfig { config: GameConfig },
    /// Add a computer player to the lobby before the game starts.
    AddBot {
        #[serde(default)]
        name: Option<String>,
    },
    /// Remove a bot seat before the game starts.
    RemoveBot { slot: PlayerId },
    /// Start the game (requires >= 2 seats).
    StartGame,
    /// Apply a game action on your turn.
    GameAction { action: Action },
    /// Ephemeral live preview of hovered/staged track or train route (for Google Meet play).
    Draft {
        #[serde(default)]
        build_edges: Vec<(MilepostId, MilepostId)>,
        #[serde(default)]
        move_path: Vec<MilepostId>,
    },
    /// Keepalive ping.
    Ping,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ServerMsg {
    /// Sent right after `Join` with the player's seat slot and reconnect token.
    Welcome {
        code: String,
        slot: Option<PlayerId>,
        token: Option<String>,
        lobby: RoomLobby,
        state: Option<PublicGameState>,
    },
    /// Broadcast whenever lobby seats or config change.
    LobbyUpdate { lobby: RoomLobby },
    /// Broadcast whenever authoritative game state advances.
    StateUpdate { seq: u64, state: PublicGameState },
    /// Broadcast ephemeral draft track/route preview from the active player.
    DraftBroadcast { draft: DraftPreview },
    /// Error response for an invalid message or illegal game action.
    Error { message: String },
    /// Pong response.
    Pong,
}
