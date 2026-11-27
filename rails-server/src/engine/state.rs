use crate::engine::map::{Card, EventEffect, MilepostId, PlayerId};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub const PLAYER_COLORS: [&str; 6] = [
    "#e11d48", // Crimson
    "#2563eb", // Cobalt
    "#16a34a", // Emerald
    "#d97706", // Amber
    "#9333ea", // Violet
    "#0891b2", // Teal
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GameMode {
    Standard,
    Fast,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GameConfig {
    pub map_id: String,
    pub mode: GameMode,
    pub events_enabled: bool,
    pub victory_cash: u32,
    pub victory_major_cities: usize,
}

impl GameConfig {
    pub fn standard() -> Self {
        Self {
            map_id: "na_classic".to_string(),
            mode: GameMode::Standard,
            events_enabled: false,
            victory_cash: 250,
            victory_major_cities: 5,
        }
    }

    pub fn fast() -> Self {
        Self {
            map_id: "na_classic".to_string(),
            mode: GameMode::Fast,
            events_enabled: false,
            victory_cash: 250,
            victory_major_cities: 5,
        }
    }

    pub fn starting_cash(&self) -> u32 {
        match self.mode {
            GameMode::Standard => 40,
            GameMode::Fast => 60,
        }
    }

    pub fn initial_build_rounds(&self) -> u8 {
        match self.mode {
            GameMode::Standard => 2,
            GameMode::Fast => 3,
        }
    }

    pub fn initial_hand_size(&self) -> usize {
        match self.mode {
            GameMode::Standard => 3,
            GameMode::Fast => 5,
        }
    }

    pub fn build_budget_per_turn(&self) -> u32 {
        20
    }

    pub fn trackage_fee(&self) -> u32 {
        4
    }

    pub fn upgrade_cost(&self) -> u32 {
        20
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrainTier {
    Freight,
    FastFreight,
    HeavyFreight,
    Superfreight,
}

impl TrainTier {
    pub fn speed(self, mode: GameMode) -> u32 {
        match (self, mode) {
            (TrainTier::Freight | TrainTier::HeavyFreight, GameMode::Standard) => 9,
            (TrainTier::FastFreight | TrainTier::Superfreight, GameMode::Standard) => 12,
            (TrainTier::Freight | TrainTier::HeavyFreight, GameMode::Fast) => 12,
            (TrainTier::FastFreight | TrainTier::Superfreight, GameMode::Fast) => 16,
        }
    }

    pub fn capacity(self) -> usize {
        match self {
            TrainTier::Freight | TrainTier::FastFreight => 2,
            TrainTier::HeavyFreight | TrainTier::Superfreight => 3,
        }
    }

    pub fn can_upgrade_to(self, target: TrainTier) -> bool {
        matches!(
            (self, target),
            (TrainTier::Freight, TrainTier::FastFreight)
                | (TrainTier::Freight, TrainTier::HeavyFreight)
                | (TrainTier::FastFreight, TrainTier::Superfreight)
                | (TrainTier::HeavyFreight, TrainTier::Superfreight)
        )
    }

    pub fn can_crossgrade_to(self, target: TrainTier) -> bool {
        matches!(
            (self, target),
            (TrainTier::FastFreight, TrainTier::HeavyFreight)
                | (TrainTier::HeavyFreight, TrainTier::FastFreight)
        )
    }

    pub fn label(self) -> &'static str {
        match self {
            TrainTier::Freight => "Freight",
            TrainTier::FastFreight => "Fast Freight",
            TrainTier::HeavyFreight => "Heavy Freight",
            TrainTier::Superfreight => "Superfreight",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlayerState {
    pub id: PlayerId,
    pub name: String,
    pub color: String,
    pub is_bot: bool,
    pub cash: u32,
    pub debt: u32,
    pub train_tier: TrainTier,
    pub train_pos: Option<MilepostId>,
    pub cargo: Vec<String>,
    pub hand: Vec<Card>,
    pub skip_next_turn: bool,
    pub deliveries_completed: u32,
    pub total_earned: u32,
    pub total_spent_building: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrackSegment {
    pub a: MilepostId,
    pub b: MilepostId,
    pub owner: PlayerId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActiveEvent {
    pub card_id: u16,
    pub title: String,
    pub description: String,
    pub effect: EventEffect,
    pub drawn_by: PlayerId,
    /// If `Some(pid)`, expires at the end of `pid`'s next turn. If `None`, persists until resolved.
    pub expires_after_turn_of: Option<PlayerId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TurnPhase {
    /// Initial build-only rounds (2 in Standard with Switchback, 3 in Fast).
    InitialBuild,
    /// Fast mode: discard down from 5 to 3 cards before regular play begins.
    TrimHand,
    /// Regular turn: move train, pick up, drop, deliver loads.
    Operate,
    /// Regular turn: build track (up to $20M) or upgrade train ($20M).
    Build,
    /// Game over.
    Finished,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnTracker {
    pub moves_used: u32,
    pub build_spent: u32,
    pub major_city_exits: u8,
    pub paid_opponents: Vec<PlayerId>,
    pub upgraded_this_turn: bool,
    pub has_acted_this_turn: bool,
    pub can_undo: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LogEntry {
    pub seq: u64,
    pub turn: u32,
    pub player_id: Option<PlayerId>,
    pub text: String,
}

/// Snapshot used for checkpoint-safe undo within the current turn (cleared on card draw).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UndoCheckpoint {
    pub players: Vec<PlayerState>,
    pub tracks: Vec<TrackSegment>,
    pub chip_supply: HashMap<String, u8>,
    pub phase: TurnPhase,
    pub turn_tracker: TurnTracker,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    pub config: GameConfig,
    pub rng_seed: u64,
    pub rng_step: u64,
    pub first_player: PlayerId,
    pub initial_step: usize,
    pub turn_number: u32,
    pub initial_round: u8,
    pub current_player: PlayerId,
    pub phase: TurnPhase,
    pub turn_tracker: TurnTracker,
    pub final_round: bool,
    pub players: Vec<PlayerState>,
    pub tracks: Vec<TrackSegment>,
    pub chip_supply: HashMap<String, u8>,
    pub draw_pile: Vec<Card>,
    pub discard_pile: Vec<Card>,
    pub active_events: Vec<ActiveEvent>,
    pub winner: Option<PlayerId>,
    pub log: Vec<LogEntry>,
    pub next_log_seq: u64,
    #[serde(skip)]
    pub undo_checkpoint: Option<UndoCheckpoint>,
}

/// Network-safe view of `GameState` that hides the undealt `draw_pile` order.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublicGameState {
    pub config: GameConfig,
    pub first_player: PlayerId,
    pub turn_number: u32,
    pub initial_round: u8,
    pub current_player: PlayerId,
    pub phase: TurnPhase,
    pub turn_tracker: TurnTracker,
    pub final_round: bool,
    pub players: Vec<PlayerState>,
    pub tracks: Vec<TrackSegment>,
    pub chip_supply: HashMap<String, u8>,
    pub draw_pile_count: usize,
    pub discard_pile_count: usize,
    pub active_events: Vec<ActiveEvent>,
    pub winner: Option<PlayerId>,
    pub log: Vec<LogEntry>,
}

impl GameState {
    pub fn to_public(&self) -> PublicGameState {
        PublicGameState {
            config: self.config.clone(),
            first_player: self.first_player,
            turn_number: self.turn_number,
            initial_round: self.initial_round,
            current_player: self.current_player,
            phase: self.phase,
            turn_tracker: self.turn_tracker.clone(),
            final_round: self.final_round,
            players: self.players.clone(),
            tracks: self.tracks.clone(),
            chip_supply: self.chip_supply.clone(),
            draw_pile_count: self.draw_pile.len(),
            discard_pile_count: self.discard_pile.len(),
            active_events: self.active_events.clone(),
            winner: self.winner,
            log: self.log.iter().rev().take(60).rev().cloned().collect(),
        }
    }

    pub fn push_log(&mut self, player_id: Option<PlayerId>, text: impl Into<String>) {
        let seq = self.next_log_seq;
        self.next_log_seq += 1;
        self.log.push(LogEntry {
            seq,
            turn: self.turn_number,
            player_id,
            text: text.into(),
        });
        if self.log.len() > 200 {
            let drain = self.log.len() - 200;
            self.log.drain(0..drain);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Action {
    /// Fast mode only: discard extra cards down to 3 before regular play.
    DiscardInitialCards { indices: Vec<usize> },
    /// Place locomotive on any city at the start of the player's first regular turn.
    PlaceTrain { milepost: MilepostId },
    /// Move locomotive along a contiguous path of mileposts (starting from current position).
    MoveTrain { path: Vec<MilepostId> },
    /// Pick up one unit of `commodity` at the train's current city.
    PickupLoad { commodity: String },
    /// Drop cargo at index `slot` (free at any city, returns chip to tray).
    DropLoad { slot: usize },
    /// Deliver cargo at `slot` to satisfy demand `demand_index` on hand card `card_index`.
    DeliverLoad {
        slot: usize,
        card_index: usize,
        demand_index: usize,
    },
    /// Deliver cargo at `slot` to satisfy a persistent global event (e.g. Heating Fuel Shortage).
    DeliverEventBonus { slot: usize, event_card_id: u16 },
    /// Discard entire hand, draw 3 new demand cards, and end turn immediately (only if no actions taken yet).
    PitchHand,
    /// Transition from Operate phase to Build phase.
    EndOperatePhase,
    /// Build a sequence of directed edges `(from, to)` during InitialBuild or Build phase.
    BuildTrack {
        edges: Vec<(MilepostId, MilepostId)>,
    },
    /// Upgrade locomotive to `target_tier` ($20M, consumes Build phase).
    UpgradeTrain { target_tier: TrainTier },
    /// Emergency loan (up to $20M, adds 2x to debt repaid automatically on deliveries).
    Borrow { amount: u32 },
    /// Undo actions back to the last checkpoint within the current turn.
    Undo,
    /// Finish current player's turn and advance to the next player.
    EndTurn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuleError {
    pub message: String,
}

impl RuleError {
    pub fn new(msg: impl Into<String>) -> Self {
        Self {
            message: msg.into(),
        }
    }
}

impl std::fmt::Display for RuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for RuleError {}
