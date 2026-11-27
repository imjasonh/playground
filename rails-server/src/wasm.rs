use crate::engine::ai::play_ai_turn;
use crate::engine::map::{edge_key, MapIndex, MilepostId, PlayerId};
use crate::engine::na_map::build_north_america_map;
use crate::engine::rules::{
    active_hazards, apply_action, can_enter_city, connected_major_cities_list, edge_owners_map,
    effective_move_limit, new_game, opponent_occupied_edges, player_build_anchors,
    player_owned_edges, reachable_mileposts, PlayerSpec,
};
use crate::engine::state::{Action, GameConfig, GameMode, GameState, PublicGameState};
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

#[derive(Deserialize)]
struct LocalPlayerInput {
    name: String,
    color: Option<String>,
    #[serde(default)]
    is_bot: bool,
}

#[derive(Deserialize)]
struct LocalGameOpts {
    mode: GameMode,
    events_enabled: bool,
    players: Vec<LocalPlayerInput>,
    seed: u64,
}

#[derive(Serialize)]
struct BuildPreview {
    edges: Vec<(MilepostId, MilepostId)>,
    total_cost: u32,
    affordable: bool,
    remaining_budget: u32,
    error: Option<String>,
}

#[derive(Serialize)]
struct MovePreview {
    path: Vec<MilepostId>,
    hops: u32,
    additional_fee: u32,
    new_opponents: Vec<PlayerId>,
    reachable: bool,
    error: Option<String>,
}

#[wasm_bindgen]
pub struct WasmEngine {
    map: MapIndex,
    local_state: Option<GameState>,
    remote_mirror: Option<PublicGameState>,
}

#[wasm_bindgen]
impl WasmEngine {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        let map = MapIndex::new(build_north_america_map());
        Self {
            map,
            local_state: None,
            remote_mirror: None,
        }
    }

    /// Return the static North America map definition as JSON for the Canvas renderer.
    pub fn get_map_json(&self) -> Result<String, JsValue> {
        serde_json::to_string(&self.map.data).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Start a local (hotseat or vs-AI) game and return its initial `PublicGameState` JSON.
    pub fn start_local_game(&mut self, opts_json: &str) -> Result<String, JsValue> {
        let opts: LocalGameOpts =
            serde_json::from_str(opts_json).map_err(|e| JsValue::from_str(&e.to_string()))?;
        let mut config = match opts.mode {
            GameMode::Standard => GameConfig::standard(),
            GameMode::Fast => GameConfig::fast(),
        };
        config.events_enabled = opts.events_enabled;

        let specs: Vec<PlayerSpec> = opts
            .players
            .into_iter()
            .map(|p| PlayerSpec {
                name: p.name,
                color: p.color,
                is_bot: p.is_bot,
            })
            .collect();

        let state = new_game(&self.map, config, &specs, opts.seed)
            .map_err(|e| JsValue::from_str(&e.message))?;
        let pub_json = serde_json::to_string(&state.to_public())
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        self.local_state = Some(state);
        self.remote_mirror = None;
        Ok(pub_json)
    }

    /// Mirror a `PublicGameState` received from the remote Cloudflare Worker for local previews.
    pub fn set_remote_state(&mut self, state_json: &str) -> Result<(), JsValue> {
        let pub_state: PublicGameState =
            serde_json::from_str(state_json).map_err(|e| JsValue::from_str(&e.to_string()))?;
        self.remote_mirror = Some(pub_state);
        self.local_state = None;
        Ok(())
    }

    /// Apply an `Action` JSON in local game mode and return the updated `PublicGameState` JSON.
    pub fn apply_local_action(
        &mut self,
        pid: PlayerId,
        action_json: &str,
    ) -> Result<String, JsValue> {
        let state = self
            .local_state
            .as_mut()
            .ok_or_else(|| JsValue::from_str("No local game active"))?;
        let action: Action =
            serde_json::from_str(action_json).map_err(|e| JsValue::from_str(&e.to_string()))?;
        apply_action(&self.map, state, pid, action).map_err(|e| JsValue::from_str(&e.message))?;
        serde_json::to_string(&state.to_public()).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Run one AI turn in local mode and return the updated `PublicGameState` JSON.
    pub fn step_local_ai(&mut self) -> Result<String, JsValue> {
        let state = self
            .local_state
            .as_mut()
            .ok_or_else(|| JsValue::from_str("No local game active"))?;
        play_ai_turn(&self.map, state).map_err(|e| JsValue::from_str(&e))?;
        serde_json::to_string(&state.to_public()).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Preview shortest track build path from player's network/major cities to `target_mp`.
    pub fn preview_build(&self, pid: PlayerId, target_mp: MilepostId) -> Result<String, JsValue> {
        let state = self.active_state_shim()?;
        let owned = player_owned_edges(&state, pid);
        let anchors = player_build_anchors(&self.map, &state, pid);
        let mut hazards = active_hazards(&self.map, &state);
        hazards
            .blocked_edges
            .extend(opponent_occupied_edges(&state, pid));
        let rem_budget = state
            .config
            .build_budget_per_turn()
            .saturating_sub(state.turn_tracker.build_spent);
        let cash = state.players[pid as usize].cash;

        let preview = match self.map.shortest_build_path(
            &anchors,
            target_mp,
            &owned,
            &hazards.blocked_edges,
            &hazards.blocked_nodes,
            |cid| can_enter_city(&self.map, &state, pid, cid),
        ) {
            Some((edges, total_cost)) => {
                let affordable = total_cost <= rem_budget && total_cost <= cash;
                let error = if edges.is_empty() {
                    Some("Already connected".into())
                } else if total_cost > rem_budget {
                    Some(format!(
                        "Cost ${total_cost}M exceeds ${rem_budget}M remaining turn budget"
                    ))
                } else if total_cost > cash {
                    Some(format!("Cost ${total_cost}M exceeds your ${cash}M cash"))
                } else {
                    None
                };
                BuildPreview {
                    edges,
                    total_cost,
                    affordable,
                    remaining_budget: rem_budget,
                    error,
                }
            }
            None => BuildPreview {
                edges: Vec::new(),
                total_cost: 0,
                affordable: false,
                remaining_budget: rem_budget,
                error: Some("No legal build route to that milepost".into()),
            },
        };

        serde_json::to_string(&preview).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Preview shortest movement path from current train position to `target_mp`.
    pub fn preview_move(&self, pid: PlayerId, target_mp: MilepostId) -> Result<String, JsValue> {
        let state = self.active_state_shim()?;
        let p = &state.players[pid as usize];
        let Some(start) = p.train_pos else {
            return serde_json::to_string(&MovePreview {
                path: Vec::new(),
                hops: 0,
                additional_fee: 0,
                new_opponents: Vec::new(),
                reachable: false,
                error: Some("Place your train first".into()),
            })
            .map_err(|e| JsValue::from_str(&e.to_string()));
        };

        let limit = effective_move_limit(&self.map, &state, pid);
        let remaining = limit.saturating_sub(state.turn_tracker.moves_used);
        let hazards = active_hazards(&self.map, &state);
        let owners = edge_owners_map(&state);
        let mut paid_mask = 0u8;
        for &opp in &state.turn_tracker.paid_opponents {
            paid_mask |= 1u8 << opp;
        }

        let preview = match self.map.shortest_move_path(
            start,
            target_mp,
            pid,
            &owners,
            &hazards.blocked_edges,
            &hazards.blocked_nodes,
            remaining,
            paid_mask,
            p.cash,
            state.config.trackage_fee(),
        ) {
            Some(res) => MovePreview {
                path: res.path,
                hops: res.hops,
                additional_fee: res.additional_fee,
                new_opponents: res.new_opponents,
                reachable: true,
                error: None,
            },
            None => MovePreview {
                path: Vec::new(),
                hops: 0,
                additional_fee: 0,
                new_opponents: Vec::new(),
                reachable: false,
                error: Some("Not reachable within remaining movement this turn".into()),
            },
        };

        serde_json::to_string(&preview).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Return all milepost IDs reachable by `pid` during the current Operate phase.
    pub fn reachable_mileposts_json(&self, pid: PlayerId) -> Result<String, JsValue> {
        let state = self.active_state_shim()?;
        let list = reachable_mileposts(&self.map, &state, pid);
        serde_json::to_string(&list).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Return connected major city IDs for every player (indexed by player slot).
    pub fn major_city_progress_json(&self) -> Result<String, JsValue> {
        let state = self.active_state_shim()?;
        let progress: Vec<Vec<String>> = state
            .players
            .iter()
            .map(|p| connected_major_cities_list(&self.map, &state, p.id))
            .collect();
        serde_json::to_string(&progress).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Return the direct cost of a single adjacent step `(from, to)`, or -1 if invalid.
    pub fn edge_step_cost(&self, from: MilepostId, to: MilepostId) -> i32 {
        let _ = edge_key(from, to);
        self.map
            .build_step_cost(from, to)
            .map(|c| c as i32)
            .unwrap_or(-1)
    }

    fn active_state_shim(&self) -> Result<GameState, JsValue> {
        if let Some(local) = &self.local_state {
            return Ok(local.clone());
        }
        if let Some(pub_s) = &self.remote_mirror {
            return Ok(GameState {
                config: pub_s.config.clone(),
                rng_seed: 0,
                rng_step: 0,
                first_player: pub_s.first_player,
                initial_step: 0,
                turn_number: pub_s.turn_number,
                initial_round: pub_s.initial_round,
                current_player: pub_s.current_player,
                phase: pub_s.phase,
                turn_tracker: pub_s.turn_tracker.clone(),
                final_round: pub_s.final_round,
                players: pub_s.players.clone(),
                tracks: pub_s.tracks.clone(),
                chip_supply: pub_s.chip_supply.clone(),
                draw_pile: Vec::new(),
                discard_pile: Vec::new(),
                active_events: pub_s.active_events.clone(),
                winner: pub_s.winner,
                log: pub_s.log.clone(),
                next_log_seq: 0,
                undo_checkpoint: None,
            });
        }
        Err(JsValue::from_str("No game state loaded"))
    }
}

impl Default for WasmEngine {
    fn default() -> Self {
        Self::new()
    }
}
