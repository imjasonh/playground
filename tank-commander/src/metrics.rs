//! Drama and stalemate metrics across simulated games.

use crate::game::{Game, Outcome};
use crate::unit::Side;
use crate::upgrades::LoadoutCensus;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GameReport {
    pub seed: u64,
    pub scenario: String,
    pub outcome: String,
    pub winner: Option<String>,
    pub first_player: String,
    pub activations: u32,
    pub shots_fired: u32,
    pub shots_missed: u32,
    pub at_shots: u32,
    pub he_shots: u32,
    pub moves_made: u32,
    pub turns_made: u32,
    pub turret_rotations: u32,
    pub hits: u32,
    pub pens: u32,
    pub glances: u32,
    pub suppressions: u32,
    pub fires: u32,
    pub cook_offs: u32,
    pub crew_wounds: u32,
    pub crew_kills: u32,
    pub abilities_used: u32,
    pub air_strikes: u32,
    pub infantry_kills: u32,
    pub smoke_deployed: u32,
    pub medkit_saves: u32,
    pub lt_covers: u32,
    pub mines_deployed: u32,
    pub mines_triggered: u32,
    pub mounts: u32,
    pub exterior_mounts: u32,
    pub embarks: u32,
    pub dismounts: u32,
    pub drop_offs: u32,
    pub passenger_kills: u32,
    pub exterior_rider_kills: u32,
    pub objectives_captured: u32,
    /// True when an infantry Capture ended the game.
    pub ended_by_capture: bool,
    pub loadout: LoadoutCensus,
    /// Lower-spend list won first activation (spoil skipped).
    pub list_initiative: bool,
    pub red_list_points: u32,
    pub blue_list_points: u32,
    pub red_units_left: u32,
    pub blue_units_left: u32,
    /// True when the game hit the activation cap with both sides still fighting.
    pub timed_out: bool,
    /// True when idle stalemate (no damage for `stalemate_after`) ended the game.
    pub ended_by_stalemate: bool,
    /// True when few shots were exchanged relative to activations.
    pub low_engagement: bool,
    /// True when many consecutive activations passed without a hit near the end.
    pub late_stalemate: bool,
    /// True when a side that was behind on HP still won.
    pub comeback: bool,
    pub red_final_hp: i32,
    pub blue_final_hp: i32,
    pub event_count: usize,
}

impl GameReport {
    pub fn from_game(game: &Game, seed: u64, hp_trace: &HpTrace) -> Self {
        let outcome = game.outcome();
        let red_alive = game
            .tanks
            .iter()
            .any(|t| t.side == Side::Red && t.is_operational());
        let blue_alive = game
            .tanks
            .iter()
            .any(|t| t.side == Side::Blue && t.is_operational());
        let hit_cap = game.activations >= game.max_activations;
        let ended_by_stalemate = game.stalemate_idle();
        let ended_by_capture = game.capture_winner().is_some();

        let low_engagement = game.shots_fired < game.activations / 4;
        let late_stalemate = game.activations_since_hit >= 6 && game.activations >= 12;

        let red_hp = hp_sum(game, Side::Red);
        let blue_hp = hp_sum(game, Side::Blue);

        let comeback = match outcome {
            Outcome::Winner(Side::Red) => hp_trace.red_was_behind,
            Outcome::Winner(Side::Blue) => hp_trace.blue_was_behind,
            _ => false,
        };

        let red_units_left = game
            .tanks
            .iter()
            .filter(|t| t.side == Side::Red && !t.destroyed)
            .count() as u32;
        let blue_units_left = game
            .tanks
            .iter()
            .filter(|t| t.side == Side::Blue && !t.destroyed)
            .count() as u32;

        GameReport {
            seed,
            scenario: game.scenario.clone(),
            outcome: outcome_str(outcome),
            winner: match outcome {
                Outcome::Winner(s) => Some(side_str(s).into()),
                _ => None,
            },
            first_player: side_str(game.first_player).into(),
            activations: game.activations,
            shots_fired: game.shots_fired,
            shots_missed: game.shots_missed,
            at_shots: game.at_shots,
            he_shots: game.he_shots,
            moves_made: game.moves_made,
            turns_made: game.turns_made,
            turret_rotations: game.turret_rotations,
            hits: game.total_hits,
            pens: game.total_pens,
            glances: game.total_glances,
            suppressions: game.total_suppressions,
            fires: game.total_fires,
            cook_offs: game.total_cook_offs,
            crew_wounds: game.total_crew_wounds,
            crew_kills: game.total_crew_kills,
            abilities_used: game.abilities_used,
            air_strikes: game.air_strikes_resolved,
            infantry_kills: game.infantry_kills,
            smoke_deployed: game.smoke_deployed,
            medkit_saves: game.medkit_saves,
            lt_covers: game.lt_covers,
            mines_deployed: game.mines_deployed,
            mines_triggered: game.mines_triggered,
            mounts: game.mounts,
            exterior_mounts: game.exterior_mounts,
            embarks: game.embarks,
            dismounts: game.dismounts,
            drop_offs: game.drop_offs,
            passenger_kills: game.passenger_kills,
            exterior_rider_kills: game.exterior_rider_kills,
            objectives_captured: game.objectives_captured,
            ended_by_capture,
            loadout: game.loadout_census.clone(),
            list_initiative: game.list_initiative,
            red_list_points: game.red_list_points,
            blue_list_points: game.blue_list_points,
            red_units_left,
            blue_units_left,
            timed_out: hit_cap
                && red_alive
                && blue_alive
                && !ended_by_stalemate
                && !ended_by_capture,
            ended_by_stalemate,
            low_engagement,
            late_stalemate,
            comeback,
            red_final_hp: red_hp,
            blue_final_hp: blue_hp,
            event_count: game.events.len(),
        }
    }
}

fn hp_sum(game: &Game, side: Side) -> i32 {
    game.tanks
        .iter()
        .filter(|t| t.side == side && !t.destroyed)
        .map(|t| t.hull_points)
        .sum()
}

fn side_str(s: Side) -> &'static str {
    match s {
        Side::Red => "Red",
        Side::Blue => "Blue",
    }
}

fn outcome_str(o: Outcome) -> String {
    match o {
        Outcome::Winner(s) => format!("Winner({})", side_str(s)),
        Outcome::Draw => "Draw".into(),
        Outcome::InProgress => "InProgress".into(),
    }
}

/// Tracks whether each side ever trailed on hull points (for comeback detection).
#[derive(Clone, Debug, Default)]
pub struct HpTrace {
    pub red_was_behind: bool,
    pub blue_was_behind: bool,
}

impl HpTrace {
    pub fn observe(&mut self, game: &Game) {
        let red = hp_sum(game, Side::Red);
        let blue = hp_sum(game, Side::Blue);
        if red < blue {
            self.red_was_behind = true;
        }
        if blue < red {
            self.blue_was_behind = true;
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AggregateReport {
    pub scenario: String,
    pub games: u32,
    pub red_wins: u32,
    pub blue_wins: u32,
    pub draws: u32,
    pub first_player_wins: u32,
    pub second_player_wins: u32,
    pub timed_out: u32,
    pub ended_by_stalemate: u32,
    pub low_engagement: u32,
    pub late_stalemate: u32,
    pub comebacks: u32,
    pub avg_activations: f64,
    pub avg_shots: f64,
    pub avg_at_shots: f64,
    pub avg_he_shots: f64,
    pub avg_moves: f64,
    pub avg_turns: f64,
    pub avg_turret: f64,
    pub avg_hits: f64,
    pub avg_pens: f64,
    pub avg_glances: f64,
    pub avg_suppressions: f64,
    pub avg_fires: f64,
    pub avg_cook_offs: f64,
    pub avg_crew_wounds: f64,
    pub avg_crew_kills: f64,
    pub avg_abilities_used: f64,
    pub avg_air_strikes: f64,
    pub avg_infantry_kills: f64,
    pub avg_smoke_deployed: f64,
    pub avg_medkit_saves: f64,
    pub avg_lt_covers: f64,
    pub avg_mines_deployed: f64,
    pub avg_mines_triggered: f64,
    pub avg_mounts: f64,
    pub avg_exterior_mounts: f64,
    pub avg_embarks: f64,
    pub avg_dismounts: f64,
    pub avg_drop_offs: f64,
    pub avg_passenger_kills: f64,
    pub avg_exterior_rider_kills: f64,
    /// Fraction of games with at least one Mount or Embark.
    pub embark_usage_rate: f64,
    pub avg_objectives_captured: f64,
    /// Fraction of games ended by Capture (not wipe / timeout).
    pub capture_win_rate: f64,
    /// Fraction of non-infantry units that bought each upgrade (0..=1).
    pub loadout_smoke_rate: f64,
    pub loadout_medkit_rate: f64,
    pub loadout_lt_rate: f64,
    pub loadout_optics_rate: f64,
    pub loadout_barrel_rate: f64,
    pub loadout_engine_rate: f64,
    pub loadout_ai_rate: f64,
    pub loadout_avg_armor_pts: f64,
    pub loadout_avg_mine_charges: f64,
    pub loadout_avg_points: f64,
    /// Fraction of games where under-spend decided initiative (spoil skipped).
    pub list_initiative_rate: f64,
    pub avg_red_list_points: f64,
    pub avg_blue_list_points: f64,
    pub avg_list_point_gap: f64,
    pub hit_rate: f64,
    pub suggestions: Vec<String>,
}

impl AggregateReport {
    pub fn from_games(reports: &[GameReport]) -> Self {
        let n = reports.len() as u32;
        if n == 0 {
            return Self::default();
        }
        let nf = f64::from(n);
        let sum = |f: fn(&GameReport) -> u32| reports.iter().map(f).sum::<u32>();
        let sum_f = |f: fn(&GameReport) -> u32| f64::from(sum(f)) / nf;

        let red_wins = reports
            .iter()
            .filter(|r| r.winner.as_deref() == Some("Red"))
            .count() as u32;
        let blue_wins = reports
            .iter()
            .filter(|r| r.winner.as_deref() == Some("Blue"))
            .count() as u32;
        let draws = reports.iter().filter(|r| r.outcome == "Draw").count() as u32;

        let mut first_player_wins = 0;
        let mut second_player_wins = 0;
        for r in reports {
            if let Some(w) = &r.winner {
                if w == &r.first_player {
                    first_player_wins += 1;
                } else {
                    second_player_wins += 1;
                }
            }
        }

        let total_shots: u32 = sum(|r| r.shots_fired);
        let total_hits: u32 = sum(|r| r.hits);
        let hit_rate = if total_shots == 0 {
            0.0
        } else {
            f64::from(total_hits) / f64::from(total_shots)
        };

        let mut agg = Self {
            scenario: reports
                .first()
                .map(|r| r.scenario.clone())
                .unwrap_or_default(),
            games: n,
            red_wins,
            blue_wins,
            draws,
            first_player_wins,
            second_player_wins,
            timed_out: sum(|r| u32::from(r.timed_out)),
            ended_by_stalemate: sum(|r| u32::from(r.ended_by_stalemate)),
            low_engagement: sum(|r| u32::from(r.low_engagement)),
            late_stalemate: sum(|r| u32::from(r.late_stalemate)),
            comebacks: sum(|r| u32::from(r.comeback)),
            avg_activations: sum_f(|r| r.activations),
            avg_shots: sum_f(|r| r.shots_fired),
            avg_at_shots: sum_f(|r| r.at_shots),
            avg_he_shots: sum_f(|r| r.he_shots),
            avg_moves: sum_f(|r| r.moves_made),
            avg_turns: sum_f(|r| r.turns_made),
            avg_turret: sum_f(|r| r.turret_rotations),
            avg_hits: sum_f(|r| r.hits),
            avg_pens: sum_f(|r| r.pens),
            avg_glances: sum_f(|r| r.glances),
            avg_suppressions: sum_f(|r| r.suppressions),
            avg_fires: sum_f(|r| r.fires),
            avg_cook_offs: sum_f(|r| r.cook_offs),
            avg_crew_wounds: sum_f(|r| r.crew_wounds),
            avg_crew_kills: sum_f(|r| r.crew_kills),
            avg_abilities_used: sum_f(|r| r.abilities_used),
            avg_air_strikes: sum_f(|r| r.air_strikes),
            avg_infantry_kills: sum_f(|r| r.infantry_kills),
            avg_smoke_deployed: sum_f(|r| r.smoke_deployed),
            avg_medkit_saves: sum_f(|r| r.medkit_saves),
            avg_lt_covers: sum_f(|r| r.lt_covers),
            avg_mines_deployed: sum_f(|r| r.mines_deployed),
            avg_mines_triggered: sum_f(|r| r.mines_triggered),
            avg_mounts: sum_f(|r| r.mounts),
            avg_exterior_mounts: sum_f(|r| r.exterior_mounts),
            avg_embarks: sum_f(|r| r.embarks),
            avg_dismounts: sum_f(|r| r.dismounts),
            avg_drop_offs: sum_f(|r| r.drop_offs),
            avg_passenger_kills: sum_f(|r| r.passenger_kills),
            avg_exterior_rider_kills: sum_f(|r| r.exterior_rider_kills),
            embark_usage_rate: reports.iter().filter(|r| r.mounts + r.embarks > 0).count() as f64
                / nf,
            avg_objectives_captured: sum_f(|r| r.objectives_captured),
            capture_win_rate: reports.iter().filter(|r| r.ended_by_capture).count() as f64 / nf,
            loadout_smoke_rate: 0.0,
            loadout_medkit_rate: 0.0,
            loadout_lt_rate: 0.0,
            loadout_optics_rate: 0.0,
            loadout_barrel_rate: 0.0,
            loadout_engine_rate: 0.0,
            loadout_ai_rate: 0.0,
            loadout_avg_armor_pts: 0.0,
            loadout_avg_mine_charges: 0.0,
            loadout_avg_points: 0.0,
            list_initiative_rate: reports.iter().filter(|r| r.list_initiative).count() as f64 / nf,
            avg_red_list_points: sum_f(|r| r.red_list_points),
            avg_blue_list_points: sum_f(|r| r.blue_list_points),
            avg_list_point_gap: reports
                .iter()
                .map(|r| f64::from(r.red_list_points.abs_diff(r.blue_list_points)))
                .sum::<f64>()
                / nf,
            hit_rate,
            suggestions: Vec::new(),
        };
        let units: u32 = reports.iter().map(|r| r.loadout.tanks).sum();
        if units > 0 {
            let uf = f64::from(units);
            let sum_l =
                |f: fn(&LoadoutCensus) -> u32| reports.iter().map(|r| f(&r.loadout)).sum::<u32>();
            agg.loadout_smoke_rate = f64::from(sum_l(|c| c.smoke)) / uf;
            agg.loadout_medkit_rate = f64::from(sum_l(|c| c.medkit)) / uf;
            agg.loadout_lt_rate = f64::from(sum_l(|c| c.lieutenant)) / uf;
            agg.loadout_optics_rate = f64::from(sum_l(|c| c.optics)) / uf;
            agg.loadout_barrel_rate = f64::from(sum_l(|c| c.barrel)) / uf;
            agg.loadout_engine_rate = f64::from(sum_l(|c| c.engine)) / uf;
            agg.loadout_ai_rate = f64::from(sum_l(|c| c.anti_infantry)) / uf;
            agg.loadout_avg_armor_pts = f64::from(sum_l(|c| c.armor_points)) / uf;
            agg.loadout_avg_mine_charges = f64::from(sum_l(|c| c.mines_charges)) / uf;
            agg.loadout_avg_points = f64::from(sum_l(|c| c.upgrade_points)) / uf;
        }
        agg.suggestions = suggest(&agg);
        agg
    }
}

/// Rules-tweak suggestions from aggregate drama / stalemate signals.
fn suggest(agg: &AggregateReport) -> Vec<String> {
    let mut s = Vec::new();
    let n = f64::from(agg.games.max(1));
    let timeout_rate = f64::from(agg.timed_out) / n;
    let low_eng = f64::from(agg.low_engagement) / n;
    let stalemate = f64::from(agg.late_stalemate) / n;
    let decisive = f64::from(agg.red_wins + agg.blue_wins) / n;
    let fp_bias = if agg.first_player_wins + agg.second_player_wins > 0 {
        f64::from(agg.first_player_wins) / f64::from(agg.first_player_wins + agg.second_player_wins)
    } else {
        0.5
    };

    if timeout_rate > 0.35 && agg.capture_win_rate < 0.2 {
        s.push(
            "High timeout rate: games often hit the activation cap with both \
             sides still fighting. On capture scenarios, check whether the AI \
             drives APCs to the flag; otherwise try a shorter gun range or \
             award board-control points so camping loses."
                .into(),
        );
    } else if timeout_rate > 0.35 {
        s.push(
            "High timeout rate: games often hit the activation cap with both \
             sides still fighting. Try objectives / VP for kills, a shorter \
             gun range, or award board-control points so camping loses."
                .into(),
        );
    }
    if low_eng > 0.25 {
        s.push(
            "Low engagement: many activations pass with few shots. \
             Consider free turret rotation once per turn, or let Move keep \
             the turret absolute facing without spending a Turret action."
                .into(),
        );
    }
    if stalemate > 0.2 {
        s.push(
            "Late stalemates: long stretches without hits near the end. \
             Check LOS blocks, plaza bottlenecks, or air/APC spray loops."
                .into(),
        );
    }
    if agg.avg_activations < 8.0 && decisive > 0.85 {
        s.push(
            "Games resolve very quickly. That can feel railroaded. \
             Check whether the first pen snowballs via crew loss. \
             A 'stun' on first pen (lose 1 action next turn) instead of always \
             wounding crew would slow the death spiral."
                .into(),
        );
    }
    if agg.avg_glances == 0.0 && agg.avg_pens > 1.0 {
        s.push(
            "No glances observed despite many pens. With the 1-always-fails \
             house rule, stock AT vs armor 6 should glance on natural 1s — \
             if glances stay at zero, something is wrong in the pen path."
                .into(),
        );
    } else if agg.avg_pens < 0.5 && agg.avg_glances > 2.0 {
        s.push(
            "Lots of glances, few pens: fights grind through crew wounds. \
             Narrative-rich, but slow. Consider AT strength 7, or armor 5/5/5 stock, \
             so hull damage shows up more often."
                .into(),
        );
    }
    if agg.avg_abilities_used < 0.5 {
        s.push(
            "Crew abilities rarely fire. The AI is shy, or the tempo never \
             feels right for spending them. Rule tweak: allow one ability \
             without counting as the turn's 'special', or make Booming Voice \
             cheaper by granting +1 action instead of +2 so it's spent earlier."
                .into(),
        );
    }
    if agg.avg_fires == 0.0 && agg.avg_he_shots < 0.1 {
        s.push(
            "Fires still absent and HE is almost never loaded. \
             Nudge the AI toward HE, or give a once-per-battle free HE load \
             so the cinematic path shows up without relying on loadout choice."
                .into(),
        );
    } else if agg.avg_fires == 0.0 && agg.avg_he_shots > 0.5 {
        s.push(
            "HE is being loaded but fires never start (need 5+). \
             Consider fire on 4+, or HE strength 5 so players feel rewarded \
             for taking the softer pen."
                .into(),
        );
    } else if agg.avg_cook_offs < 0.05 && agg.avg_fires < 0.05 {
        s.push(
            "Cook-offs and fires are still rare. Disabled tanks may be \
             finishing the battle before the 4+ cook-off roll matters — \
             not necessarily a problem."
                .into(),
        );
    }
    if (fp_bias - 0.5).abs() > 0.1 {
        s.push(format!(
            "First-player win share is {:.0}%. \
             Try simultaneous activation, or defender places terrain after \
             seeing who goes first.",
            100.0 * fp_bias
        ));
    }
    if agg.comebacks as f64 / n < 0.05 && decisive > 0.7 {
        s.push(
            "Rare comebacks: once ahead on HP, the leader usually wins. \
             Medkit / Lieutenant as stock options, or a once-per-battle \
             'last stand' (+1 armor for one activation when at 1 HP) would \
             keep narrative hope alive."
                .into(),
        );
    }
    if s.is_empty() {
        s.push(
            "No strong red flags from drama/stalemate thresholds. \
             Expand to upgrade loadouts next, then re-check matchups."
                .into(),
        );
    }
    s
}

pub fn format_aggregate(agg: &AggregateReport) -> String {
    let mut out = String::new();
    if !agg.scenario.is_empty() {
        out.push_str(&format!("Scenario: {}\n", agg.scenario));
    }
    out.push_str(&format!("Games: {}\n", agg.games));
    out.push_str(&format!(
        "Results: Red {} / Blue {} / Draw {} ({:.0}% decisive)\n",
        agg.red_wins,
        agg.blue_wins,
        agg.draws,
        100.0 * f64::from(agg.red_wins + agg.blue_wins) / f64::from(agg.games.max(1))
    ));
    out.push_str(&format!(
        "First-player wins: {}  Second-player wins: {}\n",
        agg.first_player_wins, agg.second_player_wins
    ));
    out.push_str(&format!(
        "Avg activations: {:.1}  timed-out: {} ({:.0}%)  idle-stalemate: {} ({:.0}%)\n",
        agg.avg_activations,
        agg.timed_out,
        100.0 * f64::from(agg.timed_out) / f64::from(agg.games.max(1)),
        agg.ended_by_stalemate,
        100.0 * f64::from(agg.ended_by_stalemate) / f64::from(agg.games.max(1))
    ));
    out.push_str(&format!(
        "Engagement: avg shots {:.1} (AT {:.1} / HE {:.1}), hit rate {:.0}%, low-engagement games {} ({:.0}%)\n",
        agg.avg_shots,
        agg.avg_at_shots,
        agg.avg_he_shots,
        100.0 * agg.hit_rate,
        agg.low_engagement,
        100.0 * f64::from(agg.low_engagement) / f64::from(agg.games.max(1))
    ));
    out.push_str(&format!(
        "Maneuver: avg moves {:.1}, hull turns {:.1}, turret rotates {:.1}\n",
        agg.avg_moves, agg.avg_turns, agg.avg_turret
    ));
    out.push_str(&format!(
        "Drama: pens {:.2}, glances {:.2} (suppressions {:.2}), fires {:.2}, cook-offs {:.2}, \
         crew wounds {:.2}, crew kills {:.2}, abilities {:.2}, comebacks {}\n",
        agg.avg_pens,
        agg.avg_glances,
        agg.avg_suppressions,
        agg.avg_fires,
        agg.avg_cook_offs,
        agg.avg_crew_wounds,
        agg.avg_crew_kills,
        agg.avg_abilities_used,
        agg.comebacks
    ));
    if agg.avg_air_strikes > 0.0 || agg.avg_infantry_kills > 0.0 || agg.scenario == "combined" {
        out.push_str(&format!(
            "Combined arms: avg air strikes {:.2}, infantry kills {:.2}\n",
            agg.avg_air_strikes, agg.avg_infantry_kills
        ));
    }
    if agg.avg_smoke_deployed > 0.0 || agg.avg_medkit_saves > 0.0 || agg.avg_lt_covers > 0.0 {
        out.push_str(&format!(
            "Field kit: avg smoke {:.2}, medkit saves {:.2}, LT covers {:.2}\n",
            agg.avg_smoke_deployed, agg.avg_medkit_saves, agg.avg_lt_covers
        ));
    }
    if agg.avg_mines_deployed > 0.0 || agg.avg_mines_triggered > 0.0 {
        out.push_str(&format!(
            "Mines: avg deployed {:.2}, triggered {:.2}\n",
            agg.avg_mines_deployed, agg.avg_mines_triggered
        ));
    }
    if agg.embark_usage_rate > 0.0
        || agg.avg_mounts > 0.0
        || agg.avg_embarks > 0.0
        || agg.avg_drop_offs > 0.0
    {
        out.push_str(&format!(
            "Embark: games {:.0}% | mount {:.2} (exterior {:.2}) embark {:.2} dismount {:.2} drop {:.2} | passenger kills {:.2} (exterior {:.2})\n",
            agg.embark_usage_rate * 100.0,
            agg.avg_mounts,
            agg.avg_exterior_mounts,
            agg.avg_embarks,
            agg.avg_dismounts,
            agg.avg_drop_offs,
            agg.avg_passenger_kills,
            agg.avg_exterior_rider_kills
        ));
    }
    if agg.avg_objectives_captured > 0.0 || agg.capture_win_rate > 0.0 || agg.scenario == "capture"
    {
        out.push_str(&format!(
            "Objectives: avg captures {:.2}, win-by-capture {:.0}%\n",
            agg.avg_objectives_captured,
            100.0 * agg.capture_win_rate
        ));
    }
    if agg.loadout_avg_points > 0.0 {
        out.push_str(&format!(
            "List mix (share of vehicles): smoke {:.0}% medkit {:.0}% LT {:.0}% optics {:.0}% \
             barrel {:.0}% engine {:.0}% AI {:.0}% | avg armor pts {:.1}, mine charges {:.2}, \
             points spent {:.1}\n",
            100.0 * agg.loadout_smoke_rate,
            100.0 * agg.loadout_medkit_rate,
            100.0 * agg.loadout_lt_rate,
            100.0 * agg.loadout_optics_rate,
            100.0 * agg.loadout_barrel_rate,
            100.0 * agg.loadout_engine_rate,
            100.0 * agg.loadout_ai_rate,
            agg.loadout_avg_armor_pts,
            agg.loadout_avg_mine_charges,
            agg.loadout_avg_points
        ));
        out.push_str(&format!(
            "List initiative: under-spend first {:.0}% | avg Red {:.1} / Blue {:.1} pts \
             (gap {:.1})\n",
            100.0 * agg.list_initiative_rate,
            agg.avg_red_list_points,
            agg.avg_blue_list_points,
            agg.avg_list_point_gap
        ));
    }
    out.push_str(&format!(
        "Stalemate flags: late-stalemate games {} ({:.0}%)\n",
        agg.late_stalemate,
        100.0 * f64::from(agg.late_stalemate) / f64::from(agg.games.max(1))
    ));
    out.push_str("\nSuggested rules tweaks:\n");
    for (i, suggestion) in agg.suggestions.iter().enumerate() {
        out.push_str(&format!("  {}. {}\n", i + 1, suggestion));
    }
    out
}
