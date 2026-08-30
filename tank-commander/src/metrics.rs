//! Drama and stalemate metrics across simulated games.

use crate::game::{Game, Outcome};
use crate::unit::Side;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GameReport {
    pub seed: u64,
    pub outcome: String,
    pub winner: Option<String>,
    pub first_player: String,
    pub activations: u32,
    pub shots_fired: u32,
    pub shots_missed: u32,
    pub hits: u32,
    pub pens: u32,
    pub glances: u32,
    pub fires: u32,
    pub cook_offs: u32,
    pub crew_wounds: u32,
    pub crew_kills: u32,
    pub abilities_used: u32,
    /// True when the game hit the activation cap with both tanks still fighting.
    pub timed_out: bool,
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
        let both_fighting_at_end = game.tanks.iter().filter(|t| t.is_operational()).count() == 2;
        let hit_cap = game.activations >= game.max_activations;

        let low_engagement = game.shots_fired < game.activations / 4;
        let late_stalemate = game.activations_since_hit >= 6 && game.activations >= 12;

        let red_hp = hp_sum(game, Side::Red);
        let blue_hp = hp_sum(game, Side::Blue);

        let comeback = match outcome {
            Outcome::Winner(Side::Red) => hp_trace.red_was_behind,
            Outcome::Winner(Side::Blue) => hp_trace.blue_was_behind,
            _ => false,
        };

        GameReport {
            seed,
            outcome: outcome_str(outcome),
            winner: match outcome {
                Outcome::Winner(s) => Some(side_str(s).into()),
                _ => None,
            },
            first_player: side_str(game.first_player).into(),
            activations: game.activations,
            shots_fired: game.shots_fired,
            shots_missed: game.shots_missed,
            hits: game.total_hits,
            pens: game.total_pens,
            glances: game.total_glances,
            fires: game.total_fires,
            cook_offs: game.total_cook_offs,
            crew_wounds: game.total_crew_wounds,
            crew_kills: game.total_crew_kills,
            abilities_used: game.abilities_used,
            timed_out: hit_cap && both_fighting_at_end,
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
    pub games: u32,
    pub red_wins: u32,
    pub blue_wins: u32,
    pub draws: u32,
    pub first_player_wins: u32,
    pub second_player_wins: u32,
    pub timed_out: u32,
    pub low_engagement: u32,
    pub late_stalemate: u32,
    pub comebacks: u32,
    pub avg_activations: f64,
    pub avg_shots: f64,
    pub avg_hits: f64,
    pub avg_pens: f64,
    pub avg_glances: f64,
    pub avg_fires: f64,
    pub avg_cook_offs: f64,
    pub avg_crew_wounds: f64,
    pub avg_crew_kills: f64,
    pub avg_abilities_used: f64,
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
            games: n,
            red_wins,
            blue_wins,
            draws,
            first_player_wins,
            second_player_wins,
            timed_out: sum(|r| u32::from(r.timed_out)),
            low_engagement: sum(|r| u32::from(r.low_engagement)),
            late_stalemate: sum(|r| u32::from(r.late_stalemate)),
            comebacks: sum(|r| u32::from(r.comeback)),
            avg_activations: sum_f(|r| r.activations),
            avg_shots: sum_f(|r| r.shots_fired),
            avg_hits: sum_f(|r| r.hits),
            avg_pens: sum_f(|r| r.pens),
            avg_glances: sum_f(|r| r.glances),
            avg_fires: sum_f(|r| r.fires),
            avg_cook_offs: sum_f(|r| r.cook_offs),
            avg_crew_wounds: sum_f(|r| r.crew_wounds),
            avg_crew_kills: sum_f(|r| r.crew_kills),
            avg_abilities_used: sum_f(|r| r.abilities_used),
            hit_rate,
            suggestions: Vec::new(),
        };
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

    if timeout_rate > 0.35 {
        s.push(
            "High timeout rate: games often hit the 10-turn cap with both tanks up. \
             Try a shorter gun range, more starting distance pressure (objectives), \
             or award victory points for board control so camping loses."
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
             Smoke and forest stacking may make trading shots rare — \
             soften cover (−1 accuracy only once), or let HE ignore forest."
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
    if agg.avg_fires == 0.0 && agg.avg_cook_offs < 0.05 {
        s.push(
            "Fires and cook-offs almost never appear in stock Skirmish \
             (no HE). Add HE as a free stock option, or give a one-shot \
             HE 'ready rack' so cinematic fires show up without a full upgrade pass."
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
        "Avg activations: {:.1}  timed-out: {} ({:.0}%)\n",
        agg.avg_activations,
        agg.timed_out,
        100.0 * f64::from(agg.timed_out) / f64::from(agg.games.max(1))
    ));
    out.push_str(&format!(
        "Engagement: avg shots {:.1}, hit rate {:.0}%, low-engagement games {} ({:.0}%)\n",
        agg.avg_shots,
        100.0 * agg.hit_rate,
        agg.low_engagement,
        100.0 * f64::from(agg.low_engagement) / f64::from(agg.games.max(1))
    ));
    out.push_str(&format!(
        "Drama: pens {:.2}, glances {:.2}, fires {:.2}, cook-offs {:.2}, \
         crew wounds {:.2}, crew kills {:.2}, abilities {:.2}, comebacks {}\n",
        agg.avg_pens,
        agg.avg_glances,
        agg.avg_fires,
        agg.avg_cook_offs,
        agg.avg_crew_wounds,
        agg.avg_crew_kills,
        agg.avg_abilities_used,
        agg.comebacks
    ));
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
