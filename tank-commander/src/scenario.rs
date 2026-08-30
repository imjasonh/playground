//! Built-in scenarios: Skirmish (1v1), Platoon (3v3), Combined arms.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank, UnitKind};
use rand::seq::SliceRandom;
use rand::Rng;

/// Which scenario to spin up.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScenarioKind {
    /// 1v1 stock tanks.
    Skirmish,
    /// 3v3 stock tanks.
    Platoon,
    /// 1 tank (air support) + 1 APC + 1 infantry per side.
    Combined,
}

impl ScenarioKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ScenarioKind::Skirmish => "skirmish",
            ScenarioKind::Platoon => "platoon",
            ScenarioKind::Combined => "combined",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "skirmish" => Some(Self::Skirmish),
            "platoon" => Some(Self::Platoon),
            "combined" => Some(Self::Combined),
            _ => None,
        }
    }
}

/// Fixed terrain + scatter recipe for a scenario board.
struct MapLayout<'a> {
    width: i32,
    height: i32,
    /// Impassable buildings that never move.
    wall: &'a [Hex],
    /// Must stay open (alleys / approach lanes).
    alley_clear: &'a [Hex],
    /// Pathability probes: each start must reach at least one goal.
    path_goals: &'a [Hex],
    forest: (u32, u32),
    mud: (u32, u32),
    rubble: (u32, u32),
}

/// Skirmish: 11×9, compact midline block.
const SKIRMISH_WALL: [Hex; 9] = [
    Hex::new(4, 3),
    Hex::new(4, 4),
    Hex::new(4, 5),
    Hex::new(5, 3),
    Hex::new(5, 4),
    Hex::new(5, 5),
    Hex::new(6, 3),
    Hex::new(6, 4),
    Hex::new(6, 5),
];
const SKIRMISH_ALLEY: [Hex; 6] = [
    Hex::new(5, 0),
    Hex::new(5, 1),
    Hex::new(5, 2),
    Hex::new(5, 6),
    Hex::new(5, 7),
    Hex::new(5, 8),
];
const SKIRMISH_GOALS: [Hex; 2] = [Hex::new(5, 1), Hex::new(5, 7)];
const RED_START: Hex = Hex::new(1, 3);
const BLUE_START: Hex = Hex::new(9, 5);

const SKIRMISH_MAP: MapLayout = MapLayout {
    width: 11,
    height: 9,
    wall: &SKIRMISH_WALL,
    alley_clear: &SKIRMISH_ALLEY,
    path_goals: &SKIRMISH_GOALS,
    forest: (5, 9),
    mud: (2, 4),
    rubble: (1, 3),
};

/// Platoon: 19×15 sealed midline with a wide plaza gap (no N/S through-lanes).
/// Built at runtime so the wall can span the full height.
fn platoon_wall(height: i32) -> Vec<Hex> {
    let mut wall = Vec::new();
    // Three-column spine; wide plaza at r=5..=9 so a wreck in the throat
    // cannot seal the only passage and freeze the game.
    for q in 8..=10 {
        for r in 0..height {
            if (5..=9).contains(&r) {
                continue;
            }
            wall.push(Hex::new(q, r));
        }
    }
    // West baffles: break any west-side N↔S lane so the three reds can't
    // stay in separate corridors.
    wall.extend([
        Hex::new(3, 1),
        Hex::new(3, 2),
        Hex::new(4, 2),
        Hex::new(3, 12),
        Hex::new(3, 13),
        Hex::new(4, 12),
    ]);
    // East baffles: same idea for blue.
    wall.extend([
        Hex::new(15, 1),
        Hex::new(15, 2),
        Hex::new(14, 2),
        Hex::new(15, 12),
        Hex::new(15, 13),
        Hex::new(14, 12),
    ]);
    wall
}

fn platoon_alley_clear() -> Vec<Hex> {
    // Wide plaza + approaches on both sides.
    let mut clear = Vec::new();
    for q in 6..=12 {
        for r in 5..=9 {
            clear.push(Hex::new(q, r));
        }
    }
    clear
}

/// Combined: 17×13 sealed midline with a wide plaza + forest approaches.
fn combined_wall(height: i32) -> Vec<Hex> {
    let mut wall = Vec::new();
    for q in 7..=9 {
        for r in 0..height {
            if (4..=8).contains(&r) {
                continue;
            }
            wall.push(Hex::new(q, r));
        }
    }
    wall.extend([
        Hex::new(2, 1),
        Hex::new(2, 2),
        Hex::new(14, 10),
        Hex::new(14, 11),
    ]);
    wall
}

fn combined_alley_clear() -> Vec<Hex> {
    let mut clear = Vec::new();
    for q in 5..=11 {
        for r in 4..=8 {
            clear.push(Hex::new(q, r));
        }
    }
    clear
}

pub fn setup<R: Rng>(kind: ScenarioKind, rng: &mut R) -> Game {
    match kind {
        ScenarioKind::Skirmish => skirmish(rng),
        ScenarioKind::Platoon => platoon(rng),
        ScenarioKind::Combined => combined(rng),
    }
}

/// 1v1 tank duel on the compact 11×9 board.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let starts = [RED_START, BLUE_START];
    let egress = [Hex::new(2, 3), Hex::new(8, 5)];
    let board = build_board(&SKIRMISH_MAP, rng, &starts, &egress);
    let red = Tank::stock(0, Side::Red, RED_START, Facing::E, "Red One");
    let blue = Tank::stock(1, Side::Blue, BLUE_START, Facing::W, "Blue One");
    Game::new(board, vec![red, blue], coin_flip(rng), 20, "skirmish")
}

/// 3v3 on a 19×15 board. The midline is sealed except a two-hex plaza gap, so
/// tanks cannot pair off down parallel N/S lanes — everyone funnels into the
/// same fight. Hard cap is high; idle (no hull damage) ends the game earlier.
pub fn platoon<R: Rng>(rng: &mut R) -> Game {
    let width = 19;
    let height = 15;
    let red_starts = [Hex::new(1, 4), Hex::new(1, 7), Hex::new(1, 10)];
    let blue_starts = [Hex::new(17, 5), Hex::new(17, 8), Hex::new(17, 11)];
    let reserved: Vec<Hex> = red_starts
        .iter()
        .chain(blue_starts.iter())
        .copied()
        .collect();
    let egress = [
        Hex::new(2, 4),
        Hex::new(2, 7),
        Hex::new(2, 10),
        Hex::new(16, 5),
        Hex::new(16, 8),
        Hex::new(16, 11),
    ];
    let wall = platoon_wall(height);
    let alley = platoon_alley_clear();
    let goals = [Hex::new(9, 6), Hex::new(9, 8)];
    let layout = MapLayout {
        width,
        height,
        wall: &wall,
        alley_clear: &alley,
        path_goals: &goals,
        forest: (14, 24),
        mud: (5, 9),
        rubble: (4, 8),
    };
    let board = build_board(&layout, rng, &reserved, &egress);

    let tanks = vec![
        Tank::stock(0, Side::Red, red_starts[0], Facing::E, "Red Alpha"),
        Tank::stock(1, Side::Red, red_starts[1], Facing::E, "Red Bravo"),
        Tank::stock(2, Side::Red, red_starts[2], Facing::E, "Red Charlie"),
        Tank::stock(3, Side::Blue, blue_starts[0], Facing::W, "Blue Alpha"),
        Tank::stock(4, Side::Blue, blue_starts[1], Facing::W, "Blue Bravo"),
        Tank::stock(5, Side::Blue, blue_starts[2], Facing::W, "Blue Charlie"),
    ];
    // Safety valve 200. Real stop: 40 activations with no hit after contact
    // (true circling / lost LOS), so duels can finish instead of timing out
    // mid-fight.
    Game::new(board, tanks, coin_flip(rng), 200, "platoon").with_stalemate(40)
}

/// Combined arms on a 17×13 plaza board. Infantry dig into forest approaches;
/// APC spray and air strikes matter in the shared funnel.
pub fn combined<R: Rng>(rng: &mut R) -> Game {
    let width = 17;
    let height = 13;
    let red_tank = Hex::new(1, 4);
    let red_apc = Hex::new(1, 7);
    let red_inf = Hex::new(0, 6);
    let blue_tank = Hex::new(15, 8);
    let blue_apc = Hex::new(15, 5);
    let blue_inf = Hex::new(16, 6);
    let reserved = [red_tank, red_apc, red_inf, blue_tank, blue_apc, blue_inf];
    let egress = [
        Hex::new(2, 4),
        Hex::new(2, 7),
        Hex::new(14, 8),
        Hex::new(14, 5),
    ];
    let wall = combined_wall(height);
    let alley = combined_alley_clear();
    let goals = [Hex::new(8, 5), Hex::new(8, 7)];
    let layout = MapLayout {
        width,
        height,
        wall: &wall,
        alley_clear: &alley,
        path_goals: &goals,
        forest: (12, 20),
        mud: (3, 6),
        rubble: (2, 5),
    };
    let board = build_board(&layout, rng, &reserved, &egress);

    let mut red_t = Tank::stock(0, Side::Red, red_tank, Facing::E, "Red Tank");
    red_t.has_air_support = true;
    let mut blue_t = Tank::stock(3, Side::Blue, blue_tank, Facing::W, "Blue Tank");
    blue_t.has_air_support = true;

    let tanks = vec![
        red_t,
        Tank::stock_apc(1, Side::Red, red_apc, Facing::E, "Red APC"),
        Tank::stock_infantry(2, Side::Red, red_inf, Facing::E, "Red Squad"),
        blue_t,
        Tank::stock_apc(4, Side::Blue, blue_apc, Facing::W, "Blue APC"),
        Tank::stock_infantry(5, Side::Blue, blue_inf, Facing::W, "Blue Squad"),
    ];
    let mut game = Game::new(board, tanks, coin_flip(rng), 160, "combined").with_stalemate(32);
    // Scenario: after initiative, the second player may nudge each opposing
    // unit up to 1 hex before the first activation.
    second_player_nudge_opposing(&mut game);
    game
}

/// Second player may move each first-player unit at most one hex (empty,
/// passable, on-board). Facing is unchanged. The sim picks, for each unit, the
/// legal hex that most spoils the opener (farther from second-player forces,
/// farther from the plaza, strip infantry out of forest when possible).
fn second_player_nudge_opposing(game: &mut Game) {
    let first = game.first_player;
    let second = first.other();
    let plaza = Hex::new(8, 6);
    let fp_ids: Vec<u8> = game
        .tanks
        .iter()
        .filter(|t| t.side == first)
        .map(|t| t.id)
        .collect();

    for id in fp_ids {
        let from = game.tank(id).pos;
        let kind = game.tank(id).kind;
        let name = game.tank(id).name.clone();
        let in_forest = game.board.terrain_at(from) == Terrain::Forest;

        let mut occupied: Vec<Hex> = game.tanks.iter().map(|t| t.pos).collect();
        // Free the unit's current hex so "stay" and swaps-with-self work.
        occupied.retain(|h| *h != from);

        let mut best = from;
        let mut best_score = i32::MIN;
        let mut candidates = vec![from];
        candidates.extend(from.neighbors());
        for cand in candidates {
            if !game.board.contains(cand) || game.board.terrain_at(cand).impassable() {
                continue;
            }
            if occupied.contains(&cand) {
                continue;
            }
            let min_sp = game
                .tanks
                .iter()
                .filter(|t| t.side == second)
                .map(|t| cand.distance(t.pos))
                .min()
                .unwrap_or(0);
            let mut score = min_sp * 10 + cand.distance(plaza) * 5;
            if kind == UnitKind::Infantry
                && in_forest
                && game.board.terrain_at(cand) != Terrain::Forest
            {
                score += 8;
            }
            // Prefer an actual nudge over stay when scores tie.
            if cand != from {
                score += 1;
            }
            if score > best_score {
                best_score = score;
                best = cand;
            }
        }

        if best != from {
            game.tank_mut(id).pos = best;
            game.push_setup_event(format!(
                "Second player nudges {name} {from} → {best} before start"
            ));
        }
    }
}

fn coin_flip<R: Rng>(rng: &mut R) -> Side {
    if rng.gen_bool(0.5) {
        Side::Red
    } else {
        Side::Blue
    }
}

fn build_board<R: Rng>(
    layout: &MapLayout<'_>,
    rng: &mut R,
    starts: &[Hex],
    egress: &[Hex],
) -> Board {
    for _ in 0..10 {
        let board = scatter_terrain(layout, rng, starts, egress);
        if alleys_pathable(&board, starts, layout.path_goals) {
            return board;
        }
    }
    scatter_terrain(layout, rng, starts, egress)
}

fn scatter_terrain<R: Rng>(
    layout: &MapLayout<'_>,
    rng: &mut R,
    starts: &[Hex],
    egress: &[Hex],
) -> Board {
    let mut board = Board::rect(layout.width, layout.height);
    for h in layout.wall {
        board.set_terrain(*h, Terrain::Building);
    }

    let mut candidates: Vec<Hex> = Vec::new();
    for q in board.min_q..=board.max_q {
        for r in board.min_r..=board.max_r {
            let h = Hex::new(q, r);
            if layout.wall.contains(&h) || layout.alley_clear.contains(&h) || starts.contains(&h) {
                continue;
            }
            if egress.contains(&h) {
                continue;
            }
            candidates.push(h);
        }
    }
    candidates.shuffle(rng);

    let n_forest = rng.gen_range(layout.forest.0..=layout.forest.1) as usize;
    let n_mud = rng.gen_range(layout.mud.0..=layout.mud.1) as usize;
    let n_rubble = rng.gen_range(layout.rubble.0..=layout.rubble.1) as usize;
    let need = n_forest + n_mud + n_rubble;
    let take = need.min(candidates.len());

    for (i, h) in candidates.into_iter().take(take).enumerate() {
        let terrain = if i < n_forest {
            Terrain::Forest
        } else if i < n_forest + n_mud {
            Terrain::Mud
        } else {
            Terrain::Rubble
        };
        board.set_terrain(h, terrain);
    }
    board
}

fn alleys_pathable(board: &Board, starts: &[Hex], goals: &[Hex]) -> bool {
    let mid = (board.min_q + board.max_q) / 2;
    let red: Vec<Hex> = starts.iter().copied().filter(|h| h.q < mid).collect();
    let blue: Vec<Hex> = starts.iter().copied().filter(|h| h.q > mid).collect();
    red.iter()
        .any(|s| goals.iter().any(|g| reachable(board, *s, *g)))
        && blue
            .iter()
            .any(|s| goals.iter().any(|g| reachable(board, *s, *g)))
}

fn reachable(board: &Board, start: Hex, goal: Hex) -> bool {
    use std::collections::{HashSet, VecDeque};
    let mut seen = HashSet::new();
    let mut q = VecDeque::new();
    q.push_back(start);
    seen.insert((start.q, start.r));
    while let Some(cur) = q.pop_front() {
        if cur == goal {
            return true;
        }
        for n in cur.neighbors() {
            if !board.contains(n) || board.terrain_at(n).impassable() {
                continue;
            }
            if seen.insert((n.q, n.r)) {
                q.push_back(n);
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex::Hex;
    use crate::unit::UnitKind;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn center_corridor_blocks_opening_los() {
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let g = skirmish(&mut rng);
        let red = g.tanks.iter().find(|t| t.side == Side::Red).unwrap();
        let blue = g.tanks.iter().find(|t| t.side == Side::Blue).unwrap();
        assert_eq!(red.pos, RED_START);
        assert_eq!(blue.pos, BLUE_START);
        assert!(
            !g.board.has_los(red.pos, blue.pos, &[]),
            "opening street must not allow LOS through the wall"
        );
        for h in SKIRMISH_WALL {
            assert_eq!(g.board.terrain_at(h), Terrain::Building);
        }
        for h in SKIRMISH_ALLEY {
            assert!(
                !g.board.terrain_at(h).impassable(),
                "alley {h} must stay passable"
            );
        }
    }

    #[test]
    fn scatter_varies_across_seeds() {
        let mut a = ChaCha8Rng::seed_from_u64(1);
        let mut b = ChaCha8Rng::seed_from_u64(2);
        let ga = skirmish(&mut a);
        let gb = skirmish(&mut b);
        let mut differ = false;
        for q in 0..=10 {
            for r in 0..=8 {
                let h = Hex::new(q, r);
                if SKIRMISH_WALL.contains(&h) {
                    continue;
                }
                if ga.board.terrain_at(h) != gb.board.terrain_at(h) {
                    differ = true;
                }
            }
        }
        assert!(differ, "two seeds should scatter different terrain");
    }

    #[test]
    fn platoon_has_six_tanks_on_big_board() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let g = platoon(&mut rng);
        assert_eq!(g.tanks.len(), 6);
        assert_eq!(g.scenario, "platoon");
        assert_eq!(g.board.max_q, 18);
        assert_eq!(g.board.max_r, 14);
        assert_eq!(g.max_activations, 200);
        assert_eq!(g.stalemate_after, 40);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Red).count(), 3);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Blue).count(), 3);
        assert!(g.tanks.iter().all(|t| t.kind == UnitKind::Tank));
        // Spine sealed except plaza throat.
        assert_eq!(g.board.terrain_at(Hex::new(9, 0)), Terrain::Building);
        assert_eq!(g.board.terrain_at(Hex::new(9, 14)), Terrain::Building);
        assert!(!g.board.terrain_at(Hex::new(9, 5)).impassable());
        assert!(!g.board.terrain_at(Hex::new(9, 7)).impassable());
        assert!(!g.board.terrain_at(Hex::new(9, 9)).impassable());
        // No parallel N/S through-lane at q=9 outside the plaza.
        assert!(g.board.terrain_at(Hex::new(9, 2)).impassable());
        assert!(g.board.terrain_at(Hex::new(9, 12)).impassable());
    }

    #[test]
    fn combined_has_mixed_force_on_mid_board() {
        let mut rng = ChaCha8Rng::seed_from_u64(4);
        let g = combined(&mut rng);
        assert_eq!(g.scenario, "combined");
        assert_eq!(g.board.max_q, 16);
        assert_eq!(g.board.max_r, 12);
        assert_eq!(g.tanks.len(), 6);
        let kinds: Vec<_> = g.tanks.iter().map(|t| t.kind).collect();
        assert!(kinds.contains(&UnitKind::Tank));
        assert!(kinds.contains(&UnitKind::Apc));
        assert!(kinds.contains(&UnitKind::Infantry));
        assert!(g
            .tanks
            .iter()
            .filter(|t| t.kind == UnitKind::Tank)
            .all(|t| t.has_air_support));
        // Plaza open; spine sealed outside it.
        assert!(!g.board.terrain_at(Hex::new(8, 6)).impassable());
        assert!(g.board.terrain_at(Hex::new(8, 1)).impassable());
        assert!(g.board.terrain_at(Hex::new(8, 11)).impassable());
    }

    #[test]
    fn combined_second_player_may_nudge_opposing_force() {
        let mut rng = ChaCha8Rng::seed_from_u64(11);
        let g = combined(&mut rng);
        let first = g.first_player;
        // At least one setup nudge event when the heuristic finds a better hex.
        let nudges: Vec<_> = g
            .events
            .iter()
            .filter(|e| e.text.contains("Second player nudges"))
            .collect();
        assert!(
            !nudges.is_empty(),
            "expected at least one opposing-force nudge, events={:?}",
            g.events.iter().map(|e| &e.text).collect::<Vec<_>>()
        );
        // Nudged units must still be on-board and unstacked.
        let mut seen = std::collections::HashSet::new();
        for t in &g.tanks {
            assert!(g.board.contains(t.pos));
            assert!(!g.board.terrain_at(t.pos).impassable());
            assert!(seen.insert(t.pos), "stacked at {}", t.pos);
        }
        assert_eq!(g.tanks.iter().filter(|t| t.side == first).count(), 3);
    }

    #[test]
    fn board_sizes_scale_with_scenario() {
        let mut rng = ChaCha8Rng::seed_from_u64(5);
        let s = skirmish(&mut rng);
        let c = combined(&mut rng);
        let p = platoon(&mut rng);
        let area = |g: &Game| (g.board.max_q + 1) * (g.board.max_r + 1);
        assert!(area(&s) < area(&c));
        assert!(area(&c) < area(&p));
    }
}
