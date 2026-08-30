//! Built-in scenarios: Skirmish (1v1), Platoon (3v3), Combined arms.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank};
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

/// Combined: 15×11 — between skirmish and platoon.
const COMBINED_WALL: [Hex; 17] = [
    Hex::new(6, 3),
    Hex::new(6, 4),
    Hex::new(6, 5),
    Hex::new(6, 6),
    Hex::new(6, 7),
    Hex::new(7, 3),
    Hex::new(7, 4),
    Hex::new(7, 5),
    Hex::new(7, 6),
    Hex::new(7, 7),
    Hex::new(8, 3),
    Hex::new(8, 4),
    Hex::new(8, 5),
    Hex::new(8, 6),
    Hex::new(8, 7),
    // Wing scraps.
    Hex::new(2, 8),
    Hex::new(12, 2),
];
const COMBINED_ALLEY: [Hex; 6] = [
    Hex::new(7, 0),
    Hex::new(7, 1),
    Hex::new(7, 2),
    Hex::new(7, 8),
    Hex::new(7, 9),
    Hex::new(7, 10),
];
const COMBINED_GOALS: [Hex; 2] = [Hex::new(7, 1), Hex::new(7, 9)];

const COMBINED_MAP: MapLayout = MapLayout {
    width: 15,
    height: 11,
    wall: &COMBINED_WALL,
    alley_clear: &COMBINED_ALLEY,
    path_goals: &COMBINED_GOALS,
    forest: (8, 14),
    mud: (3, 6),
    rubble: (2, 5),
};

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

/// Combined arms on a 15×11 board between skirmish and platoon scale.
pub fn combined<R: Rng>(rng: &mut R) -> Game {
    let red_tank = Hex::new(1, 3);
    let red_apc = Hex::new(1, 6);
    let red_inf = Hex::new(0, 5);
    let blue_tank = Hex::new(13, 7);
    let blue_apc = Hex::new(13, 4);
    let blue_inf = Hex::new(14, 5);
    let reserved = [red_tank, red_apc, red_inf, blue_tank, blue_apc, blue_inf];
    let egress = [
        Hex::new(2, 3),
        Hex::new(2, 6),
        Hex::new(12, 7),
        Hex::new(12, 4),
    ];
    let board = build_board(&COMBINED_MAP, rng, &reserved, &egress);

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
    Game::new(board, tanks, coin_flip(rng), 160, "combined").with_stalemate(32)
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
        assert_eq!(g.board.max_q, 14);
        assert_eq!(g.board.max_r, 10);
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
        for h in COMBINED_WALL {
            assert_eq!(g.board.terrain_at(h), Terrain::Building);
        }
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
