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

/// Fixed midline wall hexes. Everything else on the board is rolled each game.
const WALL: [Hex; 9] = [
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

/// Alley hexes that must stay passable (no mud/rubble/building).
const ALLEY_CLEAR: [Hex; 6] = [
    Hex::new(5, 0),
    Hex::new(5, 1),
    Hex::new(5, 2),
    Hex::new(5, 6),
    Hex::new(5, 7),
    Hex::new(5, 8),
];

/// Red / Blue start hexes for 1v1 (offset rows so the opening isn't a mirror).
const RED_START: Hex = Hex::new(1, 3);
const BLUE_START: Hex = Hex::new(9, 5);

pub fn setup<R: Rng>(kind: ScenarioKind, rng: &mut R) -> Game {
    match kind {
        ScenarioKind::Skirmish => skirmish(rng),
        ScenarioKind::Platoon => platoon(rng),
        ScenarioKind::Combined => combined(rng),
    }
}

/// 1v1 tank duel. The midline building wall is fixed; forest / mud / rubble
/// outside it are rolled each game so approaches and cover vary. Starts sit
/// on offset rows so each side's natural alley differs.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let board = build_board(
        rng,
        &[RED_START, BLUE_START],
        &[Hex::new(2, 3), Hex::new(8, 5)],
    );
    let red = Tank::stock(0, Side::Red, RED_START, Facing::E, "Red One");
    let blue = Tank::stock(1, Side::Blue, BLUE_START, Facing::W, "Blue One");
    let first = coin_flip(rng);
    Game::new(board, vec![red, blue], first, 20, "skirmish")
}

/// 3v3 tank platoon fight on the same walled board. Starts fan north/south of
/// the 1v1 positions so units don't stack. Longer activation budget so each
/// tank can act a few times.
pub fn platoon<R: Rng>(rng: &mut R) -> Game {
    let red_starts = [Hex::new(1, 2), Hex::new(1, 4), Hex::new(0, 3)];
    let blue_starts = [Hex::new(9, 4), Hex::new(9, 6), Hex::new(10, 5)];
    let reserved: Vec<Hex> = red_starts
        .iter()
        .chain(blue_starts.iter())
        .copied()
        .collect();
    let egress = [
        Hex::new(2, 2),
        Hex::new(2, 4),
        Hex::new(8, 4),
        Hex::new(8, 6),
    ];
    let board = build_board(rng, &reserved, &egress);

    let tanks = vec![
        Tank::stock(0, Side::Red, red_starts[0], Facing::E, "Red Alpha"),
        Tank::stock(1, Side::Red, red_starts[1], Facing::E, "Red Bravo"),
        Tank::stock(2, Side::Red, red_starts[2], Facing::E, "Red Charlie"),
        Tank::stock(3, Side::Blue, blue_starts[0], Facing::W, "Blue Alpha"),
        Tank::stock(4, Side::Blue, blue_starts[1], Facing::W, "Blue Bravo"),
        Tank::stock(5, Side::Blue, blue_starts[2], Facing::W, "Blue Charlie"),
    ];
    let first = coin_flip(rng);
    // 24 activations each side → ~8 per tank if shared evenly. 15/side
    // timed out ~98% of games (not enough pens to wipe three hulls).
    Game::new(board, tanks, first, 48, "platoon")
}

/// Combined arms: tank with air support, APC, and infantry squad per side.
pub fn combined<R: Rng>(rng: &mut R) -> Game {
    let red_tank = Hex::new(1, 3);
    let red_apc = Hex::new(1, 5);
    let red_inf = Hex::new(0, 4);
    let blue_tank = Hex::new(9, 5);
    let blue_apc = Hex::new(9, 3);
    let blue_inf = Hex::new(10, 4);
    let reserved = [red_tank, red_apc, red_inf, blue_tank, blue_apc, blue_inf];
    let egress = [
        Hex::new(2, 3),
        Hex::new(2, 5),
        Hex::new(8, 5),
        Hex::new(8, 3),
    ];
    let board = build_board(rng, &reserved, &egress);

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
    let first = coin_flip(rng);
    // 24 each: mixed force dies faster than a pure tank platoon, but air
    // strikes and infantry need room to matter.
    Game::new(board, tanks, first, 48, "combined")
}

fn coin_flip<R: Rng>(rng: &mut R) -> Side {
    if rng.gen_bool(0.5) {
        Side::Red
    } else {
        Side::Blue
    }
}

fn build_board<R: Rng>(rng: &mut R, starts: &[Hex], egress: &[Hex]) -> Board {
    for _ in 0..8 {
        let board = scatter_terrain(rng, starts, egress);
        if alleys_pathable(&board, starts) {
            return board;
        }
    }
    scatter_terrain(rng, starts, egress)
}

fn scatter_terrain<R: Rng>(rng: &mut R, starts: &[Hex], egress: &[Hex]) -> Board {
    let mut board = Board::rect(11, 9);
    for h in WALL {
        board.set_terrain(h, Terrain::Building);
    }

    let mut candidates: Vec<Hex> = Vec::new();
    for q in board.min_q..=board.max_q {
        for r in board.min_r..=board.max_r {
            let h = Hex::new(q, r);
            if WALL.contains(&h) || ALLEY_CLEAR.contains(&h) || starts.contains(&h) {
                continue;
            }
            if egress.contains(&h) {
                continue;
            }
            candidates.push(h);
        }
    }
    candidates.shuffle(rng);

    let n_forest = rng.gen_range(5..=9);
    let n_mud = rng.gen_range(2..=4);
    let n_rubble = rng.gen_range(1..=3);
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

fn alleys_pathable(board: &Board, starts: &[Hex]) -> bool {
    // At least one start on each side can reach both alleys.
    let red = starts
        .iter()
        .copied()
        .filter(|h| h.q <= 3)
        .collect::<Vec<_>>();
    let blue = starts
        .iter()
        .copied()
        .filter(|h| h.q >= 8)
        .collect::<Vec<_>>();
    let goals = [Hex::new(5, 1), Hex::new(5, 7)];
    red.iter()
        .any(|s| goals.iter().all(|g| reachable(board, *s, *g)))
        && blue
            .iter()
            .any(|s| goals.iter().all(|g| reachable(board, *s, *g)))
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
        for h in WALL {
            assert_eq!(g.board.terrain_at(h), Terrain::Building);
        }
        for h in ALLEY_CLEAR {
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
                if WALL.contains(&h) {
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
    fn platoon_has_six_tanks() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let g = platoon(&mut rng);
        assert_eq!(g.tanks.len(), 6);
        assert_eq!(g.scenario, "platoon");
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Red).count(), 3);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Blue).count(), 3);
        assert!(g.tanks.iter().all(|t| t.kind == UnitKind::Tank));
    }

    #[test]
    fn combined_has_mixed_force() {
        let mut rng = ChaCha8Rng::seed_from_u64(4);
        let g = combined(&mut rng);
        assert_eq!(g.scenario, "combined");
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
    }
}
