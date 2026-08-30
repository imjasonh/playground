//! Built-in scenarios. v1: Skirmish only.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank};
use rand::seq::SliceRandom;
use rand::Rng;

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

/// Red / Blue start hexes (offset rows so the opening isn't a mirror).
const RED_START: Hex = Hex::new(1, 3);
const BLUE_START: Hex = Hex::new(9, 5);

/// 1v1 tank duel. The midline building wall is fixed; forest / mud / rubble
/// outside it are rolled each game so approaches and cover vary. Starts sit
/// on offset rows so each side's natural alley differs.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let board = build_board(rng);

    let red = Tank::stock(0, Side::Red, RED_START, Facing::E, "Red One");
    let blue = Tank::stock(1, Side::Blue, BLUE_START, Facing::W, "Blue One");

    let first = if rng.gen_bool(0.5) {
        Side::Red
    } else {
        Side::Blue
    };

    Game {
        board,
        tanks: vec![red, blue],
        active_side: first,
        activations: 0,
        // 10 turns each side → 20 activations.
        max_activations: 20,
        events: Vec::new(),
        first_player: first,
        scenario: "skirmish".into(),
        pending_air_strikes: Vec::new(),
        air_strikes_resolved: 0,
        infantry_kills: 0,
        activations_since_hit: 0,
        activations_since_damage: 0,
        total_hits: 0,
        total_pens: 0,
        total_glances: 0,
        total_suppressions: 0,
        total_fires: 0,
        total_cook_offs: 0,
        total_crew_wounds: 0,
        total_crew_kills: 0,
        abilities_used: 0,
        shots_fired: 0,
        shots_missed: 0,
        at_shots: 0,
        he_shots: 0,
        moves_made: 0,
        turns_made: 0,
        turret_rotations: 0,
    }
}

fn build_board<R: Rng>(rng: &mut R) -> Board {
    // Re-roll a few times if a scatter somehow seals an alley (shouldn't with
    // ALLEY_CLEAR reserved, but rubble+mud stacks of bad luck are cheap to avoid).
    for _ in 0..8 {
        let board = scatter_terrain(rng);
        if alleys_pathable(&board) {
            return board;
        }
    }
    scatter_terrain(rng)
}

fn scatter_terrain<R: Rng>(rng: &mut R) -> Board {
    let mut board = Board::rect(11, 9);
    for h in WALL {
        board.set_terrain(h, Terrain::Building);
    }

    let starts = [RED_START, BLUE_START];
    let egress = [
        Hex::new(2, 3), // in front of Red
        Hex::new(8, 5), // in front of Blue
    ];
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

fn alleys_pathable(board: &Board) -> bool {
    reachable(board, RED_START, Hex::new(5, 1))
        && reachable(board, RED_START, Hex::new(5, 7))
        && reachable(board, BLUE_START, Hex::new(5, 1))
        && reachable(board, BLUE_START, Hex::new(5, 7))
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
        // Some non-wall hex should differ (very unlikely to collide on all).
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
}
