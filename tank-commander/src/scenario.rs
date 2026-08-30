//! Built-in scenarios. v1: Skirmish only.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank};
use rand::Rng;

/// 1v1 tank duel on a light-terrain board.
///
/// Board is 11×9 axial. A few forests and buildings break LOS without
/// locking the map into corridors. Starting positions face each other
/// across the long axis.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let mut board = Board::rect(11, 9);

    // Light terrain: scattered forests and a couple of buildings.
    let forests = [
        Hex::new(3, 2),
        Hex::new(3, 3),
        Hex::new(7, 5),
        Hex::new(7, 6),
        Hex::new(5, 4),
    ];
    for h in forests {
        board.set_terrain(h, Terrain::Forest);
    }
    let buildings = [Hex::new(4, 6), Hex::new(6, 2)];
    for h in buildings {
        board.set_terrain(h, Terrain::Building);
    }
    // One mud patch.
    board.set_terrain(Hex::new(5, 1), Terrain::Mud);
    board.set_terrain(Hex::new(5, 7), Terrain::Mud);

    let red = Tank::stock(0, Side::Red, Hex::new(1, 4), Facing::E, "Red One");
    let blue = Tank::stock(1, Side::Blue, Hex::new(9, 4), Facing::W, "Blue One");

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
        activations_since_hit: 0,
        activations_since_damage: 0,
        total_hits: 0,
        total_pens: 0,
        total_glances: 0,
        total_fires: 0,
        total_cook_offs: 0,
        total_crew_wounds: 0,
        total_crew_kills: 0,
        abilities_used: 0,
        shots_fired: 0,
        shots_missed: 0,
    }
}
