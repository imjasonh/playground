//! Built-in scenarios. v1: Skirmish only.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank};
use rand::Rng;

/// 1v1 tank duel on a light-terrain board with a blocked center corridor.
///
/// Board is 11×9 axial. A short building wall sits on the midline so the
/// tanks cannot trade shots down the starting street. Two alleys (north and
/// south) are the ways around; forests sit on the alley mouths so cover is
/// a real choice when peeking.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let mut board = Board::rect(11, 9);

    // Midline wall: blocks the open east-west corridor on r=3..5.
    // Gaps above (r<=1) and below (r>=7) are the flanking alleys.
    let wall = [
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
    for h in wall {
        board.set_terrain(h, Terrain::Building);
    }

    // Forests on alley approaches — sit here for -1 enemy accuracy.
    let forests = [
        Hex::new(2, 1),
        Hex::new(3, 1),
        Hex::new(7, 1),
        Hex::new(8, 1),
        Hex::new(2, 7),
        Hex::new(3, 7),
        Hex::new(7, 7),
        Hex::new(8, 7),
    ];
    for h in forests {
        board.set_terrain(h, Terrain::Forest);
    }

    // Mud in the dead corners so the long way around costs something.
    board.set_terrain(Hex::new(0, 0), Terrain::Mud);
    board.set_terrain(Hex::new(10, 0), Terrain::Mud);
    board.set_terrain(Hex::new(0, 8), Terrain::Mud);
    board.set_terrain(Hex::new(10, 8), Terrain::Mud);

    // Same street, opposite ends — LOS is blocked by the wall until someone
    // takes an alley.
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
        at_shots: 0,
        he_shots: 0,
        moves_made: 0,
        turns_made: 0,
        turret_rotations: 0,
    }
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
        assert!(
            !g.board.has_los(red.pos, blue.pos, &[]),
            "opening street must not allow LOS through the wall"
        );
        // Alleys clear of buildings.
        assert_eq!(
            g.board.terrain_at(Hex::new(5, 1)),
            crate::board::Terrain::Open
        );
        assert_eq!(
            g.board.terrain_at(Hex::new(5, 7)),
            crate::board::Terrain::Open
        );
    }
}
