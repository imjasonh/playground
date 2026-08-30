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
    /// 2 tanks (air) + 2 APCs + 2 infantry per side.
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
    /// When true, place scatter only on the west half and mirror each tile
    /// east–west so both approaches get the same cover/mud/rubble.
    mirror_scatter: bool,
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
    mirror_scatter: false,
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

/// Combined: 17×13 sealed midline with a wide plaza + mirrored side baffles.
fn combined_wall(width: i32, height: i32) -> Vec<Hex> {
    let mut wall = Vec::new();
    for q in 7..=9 {
        for r in 0..height {
            if (4..=8).contains(&r) {
                continue;
            }
            wall.push(Hex::new(q, r));
        }
    }
    // Side baffles — west pair, then east–west mirrors.
    let west_baffles = [Hex::new(2, 1), Hex::new(2, 2)];
    for h in west_baffles {
        wall.push(h);
        wall.push(mirror_ew(h, width));
    }
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

/// Reflect across the vertical midline (east–west symmetry).
fn mirror_ew(h: Hex, width: i32) -> Hex {
    Hex::new(width - 1 - h.q, h.r)
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
    let mut game = Game::new(board, vec![red, blue], coin_flip(rng), 20, "skirmish");
    // Scenario: terrain-only spoil on skirmish (unit nudge skewed color on the
    // offset start map).
    second_player_nudge_terrain(&mut game, 2);
    game
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
        mirror_scatter: false,
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
    let mut game = Game::new(board, tanks, coin_flip(rng), 200, "platoon").with_stalemate(40);
    second_player_setup(&mut game, 3);
    game
}

/// Combined arms on a 17×13 plaza board. Each side fields **2 tanks** (each
/// with air), **2 APCs**, and **2 infantry**. Starts, baffles, and scatter are
/// east–west mirrors.
pub fn combined<R: Rng>(rng: &mut R) -> Game {
    let width = 17;
    let height = 13;
    // West starts — east mirrors via `mirror_ew`.
    let red_tanks = [Hex::new(1, 3), Hex::new(1, 5)];
    let red_apcs = [Hex::new(1, 7), Hex::new(1, 9)];
    let red_inf = [Hex::new(0, 4), Hex::new(0, 8)];
    let blue_tanks = [
        mirror_ew(red_tanks[0], width),
        mirror_ew(red_tanks[1], width),
    ];
    let blue_apcs = [mirror_ew(red_apcs[0], width), mirror_ew(red_apcs[1], width)];
    let blue_inf = [mirror_ew(red_inf[0], width), mirror_ew(red_inf[1], width)];
    let reserved: Vec<Hex> = red_tanks
        .iter()
        .chain(red_apcs.iter())
        .chain(red_inf.iter())
        .chain(blue_tanks.iter())
        .chain(blue_apcs.iter())
        .chain(blue_inf.iter())
        .copied()
        .collect();
    let egress = [
        Hex::new(2, 3),
        Hex::new(2, 5),
        Hex::new(2, 7),
        Hex::new(2, 9),
        mirror_ew(Hex::new(2, 3), width),
        mirror_ew(Hex::new(2, 5), width),
        mirror_ew(Hex::new(2, 7), width),
        mirror_ew(Hex::new(2, 9), width),
    ];
    let wall = combined_wall(width, height);
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
        mirror_scatter: true,
    };
    let board = build_board(&layout, rng, &reserved, &egress);

    let mut red_t0 = Tank::stock(0, Side::Red, red_tanks[0], Facing::E, "Red Tank A");
    red_t0.has_air_support = true;
    let mut red_t1 = Tank::stock(1, Side::Red, red_tanks[1], Facing::E, "Red Tank B");
    red_t1.has_air_support = true;
    let mut blue_t0 = Tank::stock(6, Side::Blue, blue_tanks[0], Facing::W, "Blue Tank A");
    blue_t0.has_air_support = true;
    let mut blue_t1 = Tank::stock(7, Side::Blue, blue_tanks[1], Facing::W, "Blue Tank B");
    blue_t1.has_air_support = true;

    let tanks = vec![
        red_t0,
        red_t1,
        Tank::stock_apc(2, Side::Red, red_apcs[0], Facing::E, "Red APC A"),
        Tank::stock_apc(3, Side::Red, red_apcs[1], Facing::E, "Red APC B"),
        Tank::stock_infantry(4, Side::Red, red_inf[0], Facing::E, "Red Squad A"),
        Tank::stock_infantry(5, Side::Red, red_inf[1], Facing::E, "Red Squad B"),
        blue_t0,
        blue_t1,
        Tank::stock_apc(8, Side::Blue, blue_apcs[0], Facing::W, "Blue APC A"),
        Tank::stock_apc(9, Side::Blue, blue_apcs[1], Facing::W, "Blue APC B"),
        Tank::stock_infantry(10, Side::Blue, blue_inf[0], Facing::W, "Blue Squad A"),
        Tank::stock_infantry(11, Side::Blue, blue_inf[1], Facing::W, "Blue Squad B"),
    ];
    // More units → higher safety valve / idle window so a full wipe can finish.
    let mut game = Game::new(board, tanks, coin_flip(rng), 240, "combined").with_stalemate(48);
    // Scenario: after initiative, the second player may nudge each opposing
    // unit up to 1 hex and shift a few scatter terrain tiles before the first
    // activation.
    second_player_setup(&mut game, 4);
    game
}

/// Second-player post-initiative spoil: unit nudges, then scatter-terrain shifts.
fn second_player_setup(game: &mut Game, terrain_budget: u32) {
    second_player_nudge_opposing(game);
    second_player_nudge_terrain(game, terrain_budget);
}

/// Second player may move each first-player unit at most one hex (empty,
/// passable, on-board). Facing is unchanged. The sim picks, for each unit, the
/// legal hex that most spoils the opener (farther from second-player forces,
/// farther from the plaza, strip infantry out of forest when possible).
fn second_player_nudge_opposing(game: &mut Game) {
    let first = game.first_player;
    let second = first.other();
    let plaza = Hex::new(
        (game.board.min_q + game.board.max_q) / 2,
        (game.board.min_r + game.board.max_r) / 2,
    );
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

fn is_scatter(t: Terrain) -> bool {
    matches!(t, Terrain::Forest | Terrain::Mud | Terrain::Rubble)
}

/// Second player may shift up to `budget` non-static terrain tiles (forest /
/// mud / rubble) by 1 hex onto Open hexes. Buildings stay fixed. Destination
/// may be occupied (e.g. drop mud under a first-player tank); source becomes
/// Open. May break mirrored scatter — that is the point of the spoil.
///
/// Tiles may hop across the budget (1 hex per spend). A tile that lands on a
/// first-player vehicle is frozen so mud cannot walk in circles.
fn second_player_nudge_terrain(game: &mut Game, budget: u32) {
    use std::collections::HashSet;
    let first = game.first_player;
    let second = first.other();
    let plaza = Hex::new(
        (game.board.min_q + game.board.max_q) / 2,
        (game.board.min_r + game.board.max_r) / 2,
    );
    let mut frozen: HashSet<(i32, i32)> = HashSet::new();

    for _ in 0..budget {
        let scatter: Vec<Hex> = {
            let mut out = Vec::new();
            for q in game.board.min_q..=game.board.max_q {
                for r in game.board.min_r..=game.board.max_r {
                    let h = Hex::new(q, r);
                    if frozen.contains(&(h.q, h.r)) {
                        continue;
                    }
                    if is_scatter(game.board.terrain_at(h)) {
                        out.push(h);
                    }
                }
            }
            out
        };
        if scatter.is_empty() {
            break;
        }

        let mut best: Option<(Hex, Hex, Terrain, i32)> = None;
        for from in &scatter {
            let terrain = game.board.terrain_at(*from);
            for to in from.neighbors() {
                if !game.board.contains(to) {
                    continue;
                }
                if frozen.contains(&(to.q, to.r)) {
                    continue;
                }
                if game.board.terrain_at(to) != Terrain::Open {
                    continue;
                }
                let score = score_terrain_nudge(game, first, second, plaza, *from, to, terrain);
                if best.is_none_or(|(_, _, _, s)| score > s) {
                    best = Some((*from, to, terrain, score));
                }
            }
        }
        let Some((from, to, terrain, score)) = best else {
            break;
        };
        if score < 6 {
            break;
        }
        game.board.set_terrain(from, Terrain::Open);
        game.board.set_terrain(to, terrain);
        let landed_on_fp_vehicle = game
            .tanks
            .iter()
            .any(|t| t.side == first && t.kind != UnitKind::Infantry && t.pos == to);
        if landed_on_fp_vehicle {
            frozen.insert((to.q, to.r));
        }
        for t in game.tanks.iter_mut() {
            if t.kind == UnitKind::Infantry && t.pos == from && t.in_cover {
                t.in_cover = false;
            }
            if t.kind == UnitKind::Infantry && t.pos == to && terrain == Terrain::Forest {
                t.in_cover = true;
            }
        }
        game.push_setup_event(format!(
            "Second player shifts {terrain:?} {from} → {to} before start"
        ));
    }
}

fn score_terrain_nudge(
    game: &Game,
    first: Side,
    second: Side,
    plaza: Hex,
    from: Hex,
    to: Hex,
    terrain: Terrain,
) -> i32 {
    let mut score = 0i32;
    let fp: Vec<&Tank> = game.tanks.iter().filter(|t| t.side == first).collect();
    let sp: Vec<&Tank> = game.tanks.iter().filter(|t| t.side == second).collect();

    if terrain == Terrain::Forest {
        for t in &fp {
            if t.kind == UnitKind::Infantry && t.pos == from {
                score += 24;
            }
        }
        for t in &sp {
            if t.kind == UnitKind::Infantry && t.pos == to {
                score += 14;
            }
        }
        for t in &fp {
            if t.kind == UnitKind::Infantry && t.pos == to {
                score -= 20;
            }
        }
        for t in &fp {
            if t.kind == UnitKind::Tank
                && to.distance(t.pos) == 1
                && to.distance(plaza) < t.pos.distance(plaza)
            {
                score += 10;
            }
        }
    }

    if matches!(terrain, Terrain::Mud | Terrain::Rubble) {
        let mut best_before = i32::MAX;
        let mut best_after = i32::MAX;
        for t in &fp {
            if t.kind == UnitKind::Infantry {
                continue;
            }
            best_before = best_before.min(from.distance(t.pos));
            best_after = best_after.min(to.distance(t.pos));
            if to == t.pos {
                score += 30;
            } else if to.distance(t.pos) == 1 && to.distance(plaza) <= t.pos.distance(plaza) {
                score += 8;
            }
        }
        if best_before < i32::MAX {
            // Reward closing on the nearest first-player vehicle (enables hops).
            score += (best_before - best_after) * 12;
        }
    }

    score
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

    let mid_q = (layout.width - 1) / 2;
    let mut candidates: Vec<Hex> = Vec::new();
    for q in board.min_q..=board.max_q {
        if layout.mirror_scatter && q > mid_q {
            // East half is filled by mirroring west placements.
            continue;
        }
        if layout.mirror_scatter && q == mid_q {
            // Midline is wall/plaza; don't place unpaired center scatter.
            continue;
        }
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
    // With mirror scatter, counts are per-half; total tiles ≈ 2×.
    let (n_forest, n_mud, n_rubble) = if layout.mirror_scatter {
        (
            n_forest.div_ceil(2),
            n_mud.div_ceil(2),
            n_rubble.div_ceil(2),
        )
    } else {
        (n_forest, n_mud, n_rubble)
    };
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
        if layout.mirror_scatter {
            let m = mirror_ew(h, layout.width);
            if board.contains(m)
                && !layout.wall.contains(&m)
                && !layout.alley_clear.contains(&m)
                && !starts.contains(&m)
                && !egress.contains(&m)
            {
                board.set_terrain(m, terrain);
            }
        }
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
        // Stock starts (pre-nudge) have no LOS through the wall.
        assert!(
            !g.board.has_los(RED_START, BLUE_START, &[]),
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
        // Second-player spoil may move the first-player tank off RED_START /
        // BLUE_START; both must still be on-board and unstacked.
        let mut seen = std::collections::HashSet::new();
        for t in &g.tanks {
            assert!(g.board.contains(t.pos));
            assert!(seen.insert(t.pos));
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
        assert_eq!(g.tanks.len(), 12);
        assert_eq!(g.max_activations, 240);
        assert_eq!(g.stalemate_after, 48);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Red).count(), 6);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Blue).count(), 6);
        let count = |kind| g.tanks.iter().filter(|t| t.kind == kind).count();
        assert_eq!(count(UnitKind::Tank), 4);
        assert_eq!(count(UnitKind::Apc), 4);
        assert_eq!(count(UnitKind::Infantry), 4);
        assert!(g
            .tanks
            .iter()
            .filter(|t| t.kind == UnitKind::Tank)
            .all(|t| t.has_air_support));
        // Plaza open; spine sealed outside it.
        assert!(!g.board.terrain_at(Hex::new(8, 6)).impassable());
        assert!(g.board.terrain_at(Hex::new(8, 1)).impassable());
        assert!(g.board.terrain_at(Hex::new(8, 11)).impassable());
        // Constant skeleton is east–west mirrored (nudge may move units after).
        let width = 17;
        assert_eq!(mirror_ew(Hex::new(1, 3), width), Hex::new(15, 3));
        assert_eq!(mirror_ew(Hex::new(1, 9), width), Hex::new(15, 9));
        assert_eq!(mirror_ew(Hex::new(0, 4), width), Hex::new(16, 4));
        assert_eq!(g.board.terrain_at(Hex::new(2, 1)), Terrain::Building);
        assert_eq!(
            g.board.terrain_at(mirror_ew(Hex::new(2, 1), width)),
            Terrain::Building
        );
        assert_eq!(g.board.terrain_at(Hex::new(2, 2)), Terrain::Building);
        assert_eq!(
            g.board.terrain_at(mirror_ew(Hex::new(2, 2), width)),
            Terrain::Building
        );
        // Old asymmetric south baffles must be gone.
        assert_ne!(g.board.terrain_at(Hex::new(14, 10)), Terrain::Building);
        assert_ne!(g.board.terrain_at(Hex::new(14, 11)), Terrain::Building);
    }

    #[test]
    fn combined_starts_mirrored_before_nudge() {
        let width = 17;
        let red_tanks = [Hex::new(1, 3), Hex::new(1, 5)];
        let red_apcs = [Hex::new(1, 7), Hex::new(1, 9)];
        let red_inf = [Hex::new(0, 4), Hex::new(0, 8)];
        for h in red_tanks
            .iter()
            .chain(red_apcs.iter())
            .chain(red_inf.iter())
        {
            let m = mirror_ew(*h, width);
            assert_ne!(*h, m);
            assert_eq!(m.r, h.r);
            assert_eq!(m.q + h.q, width - 1);
        }
        // Spot-check kind pairing via a live setup's pre-nudge positions:
        // rebuild without nudge.
        let height = 13;
        let mut rng = ChaCha8Rng::seed_from_u64(4);
        let blue_tanks = [
            mirror_ew(red_tanks[0], width),
            mirror_ew(red_tanks[1], width),
        ];
        let blue_apcs = [mirror_ew(red_apcs[0], width), mirror_ew(red_apcs[1], width)];
        let blue_inf = [mirror_ew(red_inf[0], width), mirror_ew(red_inf[1], width)];
        let reserved: Vec<Hex> = red_tanks
            .iter()
            .chain(red_apcs.iter())
            .chain(red_inf.iter())
            .chain(blue_tanks.iter())
            .chain(blue_apcs.iter())
            .chain(blue_inf.iter())
            .copied()
            .collect();
        let egress = [
            Hex::new(2, 3),
            Hex::new(2, 5),
            Hex::new(2, 7),
            Hex::new(2, 9),
            mirror_ew(Hex::new(2, 3), width),
            mirror_ew(Hex::new(2, 5), width),
            mirror_ew(Hex::new(2, 7), width),
            mirror_ew(Hex::new(2, 9), width),
        ];
        let wall = combined_wall(width, height);
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
            mirror_scatter: true,
        };
        let _board = build_board(&layout, &mut rng, &reserved, &egress);
        let tanks = vec![
            Tank::stock(0, Side::Red, red_tanks[0], Facing::E, "Red Tank A"),
            Tank::stock(1, Side::Red, red_tanks[1], Facing::E, "Red Tank B"),
            Tank::stock_apc(2, Side::Red, red_apcs[0], Facing::E, "Red APC A"),
            Tank::stock_apc(3, Side::Red, red_apcs[1], Facing::E, "Red APC B"),
            Tank::stock_infantry(4, Side::Red, red_inf[0], Facing::E, "Red Squad A"),
            Tank::stock_infantry(5, Side::Red, red_inf[1], Facing::E, "Red Squad B"),
            Tank::stock(6, Side::Blue, blue_tanks[0], Facing::W, "Blue Tank A"),
            Tank::stock(7, Side::Blue, blue_tanks[1], Facing::W, "Blue Tank B"),
            Tank::stock_apc(8, Side::Blue, blue_apcs[0], Facing::W, "Blue APC A"),
            Tank::stock_apc(9, Side::Blue, blue_apcs[1], Facing::W, "Blue APC B"),
            Tank::stock_infantry(10, Side::Blue, blue_inf[0], Facing::W, "Blue Squad A"),
            Tank::stock_infantry(11, Side::Blue, blue_inf[1], Facing::W, "Blue Squad B"),
        ];
        for t in &tanks {
            if t.side == Side::Red {
                let m = mirror_ew(t.pos, width);
                assert!(
                    tanks
                        .iter()
                        .any(|b| b.side == Side::Blue && b.pos == m && b.kind == t.kind),
                    "no blue mirror for {:?}",
                    t.pos
                );
            }
        }
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
        assert_eq!(g.tanks.iter().filter(|t| t.side == first).count(), 6);
    }

    #[test]
    fn combined_second_player_may_shift_scatter_terrain() {
        let mut any_shift = false;
        let mut g = None;
        for seed in 0..30u64 {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            let game = combined(&mut rng);
            let shifts = game
                .events
                .iter()
                .any(|e| e.text.contains("Second player shifts"));
            if shifts {
                any_shift = true;
                g = Some(game);
                break;
            }
        }
        assert!(any_shift, "expected some seed to shift scatter terrain");
        let g = g.unwrap();
        // Buildings (static) must still be mirrored.
        let width = g.board.max_q + 1;
        for q in g.board.min_q..=g.board.max_q {
            for r in g.board.min_r..=g.board.max_r {
                let h = Hex::new(q, r);
                if g.board.terrain_at(h) == Terrain::Building {
                    assert_eq!(
                        g.board.terrain_at(mirror_ew(h, width)),
                        Terrain::Building,
                        "building at {h} lost its mirror"
                    );
                }
            }
        }
    }

    #[test]
    fn combined_scatter_generated_east_west_mirrored() {
        // Scatter is mirrored at generation; second-player terrain spoil may
        // break that afterward — so check the board *before* setup.
        let width = 17;
        let height = 13;
        let mut rng = ChaCha8Rng::seed_from_u64(9);
        let red_tanks = [Hex::new(1, 3), Hex::new(1, 5)];
        let red_apcs = [Hex::new(1, 7), Hex::new(1, 9)];
        let red_inf = [Hex::new(0, 4), Hex::new(0, 8)];
        let blue_tanks = [
            mirror_ew(red_tanks[0], width),
            mirror_ew(red_tanks[1], width),
        ];
        let blue_apcs = [mirror_ew(red_apcs[0], width), mirror_ew(red_apcs[1], width)];
        let blue_inf = [mirror_ew(red_inf[0], width), mirror_ew(red_inf[1], width)];
        let reserved: Vec<Hex> = red_tanks
            .iter()
            .chain(red_apcs.iter())
            .chain(red_inf.iter())
            .chain(blue_tanks.iter())
            .chain(blue_apcs.iter())
            .chain(blue_inf.iter())
            .copied()
            .collect();
        let egress = [
            Hex::new(2, 3),
            Hex::new(2, 5),
            Hex::new(2, 7),
            Hex::new(2, 9),
            mirror_ew(Hex::new(2, 3), width),
            mirror_ew(Hex::new(2, 5), width),
            mirror_ew(Hex::new(2, 7), width),
            mirror_ew(Hex::new(2, 9), width),
        ];
        let wall = combined_wall(width, height);
        let alley = combined_alley_clear();
        let goals = [Hex::new(8, 5), Hex::new(8, 7)];
        let layout = MapLayout {
            width,
            height,
            wall: &wall,
            alley_clear: &alley,
            path_goals: &goals,
            forest: (10, 16),
            mud: (4, 7),
            rubble: (3, 6),
            mirror_scatter: true,
        };
        let board = build_board(&layout, &mut rng, &reserved, &egress);
        let mid = (width - 1) / 2;
        for q in 0..=mid {
            for r in 0..height {
                let h = Hex::new(q, r);
                let m = mirror_ew(h, width);
                let th = board.terrain_at(h);
                let tm = board.terrain_at(m);
                if matches!(th, Terrain::Forest | Terrain::Mud | Terrain::Rubble)
                    || matches!(tm, Terrain::Forest | Terrain::Mud | Terrain::Rubble)
                {
                    assert_eq!(th, tm, "scatter mismatch at {h} ({th:?}) vs {m} ({tm:?})");
                }
            }
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
