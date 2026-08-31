//! Built-in scenarios: learning ladder from 1v1 stock to combined arms.

use crate::board::{Board, Terrain};
use crate::game::Game;
use crate::hex::{Facing, Hex};
use crate::unit::{Side, Tank, UnitKind};
use crate::upgrades::{initiative_from_lists, spend_budget};
use rand::seq::SliceRandom;
use rand::Rng;

/// Which scenario to spin up.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScenarioKind {
    /// Intro: 1v1 stock tanks, no upgrades.
    Skirmish,
    /// 3v3 stock tanks, no upgrades (group tactics).
    Squadron,
    /// 3v3 with list upgrades.
    Platoon,
    /// 2 tanks (air) + 2 APCs + 2 infantry per side, with lists.
    Combined,
    /// Flag raid: 1 tank + 3 loaded APCs per side; infantry Capture wins.
    Capture,
    /// Attacker/defender: one side Captures a single flag; the other holds or wipes.
    Assault,
}

impl ScenarioKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ScenarioKind::Skirmish => "skirmish",
            ScenarioKind::Squadron => "squadron",
            ScenarioKind::Platoon => "platoon",
            ScenarioKind::Combined => "combined",
            ScenarioKind::Capture => "capture",
            ScenarioKind::Assault => "assault",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "skirmish" | "intro" => Some(Self::Skirmish),
            "squadron" => Some(Self::Squadron),
            "platoon" => Some(Self::Platoon),
            "combined" => Some(Self::Combined),
            "capture" | "raid" | "flag" => Some(Self::Capture),
            "assault" | "attack" | "defend" => Some(Self::Assault),
            _ => None,
        }
    }
}

/// Fixed terrain + scatter recipe for a scenario board.
struct MapLayout<'a> {
    width: i32,
    height: i32,
    /// Impassable buildings that never move (may be empty).
    wall: &'a [Hex],
    /// Must stay open (approaches / reserved lanes).
    alley_clear: &'a [Hex],
    /// Pathability probes: each start must reach at least one goal.
    path_goals: &'a [Hex],
    /// Random building clumps (count range, size range per clump).
    building_clumps: (u32, u32),
    building_clump_size: (u32, u32),
    /// Forest hex budget, grown as clumps of `forest_clump_size`.
    forest: (u32, u32),
    forest_clump_size: (u32, u32),
    mud: (u32, u32),
    rubble: (u32, u32),
    /// When true, place scatter only on the west half and mirror each tile
    /// east–west so both approaches get the same cover/mud/rubble.
    mirror_scatter: bool,
}

/// Shared battle mat for squadron / platoon / combined (columns × rows).
const BATTLE_WIDTH: i32 = 18;
const BATTLE_HEIGHT: i32 = 12;
/// Skirmish: half the battle width, same height.
const SKIRMISH_WIDTH: i32 = 9;
const SKIRMISH_HEIGHT: i32 = 12;

/// Skirmish: compact midline block on the half-width mat.
const SKIRMISH_WALL: [Hex; 9] = [
    Hex::offset(3, 4),
    Hex::offset(3, 5),
    Hex::offset(3, 6),
    Hex::offset(4, 4),
    Hex::offset(4, 5),
    Hex::offset(4, 6),
    Hex::offset(5, 4),
    Hex::offset(5, 5),
    Hex::offset(5, 6),
];
const SKIRMISH_ALLEY: [Hex; 8] = [
    Hex::offset(4, 0),
    Hex::offset(4, 1),
    Hex::offset(4, 2),
    Hex::offset(4, 3),
    Hex::offset(4, 7),
    Hex::offset(4, 8),
    Hex::offset(4, 9),
    Hex::offset(4, 10),
];
const SKIRMISH_GOALS: [Hex; 2] = [Hex::offset(4, 2), Hex::offset(4, 9)];

const SKIRMISH_MAP: MapLayout = MapLayout {
    width: SKIRMISH_WIDTH,
    height: SKIRMISH_HEIGHT,
    wall: &SKIRMISH_WALL,
    alley_clear: &SKIRMISH_ALLEY,
    path_goals: &SKIRMISH_GOALS,
    building_clumps: (0, 0),
    building_clump_size: (1, 1),
    forest: (5, 9),
    forest_clump_size: (2, 4),
    mud: (2, 4),
    rubble: (1, 3),
    mirror_scatter: false,
};

/// Reflect across the vertical midline (east–west symmetry) in offset space.
fn mirror_ew(h: Hex, width: i32) -> Hex {
    let (col, row) = h.to_offset();
    Hex::offset(width - 1 - col, row)
}

/// How deep each side's deployment zone reaches from its home edge.
const DEPLOY_DEPTH_BATTLE: i32 = 3;
const DEPLOY_DEPTH_SKIRMISH: i32 = 2;

fn deploy_zone_hexes(width: i32, height: i32, depth: i32) -> Vec<Hex> {
    let mut out = Vec::with_capacity((depth * height * 2) as usize);
    for row in 0..height {
        for d in 0..depth {
            out.push(Hex::offset(d, row));
            out.push(Hex::offset(width - 1 - d, row));
        }
    }
    out
}

/// Provisional seed hex inside a side's zone (before alternating placement).
fn zone_seed(side: Side, width: i32, height: i32, depth: i32, slot: usize) -> Hex {
    let row = ((slot as i32 * 3) + 2).clamp(0, height - 1);
    let col = match side {
        Side::Red => (depth / 2).min(depth - 1).max(0),
        Side::Blue => (width - 1 - depth / 2).clamp(0, width - 1),
    };
    Hex::offset(col, row)
}

/// Scenario-aware reason a unit is being placed.
#[derive(Clone, Copy, Debug)]
enum PlaceGoal {
    /// Close and shoot (skirmish / squadron / platoon).
    Duel,
    /// Combined: tanks hold lanes; APCs/infantry want cover / mutual support.
    Combined,
    /// Race enemy flag with APCs; tank covers.
    Capture,
    /// Assault attacker: push the flag.
    AssaultAttack,
    /// Assault defender: sit on the flag.
    AssaultDefend,
}

fn place_goal_for(game: &Game, side: Side) -> PlaceGoal {
    match game.scenario.as_str() {
        "capture" => PlaceGoal::Capture,
        "assault" => {
            if game.is_attacker(side) {
                PlaceGoal::AssaultAttack
            } else {
                PlaceGoal::AssaultDefend
            }
        }
        "combined" => PlaceGoal::Combined,
        _ => PlaceGoal::Duel,
    }
}

/// Alternating placement into edge deployment zones.
///
/// `first_to_place` puts the first unit (usually the second player / defender),
/// then sides alternate. Embarked infantry are skipped (they ride with their
/// vehicle). Scoring is scenario-aware so a Red distance bias from fixed
/// mirrored seeds is an AI/placement bug, not a map rule.
fn deploy_alternating(game: &mut Game, depth: i32, first_to_place: Side) {
    let mut red_q: Vec<u8> = game
        .tanks
        .iter()
        .filter(|t| t.side == Side::Red && !t.is_embarked())
        .map(|t| t.id)
        .collect();
    let mut blue_q: Vec<u8> = game
        .tanks
        .iter()
        .filter(|t| t.side == Side::Blue && !t.is_embarked())
        .map(|t| t.id)
        .collect();
    // Prefer vehicles before lone infantry when both are in the queue.
    let sort_q = |q: &mut Vec<u8>, g: &Game| {
        q.sort_by_key(|id| match g.tank(*id).kind {
            UnitKind::Tank => 0,
            UnitKind::Apc => 1,
            UnitKind::Infantry => 2,
        });
    };
    sort_q(&mut red_q, game);
    sort_q(&mut blue_q, game);
    // `pop` takes the last element — reverse so tanks come off first.
    red_q.reverse();
    blue_q.reverse();

    let mut placed: std::collections::HashSet<u8> = std::collections::HashSet::new();
    let mut side = first_to_place;
    let total = red_q.len() + blue_q.len();
    for _ in 0..total {
        let q = match side {
            Side::Red => &mut red_q,
            Side::Blue => &mut blue_q,
        };
        let Some(id) = q.pop() else {
            side = side.other();
            continue;
        };
        let goal = place_goal_for(game, side);
        let hex = pick_deploy_hex(game, id, depth, goal, &placed);
        let name = game.tank(id).name.clone();
        let from = game.tank(id).pos;
        game.tank_mut(id).pos = hex;
        if let Some(pid) = game.tank(id).passenger {
            game.tank_mut(pid).pos = hex;
            placed.insert(pid);
        }
        // Dig infantry into forest when defending / combined.
        if game.tank(id).kind == UnitKind::Infantry
            && game.board.terrain_at(hex) == Terrain::Forest
            && matches!(goal, PlaceGoal::AssaultDefend | PlaceGoal::Combined)
        {
            game.tank_mut(id).in_cover = true;
        }
        placed.insert(id);
        if hex != from {
            game.push_setup_event(format!("{side:?} deploys {name} → {hex} ({goal:?})"));
        }
        side = side.other();
    }
}

fn pick_deploy_hex(
    game: &Game,
    unit_id: u8,
    depth: i32,
    goal: PlaceGoal,
    placed: &std::collections::HashSet<u8>,
) -> Hex {
    let unit = game.tank(unit_id);
    let side = unit.side;
    let width = game.board.width;
    let height = game.board.height;
    let occupied: Vec<Hex> = game
        .tanks
        .iter()
        .filter(|t| placed.contains(&t.id))
        .map(|t| t.pos)
        .collect();
    let mut best = unit.pos;
    let mut best_score = i32::MIN;
    for row in 0..height {
        for d in 0..depth {
            let col = match side {
                Side::Red => d,
                Side::Blue => width - 1 - d,
            };
            let hex = Hex::offset(col, row);
            if !game.board.contains(hex) || game.board.terrain_at(hex).impassable() {
                continue;
            }
            if occupied.contains(&hex) {
                continue;
            }
            // Flags are not units; keep them free for Capture/Assault.
            if game.objectives.iter().any(|o| o.hex == hex) {
                continue;
            }
            let score = score_deploy_hex(game, unit_id, hex, goal, depth, placed);
            if score > best_score {
                best_score = score;
                best = hex;
            }
        }
    }
    best
}

fn score_deploy_hex(
    game: &Game,
    unit_id: u8,
    hex: Hex,
    goal: PlaceGoal,
    depth: i32,
    placed: &std::collections::HashSet<u8>,
) -> i32 {
    let unit = game.tank(unit_id);
    let side = unit.side;
    let width = game.board.width;
    let (col, row) = hex.to_offset();
    // Forward edge of the zone (toward the enemy).
    let forward_col = match side {
        Side::Red => depth - 1,
        Side::Blue => width - depth,
    };
    let forwardness = depth - 1 - (col - forward_col).abs();
    let mut score = forwardness * 3;

    // Spread: avoid stacking on same row as already-placed friendly vehicles.
    let same_row_friends = game
        .tanks
        .iter()
        .filter(|t| {
            t.side == side
                && placed.contains(&t.id)
                && t.id != unit_id
                && !t.is_embarked()
                && t.pos.to_offset().1 == row
        })
        .count() as i32;
    score -= same_row_friends * 4;

    let terrain = game.board.terrain_at(hex);
    match goal {
        PlaceGoal::Duel => {
            score += forwardness * 8;
            // Prefer open firing lanes toward board center.
            let center = game.board.center();
            score += (20 - hex.distance(center).min(20)) * 2;
            if terrain == Terrain::Mud {
                score -= 6;
            }
        }
        PlaceGoal::Combined => match unit.kind {
            UnitKind::Tank => {
                score += forwardness * 6;
                score += (18 - hex.distance(game.board.center()).min(18)) * 2;
            }
            UnitKind::Apc => {
                score += forwardness * 4;
                if terrain == Terrain::Forest {
                    score += 4;
                }
            }
            UnitKind::Infantry => {
                if terrain == Terrain::Forest {
                    score += 20;
                }
                // Near a friendly APC already placed.
                let near_apc = game
                    .tanks
                    .iter()
                    .filter(|t| {
                        t.side == side
                            && t.kind == UnitKind::Apc
                            && placed.contains(&t.id)
                            && t.pos.distance(hex) <= 2
                    })
                    .count() as i32;
                score += near_apc * 6;
            }
        },
        PlaceGoal::Capture | PlaceGoal::AssaultAttack => {
            if let Some(flag) = game.enemy_flag(side) {
                let dist = hex.distance(flag);
                // Primary: race. Equalize by picking the globally shortest path hex.
                score += (40 - dist.min(40)) * 20;
                if matches!(unit.kind, UnitKind::Apc) {
                    score += 8; // APCs are the carriers
                }
                if unit.kind == UnitKind::Tank {
                    score -= 4; // tank slightly less obsessed with pure race
                }
            }
            if terrain == Terrain::Mud {
                score -= 10;
            }
        }
        PlaceGoal::AssaultDefend => {
            if let Some(flag) = game.own_flag(side) {
                let dist = hex.distance(flag);
                score += (12 - dist.min(12)) * 25;
                if unit.kind == UnitKind::Infantry && terrain == Terrain::Forest {
                    score += 30;
                }
                if unit.kind == UnitKind::Tank {
                    score += forwardness * 2;
                }
            }
        }
    }
    score
}

pub fn setup<R: Rng>(kind: ScenarioKind, rng: &mut R) -> Game {
    match kind {
        ScenarioKind::Skirmish => skirmish(rng),
        ScenarioKind::Squadron => squadron(rng),
        ScenarioKind::Platoon => platoon(rng),
        ScenarioKind::Combined => combined(rng),
        ScenarioKind::Capture => capture(rng),
        ScenarioKind::Assault => assault(rng),
    }
}

fn coin_flip<R: Rng>(rng: &mut R) -> Side {
    if rng.gen_bool(0.5) {
        Side::Red
    } else {
        Side::Blue
    }
}

/// Intro / skirmish: 1v1 stock tanks on the half-width mat (9×12). No upgrades.
pub fn skirmish<R: Rng>(rng: &mut R) -> Game {
    let depth = DEPLOY_DEPTH_SKIRMISH;
    let zones = deploy_zone_hexes(SKIRMISH_WIDTH, SKIRMISH_HEIGHT, depth);
    let egress = [Hex::offset(2, 4), Hex::offset(6, 7)];
    let reserved: Vec<Hex> = zones.iter().chain(egress.iter()).copied().collect();
    let board = build_board(&SKIRMISH_MAP, rng, &reserved, &egress);
    let red = Tank::stock(
        0,
        Side::Red,
        zone_seed(Side::Red, SKIRMISH_WIDTH, SKIRMISH_HEIGHT, depth, 0),
        Facing::E,
        "Red One",
    );
    let blue = Tank::stock(
        1,
        Side::Blue,
        zone_seed(Side::Blue, SKIRMISH_WIDTH, SKIRMISH_HEIGHT, depth, 0),
        Facing::W,
        "Blue One",
    );
    let first = coin_flip(rng);
    let mut game = Game::new(board, vec![red, blue], first, 20, "skirmish");
    // Second player places first, then alternate (1v1: SP then FP).
    deploy_alternating(&mut game, depth, first.other());
    // Terrain-only spoil: unit nudges skewed color on offset starts.
    second_player_nudge_terrain(&mut game, 2);
    game
}

fn open_battle_board<R: Rng>(rng: &mut R) -> Board {
    let width = BATTLE_WIDTH;
    let height = BATTLE_HEIGHT;
    let depth = DEPLOY_DEPTH_BATTLE;
    let zones = deploy_zone_hexes(width, height, depth);
    let egress = [
        Hex::offset(3, 3),
        Hex::offset(3, 6),
        Hex::offset(3, 9),
        Hex::offset(14, 3),
        Hex::offset(14, 6),
        Hex::offset(14, 9),
    ];
    let reserved: Vec<Hex> = zones.iter().chain(egress.iter()).copied().collect();
    let goals = [Hex::offset(8, 5), Hex::offset(9, 6)];
    let layout = MapLayout {
        width,
        height,
        wall: &[],
        alley_clear: &egress,
        path_goals: &goals,
        building_clumps: (4, 7),
        building_clump_size: (2, 5),
        forest: (18, 30),
        forest_clump_size: (3, 6),
        mud: (3, 6),
        rubble: (2, 5),
        mirror_scatter: false,
    };
    build_board(&layout, rng, &reserved, &egress)
}

fn seed_six_tank_force(width: i32, height: i32, depth: i32) -> Vec<Tank> {
    vec![
        Tank::stock(
            0,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 0),
            Facing::E,
            "Red Alpha",
        ),
        Tank::stock(
            1,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 1),
            Facing::E,
            "Red Bravo",
        ),
        Tank::stock(
            2,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 2),
            Facing::E,
            "Red Charlie",
        ),
        Tank::stock(
            3,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 0),
            Facing::W,
            "Blue Alpha",
        ),
        Tank::stock(
            4,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 1),
            Facing::W,
            "Blue Bravo",
        ),
        Tank::stock(
            5,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 2),
            Facing::W,
            "Blue Charlie",
        ),
    ]
}

/// Squadron: 3v3 stock tanks, no upgrades — learn pass activation / group play.
pub fn squadron<R: Rng>(rng: &mut R) -> Game {
    let depth = DEPLOY_DEPTH_BATTLE;
    let board = open_battle_board(rng);
    let tanks = seed_six_tank_force(BATTLE_WIDTH, BATTLE_HEIGHT, depth);
    let first = coin_flip(rng);
    let mut game = Game::new(board, tanks, first, 200, "squadron").with_stalemate(40);
    deploy_alternating(&mut game, depth, first.other());
    second_player_setup(&mut game, 3);
    game
}

/// Platoon: 3v3 with list upgrades on the shared 18×12 open board.
pub fn platoon<R: Rng>(rng: &mut R) -> Game {
    let depth = DEPLOY_DEPTH_BATTLE;
    let board = open_battle_board(rng);
    let mut tanks = seed_six_tank_force(BATTLE_WIDTH, BATTLE_HEIGHT, depth);
    for t in &mut tanks {
        spend_budget(t, 10, false, rng);
    }
    let (first, spoil) = initiative_from_lists(&tanks, rng);
    let mut game = Game::new(board, tanks, first, 200, "platoon")
        .with_stalemate(40)
        .with_list_initiative(!spoil);
    deploy_alternating(&mut game, depth, first.other());
    if spoil {
        second_player_setup(&mut game, 3);
    }
    game
}

/// Combined arms on the same 18×12 open board as squadron/platoon. Each side fields
/// **2 tanks** (each with air), **2 APCs**, and **2 infantry**. Scatter is
/// east–west mirrored at generation; units place alternately into edge zones.
pub fn combined<R: Rng>(rng: &mut R) -> Game {
    let width = BATTLE_WIDTH;
    let height = BATTLE_HEIGHT;
    let depth = DEPLOY_DEPTH_BATTLE;
    let zones = deploy_zone_hexes(width, height, depth);
    let egress = [
        Hex::offset(3, 3),
        Hex::offset(3, 5),
        Hex::offset(3, 7),
        Hex::offset(3, 9),
        mirror_ew(Hex::offset(3, 3), width),
        mirror_ew(Hex::offset(3, 5), width),
        mirror_ew(Hex::offset(3, 7), width),
        mirror_ew(Hex::offset(3, 9), width),
    ];
    let reserved: Vec<Hex> = zones.iter().chain(egress.iter()).copied().collect();
    let goals = [Hex::offset(8, 5), Hex::offset(9, 6)];
    let layout = MapLayout {
        width,
        height,
        wall: &[],
        alley_clear: &egress,
        path_goals: &goals,
        building_clumps: (4, 7),
        building_clump_size: (2, 5),
        forest: (18, 30),
        forest_clump_size: (3, 6),
        mud: (3, 6),
        rubble: (2, 5),
        mirror_scatter: true,
    };
    let board = build_board(&layout, rng, &reserved, &egress);

    let mut red_t0 = Tank::stock(
        0,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 0),
        Facing::E,
        "Red Tank A",
    );
    spend_budget(&mut red_t0, 10, true, rng);
    red_t0.has_air_support = true; // scenario grant (on top of list)
    let mut red_t1 = Tank::stock(
        1,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 1),
        Facing::E,
        "Red Tank B",
    );
    spend_budget(&mut red_t1, 10, true, rng);
    red_t1.has_air_support = true;
    let mut blue_t0 = Tank::stock(
        6,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 0),
        Facing::W,
        "Blue Tank A",
    );
    spend_budget(&mut blue_t0, 10, true, rng);
    blue_t0.has_air_support = true;
    let mut blue_t1 = Tank::stock(
        7,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 1),
        Facing::W,
        "Blue Tank B",
    );
    spend_budget(&mut blue_t1, 10, true, rng);
    blue_t1.has_air_support = true;

    let mut red_apc_a = Tank::stock_apc(
        2,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 2),
        Facing::E,
        "Red APC A",
    );
    spend_budget(&mut red_apc_a, 4, false, rng);
    let mut red_apc_b = Tank::stock_apc(
        3,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 3),
        Facing::E,
        "Red APC B",
    );
    spend_budget(&mut red_apc_b, 4, false, rng);
    let mut blue_apc_a = Tank::stock_apc(
        8,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 2),
        Facing::W,
        "Blue APC A",
    );
    spend_budget(&mut blue_apc_a, 4, false, rng);
    let mut blue_apc_b = Tank::stock_apc(
        9,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 3),
        Facing::W,
        "Blue APC B",
    );
    spend_budget(&mut blue_apc_b, 4, false, rng);

    let tanks = vec![
        red_t0,
        red_t1,
        red_apc_a,
        red_apc_b,
        Tank::stock_infantry(
            4,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 4),
            Facing::E,
            "Red Squad A",
        ),
        Tank::stock_infantry(
            5,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 5),
            Facing::E,
            "Red Squad B",
        ),
        blue_t0,
        blue_t1,
        blue_apc_a,
        blue_apc_b,
        Tank::stock_infantry(
            10,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 4),
            Facing::W,
            "Blue Squad A",
        ),
        Tank::stock_infantry(
            11,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 5),
            Facing::W,
            "Blue Squad B",
        ),
    ];
    let (first, spoil) = initiative_from_lists(&tanks, rng);
    let mut game = Game::new(board, tanks, first, 240, "combined")
        .with_stalemate(48)
        .with_list_initiative(!spoil);
    deploy_alternating(&mut game, depth, first.other());
    // Mines go down during deployment, after unit placement, before spoil.
    game.place_deployment_mines(rng);
    if spoil {
        second_player_setup(&mut game, 4);
    }
    game
}

/// Flag raid: each side fields **1 tank** + **3 APCs** already loaded with
/// infantry. Each side has a backline flag; infantry **Capture** on the enemy
/// flag wins immediately. List upgrades (tanks ≤10 with mines, APCs ≤4).
pub fn capture<R: Rng>(rng: &mut R) -> Game {
    let width = BATTLE_WIDTH;
    let height = BATTLE_HEIGHT;
    let depth = DEPLOY_DEPTH_BATTLE;
    let red_flag = Hex::offset(0, 6);
    let blue_flag = Hex::offset(width - 1, 6);
    let zones = deploy_zone_hexes(width, height, depth);
    let egress = [
        Hex::offset(3, 2),
        Hex::offset(3, 5),
        Hex::offset(3, 7),
        Hex::offset(3, 10),
        mirror_ew(Hex::offset(3, 2), width),
        mirror_ew(Hex::offset(3, 5), width),
        mirror_ew(Hex::offset(3, 7), width),
        mirror_ew(Hex::offset(3, 10), width),
        red_flag,
        blue_flag,
    ];
    let reserved: Vec<Hex> = zones.iter().chain(egress.iter()).copied().collect();
    let goals = [Hex::offset(8, 5), Hex::offset(9, 6), red_flag, blue_flag];
    let layout = MapLayout {
        width,
        height,
        wall: &[],
        alley_clear: &egress,
        path_goals: &goals,
        building_clumps: (4, 7),
        building_clump_size: (2, 5),
        forest: (18, 30),
        forest_clump_size: (3, 6),
        mud: (3, 6),
        rubble: (2, 5),
        mirror_scatter: true,
    };
    let mut board = build_board(&layout, rng, &reserved, &egress);
    board.set_terrain(red_flag, Terrain::Open);
    board.set_terrain(blue_flag, Terrain::Open);

    let mut red_t = Tank::stock(
        0,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 0),
        Facing::E,
        "Red Tank",
    );
    spend_budget(&mut red_t, 10, true, rng);
    let mut red_apc_a = Tank::stock_apc(
        1,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 1),
        Facing::E,
        "Red APC A",
    );
    spend_budget(&mut red_apc_a, 4, false, rng);
    let mut red_apc_b = Tank::stock_apc(
        2,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 2),
        Facing::E,
        "Red APC B",
    );
    spend_budget(&mut red_apc_b, 4, false, rng);
    let mut red_apc_c = Tank::stock_apc(
        3,
        Side::Red,
        zone_seed(Side::Red, width, height, depth, 3),
        Facing::E,
        "Red APC C",
    );
    spend_budget(&mut red_apc_c, 4, false, rng);
    let mut blue_t = Tank::stock(
        7,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 0),
        Facing::W,
        "Blue Tank",
    );
    spend_budget(&mut blue_t, 10, true, rng);
    let mut blue_apc_a = Tank::stock_apc(
        8,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 1),
        Facing::W,
        "Blue APC A",
    );
    spend_budget(&mut blue_apc_a, 4, false, rng);
    let mut blue_apc_b = Tank::stock_apc(
        9,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 2),
        Facing::W,
        "Blue APC B",
    );
    spend_budget(&mut blue_apc_b, 4, false, rng);
    let mut blue_apc_c = Tank::stock_apc(
        10,
        Side::Blue,
        zone_seed(Side::Blue, width, height, depth, 3),
        Facing::W,
        "Blue APC C",
    );
    spend_budget(&mut blue_apc_c, 4, false, rng);

    let mut tanks = vec![
        red_t,
        red_apc_a,
        red_apc_b,
        red_apc_c,
        Tank::stock_infantry(
            4,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 1),
            Facing::E,
            "Red Squad A",
        ),
        Tank::stock_infantry(
            5,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 2),
            Facing::E,
            "Red Squad B",
        ),
        Tank::stock_infantry(
            6,
            Side::Red,
            zone_seed(Side::Red, width, height, depth, 3),
            Facing::E,
            "Red Squad C",
        ),
        blue_t,
        blue_apc_a,
        blue_apc_b,
        blue_apc_c,
        Tank::stock_infantry(
            11,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 1),
            Facing::W,
            "Blue Squad A",
        ),
        Tank::stock_infantry(
            12,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 2),
            Facing::W,
            "Blue Squad B",
        ),
        Tank::stock_infantry(
            13,
            Side::Blue,
            zone_seed(Side::Blue, width, height, depth, 3),
            Facing::W,
            "Blue Squad C",
        ),
    ];
    // Pre-load each squad into its APC.
    for (apc_id, inf_id) in [(1u8, 4u8), (2, 5), (3, 6), (8, 11), (9, 12), (10, 13)] {
        let pos = tanks.iter().find(|t| t.id == apc_id).unwrap().pos;
        if let Some(apc) = tanks.iter_mut().find(|t| t.id == apc_id) {
            apc.passenger = Some(inf_id);
        }
        if let Some(inf) = tanks.iter_mut().find(|t| t.id == inf_id) {
            inf.embarked_in = Some(apc_id);
            inf.pos = pos;
        }
    }

    let (first, spoil) = initiative_from_lists(&tanks, rng);
    let objectives = vec![
        crate::game::Objective {
            hex: red_flag,
            home: Side::Red,
            captured_by: None,
        },
        crate::game::Objective {
            hex: blue_flag,
            home: Side::Blue,
            captured_by: None,
        },
    ];
    let mut game = Game::new(board, tanks, first, 200, "capture")
        .with_stalemate(40)
        .with_list_initiative(!spoil)
        .with_objectives(objectives);
    game.push_setup_event(format!("Flags at {red_flag} (Red) and {blue_flag} (Blue)"));
    deploy_alternating(&mut game, depth, first.other());
    game.place_deployment_mines(rng);
    if spoil {
        second_player_setup(&mut game, 3);
    }
    // Spoil must not bury flags under buildings.
    game.board.set_terrain(red_flag, Terrain::Open);
    game.board.set_terrain(blue_flag, Terrain::Open);
    game
}

/// Assault: attacker tries to Capture one defender flag; defender wins by wipe
/// or by holding until the clock runs out. Attacker fields **1 tank + 3 loaded
/// APCs**; defender fields **1 tank + 2 infantry** dug in near the flag.
/// List upgrades (tanks ≤10 with mines, APCs ≤4). Attacker always activates
/// first; defender places first and gets spoil.
pub fn assault<R: Rng>(rng: &mut R) -> Game {
    let width = BATTLE_WIDTH;
    let height = BATTLE_HEIGHT;
    let depth = DEPLOY_DEPTH_BATTLE;
    // Coin-flip who attacks so color bias does not hard-code the role.
    let attacker = coin_flip(rng);
    let defender = attacker.other();

    // Defender flag sits on the defender's home edge (backline).
    let def_flag = match defender {
        Side::Red => Hex::offset(0, 6),
        Side::Blue => Hex::offset(width - 1, 6),
    };
    let atk_facing = if attacker == Side::Red {
        Facing::E
    } else {
        Facing::W
    };
    let def_facing = atk_facing.turn_left().turn_left().turn_left(); // opposite

    let zones = deploy_zone_hexes(width, height, depth);
    let egress = [
        Hex::offset(3, 2),
        Hex::offset(3, 5),
        Hex::offset(3, 7),
        Hex::offset(3, 10),
        Hex::offset(14, 2),
        Hex::offset(14, 5),
        Hex::offset(14, 7),
        Hex::offset(14, 10),
        def_flag,
    ];
    let reserved: Vec<Hex> = zones.iter().chain(egress.iter()).copied().collect();
    let goals = [Hex::offset(8, 5), Hex::offset(9, 6), def_flag];
    let layout = MapLayout {
        width,
        height,
        wall: &[],
        alley_clear: &egress,
        path_goals: &goals,
        building_clumps: (4, 7),
        building_clump_size: (2, 5),
        forest: (18, 30),
        forest_clump_size: (3, 6),
        mud: (3, 6),
        rubble: (2, 5),
        // Not mirrored — assault is asymmetric by design.
        mirror_scatter: false,
    };
    let mut board = build_board(&layout, rng, &reserved, &egress);
    board.set_terrain(def_flag, Terrain::Open);
    // Seed light cover near the flag for dug-in infantry.
    for drow in [4i32, 7] {
        let h = match defender {
            Side::Red => Hex::offset(1, drow),
            Side::Blue => Hex::offset(width - 2, drow),
        };
        if board.terrain_at(h) == Terrain::Open {
            board.set_terrain(h, Terrain::Forest);
        }
    }

    let mut atk_t = Tank::stock(
        0,
        attacker,
        zone_seed(attacker, width, height, depth, 0),
        atk_facing,
        "Attack Tank",
    );
    spend_budget(&mut atk_t, 10, true, rng);
    let mut atk_apc_a = Tank::stock_apc(
        1,
        attacker,
        zone_seed(attacker, width, height, depth, 1),
        atk_facing,
        "Attack APC A",
    );
    spend_budget(&mut atk_apc_a, 4, false, rng);
    let mut atk_apc_b = Tank::stock_apc(
        2,
        attacker,
        zone_seed(attacker, width, height, depth, 2),
        atk_facing,
        "Attack APC B",
    );
    spend_budget(&mut atk_apc_b, 4, false, rng);
    let mut atk_apc_c = Tank::stock_apc(
        3,
        attacker,
        zone_seed(attacker, width, height, depth, 3),
        atk_facing,
        "Attack APC C",
    );
    spend_budget(&mut atk_apc_c, 4, false, rng);
    let mut def_t = Tank::stock(
        7,
        defender,
        zone_seed(defender, width, height, depth, 0),
        def_facing,
        "Defend Tank",
    );
    spend_budget(&mut def_t, 10, true, rng);

    let mut tanks = vec![
        atk_t,
        atk_apc_a,
        atk_apc_b,
        atk_apc_c,
        Tank::stock_infantry(
            4,
            attacker,
            zone_seed(attacker, width, height, depth, 1),
            atk_facing,
            "Attack Squad A",
        ),
        Tank::stock_infantry(
            5,
            attacker,
            zone_seed(attacker, width, height, depth, 2),
            atk_facing,
            "Attack Squad B",
        ),
        Tank::stock_infantry(
            6,
            attacker,
            zone_seed(attacker, width, height, depth, 3),
            atk_facing,
            "Attack Squad C",
        ),
        def_t,
        Tank::stock_infantry(
            8,
            defender,
            zone_seed(defender, width, height, depth, 1),
            def_facing,
            "Defend Squad A",
        ),
        Tank::stock_infantry(
            9,
            defender,
            zone_seed(defender, width, height, depth, 2),
            def_facing,
            "Defend Squad B",
        ),
    ];
    for (apc_id, inf_id) in [(1u8, 4u8), (2, 5), (3, 6)] {
        let pos = tanks.iter().find(|t| t.id == apc_id).unwrap().pos;
        if let Some(apc) = tanks.iter_mut().find(|t| t.id == apc_id) {
            apc.passenger = Some(inf_id);
        }
        if let Some(inf) = tanks.iter_mut().find(|t| t.id == inf_id) {
            inf.embarked_in = Some(apc_id);
            inf.pos = pos;
        }
    }

    let objectives = vec![crate::game::Objective {
        hex: def_flag,
        home: defender,
        captured_by: None,
    }];
    // Attacker first; defender places first and spoils.
    let mut game = Game::new(board, tanks, attacker, 180, "assault")
        .with_stalemate(50)
        .with_objectives(objectives)
        .with_attacker(attacker);
    game.push_setup_event(format!(
        "{attacker:?} assaults; {defender:?} holds flag at {def_flag}"
    ));
    deploy_alternating(&mut game, depth, defender);
    game.place_deployment_mines(rng);
    second_player_setup(&mut game, 3);
    game.board.set_terrain(def_flag, Terrain::Open);
    game
}

/// Second-player post-initiative spoil: unit nudges, then scatter-terrain shifts.
fn second_player_setup(game: &mut Game, terrain_budget: u32) {
    second_player_nudge_opposing(game);
    second_player_nudge_terrain(game, terrain_budget);
}

/// Nudge up to **half** of the first-player's unembarked units by at most one
/// hex (empty, passable). Facing unchanged. Sim picks the hex that most spoils
/// the opener, and only the highest-value half of targets are moved.
fn second_player_nudge_opposing(game: &mut Game) {
    let first = game.first_player;
    let second = first.other();
    let plaza = game.board.center();
    let fp_ids: Vec<u8> = game
        .tanks
        .iter()
        .filter(|t| t.side == first && !t.is_embarked())
        .map(|t| t.id)
        .collect();
    let budget = fp_ids.len() / 2;
    if budget == 0 {
        return;
    }

    // Score each unit's best spoil nudge, then apply only the top half.
    let mut ranked: Vec<(u8, Hex, Hex, i32, String)> = Vec::new();
    for id in fp_ids {
        let from = game.tank(id).pos;
        let kind = game.tank(id).kind;
        let name = game.tank(id).name.clone();
        let in_forest = game.board.terrain_at(from) == Terrain::Forest;

        let mut occupied: Vec<Hex> = game.tanks.iter().map(|t| t.pos).collect();
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
            if game.objectives.iter().any(|o| o.hex == cand) {
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
            if cand != from {
                score += 1;
            }
            if score > best_score {
                best_score = score;
                best = cand;
            }
        }
        if best != from {
            ranked.push((id, from, best, best_score, name));
        }
    }
    ranked.sort_by(|a, b| b.3.cmp(&a.3));
    let mut moved = 0usize;
    for (id, from, best, _, name) in ranked {
        if moved >= budget {
            break;
        }
        // Re-check occupation after earlier nudges in this pass.
        let blocked = game
            .tanks
            .iter()
            .any(|t| t.id != id && !t.is_embarked() && t.pos == best);
        if blocked {
            continue;
        }
        game.tank_mut(id).pos = best;
        if let Some(pid) = game.tank(id).passenger {
            game.tank_mut(pid).pos = best;
        }
        game.push_setup_event(format!(
            "Second player nudges {name} {from} → {best} before start"
        ));
        moved += 1;
    }
}

fn is_scatter(t: Terrain) -> bool {
    matches!(t, Terrain::Forest | Terrain::Mud | Terrain::Rubble)
}

/// Shift up to `budget` forest/mud/rubble tiles by 1 hex onto Open (may land
/// under units). Buildings stay put. Destinations on first-player vehicles are
/// frozen so mud cannot circle.
fn second_player_nudge_terrain(game: &mut Game, budget: u32) {
    use std::collections::HashSet;
    let first = game.first_player;
    let second = first.other();
    let plaza = game.board.center();
    let mut frozen: HashSet<(i32, i32)> = HashSet::new();

    for _ in 0..budget {
        let scatter: Vec<Hex> = {
            let mut out = Vec::new();
            for h in game.board.hexes() {
                if frozen.contains(&(h.q, h.r)) {
                    continue;
                }
                if is_scatter(game.board.terrain_at(h)) {
                    out.push(h);
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
            score += (best_before - best_after) * 12;
        }
    }

    score
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

    let mut candidates = open_candidates(layout, &board, starts, egress);
    candidates.shuffle(rng);

    let n_building_clumps =
        rng.gen_range(layout.building_clumps.0..=layout.building_clumps.1) as usize;
    let n_forest = rng.gen_range(layout.forest.0..=layout.forest.1) as usize;
    let n_mud = rng.gen_range(layout.mud.0..=layout.mud.1) as usize;
    let n_rubble = rng.gen_range(layout.rubble.0..=layout.rubble.1) as usize;
    let (n_building_clumps, n_forest, n_mud, n_rubble) = if layout.mirror_scatter {
        (
            n_building_clumps.div_ceil(2),
            n_forest.div_ceil(2),
            n_mud.div_ceil(2),
            n_rubble.div_ceil(2),
        )
    } else {
        (n_building_clumps, n_forest, n_mud, n_rubble)
    };

    place_clumps(
        &mut board,
        rng,
        &mut candidates,
        Terrain::Building,
        n_building_clumps,
        layout.building_clump_size,
        layout,
        starts,
        egress,
    );
    place_forest_clumps(
        &mut board,
        rng,
        &mut candidates,
        n_forest,
        layout.forest_clump_size,
        layout,
        starts,
        egress,
    );

    // Mud / rubble stay as single tiles.
    candidates.shuffle(rng);
    let singles = n_mud + n_rubble;
    for (i, h) in candidates.into_iter().take(singles).enumerate() {
        if board.terrain_at(h) != Terrain::Open {
            continue;
        }
        let terrain = if i < n_mud {
            Terrain::Mud
        } else {
            Terrain::Rubble
        };
        set_scatter(&mut board, h, terrain, layout, starts, egress);
    }
    board
}

fn open_candidates(
    layout: &MapLayout<'_>,
    board: &Board,
    starts: &[Hex],
    egress: &[Hex],
) -> Vec<Hex> {
    let mid_col = (layout.width - 1) / 2;
    let mut candidates = Vec::new();
    for h in board.hexes() {
        let (col, _row) = h.to_offset();
        if layout.mirror_scatter && col >= mid_col {
            continue;
        }
        if layout.wall.contains(&h) || layout.alley_clear.contains(&h) || starts.contains(&h) {
            continue;
        }
        if egress.contains(&h) {
            continue;
        }
        if board.terrain_at(h) != Terrain::Open {
            continue;
        }
        candidates.push(h);
    }
    candidates
}

fn set_scatter(
    board: &mut Board,
    h: Hex,
    terrain: Terrain,
    layout: &MapLayout<'_>,
    starts: &[Hex],
    egress: &[Hex],
) {
    board.set_terrain(h, terrain);
    if !layout.mirror_scatter {
        return;
    }
    let m = mirror_ew(h, layout.width);
    if board.contains(m)
        && board.terrain_at(m) == Terrain::Open
        && !layout.wall.contains(&m)
        && !layout.alley_clear.contains(&m)
        && !starts.contains(&m)
        && !egress.contains(&m)
    {
        board.set_terrain(m, terrain);
    }
}

/// Grow `n_clumps` connected patches of `terrain`.
#[allow(clippy::too_many_arguments)]
fn place_clumps<R: Rng>(
    board: &mut Board,
    rng: &mut R,
    candidates: &mut Vec<Hex>,
    terrain: Terrain,
    n_clumps: usize,
    size_range: (u32, u32),
    layout: &MapLayout<'_>,
    starts: &[Hex],
    egress: &[Hex],
) {
    if n_clumps == 0 || size_range.1 == 0 {
        return;
    }
    candidates.shuffle(rng);
    let mut placed = 0;
    let mut seed_i = 0;
    while placed < n_clumps && seed_i < candidates.len() {
        let seed = candidates[seed_i];
        seed_i += 1;
        if board.terrain_at(seed) != Terrain::Open {
            continue;
        }
        let target = rng.gen_range(size_range.0..=size_range.1) as usize;
        let mut clump = vec![seed];
        while clump.len() < target {
            let mut nbrs = Vec::new();
            for h in &clump {
                for n in h.neighbors() {
                    if !board.contains(n) || board.terrain_at(n) != Terrain::Open {
                        continue;
                    }
                    if starts.contains(&n)
                        || egress.contains(&n)
                        || layout.alley_clear.contains(&n)
                        || layout.wall.contains(&n)
                    {
                        continue;
                    }
                    if layout.mirror_scatter {
                        let (col, _) = n.to_offset();
                        if col >= (layout.width - 1) / 2 {
                            continue;
                        }
                    }
                    if !clump.contains(&n) {
                        nbrs.push(n);
                    }
                }
            }
            if nbrs.is_empty() {
                break;
            }
            nbrs.shuffle(rng);
            clump.push(nbrs[0]);
        }
        for h in &clump {
            set_scatter(board, *h, terrain, layout, starts, egress);
        }
        placed += 1;
    }
    candidates.retain(|h| board.terrain_at(*h) == Terrain::Open);
}

/// Place about `budget` forest hexes as clumps of `size_range`.
#[allow(clippy::too_many_arguments)]
fn place_forest_clumps<R: Rng>(
    board: &mut Board,
    rng: &mut R,
    candidates: &mut Vec<Hex>,
    budget: usize,
    size_range: (u32, u32),
    layout: &MapLayout<'_>,
    starts: &[Hex],
    egress: &[Hex],
) {
    if budget == 0 {
        return;
    }
    let avg = ((size_range.0 + size_range.1) / 2).max(1) as usize;
    let n_clumps = budget.div_ceil(avg).max(1);
    // Grow clumps until we hit the hex budget.
    candidates.shuffle(rng);
    let mut remaining = budget;
    let mut seed_i = 0;
    let mut clumps_left = n_clumps;
    while remaining > 0 && clumps_left > 0 && seed_i < candidates.len() {
        let seed = candidates[seed_i];
        seed_i += 1;
        if board.terrain_at(seed) != Terrain::Open {
            continue;
        }
        let want = rng.gen_range(size_range.0..=size_range.1) as usize;
        let target = want.min(remaining);
        let mut clump = vec![seed];
        while clump.len() < target {
            let mut nbrs = Vec::new();
            for h in &clump {
                for n in h.neighbors() {
                    if !board.contains(n) || board.terrain_at(n) != Terrain::Open {
                        continue;
                    }
                    if starts.contains(&n)
                        || egress.contains(&n)
                        || layout.alley_clear.contains(&n)
                        || layout.wall.contains(&n)
                    {
                        continue;
                    }
                    if layout.mirror_scatter {
                        let (col, _) = n.to_offset();
                        if col >= (layout.width - 1) / 2 {
                            continue;
                        }
                    }
                    if !clump.contains(&n) {
                        nbrs.push(n);
                    }
                }
            }
            if nbrs.is_empty() {
                break;
            }
            nbrs.shuffle(rng);
            clump.push(nbrs[0]);
        }
        for h in &clump {
            set_scatter(board, *h, Terrain::Forest, layout, starts, egress);
        }
        remaining = remaining.saturating_sub(clump.len());
        clumps_left -= 1;
    }
    candidates.retain(|h| board.terrain_at(*h) == Terrain::Open);
}

fn alleys_pathable(board: &Board, starts: &[Hex], goals: &[Hex]) -> bool {
    let mid = board.width / 2;
    let red: Vec<Hex> = starts
        .iter()
        .copied()
        .filter(|h| h.to_offset().0 < mid)
        .collect();
    let blue: Vec<Hex> = starts
        .iter()
        .copied()
        .filter(|h| h.to_offset().0 > mid)
        .collect();
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
        let red_start = Hex::offset(1, 4);
        let blue_start = Hex::offset(7, 7);
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let g = skirmish(&mut rng);
        // Stock corridor (pre-deploy seeds) have no LOS through the wall.
        assert!(
            !g.board.has_los(red_start, blue_start, &[]),
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
        // Deployment + spoil may move tanks; both must still be on-board and
        // unstacked.
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
        for q in 0..SKIRMISH_WIDTH {
            for r in 0..SKIRMISH_HEIGHT {
                let h = Hex::offset(q, r);
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
    fn combined_places_mines_at_deployment() {
        let mut rng = ChaCha8Rng::seed_from_u64(8);
        let g = combined(&mut rng);
        // All charges spent onto the board; none left for mid-battle DeployMine.
        for t in &g.tanks {
            assert_eq!(t.mines_left, 0, "{} still holds mines", t.name);
        }
        assert_eq!(g.mines_deployed as usize, g.board.mines.len());
        // Combined lists often buy mines — expect at least some across seeds.
        let mut any = false;
        for seed in 0..25u64 {
            let mut r = ChaCha8Rng::seed_from_u64(seed);
            let g = combined(&mut r);
            if g.mines_deployed > 0 {
                any = true;
                break;
            }
        }
        assert!(any, "expected some Combined seed to deploy mines");
    }

    #[test]
    fn deployment_mines_respect_enemy_clearance() {
        use crate::game::Game;
        let c = Game::DEPLOYMENT_MINE_CLEARANCE;
        for seed in 0..40u64 {
            let mut r = ChaCha8Rng::seed_from_u64(seed);
            let g = combined(&mut r);
            for &(q, rhex) in &g.board.mines {
                let h = Hex::new(q, rhex);
                let mut min_red = i32::MAX;
                let mut min_blue = i32::MAX;
                for t in &g.tanks {
                    if !matches!(t.kind, UnitKind::Tank | UnitKind::Apc) {
                        continue;
                    }
                    let d = h.distance(t.pos);
                    match t.side {
                        Side::Red => min_red = min_red.min(d),
                        Side::Blue => min_blue = min_blue.min(d),
                    }
                }
                // A legal mine is clear of every vehicle on at least one side
                // (its enemy). Own-side vehicles may sit closer.
                let clear_of_red = min_red >= c;
                let clear_of_blue = min_blue >= c;
                assert!(
                    clear_of_red || clear_of_blue,
                    "seed {seed} mine {h} within enemy clearance (red≥{min_red}, blue≥{min_blue}, need {c})"
                );
            }
        }
    }

    #[test]
    fn skirmish_is_stock_no_upgrades() {
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let g = skirmish(&mut rng);
        assert_eq!(g.scenario, "skirmish");
        assert!(!g.list_initiative);
        for t in &g.tanks {
            assert_eq!(t.upgrade_points_spent, 0);
            assert!(!t.has_smoke_launcher);
            assert!(!t.has_medkit);
            assert!(!t.has_engine);
            assert!(!t.has_optics);
            assert!(!t.has_barrel);
            assert_eq!(t.mines_left, 0);
            assert!(!t
                .crew
                .iter()
                .any(|m| m.role == crate::unit::CrewRole::Lieutenant));
        }
    }

    #[test]
    fn platoon_has_six_tanks_on_big_board() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let g = platoon(&mut rng);
        assert_eq!(g.tanks.len(), 6);
        assert_eq!(g.scenario, "platoon");
        assert_eq!(g.board.width, 18);
        assert_eq!(g.board.height, 12);
        assert_eq!(g.max_activations, 200);
        assert_eq!(g.stalemate_after, 40);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Red).count(), 3);
        assert_eq!(g.tanks.iter().filter(|t| t.side == Side::Blue).count(), 3);
        assert!(g.tanks.iter().all(|t| t.kind == UnitKind::Tank));
        // Open board: scattered buildings and forests, no sealed midline.
        let buildings = g
            .board
            .hexes()
            .filter(|h| g.board.terrain_at(*h) == Terrain::Building)
            .count();
        let forests = g
            .board
            .hexes()
            .filter(|h| g.board.terrain_at(*h) == Terrain::Forest)
            .count();
        assert!(buildings >= 8, "expected building clumps, got {buildings}");
        assert!(forests >= 12, "expected forest clumps, got {forests}");
        assert_ne!(
            g.board.terrain_at(Hex::offset(8, 0)),
            Terrain::Building,
            "no sealed spine at north midline"
        );
        assert_ne!(
            g.board.terrain_at(Hex::offset(8, 11)),
            Terrain::Building,
            "no sealed spine at south midline"
        );
        // Lists spend something on average (seeded random).
        assert!(g.tanks.iter().any(|t| t.upgrade_points_spent > 0));
    }

    #[test]
    fn squadron_is_stock_3v3_no_upgrades() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let g = squadron(&mut rng);
        assert_eq!(g.scenario, "squadron");
        assert_eq!(g.tanks.len(), 6);
        assert_eq!(g.board.width, BATTLE_WIDTH);
        assert_eq!(g.board.height, BATTLE_HEIGHT);
        assert_eq!(g.max_activations, 200);
        assert_eq!(g.stalemate_after, 40);
        assert!(!g.list_initiative);
        assert!(g.tanks.iter().all(|t| t.kind == UnitKind::Tank));
        assert!(g.tanks.iter().all(|t| t.upgrade_points_spent == 0));
        assert!(g
            .tanks
            .iter()
            .all(|t| !t.has_smoke_launcher && !t.has_medkit));
    }

    #[test]
    fn combined_has_mixed_force_on_mid_board() {
        let mut rng = ChaCha8Rng::seed_from_u64(4);
        let g = combined(&mut rng);
        assert_eq!(g.scenario, "combined");
        assert_eq!(g.board.width, BATTLE_WIDTH);
        assert_eq!(g.board.height, BATTLE_HEIGHT);
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
        // Open mirrored board — buildings exist and stay east–west mirrored.
        let width = BATTLE_WIDTH;
        assert_eq!(mirror_ew(Hex::offset(1, 3), width), Hex::offset(16, 3));
        let buildings = g
            .board
            .hexes()
            .filter(|h| g.board.terrain_at(*h) == Terrain::Building)
            .count();
        assert!(buildings >= 6, "expected building clumps, got {buildings}");
        for h in g.board.hexes() {
            if g.board.terrain_at(h) == Terrain::Building {
                assert_eq!(
                    g.board.terrain_at(mirror_ew(h, width)),
                    Terrain::Building,
                    "building at {h} lost its mirror"
                );
            }
        }
    }

    #[test]
    fn combined_starts_mirrored_before_nudge() {
        let width = BATTLE_WIDTH;
        let red_tanks = [Hex::offset(1, 3), Hex::offset(1, 5)];
        let red_apcs = [Hex::offset(1, 7), Hex::offset(1, 9)];
        let red_inf = [Hex::offset(0, 4), Hex::offset(0, 8)];
        for h in red_tanks
            .iter()
            .chain(red_apcs.iter())
            .chain(red_inf.iter())
        {
            let m = mirror_ew(*h, width);
            assert_ne!(*h, m);
            let (hc, hr) = h.to_offset();
            let (mc, mr) = m.to_offset();
            assert_eq!(mr, hr);
            assert_eq!(mc + hc, width - 1);
        }
        // Spot-check kind pairing via a live setup's pre-nudge positions:
        // rebuild without nudge.
        let height = BATTLE_HEIGHT;
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
            Hex::offset(2, 3),
            Hex::offset(2, 5),
            Hex::offset(2, 7),
            Hex::offset(2, 9),
            mirror_ew(Hex::offset(2, 3), width),
            mirror_ew(Hex::offset(2, 5), width),
            mirror_ew(Hex::offset(2, 7), width),
            mirror_ew(Hex::offset(2, 9), width),
        ];
        let goals = [Hex::offset(8, 5), Hex::offset(9, 6)];
        let layout = MapLayout {
            width,
            height,
            wall: &[],
            alley_clear: &egress,
            path_goals: &goals,
            building_clumps: (4, 7),
            building_clump_size: (2, 5),
            forest: (18, 30),
            forest_clump_size: (3, 6),
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
        let mut g = combined(&mut rng);
        // Under-spend often skips spoil; exercise the nudge path directly.
        g.events.clear();
        super::second_player_setup(&mut g, 4);
        let first = g.first_player;
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
        // Half of first-player unembarked units at most.
        let fp_unembarked = g
            .tanks
            .iter()
            .filter(|t| t.side == first && !t.is_embarked())
            .count();
        assert!(
            nudges.len() <= fp_unembarked / 2,
            "spoil should move at most half of FP units ({} nudges, {} FP)",
            nudges.len(),
            fp_unembarked
        );
        let mut seen = std::collections::HashSet::new();
        for t in &g.tanks {
            if t.is_embarked() {
                continue;
            }
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
        for seed in 0..40u64 {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            let mut game = combined(&mut rng);
            // Force spoil terrain even when under-spend skipped it.
            game.events.clear();
            super::second_player_nudge_terrain(&mut game, 4);
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
        let width = g.board.width;
        for h in g.board.hexes() {
            if g.board.terrain_at(h) == Terrain::Building {
                assert_eq!(
                    g.board.terrain_at(mirror_ew(h, width)),
                    Terrain::Building,
                    "building at {h} lost its mirror"
                );
            }
        }
    }

    #[test]
    fn combined_scatter_generated_east_west_mirrored() {
        // Scatter is mirrored at generation; second-player terrain spoil may
        // break that afterward — so check the board *before* setup.
        let width = BATTLE_WIDTH;
        let height = BATTLE_HEIGHT;
        let mut rng = ChaCha8Rng::seed_from_u64(9);
        let red_tanks = [Hex::offset(1, 3), Hex::offset(1, 5)];
        let red_apcs = [Hex::offset(1, 7), Hex::offset(1, 9)];
        let red_inf = [Hex::offset(0, 4), Hex::offset(0, 8)];
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
            Hex::offset(2, 3),
            Hex::offset(2, 5),
            Hex::offset(2, 7),
            Hex::offset(2, 9),
            mirror_ew(Hex::offset(2, 3), width),
            mirror_ew(Hex::offset(2, 5), width),
            mirror_ew(Hex::offset(2, 7), width),
            mirror_ew(Hex::offset(2, 9), width),
        ];
        let goals = [Hex::offset(8, 5), Hex::offset(9, 6)];
        let layout = MapLayout {
            width,
            height,
            wall: &[],
            alley_clear: &egress,
            path_goals: &goals,
            building_clumps: (4, 7),
            building_clump_size: (2, 5),
            forest: (18, 30),
            forest_clump_size: (3, 6),
            mud: (3, 6),
            rubble: (2, 5),
            mirror_scatter: true,
        };
        let board = build_board(&layout, &mut rng, &reserved, &egress);
        let mid = (width - 1) / 2;
        for q in 0..=mid {
            for r in 0..height {
                let h = Hex::offset(q, r);
                let m = mirror_ew(h, width);
                let th = board.terrain_at(h);
                let tm = board.terrain_at(m);
                if matches!(
                    th,
                    Terrain::Forest | Terrain::Mud | Terrain::Rubble | Terrain::Building
                ) || matches!(
                    tm,
                    Terrain::Forest | Terrain::Mud | Terrain::Rubble | Terrain::Building
                ) {
                    assert_eq!(th, tm, "scatter mismatch at {h} ({th:?}) vs {m} ({tm:?})");
                }
            }
        }
    }

    #[test]
    fn board_sizes_scale_with_scenario() {
        let mut rng = ChaCha8Rng::seed_from_u64(5);
        let s = skirmish(&mut rng);
        let q = squadron(&mut rng);
        let c = combined(&mut rng);
        let p = platoon(&mut rng);
        let cap = capture(&mut rng);
        let area = |g: &Game| g.board.width * g.board.height;
        assert_eq!(s.board.width, SKIRMISH_WIDTH);
        assert_eq!(s.board.height, SKIRMISH_HEIGHT);
        assert_eq!(q.board.width, BATTLE_WIDTH);
        assert_eq!(q.board.height, BATTLE_HEIGHT);
        assert_eq!(c.board.width, BATTLE_WIDTH);
        assert_eq!(c.board.height, BATTLE_HEIGHT);
        assert_eq!(p.board.width, BATTLE_WIDTH);
        assert_eq!(p.board.height, BATTLE_HEIGHT);
        assert_eq!(cap.board.width, BATTLE_WIDTH);
        assert_eq!(cap.board.height, BATTLE_HEIGHT);
        assert_eq!(area(&c), area(&p), "platoon and combined share one mat");
        assert_eq!(area(&q), area(&p), "squadron shares the battle mat");
        assert_eq!(area(&cap), area(&p), "capture shares the battle mat");
        assert_eq!(
            s.board.height, p.board.height,
            "skirmish keeps battle height"
        );
        assert_eq!(
            s.board.width * 2,
            p.board.width,
            "skirmish is half battle width"
        );
    }

    #[test]
    fn capture_scenario_loads_apcs_and_places_flags() {
        let mut rng = ChaCha8Rng::seed_from_u64(9);
        let g = capture(&mut rng);
        assert_eq!(g.scenario, "capture");
        assert_eq!(g.tanks.len(), 14);
        assert_eq!(g.objectives.len(), 2);
        assert_eq!(g.max_activations, 200);
        assert_eq!(g.stalemate_after, 40);
        for side in [Side::Red, Side::Blue] {
            assert_eq!(
                g.tanks
                    .iter()
                    .filter(|t| t.side == side && t.kind == UnitKind::Tank)
                    .count(),
                1
            );
            assert_eq!(
                g.tanks
                    .iter()
                    .filter(|t| t.side == side && t.kind == UnitKind::Apc)
                    .count(),
                3
            );
            assert_eq!(
                g.tanks
                    .iter()
                    .filter(|t| t.side == side && t.kind == UnitKind::Infantry)
                    .count(),
                3
            );
            assert!(g.enemy_flag(side).is_some());
            assert!(g.own_flag(side).is_some());
        }
        // All infantry start embarked in APCs.
        for t in &g.tanks {
            if t.kind == UnitKind::Infantry {
                assert!(t.is_embarked(), "{} should start embarked", t.name);
            }
            if t.kind == UnitKind::Apc {
                assert!(t.passenger.is_some(), "{} should start loaded", t.name);
            }
        }
        // Units live in their edge deploy zones.
        let depth = DEPLOY_DEPTH_BATTLE;
        for t in &g.tanks {
            if t.is_embarked() {
                continue;
            }
            let (col, _) = t.pos.to_offset();
            match t.side {
                Side::Red => assert!(col < depth, "{} col {col} outside red zone", t.name),
                Side::Blue => assert!(
                    col >= BATTLE_WIDTH - depth,
                    "{} col {col} outside blue zone",
                    t.name
                ),
            }
        }
        // Race distances should match when both AIs place optimally.
        let red_flag = g.own_flag(Side::Red).unwrap();
        let blue_flag = g.own_flag(Side::Blue).unwrap();
        let red_min = g
            .tanks
            .iter()
            .filter(|t| t.side == Side::Red && t.kind == UnitKind::Apc)
            .map(|t| t.pos.distance(blue_flag))
            .min()
            .unwrap();
        let blue_min = g
            .tanks
            .iter()
            .filter(|t| t.side == Side::Blue && t.kind == UnitKind::Apc)
            .map(|t| t.pos.distance(red_flag))
            .min()
            .unwrap();
        assert!(
            (red_min - blue_min).abs() <= 1,
            "capture race distance skew red_min={red_min} blue_min={blue_min}"
        );
        assert!(
            g.tanks
                .iter()
                .any(|t| t.kind != UnitKind::Infantry && t.upgrade_points_spent > 0),
            "expected Capture lists to spend upgrades"
        );
        for obj in &g.objectives {
            assert_eq!(g.board.terrain_at(obj.hex), Terrain::Open);
            assert!(obj.captured_by.is_none());
        }
    }

    #[test]
    fn alternating_deploy_keeps_units_in_edge_zones() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        for kind in [
            ScenarioKind::Squadron,
            ScenarioKind::Platoon,
            ScenarioKind::Combined,
        ] {
            let g = setup(kind, &mut rng);
            let depth = DEPLOY_DEPTH_BATTLE;
            for t in &g.tanks {
                if t.is_embarked() {
                    continue;
                }
                let (col, _) = t.pos.to_offset();
                match t.side {
                    Side::Red => assert!(
                        col < depth,
                        "{:?} {} col {col} outside red zone",
                        kind,
                        t.name
                    ),
                    Side::Blue => assert!(
                        col >= BATTLE_WIDTH - depth,
                        "{:?} {} col {col} outside blue zone",
                        kind,
                        t.name
                    ),
                }
            }
        }
    }

    #[test]
    fn assault_scenario_is_asymmetric_attacker_defender() {
        let mut rng = ChaCha8Rng::seed_from_u64(11);
        let g = assault(&mut rng);
        assert_eq!(g.scenario, "assault");
        assert!(g.attacker.is_some());
        let attacker = g.attacker.unwrap();
        let defender = attacker.other();
        assert_eq!(g.first_player, attacker);
        assert_eq!(g.objectives.len(), 1);
        assert_eq!(g.objectives[0].home, defender);
        assert_eq!(g.enemy_flag(attacker), Some(g.objectives[0].hex));
        assert!(g.enemy_flag(defender).is_none());
        assert_eq!(
            g.tanks
                .iter()
                .filter(|t| t.side == attacker && t.kind == UnitKind::Tank)
                .count(),
            1
        );
        assert_eq!(
            g.tanks
                .iter()
                .filter(|t| t.side == attacker && t.kind == UnitKind::Apc)
                .count(),
            3
        );
        assert_eq!(
            g.tanks
                .iter()
                .filter(|t| t.side == defender && t.kind == UnitKind::Tank)
                .count(),
            1
        );
        assert_eq!(
            g.tanks
                .iter()
                .filter(|t| t.side == defender && t.kind == UnitKind::Infantry)
                .count(),
            2
        );
        for t in &g.tanks {
            if t.side == attacker && t.kind == UnitKind::Infantry {
                assert!(t.is_embarked());
            }
            if t.side == defender && t.kind == UnitKind::Infantry {
                assert!(!t.is_embarked());
                assert!(t.in_cover);
            }
        }
        assert!(
            g.tanks
                .iter()
                .any(|t| t.kind != UnitKind::Infantry && t.upgrade_points_spent > 0),
            "expected Assault lists to spend upgrades"
        );
    }
}
