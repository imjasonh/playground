use crate::engine::map::{
    edge_key, Card, City, CitySize, Commodity, DemandEntry, EdgeDef, EdgeKind, EventEffect,
    MapData, MapGeography, Milepost, MilepostId, Polyline, Terrain,
};
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use serde::Deserialize;
use std::collections::{HashMap, HashSet, VecDeque};

const ROW_STEP: f32 = 0.866_025_4; // sqrt(3) / 2
const NA_GEO_JSON: &str = include_str!("../../maps/na_geo.json");

#[derive(Deserialize)]
struct NaGeo {
    width: f32,
    height: f32,
    land_polygons: Vec<Vec<[f32; 2]>>,
    lake_polygons: Vec<Vec<[f32; 2]>>,
    rivers: Vec<Polyline>,
    borders: Vec<Polyline>,
    city_points: HashMap<String, [f32; 2]>,
}

/// Build the North America (US + Southern Canada) map and deck using Natural Earth 50m
/// Albers Equal-Area Conic coastlines, lakes, rivers, borders, and real city coordinates.
pub fn build_north_america_map() -> MapData {
    let geo: NaGeo = serde_json::from_str(NA_GEO_JSON).expect("valid embedded na_geo.json");

    let is_land = |pt: [f32; 2]| -> bool {
        let on_land = geo
            .land_polygons
            .iter()
            .any(|poly| point_in_polygon(pt, poly));
        if !on_land {
            return false;
        }
        let in_lake = geo
            .lake_polygons
            .iter()
            .any(|poly| point_in_polygon(pt, poly));
        !in_lake
    };

    // 1. Place mileposts on the equilateral hex lattice across the Natural Earth landmass.
    let mut raw_mps: Vec<Milepost> = Vec::new();
    let max_col = geo.width.ceil() as u16;
    let max_row = (geo.height / ROW_STEP).ceil() as u16;

    for row in 2..max_row {
        for col in 1..max_col {
            let x = col as f32 + if row % 2 == 1 { 0.5 } else { 0.0 };
            let y = row as f32 * ROW_STEP;
            if y < 1.8 || y > geo.height - 0.6 {
                continue;
            }
            if !is_land([x, y]) {
                continue;
            }
            let id = raw_mps.len() as MilepostId;
            raw_mps.push(Milepost {
                id,
                col,
                row,
                x,
                y,
                terrain: default_terrain(x, y),
                city_id: None,
            });
        }
    }

    // 2. Build hex adjacency and keep only the main continental connected component
    //    (drops isolated offshore slivers like PEI/small islands so every milepost is reachable).
    let raw_adj = build_hex_neighbors(&raw_mps, &is_land);
    let main_comp = largest_component(&raw_adj);
    let mut old_to_new: HashMap<MilepostId, MilepostId> = HashMap::with_capacity(main_comp.len());
    let mut mileposts: Vec<Milepost> = Vec::with_capacity(main_comp.len());
    for (old_id, mp) in raw_mps.into_iter().enumerate() {
        if main_comp.contains(&(old_id as MilepostId)) {
            let new_id = mileposts.len() as MilepostId;
            old_to_new.insert(old_id as MilepostId, new_id);
            mileposts.push(Milepost { id: new_id, ..mp });
        }
    }
    let raw_neighbors = build_hex_neighbors(&mileposts, &is_land);

    let find_nearest =
        |mileposts: &[Milepost], tx: f32, ty: f32, used: &HashSet<MilepostId>| -> MilepostId {
            mileposts
                .iter()
                .filter(|m| !used.contains(&m.id))
                .min_by(|a, b| {
                    let da = (a.x - tx).powi(2) + (a.y - ty).powi(2);
                    let db = (b.x - tx).powi(2) + (b.y - ty).powi(2);
                    da.total_cmp(&db)
                })
                .expect("map must have available mileposts")
                .id
        };

    // 3. Place classic Empire Builder US + Southern Canada cities at their projected lat/lon!
    struct CitySpec {
        id: &'static str,
        name: &'static str,
        size: CitySize,
        commodities: &'static [&'static str],
    }

    let specs: &[CitySpec] = &[
        // 6 Major Cities (5 connected + $250M to win)
        CitySpec {
            id: "new_york",
            name: "New York",
            size: CitySize::Major,
            commodities: &["imports", "machinery", "books"],
        },
        CitySpec {
            id: "chicago",
            name: "Chicago",
            size: CitySize::Major,
            commodities: &["machinery", "steel", "wheat"],
        },
        CitySpec {
            id: "toronto",
            name: "Toronto",
            size: CitySize::Major,
            commodities: &["beer", "wheat", "cars"],
        },
        CitySpec {
            id: "new_orleans",
            name: "New Orleans",
            size: CitySize::Major,
            commodities: &["imports", "sugar", "oil"],
        },
        CitySpec {
            id: "los_angeles",
            name: "Los Angeles",
            size: CitySize::Major,
            commodities: &["cars", "oranges", "imports"],
        },
        CitySpec {
            id: "san_francisco",
            name: "San Francisco",
            size: CitySize::Major,
            commodities: &["wine", "imports", "fish"],
        },
        // Northeast & Eastern Canada
        CitySpec {
            id: "boston",
            name: "Boston",
            size: CitySize::Medium,
            commodities: &["fish", "books", "imports"],
        },
        CitySpec {
            id: "montreal",
            name: "Montreal",
            size: CitySize::Medium,
            commodities: &["paper", "beer", "aluminum"],
        },
        CitySpec {
            id: "quebec",
            name: "Quebec",
            size: CitySize::Small,
            commodities: &["timber", "paper", "iron"],
        },
        CitySpec {
            id: "philadelphia",
            name: "Philadelphia",
            size: CitySize::Medium,
            commodities: &["chemicals", "books", "imports"],
        },
        CitySpec {
            id: "washington",
            name: "Washington",
            size: CitySize::Medium,
            commodities: &["books", "tobacco"],
        },
        CitySpec {
            id: "pittsburgh",
            name: "Pittsburgh",
            size: CitySize::Medium,
            commodities: &["coal", "steel", "chemicals"],
        },
        CitySpec {
            id: "buffalo",
            name: "Buffalo",
            size: CitySize::Small,
            commodities: &["wheat", "steel"],
        },
        CitySpec {
            id: "detroit",
            name: "Detroit",
            size: CitySize::Medium,
            commodities: &["cars", "steel", "machinery"],
        },
        CitySpec {
            id: "cleveland",
            name: "Cleveland",
            size: CitySize::Small,
            commodities: &["steel", "chemicals"],
        },
        CitySpec {
            id: "cincinnati",
            name: "Cincinnati",
            size: CitySize::Medium,
            commodities: &["machinery", "hogs", "coal"],
        },
        // Southeast
        CitySpec {
            id: "norfolk",
            name: "Norfolk",
            size: CitySize::Small,
            commodities: &["imports", "tobacco", "fish"],
        },
        CitySpec {
            id: "raleigh",
            name: "Raleigh",
            size: CitySize::Small,
            commodities: &["tobacco", "textiles"],
        },
        CitySpec {
            id: "charlotte",
            name: "Charlotte",
            size: CitySize::Small,
            commodities: &["textiles", "tobacco"],
        },
        CitySpec {
            id: "atlanta",
            name: "Atlanta",
            size: CitySize::Medium,
            commodities: &["textiles", "cotton", "paper"],
        },
        CitySpec {
            id: "birmingham",
            name: "Birmingham",
            size: CitySize::Small,
            commodities: &["coal", "iron", "steel"],
        },
        CitySpec {
            id: "jacksonville",
            name: "Jacksonville",
            size: CitySize::Small,
            commodities: &["oranges", "paper", "fish"],
        },
        CitySpec {
            id: "tampa",
            name: "Tampa",
            size: CitySize::Small,
            commodities: &["oranges", "fish"],
        },
        CitySpec {
            id: "miami",
            name: "Miami",
            size: CitySize::Medium,
            commodities: &["oranges", "sugar", "imports"],
        },
        // Midwest, Plains & Central Canada
        CitySpec {
            id: "minneapolis",
            name: "Minneapolis",
            size: CitySize::Medium,
            commodities: &["wheat", "iron", "beer"],
        },
        CitySpec {
            id: "duluth",
            name: "Duluth",
            size: CitySize::Small,
            commodities: &["iron", "wheat", "timber"],
        },
        CitySpec {
            id: "winnipeg",
            name: "Winnipeg",
            size: CitySize::Medium,
            commodities: &["wheat", "timber", "copper"],
        },
        CitySpec {
            id: "st_louis",
            name: "St. Louis",
            size: CitySize::Medium,
            commodities: &["beer", "corn", "hogs"],
        },
        CitySpec {
            id: "memphis",
            name: "Memphis",
            size: CitySize::Small,
            commodities: &["cotton", "timber", "hogs"],
        },
        CitySpec {
            id: "kansas_city",
            name: "Kansas City",
            size: CitySize::Medium,
            commodities: &["wheat", "cattle", "corn"],
        },
        CitySpec {
            id: "omaha",
            name: "Omaha",
            size: CitySize::Small,
            commodities: &["corn", "cattle", "hogs"],
        },
        CitySpec {
            id: "oklahoma_city",
            name: "Oklahoma City",
            size: CitySize::Small,
            commodities: &["oil", "cattle", "wheat"],
        },
        CitySpec {
            id: "dallas",
            name: "Dallas",
            size: CitySize::Medium,
            commodities: &["oil", "cotton", "cattle"],
        },
        CitySpec {
            id: "houston",
            name: "Houston",
            size: CitySize::Medium,
            commodities: &["oil", "chemicals", "sugar"],
        },
        CitySpec {
            id: "san_antonio",
            name: "San Antonio",
            size: CitySize::Small,
            commodities: &["cattle", "cotton"],
        },
        // West, Mountains & Western Canada
        CitySpec {
            id: "calgary",
            name: "Calgary",
            size: CitySize::Medium,
            commodities: &["oil", "cattle", "coal"],
        },
        CitySpec {
            id: "vancouver",
            name: "Vancouver",
            size: CitySize::Medium,
            commodities: &["timber", "fish", "aluminum"],
        },
        CitySpec {
            id: "seattle",
            name: "Seattle",
            size: CitySize::Medium,
            commodities: &["timber", "fish", "aluminum"],
        },
        CitySpec {
            id: "portland",
            name: "Portland",
            size: CitySize::Small,
            commodities: &["timber", "wine", "wheat"],
        },
        CitySpec {
            id: "boise",
            name: "Boise",
            size: CitySize::Small,
            commodities: &["silver", "cattle"],
        },
        CitySpec {
            id: "salt_lake",
            name: "Salt Lake City",
            size: CitySize::Medium,
            commodities: &["copper", "silver", "chemicals"],
        },
        CitySpec {
            id: "denver",
            name: "Denver",
            size: CitySize::Medium,
            commodities: &["coal", "silver", "cattle"],
        },
        CitySpec {
            id: "las_vegas",
            name: "Las Vegas",
            size: CitySize::Small,
            commodities: &["silver", "copper"],
        },
        CitySpec {
            id: "phoenix",
            name: "Phoenix",
            size: CitySize::Medium,
            commodities: &["copper", "cotton", "oranges"],
        },
        CitySpec {
            id: "albuquerque",
            name: "Albuquerque",
            size: CitySize::Small,
            commodities: &["copper", "oil"],
        },
        CitySpec {
            id: "el_paso",
            name: "El Paso",
            size: CitySize::Small,
            commodities: &["copper", "cattle"],
        },
    ];

    let mut used_mps: HashSet<MilepostId> = HashSet::new();
    let mut cities: Vec<City> = Vec::with_capacity(specs.len());

    for spec in specs {
        let [tx, ty] = geo
            .city_points
            .get(spec.id)
            .copied()
            .unwrap_or_else(|| panic!("missing city_points for {}", spec.id));
        let center = find_nearest(&mileposts, tx, ty, &used_mps);
        let mut city_mps = vec![center];
        used_mps.insert(center);

        if spec.size == CitySize::Major {
            for &nb in &raw_neighbors[center as usize] {
                if !used_mps.contains(&nb) {
                    city_mps.push(nb);
                    used_mps.insert(nb);
                }
            }
        }

        let terrain = match spec.size {
            CitySize::Major => Terrain::MajorCity,
            CitySize::Medium => Terrain::MediumCity,
            CitySize::Small => Terrain::SmallCity,
        };
        for &mp in &city_mps {
            mileposts[mp as usize].terrain = terrain;
            mileposts[mp as usize].city_id = Some(spec.id.to_string());
        }

        cities.push(City {
            id: spec.id.to_string(),
            name: spec.name.to_string(),
            size: spec.size,
            center_mp: center,
            mileposts: city_mps,
            commodities: spec.commodities.iter().map(|s| (*s).to_string()).collect(),
        });
    }

    // 4. Build edges with River (+$2M) and Lake Channel / Inlet (+$3M / +$2M) surcharges.
    let mut edges: Vec<EdgeDef> = Vec::new();
    let mut seen_edges: HashSet<(MilepostId, MilepostId)> = HashSet::new();

    for (i, nbs) in raw_neighbors.iter().enumerate() {
        for &j in nbs {
            let ek = edge_key(i as MilepostId, j);
            if !seen_edges.insert(ek) {
                continue;
            }
            let a = &mileposts[ek.0 as usize];
            let b = &mileposts[ek.1 as usize];

            let same_major = a.terrain == Terrain::MajorCity
                && b.terrain == Terrain::MajorCity
                && a.city_id == b.city_id;

            let mid = [(a.x + b.x) * 0.5, (a.y + b.y) * 0.5];
            let crosses_water = !is_land(mid);

            let (kind, river_name) = if same_major {
                (EdgeKind::Normal, None)
            } else if crosses_water {
                (EdgeKind::Inlet, None)
            } else if let Some(rname) = river_crossed([a.x, a.y], [b.x, b.y], &geo.rivers) {
                (EdgeKind::River, Some(rname))
            } else {
                (EdgeKind::Normal, None)
            };

            edges.push(EdgeDef {
                a: ek.0,
                b: ek.1,
                kind,
                river_name,
            });
        }
    }

    // 5. Define 26 classic commodities.
    let commodities = vec![
        commodity("coal", "Coal", "COA", 4, "#334155"),
        commodity("iron", "Iron", "IRN", 3, "#64748b"),
        commodity("steel", "Steel", "STL", 4, "#475569"),
        commodity("oil", "Oil", "OIL", 4, "#1e293b"),
        commodity("wheat", "Wheat", "WHT", 4, "#eab308"),
        commodity("corn", "Corn", "CRN", 3, "#facc15"),
        commodity("cattle", "Cattle", "CTL", 4, "#92400e"),
        commodity("hogs", "Hogs", "HOG", 3, "#f472b6"),
        commodity("cotton", "Cotton", "CTN", 4, "#e2e8f0"),
        commodity("timber", "Timber", "TMB", 4, "#15803d"),
        commodity("fish", "Fish", "FSH", 4, "#0284c7"),
        commodity("oranges", "Oranges", "ORG", 3, "#f97316"),
        commodity("sugar", "Sugar", "SGR", 3, "#f8fafc"),
        commodity("tobacco", "Tobacco", "TBC", 3, "#a16207"),
        commodity("copper", "Copper", "CPR", 4, "#ea580c"),
        commodity("silver", "Silver", "SLV", 3, "#cbd5e1"),
        commodity("cars", "Autos", "CAR", 3, "#dc2626"),
        commodity("machinery", "Machinery", "MCH", 3, "#2563eb"),
        commodity("imports", "Imports", "IMP", 4, "#7c3aed"),
        commodity("beer", "Beer", "BER", 3, "#d97706"),
        commodity("wine", "Wine", "WIN", 3, "#9f1239"),
        commodity("paper", "Paper", "PPR", 3, "#d6d3d1"),
        commodity("chemicals", "Chemicals", "CHM", 3, "#10b981"),
        commodity("textiles", "Textiles", "TXT", 3, "#ec4899"),
        commodity("books", "Books", "BKS", 3, "#4f46e5"),
        commodity("aluminum", "Aluminum", "ALU", 3, "#94a3b8"),
    ];

    let deck = build_deck(&cities, &mileposts, &commodities);

    MapData {
        id: "na_classic".to_string(),
        name: "North America (US & Southern Canada)".to_string(),
        default_victory_cash: 250,
        default_victory_major_cities: 5,
        geography: MapGeography {
            width: geo.width,
            height: geo.height,
            land_polygons: geo.land_polygons,
            lake_polygons: geo.lake_polygons,
            rivers: geo.rivers,
            borders: geo.borders,
        },
        mileposts,
        cities,
        edges,
        commodities,
        deck,
    }
}

fn build_hex_neighbors<F>(mileposts: &[Milepost], is_land: &F) -> Vec<Vec<MilepostId>>
where
    F: Fn([f32; 2]) -> bool,
{
    let n = mileposts.len();
    let mut adj = vec![Vec::new(); n];
    for i in 0..n {
        for j in (i + 1)..n {
            let dx = mileposts[i].x - mileposts[j].x;
            let dy = mileposts[i].y - mileposts[j].y;
            let d2 = dx * dx + dy * dy;
            if d2 > 0.7 && d2 < 1.25 {
                // Allow narrow water crossings (e.g. Great Lakes channels, bays) if endpoints are adjacent,
                // while preventing jumps across wide open water by checking two intermediate sample points.
                let p1 = [
                    mileposts[i].x * 0.67 + mileposts[j].x * 0.33,
                    mileposts[i].y * 0.67 + mileposts[j].y * 0.33,
                ];
                let p2 = [
                    mileposts[i].x * 0.33 + mileposts[j].x * 0.67,
                    mileposts[i].y * 0.33 + mileposts[j].y * 0.67,
                ];
                if !is_land(p1) && !is_land(p2) {
                    continue;
                }
                adj[i].push(j as MilepostId);
                adj[j].push(i as MilepostId);
            }
        }
    }
    adj
}

fn largest_component(adj: &[Vec<MilepostId>]) -> HashSet<MilepostId> {
    let mut visited = vec![false; adj.len()];
    let mut best: Vec<MilepostId> = Vec::new();
    for start in 0..adj.len() {
        if visited[start] {
            continue;
        }
        let mut comp = Vec::new();
        let mut q = VecDeque::new();
        visited[start] = true;
        q.push_back(start as MilepostId);
        while let Some(u) = q.pop_front() {
            comp.push(u);
            for &v in &adj[u as usize] {
                if !visited[v as usize] {
                    visited[v as usize] = true;
                    q.push_back(v);
                }
            }
        }
        if comp.len() > best.len() {
            best = comp;
        }
    }
    best.into_iter().collect()
}

fn commodity(id: &str, name: &str, short: &str, chips: u8, color: &str) -> Commodity {
    Commodity {
        id: id.to_string(),
        name: name.to_string(),
        short: short.to_string(),
        chips,
        color: color.to_string(),
    }
}

/// Approximate Rocky Mountains, Cascades/Sierra Nevada, and Appalachians in Albers lattice coordinates.
fn default_terrain(x: f32, y: f32) -> Terrain {
    // Rocky Mountains spine (running NW from Calgary/Montana down through Colorado/New Mexico)
    let rockies = (11.5..=19.2).contains(&x)
        && (2.2..=20.0).contains(&y)
        && ((x - (12.5 + (y - 2.2) * 0.34)).abs() < 2.2);
    // Cascades / Sierra Nevada
    let cascades = (5.0..=8.6).contains(&x)
        && (3.5..=17.8).contains(&y)
        && ((x - (6.0 + (y - 3.5) * 0.14)).abs() < 1.15);
    // Appalachian Mountains (SW from Maine/NY down through WV/NC/GA)
    let appalachians = (32.5..=40.0).contains(&x)
        && (9.5..=19.0).contains(&y)
        && ((x - (39.5 - (y - 9.5) * 0.65)).abs() < 1.35);

    if rockies || cascades || appalachians {
        Terrain::Mountain
    } else {
        Terrain::Clear
    }
}

fn build_deck(cities: &[City], mileposts: &[Milepost], commodities: &[Commodity]) -> Vec<Card> {
    let mut rng = ChaCha8Rng::seed_from_u64(0xEB_2026_0002);

    let mut sources: HashMap<&str, Vec<(f32, f32)>> = HashMap::new();
    for c in cities {
        let mp = &mileposts[c.center_mp as usize];
        for comm in &c.commodities {
            sources.entry(comm.as_str()).or_default().push((mp.x, mp.y));
        }
    }

    let mut all_demands: Vec<DemandEntry> = Vec::with_capacity(324);
    let mut city_indices: Vec<usize> = (0..cities.len()).collect();

    for round in 0..10 {
        city_indices.shuffle(&mut rng);
        for &ci in &city_indices {
            if all_demands.len() >= 324 {
                break;
            }
            let dest = &cities[ci];
            let dest_mp = &mileposts[dest.center_mp as usize];

            let comm = loop {
                let c =
                    &commodities[(all_demands.len() * 7 + round * 11 + ci * 3) % commodities.len()];
                if !dest.commodities.iter().any(|x| x == &c.id) {
                    break c;
                }
                if let Some(alt) = commodities
                    .iter()
                    .find(|x| !dest.commodities.iter().any(|d| d == &x.id))
                {
                    break alt;
                }
            };

            let srcs = &sources[comm.id.as_str()];
            let min_dist = srcs
                .iter()
                .map(|&(sx, sy)| ((sx - dest_mp.x).powi(2) + (sy - dest_mp.y).powi(2)).sqrt())
                .fold(f32::INFINITY, f32::min);

            // Calibrate payout to Albers lattice distance (~$1.20M per milepost + base $5M, clamped $7M..$48M).
            let raw = (5.0 + min_dist * 1.25).round() as u32;
            let payout = raw.clamp(7, 48);

            all_demands.push(DemandEntry {
                commodity: comm.id.clone(),
                city_id: dest.id.clone(),
                payout,
            });
        }
    }

    all_demands.sort_by_key(|d| d.payout);
    let third = all_demands.len() / 3;
    let mut low = all_demands[..third].to_vec();
    let mut mid = all_demands[third..(2 * third)].to_vec();
    let mut high = all_demands[(2 * third)..].to_vec();
    low.shuffle(&mut rng);
    mid.shuffle(&mut rng);
    high.shuffle(&mut rng);

    let mut deck: Vec<Card> = Vec::with_capacity(third + 16);
    for i in 0..third {
        deck.push(Card::Demand {
            id: (i + 1) as u16,
            demands: [low[i].clone(), mid[i].clone(), high[i].clone()],
        });
    }

    let mut eid = (third + 1) as u16;
    let mut push_event = |title: &str, desc: &str, effect: EventEffect| {
        deck.push(Card::Event {
            id: eid,
            title: title.to_string(),
            description: desc.to_string(),
            effect,
        });
        eid += 1;
    };

    push_event(
        "Derailment: Midwest",
        "Trains within 3 mileposts of Chicago or St. Louis lose their next turn and 1 load.",
        EventEffect::Derailment {
            cities: vec!["chicago".into(), "st_louis".into()],
            radius: 3,
        },
    );
    push_event(
        "Derailment: Northeast",
        "Trains within 3 mileposts of New York or Pittsburgh lose their next turn and 1 load.",
        EventEffect::Derailment {
            cities: vec!["new_york".into(), "pittsburgh".into()],
            radius: 3,
        },
    );
    push_event(
        "Derailment: West Coast",
        "Trains within 3 mileposts of Los Angeles or San Francisco lose their next turn and 1 load.",
        EventEffect::Derailment {
            cities: vec!["los_angeles".into(), "san_francisco".into()],
            radius: 3,
        },
    );
    push_event(
        "Derailment: Plains & Rockies",
        "Trains within 3 mileposts of Denver or Dallas lose their next turn and 1 load.",
        EventEffect::Derailment {
            cities: vec!["denver".into(), "dallas".into()],
            radius: 3,
        },
    );
    push_event(
        "Mississippi Flood",
        "Mississippi River bridges within 5 mileposts of St. Louis are washed out and closed for 1 round.",
        EventEffect::Flood {
            river_name: "Mississippi".into(),
            city_id: "st_louis".into(),
            radius: 5,
        },
    );
    push_event(
        "Missouri Flood",
        "Missouri River bridges within 5 mileposts of Kansas City are washed out and closed for 1 round.",
        EventEffect::Flood {
            river_name: "Missouri".into(),
            city_id: "kansas_city".into(),
            radius: 5,
        },
    );
    push_event(
        "Ohio River Flood",
        "Ohio River bridges within 5 mileposts of Pittsburgh are washed out and closed for 1 round.",
        EventEffect::Flood {
            river_name: "Ohio".into(),
            city_id: "pittsburgh".into(),
            radius: 5,
        },
    );
    push_event(
        "Plains Tornado",
        "Within 5 mileposts of Oklahoma City: trains move at half speed; no clear-terrain move or build.",
        EventEffect::Storm {
            city_id: "oklahoma_city".into(),
            radius: 5,
            block_terrain: Some(Terrain::Clear),
        },
    );
    push_event(
        "Rocky Mountain Blizzard",
        "Within 5 mileposts of Denver: trains move at half speed; no mountain move or build.",
        EventEffect::Storm {
            city_id: "denver".into(),
            radius: 5,
            block_terrain: Some(Terrain::Mountain),
        },
    );
    push_event(
        "Gulf Hurricane",
        "Within 5 mileposts of New Orleans: trains move at half speed; no clear-terrain move or build.",
        EventEffect::Storm {
            city_id: "new_orleans".into(),
            radius: 5,
            block_terrain: Some(Terrain::Clear),
        },
    );
    push_event(
        "Atlantic Nor'easter",
        "Within 4 mileposts of Boston: trains move at half speed for 1 round.",
        EventEffect::Storm {
            city_id: "boston".into(),
            radius: 4,
            block_terrain: None,
        },
    );
    push_event(
        "Canadian Rail Strike",
        "No rail building, movement, pickup, or delivery within 3 mileposts of Toronto, Montreal, or Winnipeg.",
        EventEffect::Strike {
            cities: vec!["toronto".into(), "montreal".into(), "winnipeg".into()],
            radius: 3,
        },
    );
    push_event(
        "Pacific Dock Strike",
        "No rail building, movement, pickup, or delivery within 3 mileposts of Seattle or Vancouver.",
        EventEffect::Strike {
            cities: vec!["seattle".into(), "vancouver".into()],
            radius: 3,
        },
    );
    push_event(
        "Rail Tax",
        "Every player with $50M or more pays a progressive federal rail tax.",
        EventEffect::RailTax,
    );
    push_event(
        "Rail Tax",
        "Every player with $50M or more pays a progressive federal rail tax.",
        EventEffect::RailTax,
    );
    push_event(
        "Heating Fuel Shortage",
        "Any player delivering Oil or Coal to Boston, New York, Toronto, or Minneapolis earns a $24M bonus!",
        EventEffect::HeatingFuelShortage {
            commodity: "oil".into(),
            target_cities: vec![
                "boston".into(),
                "new_york".into(),
                "toronto".into(),
                "minneapolis".into(),
            ],
            bonus: 24,
        },
    );

    deck
}

fn point_in_polygon(p: [f32; 2], poly: &[[f32; 2]]) -> bool {
    let mut inside = false;
    let n = poly.len();
    let mut j = n - 1;
    for i in 0..n {
        let [xi, yi] = poly[i];
        let [xj, yj] = poly[j];
        let intersect = ((yi > p[1]) != (yj > p[1]))
            && (p[0] < (xj - xi) * (p[1] - yi) / (yj - yi + 1e-9) + xi);
        if intersect {
            inside = !inside;
        }
        j = i;
    }
    inside
}

fn river_crossed(a: [f32; 2], b: [f32; 2], rivers: &[Polyline]) -> Option<String> {
    for r in rivers {
        for win in r.points.windows(2) {
            if segments_intersect(a, b, win[0], win[1]) {
                return Some(r.name.clone());
            }
        }
    }
    None
}

fn segments_intersect(a: [f32; 2], b: [f32; 2], c: [f32; 2], d: [f32; 2]) -> bool {
    fn orient(p: [f32; 2], q: [f32; 2], r: [f32; 2]) -> f32 {
        (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    }
    let o1 = orient(a, b, c);
    let o2 = orient(a, b, d);
    let o3 = orient(c, d, a);
    let o4 = orient(c, d, b);
    (o1 * o2 < 0.0) && (o3 * o4 < 0.0)
}
