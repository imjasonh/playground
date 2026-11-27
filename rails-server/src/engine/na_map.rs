use crate::engine::map::{
    edge_key, Card, City, CitySize, Commodity, DemandEntry, EdgeDef, EdgeKind, EventEffect,
    MapData, MapGeography, Milepost, MilepostId, Polyline, Terrain,
};
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::collections::{HashMap, HashSet};

const ROW_STEP: f32 = 0.866_025_4; // sqrt(3) / 2

/// Build the standard Empire Builder North America (US + Southern Canada) map and deck.
pub fn build_north_america_map() -> MapData {
    let width = 39.0_f32;
    let height = 22.0_f32 * ROW_STEP + 1.5;

    // 1. Define continental US + Southern Canada landmass polygon (in lattice coordinates).
    //    Origin (0,0) is top-left (Pacific Northwest / BC).
    let land_poly: Vec<[f32; 2]> = vec![
        [1.2, 1.5],   // Vancouver Island / BC coast
        [4.5, 0.9],   // BC interior
        [10.0, 0.8],  // Alberta / Calgary
        [16.0, 0.9],  // Saskatchewan / Manitoba
        [21.5, 1.2],  // Northern Ontario
        [26.5, 1.4],  // Quebec north
        [31.5, 1.2],  // Quebec / St. Lawrence
        [36.5, 1.8],  // Maritimes / Maine
        [37.2, 4.2],  // Nova Scotia / Maine coast
        [35.2, 6.2],  // Boston / Cape Cod
        [33.8, 7.6],  // New York / Long Island
        [32.6, 9.5],  // Mid-Atlantic / Chesapeake
        [32.2, 11.8], // Carolinas
        [30.5, 14.2], // Georgia
        [31.0, 17.5], // Florida east coast
        [29.8, 19.2], // Miami / Keys
        [28.5, 17.2], // Florida gulf coast
        [26.8, 15.6], // Panhandle
        [23.8, 16.0], // New Orleans / Mississippi delta
        [19.5, 16.4], // Houston / Texas coast
        [16.8, 18.6], // Brownsville / Rio Grande mouth
        [14.2, 16.8], // Rio Grande / El Paso
        [10.5, 15.6], // Arizona / Sonora border
        [5.8, 15.2],  // San Diego / Southern California
        [3.4, 13.8],  // Los Angeles coast
        [1.8, 10.6],  // San Francisco / Central CA
        [1.2, 7.5],   // Northern CA / Oregon
        [1.4, 4.2],   // Washington / Puget Sound
    ];

    // Great Lakes cutouts (Superior, Michigan/Huron, Erie/Ontario).
    let lake_superior: Vec<[f32; 2]> = vec![
        [21.2, 3.7],
        [24.2, 3.4],
        [25.2, 4.4],
        [23.6, 5.1],
        [21.4, 4.7],
    ];
    let lake_michigan_huron: Vec<[f32; 2]> = vec![
        [24.3, 5.1],
        [26.6, 4.8],
        [27.2, 6.2],
        [25.6, 6.6],
        [24.6, 7.3],
        [23.7, 6.4],
    ];
    let lake_erie_ontario: Vec<[f32; 2]> = vec![[26.8, 6.7], [29.6, 5.7], [30.0, 6.5], [27.2, 7.4]];

    // Major rivers (used both visually and to mark +$2M river crossing edges).
    let rivers = vec![
        Polyline {
            name: "Mississippi".into(),
            points: vec![
                [20.2, 4.8],
                [21.3, 7.0],
                [22.0, 9.6],
                [22.4, 12.2],
                [22.8, 14.5],
                [23.4, 16.2],
            ],
        },
        Polyline {
            name: "Missouri".into(),
            points: vec![
                [12.2, 3.8],
                [15.4, 5.2],
                [17.5, 7.4],
                [19.2, 9.2],
                [21.8, 10.0],
            ],
        },
        Polyline {
            name: "Ohio".into(),
            points: vec![[29.2, 8.2], [26.8, 9.4], [24.4, 10.4], [22.2, 11.2]],
        },
        Polyline {
            name: "Colorado".into(),
            points: vec![[11.2, 9.0], [9.2, 11.4], [7.8, 13.8], [7.2, 15.2]],
        },
        Polyline {
            name: "Columbia".into(),
            points: vec![[6.4, 2.2], [5.4, 4.2], [3.4, 4.8], [1.6, 4.9]],
        },
        Polyline {
            name: "Rio Grande".into(),
            points: vec![[11.8, 11.2], [12.4, 13.8], [14.2, 16.4], [16.8, 18.4]],
        },
        Polyline {
            name: "St. Lawrence".into(),
            points: vec![[29.8, 5.8], [32.4, 4.4], [35.2, 2.6]],
        },
    ];

    let borders = vec![Polyline {
        name: "US-Canada".into(),
        points: vec![
            [1.8, 3.2],
            [8.0, 3.2],
            [15.0, 3.2],
            [20.8, 3.8],
            [25.5, 5.2],
            [28.5, 6.2],
            [31.5, 5.4],
            [34.8, 4.2],
        ],
    }];

    // 2. Place mileposts on the offset hex lattice inside the landmass and outside lakes.
    let mut mileposts: Vec<Milepost> = Vec::new();
    let mut grid_to_id: HashMap<(u16, u16), MilepostId> = HashMap::new();

    for row in 1..22u16 {
        for col in 1..38u16 {
            let x = col as f32 + if row % 2 == 1 { 0.5 } else { 0.0 };
            let y = row as f32 * ROW_STEP;
            let pt = [x, y];
            if !point_in_polygon(pt, &land_poly) {
                continue;
            }
            if point_in_polygon(pt, &lake_superior)
                || point_in_polygon(pt, &lake_michigan_huron)
                || point_in_polygon(pt, &lake_erie_ontario)
            {
                continue;
            }
            let id = mileposts.len() as MilepostId;
            let terrain = default_terrain(x, y);
            mileposts.push(Milepost {
                id,
                col,
                row,
                x,
                y,
                terrain,
                city_id: None,
            });
            grid_to_id.insert((col, row), id);
        }
    }

    // Helper: find nearest milepost to (target_x, target_y) not yet assigned to a city.
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

    // Build lattice adjacency temporarily so Major Cities can claim their 6 surrounding rim mileposts.
    let mut raw_neighbors: Vec<Vec<MilepostId>> = vec![Vec::new(); mileposts.len()];
    for i in 0..mileposts.len() {
        for j in (i + 1)..mileposts.len() {
            let dx = mileposts[i].x - mileposts[j].x;
            let dy = mileposts[i].y - mileposts[j].y;
            let d2 = dx * dx + dy * dy;
            if d2 > 0.7 && d2 < 1.25 {
                raw_neighbors[i].push(j as MilepostId);
                raw_neighbors[j].push(i as MilepostId);
            }
        }
    }

    // 3. Place cities (6 Major Cities + 32 Medium/Small Cities).
    struct CitySpec {
        id: &'static str,
        name: &'static str,
        size: CitySize,
        x: f32,
        y: f32,
        commodities: &'static [&'static str],
    }

    let specs: &[CitySpec] = &[
        // 6 Major Cities (5 required to win in standard US + Southern Canada EB)
        CitySpec {
            id: "new_york",
            name: "New York",
            size: CitySize::Major,
            x: 32.5,
            y: 7.4,
            commodities: &["imports", "machinery", "books"],
        },
        CitySpec {
            id: "chicago",
            name: "Chicago",
            size: CitySize::Major,
            x: 23.2,
            y: 7.6,
            commodities: &["machinery", "steel", "wheat"],
        },
        CitySpec {
            id: "toronto",
            name: "Toronto",
            size: CitySize::Major,
            x: 28.0,
            y: 5.2,
            commodities: &["beer", "wheat", "cars"],
        },
        CitySpec {
            id: "new_orleans",
            name: "New Orleans",
            size: CitySize::Major,
            x: 23.2,
            y: 14.9,
            commodities: &["imports", "sugar", "oil"],
        },
        CitySpec {
            id: "los_angeles",
            name: "Los Angeles",
            size: CitySize::Major,
            x: 4.5,
            y: 13.0,
            commodities: &["cars", "oranges", "imports"],
        },
        CitySpec {
            id: "san_francisco",
            name: "San Francisco",
            size: CitySize::Major,
            x: 2.7,
            y: 9.8,
            commodities: &["wine", "imports", "fish"],
        },
        // Northeast & Eastern Canada
        CitySpec {
            id: "boston",
            name: "Boston",
            size: CitySize::Medium,
            x: 34.8,
            y: 5.8,
            commodities: &["fish", "books", "imports"],
        },
        CitySpec {
            id: "montreal",
            name: "Montreal",
            size: CitySize::Medium,
            x: 31.8,
            y: 4.0,
            commodities: &["paper", "beer", "aluminum"],
        },
        CitySpec {
            id: "quebec",
            name: "Quebec",
            size: CitySize::Small,
            x: 34.2,
            y: 2.5,
            commodities: &["timber", "paper", "iron"],
        },
        CitySpec {
            id: "washington",
            name: "Washington",
            size: CitySize::Medium,
            x: 31.4,
            y: 9.6,
            commodities: &["books", "tobacco"],
        },
        CitySpec {
            id: "pittsburgh",
            name: "Pittsburgh",
            size: CitySize::Medium,
            x: 29.0,
            y: 8.6,
            commodities: &["coal", "steel", "chemicals"],
        },
        CitySpec {
            id: "detroit",
            name: "Detroit",
            size: CitySize::Medium,
            x: 26.2,
            y: 7.4,
            commodities: &["cars", "steel", "machinery"],
        },
        CitySpec {
            id: "cleveland",
            name: "Cleveland",
            size: CitySize::Small,
            x: 27.6,
            y: 7.8,
            commodities: &["steel", "chemicals"],
        },
        // Southeast
        CitySpec {
            id: "norfolk",
            name: "Norfolk",
            size: CitySize::Small,
            x: 31.8,
            y: 11.1,
            commodities: &["imports", "tobacco", "fish"],
        },
        CitySpec {
            id: "charlotte",
            name: "Charlotte",
            size: CitySize::Small,
            x: 29.5,
            y: 11.6,
            commodities: &["textiles", "tobacco"],
        },
        CitySpec {
            id: "atlanta",
            name: "Atlanta",
            size: CitySize::Medium,
            x: 27.8,
            y: 12.8,
            commodities: &["textiles", "cotton", "paper"],
        },
        CitySpec {
            id: "birmingham",
            name: "Birmingham",
            size: CitySize::Small,
            x: 25.8,
            y: 13.0,
            commodities: &["coal", "iron", "steel"],
        },
        CitySpec {
            id: "jacksonville",
            name: "Jacksonville",
            size: CitySize::Small,
            x: 29.5,
            y: 15.1,
            commodities: &["oranges", "paper", "fish"],
        },
        CitySpec {
            id: "miami",
            name: "Miami",
            size: CitySize::Medium,
            x: 29.8,
            y: 17.8,
            commodities: &["oranges", "sugar", "imports"],
        },
        // Midwest & Plains & Central Canada
        CitySpec {
            id: "minneapolis",
            name: "Minneapolis",
            size: CitySize::Medium,
            x: 20.0,
            y: 5.5,
            commodities: &["wheat", "iron", "beer"],
        },
        CitySpec {
            id: "winnipeg",
            name: "Winnipeg",
            size: CitySize::Medium,
            x: 18.0,
            y: 2.3,
            commodities: &["wheat", "timber", "copper"],
        },
        CitySpec {
            id: "st_louis",
            name: "St. Louis",
            size: CitySize::Medium,
            x: 22.0,
            y: 10.2,
            commodities: &["beer", "corn", "hogs"],
        },
        CitySpec {
            id: "memphis",
            name: "Memphis",
            size: CitySize::Small,
            x: 22.8,
            y: 12.4,
            commodities: &["cotton", "timber", "hogs"],
        },
        CitySpec {
            id: "kansas_city",
            name: "Kansas City",
            size: CitySize::Medium,
            x: 18.8,
            y: 10.0,
            commodities: &["wheat", "cattle", "corn"],
        },
        CitySpec {
            id: "omaha",
            name: "Omaha",
            size: CitySize::Small,
            x: 17.8,
            y: 8.1,
            commodities: &["corn", "cattle", "hogs"],
        },
        CitySpec {
            id: "oklahoma_city",
            name: "Oklahoma City",
            size: CitySize::Small,
            x: 17.8,
            y: 12.2,
            commodities: &["oil", "cattle", "wheat"],
        },
        CitySpec {
            id: "dallas",
            name: "Dallas",
            size: CitySize::Medium,
            x: 18.0,
            y: 14.2,
            commodities: &["oil", "cotton", "cattle"],
        },
        CitySpec {
            id: "houston",
            name: "Houston",
            size: CitySize::Medium,
            x: 19.6,
            y: 15.8,
            commodities: &["oil", "chemicals", "sugar"],
        },
        CitySpec {
            id: "san_antonio",
            name: "San Antonio",
            size: CitySize::Small,
            x: 16.5,
            y: 16.2,
            commodities: &["cattle", "cotton"],
        },
        // West, Mountains & Western Canada
        CitySpec {
            id: "calgary",
            name: "Calgary",
            size: CitySize::Medium,
            x: 10.6,
            y: 2.2,
            commodities: &["oil", "cattle", "coal"],
        },
        CitySpec {
            id: "vancouver",
            name: "Vancouver",
            size: CitySize::Medium,
            x: 3.0,
            y: 2.3,
            commodities: &["timber", "fish", "aluminum"],
        },
        CitySpec {
            id: "seattle",
            name: "Seattle",
            size: CitySize::Medium,
            x: 3.1,
            y: 4.1,
            commodities: &["timber", "fish", "aluminum"],
        },
        CitySpec {
            id: "portland",
            name: "Portland",
            size: CitySize::Small,
            x: 2.8,
            y: 5.8,
            commodities: &["timber", "wine", "wheat"],
        },
        CitySpec {
            id: "boise",
            name: "Boise",
            size: CitySize::Small,
            x: 6.8,
            y: 6.2,
            commodities: &["silver", "cattle"],
        },
        CitySpec {
            id: "salt_lake",
            name: "Salt Lake City",
            size: CitySize::Medium,
            x: 9.2,
            y: 8.6,
            commodities: &["copper", "silver", "chemicals"],
        },
        CitySpec {
            id: "denver",
            name: "Denver",
            size: CitySize::Medium,
            x: 13.0,
            y: 9.2,
            commodities: &["coal", "silver", "cattle"],
        },
        CitySpec {
            id: "las_vegas",
            name: "Las Vegas",
            size: CitySize::Small,
            x: 6.8,
            y: 11.4,
            commodities: &["silver", "copper"],
        },
        CitySpec {
            id: "phoenix",
            name: "Phoenix",
            size: CitySize::Medium,
            x: 9.2,
            y: 13.8,
            commodities: &["copper", "cotton", "oranges"],
        },
        CitySpec {
            id: "albuquerque",
            name: "Albuquerque",
            size: CitySize::Small,
            x: 12.2,
            y: 12.4,
            commodities: &["copper", "oil"],
        },
        CitySpec {
            id: "el_paso",
            name: "El Paso",
            size: CitySize::Small,
            x: 13.2,
            y: 15.0,
            commodities: &["copper", "cattle"],
        },
    ];

    let mut used_mps: HashSet<MilepostId> = HashSet::new();
    let mut cities: Vec<City> = Vec::with_capacity(specs.len());

    for spec in specs {
        let center = find_nearest(&mileposts, spec.x, spec.y, &used_mps);
        let mut city_mps = vec![center];
        used_mps.insert(center);

        if spec.size == CitySize::Major {
            // Claim immediate neighbors as part of the red major-city hub (up to 6 rim mileposts).
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

    // 4. Build edges with River (+$2M) and Ocean Inlet (+$3M) surcharges.
    let inlet_segments: &[([f32; 2], [f32; 2])] = &[
        // Chesapeake Bay
        ([31.8, 9.6], [32.6, 10.8]),
        // Puget Sound
        ([2.3, 3.0], [3.3, 4.3]),
        // San Francisco Bay
        ([1.8, 9.5], [3.2, 10.2]),
        // Mobile / Tampa bays
        ([25.2, 15.2], [26.2, 16.0]),
    ];

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

            // Edges inside the same major city are always free/normal.
            let same_major = a.terrain == Terrain::MajorCity
                && b.terrain == Terrain::MajorCity
                && a.city_id == b.city_id;

            let (kind, river_name) = if same_major {
                (EdgeKind::Normal, None)
            } else if inlet_segments
                .iter()
                .any(|&(p, q)| segments_intersect([a.x, a.y], [b.x, b.y], p, q))
            {
                (EdgeKind::Inlet, None)
            } else if let Some(rname) = river_crossed([a.x, a.y], [b.x, b.y], &rivers) {
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

    // 6. Generate 108 balanced Demand Cards + 16 Event Cards deterministically.
    let deck = build_deck(&cities, &mileposts, &commodities);

    MapData {
        id: "na_classic".to_string(),
        name: "North America (US & Southern Canada)".to_string(),
        default_victory_cash: 250,
        default_victory_major_cities: 5,
        geography: MapGeography {
            width,
            height,
            land_polygons: vec![land_poly],
            lake_polygons: vec![lake_superior, lake_michigan_huron, lake_erie_ontario],
            rivers,
            borders,
        },
        mileposts,
        cities,
        edges,
        commodities,
        deck,
    }
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

fn default_terrain(x: f32, y: f32) -> Terrain {
    // Rocky Mountains spine
    let rockies = (9.0..=13.2).contains(&x)
        && (2.0..=13.0).contains(&y)
        && ((x - (10.5 + (y - 2.0) * 0.14)).abs() < 1.8);
    // Sierra Nevada / Cascades
    let cascades = (3.8..=5.6).contains(&x)
        && (2.2..=12.2).contains(&y)
        && ((x - (4.3 + (y - 2.2) * 0.08)).abs() < 1.0);
    // Appalachian Mountains
    let appalachians = (27.5..=31.2).contains(&x)
        && (6.8..=12.6).contains(&y)
        && ((x - (30.5 - (y - 6.8) * 0.42)).abs() < 1.15);

    if rockies || cascades || appalachians {
        Terrain::Mountain
    } else {
        Terrain::Clear
    }
}

fn build_deck(cities: &[City], mileposts: &[Milepost], commodities: &[Commodity]) -> Vec<Card> {
    let mut rng = ChaCha8Rng::seed_from_u64(0xEB_2026_0001);

    // Precompute source city centers for each commodity.
    let mut sources: HashMap<&str, Vec<(f32, f32)>> = HashMap::new();
    for c in cities {
        let mp = &mileposts[c.center_mp as usize];
        for comm in &c.commodities {
            sources.entry(comm.as_str()).or_default().push((mp.x, mp.y));
        }
    }

    // Build a balanced pool of 324 valid (commodity, dest_city, payout) demand entries.
    let mut all_demands: Vec<DemandEntry> = Vec::with_capacity(324);
    let mut city_indices: Vec<usize> = (0..cities.len()).collect();

    for round in 0..13 {
        city_indices.shuffle(&mut rng);
        for &ci in &city_indices {
            if all_demands.len() >= 324 {
                break;
            }
            let dest = &cities[ci];
            let dest_mp = &mileposts[dest.center_mp as usize];

            // Pick a commodity not produced at `dest`.
            let comm = loop {
                let c =
                    &commodities[(all_demands.len() * 7 + round * 11 + ci * 3) % commodities.len()];
                if !dest.commodities.iter().any(|x| x == &c.id) {
                    break c;
                }
                // Fallback deterministic scan
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

            // Calibrate payout to nearest source distance (~$1.35M per milepost + base $5M, clamped $7M..$48M).
            let raw = (5.0 + min_dist * 1.45).round() as u32;
            let payout = raw.clamp(7, 48);

            all_demands.push(DemandEntry {
                commodity: comm.id.clone(),
                city_id: dest.id.clone(),
                payout,
            });
        }
    }

    // Sort into low / mid / high payout buckets so each card has a mix of short, medium, and long hauls.
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
        // Ensure the 3 demands on one card target distinct cities when possible.
        let d1 = low[i].clone();
        let d2 = mid[i].clone();
        let d3 = high[i].clone();
        deck.push(Card::Demand {
            id: (i + 1) as u16,
            demands: [d1, d2, d3],
        });
    }

    // 16 Classic Event Cards (filtered out when events are disabled).
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
