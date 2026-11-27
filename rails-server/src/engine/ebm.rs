use crate::engine::map::{
    edge_key, Card, City, CitySize, Commodity, DemandEntry, EdgeDef, EdgeKind, EventEffect,
    MapData, MapGeography, Milepost, MilepostId, Polyline, Terrain,
};
use std::collections::{HashMap, HashSet, VecDeque};

/// Default embedded classic Empire Builder USA + Southern Canada `.ebm` map.
pub const DEFAULT_EBM: &str = include_str!("../../maps/USAMAP.EBM");

const SQRT3_OVER_2: f32 = 0.866_025_4;

const COMMODITY_PALETTE: [&str; 26] = [
    "#7c2d12", // Bauxite
    "#dc2626", // Cars
    "#92400e", // Cattle
    "#334155", // Coal
    "#ea580c", // Copper
    "#eab308", // Corn
    "#64748b", // Cotton
    "#0284c7", // Fish
    "#f97316", // Fruit
    "#7c3aed", // Imports
    "#475569", // Iron
    "#52525b", // Lead
    "#2563eb", // Machinery
    "#0d9488", // Nickel
    "#ca8a04", // Oats
    "#1e293b", // Oil
    "#65a30d", // Rice
    "#a8a29e", // Sheep
    "#3b82f6", // Steel
    "#db2777", // Sugar
    "#f472b6", // Swine
    "#a16207", // Tobacco
    "#ec4899", // Tourists
    "#16a34a", // Uranium
    "#d97706", // Wheat
    "#15803d", // Wood
];

/// Load the default classic Empire Builder USA `.ebm` map.
pub fn build_default_ebm_map() -> MapData {
    parse_ebm(DEFAULT_EBM).expect("embedded USAMAP.EBM must parse cleanly")
}

/// Parse any EB Pronto / EBPEdit `.ebm` text map file into a `MapData` graph & deck.
pub fn parse_ebm(text: &str) -> Result<MapData, String> {
    let mut section = String::new();
    let mut map_kv: HashMap<String, String> = HashMap::new();
    let mut win_kv: HashMap<String, String> = HashMap::new();
    let mut upper_dots: HashMap<(i32, i32), Vec<String>> = HashMap::new();
    let mut lower_dots: HashMap<(i32, i32), String> = HashMap::new();
    let mut city_lines: Vec<String> = Vec::new();
    let mut load_lines: Vec<String> = Vec::new();
    let mut demand_lines: Vec<String> = Vec::new();
    let mut event_lines: Vec<String> = Vec::new();

    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            section = line[1..line.len() - 1].to_ascii_lowercase();
            continue;
        }

        match section.as_str() {
            "map" => {
                if let Some((k, v)) = line.split_once('=') {
                    map_kv.insert(k.trim().to_ascii_lowercase(), v.trim().to_string());
                }
            }
            "win" => {
                if let Some((k, v)) = line.split_once('=') {
                    win_kv.insert(k.trim().to_ascii_lowercase(), v.trim().to_string());
                }
            }
            "dots" => {
                let parts: Vec<String> = line.split(';').map(|s| s.trim().to_string()).collect();
                if parts.len() < 2 {
                    continue;
                }
                if let Some((x, y, is_upper)) = parse_ebm_coord(&parts[0]) {
                    if is_upper {
                        upper_dots.insert((x, y), parts[1..].to_vec());
                    } else {
                        lower_dots.insert((x, y), parts[1].clone());
                    }
                }
            }
            "cities" => city_lines.push(line.to_string()),
            "loads" => load_lines.push(line.to_string()),
            "demands" => demand_lines.push(line.to_string()),
            "events" => event_lines.push(line.to_string()),
            _ => {}
        }
    }

    let mp_x: i32 = map_kv
        .get("milepostsx")
        .and_then(|s| s.parse().ok())
        .unwrap_or(63);
    let mp_y: i32 = map_kv
        .get("milepostsy")
        .and_then(|s| s.parse().ok())
        .unwrap_or(36);
    let coastline_cross = map_kv
        .get("coastlinecross")
        .and_then(|s| s.parse::<i32>().ok())
        .unwrap_or(1)
        != 0;

    let name = map_kv
        .get("name")
        .cloned()
        .unwrap_or_else(|| "Classic USA".to_string());
    let id = slugify(&name);
    let victory_cash: u32 = win_kv
        .get("wincash")
        .and_then(|s| s.parse().ok())
        .unwrap_or(250);
    let victory_major_cities: usize = win_kv
        .get("winmajor")
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    // Sub-grid dimensions: x in 0..=max_x, y in 0..=max_y
    let max_x = (mp_x * 4).max(lower_dots.keys().map(|&(x, _)| x).max().unwrap_or(mp_x * 4));
    let max_y = (mp_y * 4 - 1).max(
        lower_dots
            .keys()
            .map(|&(_, y)| y)
            .max()
            .unwrap_or(mp_y * 4 - 1),
    );
    let w = (max_x + 1) as usize;
    let h = (max_y + 1) as usize;

    // 1. Exterior ocean flood-fill bounded by 'O' (Ocean) and southern border 'Y' (y >= 2/3 height).
    //    Northern 'Y' (US-Canada border) is interior playable territory.
    let south_y_thresh = (max_y * 2) / 3;
    let mut ext_pts: HashSet<(i32, i32)> = HashSet::new();
    for (&(x, y), fl) in &lower_dots {
        if fl.contains('O') || (fl.contains('Y') && y >= south_y_thresh) {
            ext_pts.insert((x, y));
        }
    }

    let mut barrier = vec![false; w * h];
    for &(x, y) in &ext_pts {
        if x >= 0 && y >= 0 && (x as usize) < w && (y as usize) < h {
            barrier[y as usize * w + x as usize] = true;
        }
        // Seal 8-connected diagonal steps so 4-connected flood-fill cannot leak.
        for dx in -1..=1 {
            for dy in -1..=1 {
                if ext_pts.contains(&(x + dx, y + dy)) {
                    let bx = x + dx;
                    if bx >= 0 && y >= 0 && (bx as usize) < w && (y as usize) < h {
                        barrier[y as usize * w + bx as usize] = true;
                    }
                }
            }
        }
    }

    let mut ocean = vec![false; w * h];
    let mut q = VecDeque::new();
    for (sx, sy) in [(0i32, 0i32), (0, max_y), (max_x, max_y)] {
        if sx >= 0 && sy >= 0 && (sx as usize) < w && (sy as usize) < h {
            let idx = sy as usize * w + sx as usize;
            if !barrier[idx] && !ocean[idx] {
                ocean[idx] = true;
                q.push_back((sx, sy));
            }
        }
    }
    while let Some((x, y)) = q.pop_front() {
        for (dx, dy) in [(1, 0), (-1, 0), (0, 1), (0, -1)] {
            let (nx, ny) = (x + dx, y + dy);
            if nx >= 0 && ny >= 0 && (nx as usize) < w && (ny as usize) < h {
                let nidx = ny as usize * w + nx as usize;
                if !barrier[nidx] && !ocean[nidx] {
                    ocean[nidx] = true;
                    q.push_back((nx, ny));
                }
            }
        }
    }

    // 2. Parse [loads] -> commodities
    let mut commodities: Vec<Commodity> = Vec::new();
    let mut comm_name_to_id: HashMap<String, String> = HashMap::new();
    for (i, line) in load_lines.iter().enumerate() {
        let p: Vec<&str> = line.split(';').map(|s| s.trim()).collect();
        if p.len() < 2 || p[0].is_empty() {
            continue;
        }
        let cname = p[0].to_string();
        let cid = slugify(&cname);
        let chips: u8 = p[1].parse().unwrap_or(3).max(1);
        let short = short_code(&cname);
        let color = COMMODITY_PALETTE[i % COMMODITY_PALETTE.len()].to_string();
        comm_name_to_id.insert(cname.to_ascii_lowercase(), cid.clone());
        commodities.push(Commodity {
            id: cid,
            name: cname,
            short,
            chips,
            color,
        });
    }

    // 3. Parse [cities] metadata
    struct RawCityMeta {
        name: String,
        size: CitySize,
        commodities: Vec<String>,
    }
    let mut city_meta: HashMap<String, RawCityMeta> = HashMap::new();
    for line in &city_lines {
        let p: Vec<&str> = line.split(';').map(|s| s.trim()).collect();
        if p.len() < 2 || p[0].is_empty() {
            continue;
        }
        let cname = p[0].to_string();
        let size = match p[1] {
            "2" | "3" | "4" => CitySize::Major,
            "1" => CitySize::Medium,
            _ => CitySize::Small,
        };
        let mut comms = Vec::new();
        if let Some(raw_comms) = p.get(4) {
            for item in raw_comms.split('|') {
                let clean = item.trim();
                if clean.is_empty() {
                    continue;
                }
                if let Some(cid) = comm_name_to_id.get(&clean.to_ascii_lowercase()) {
                    comms.push(cid.clone());
                }
            }
        }
        city_meta.insert(
            cname.to_ascii_lowercase(),
            RawCityMeta {
                name: cname,
                size,
                commodities: comms,
            },
        );
    }

    // 4. Enumerate all playable hex lattice mileposts (exact 63x36 staggered grid).
    let mut grid_to_mp: HashMap<(i32, i32), MilepostId> = HashMap::new();
    let mut mileposts: Vec<Milepost> = Vec::new();
    let mut mp_subcoords: Vec<(i32, i32)> = Vec::new();
    let mut mp_regions: HashMap<MilepostId, String> = HashMap::new();
    let mut city_centers: Vec<(String, MilepostId, (i32, i32))> = Vec::new();

    for row in 0..mp_y {
        for col in 0..mp_x {
            let sx = col * 4 + 2;
            let sy = row * 4 + if col % 2 == 0 { 2 } else { 0 };
            if sx < 0 || sy < 0 || (sx as usize) >= w || (sy as usize) >= h {
                continue;
            }
            let explicit = upper_dots.get(&(sx, sy));
            let (terrain, city_name, region) = if let Some(parts) = explicit {
                let code = parts[0].as_str();
                if code == "H" || code == "W" {
                    continue;
                }
                let reg = parts.get(1).cloned().unwrap_or_default();
                let t = match code {
                    "M" => Terrain::Mountain,
                    "A" => Terrain::Alpine,
                    "C" => Terrain::SmallCity, // refined below from [cities]
                    _ => Terrain::Clear,
                };
                let cname = if code == "C" {
                    parts.get(2).cloned().filter(|s| !s.is_empty())
                } else {
                    None
                };
                (t, cname, reg)
            } else {
                let idx = sy as usize * w + sx as usize;
                if ocean[idx] || barrier[idx] {
                    continue;
                }
                (Terrain::Clear, None, String::new())
            };

            let id = mileposts.len() as MilepostId;
            let (wx, wy) = sub_to_world(sx, sy);
            grid_to_mp.insert((sx, sy), id);
            mp_subcoords.push((sx, sy));
            if !region.is_empty() {
                mp_regions.insert(id, region);
            }
            if let Some(cn) = city_name {
                city_centers.push((cn, id, (sx, sy)));
            }
            mileposts.push(Milepost {
                id,
                col: col as u16,
                row: row as u16,
                x: wx,
                y: wy,
                terrain,
                city_id: None,
            });
        }
    }

    // 5. Assign cities (and expand Major Cities to their playable hex neighbors!).
    let mut cities: Vec<City> = Vec::new();
    let mut city_name_to_id: HashMap<String, String> = HashMap::new();
    let mut claimed_by_city: HashSet<MilepostId> = HashSet::new();

    // First reserve all city centers so Major City expansion never steals another city's dot.
    for &(_, center_id, _) in &city_centers {
        claimed_by_city.insert(center_id);
    }

    for (raw_name, center_id, (cx, cy)) in city_centers {
        let meta = city_meta.get(&raw_name.to_ascii_lowercase());
        let display_name = meta.map(|m| m.name.clone()).unwrap_or(raw_name.clone());
        let size = meta.map(|m| m.size).unwrap_or(CitySize::Small);
        let comms = meta.map(|m| m.commodities.clone()).unwrap_or_default();
        let cid = slugify(&display_name);

        let mut city_mps = vec![center_id];
        if size == CitySize::Major {
            for (dx, dy) in [(0, -4), (0, 4), (-4, -2), (-4, 2), (4, -2), (4, 2)] {
                if let Some(&nb) = grid_to_mp.get(&(cx + dx, cy + dy)) {
                    if !claimed_by_city.contains(&nb) {
                        claimed_by_city.insert(nb);
                        city_mps.push(nb);
                    }
                }
            }
        }

        let terrain = match size {
            CitySize::Major => Terrain::MajorCity,
            CitySize::Medium => Terrain::MediumCity,
            CitySize::Small => Terrain::SmallCity,
        };
        for &mp in &city_mps {
            mileposts[mp as usize].terrain = terrain;
            mileposts[mp as usize].city_id = Some(cid.clone());
        }

        city_name_to_id.insert(display_name.to_ascii_lowercase(), cid.clone());
        cities.push(City {
            id: cid,
            name: display_name,
            size,
            center_mp: center_id,
            mileposts: city_mps,
            commodities: comms,
        });
    }

    // 6. Build hex edges with exact River ('R' -> +$2M), Lake ('L' -> +$2M), and Ocean ('O' -> +$3M) detection.
    let mut edges: Vec<EdgeDef> = Vec::new();
    let mut seen_edges: HashSet<(MilepostId, MilepostId)> = HashSet::new();

    for (i, &(x1, y1)) in mp_subcoords.iter().enumerate() {
        let a_id = i as MilepostId;
        for (dx, dy) in [(0, 4), (4, -2), (4, 2)] {
            let (x2, y2) = (x1 + dx, y1 + dy);
            let Some(&b_id) = grid_to_mp.get(&(x2, y2)) else {
                continue;
            };
            let ek = edge_key(a_id, b_id);
            if !seen_edges.insert(ek) {
                continue;
            }

            let same_major = mileposts[a_id as usize].terrain == Terrain::MajorCity
                && mileposts[b_id as usize].terrain == Terrain::MajorCity
                && mileposts[a_id as usize].city_id == mileposts[b_id as usize].city_id;

            if same_major {
                edges.push(EdgeDef {
                    a: ek.0,
                    b: ek.1,
                    kind: EdgeKind::Normal,
                    river_name: None,
                });
                continue;
            }

            // Sample sub-grid cells along the segment from (x1, y1) to (x2, y2).
            let mut crosses_ocean = false;
            let mut crosses_lake = false;
            let mut crosses_river = false;
            for step in 1..=3 {
                let sx = (x1 * (4 - step) + x2 * step + 2) / 4;
                let sy = (y1 * (4 - step) + y2 * step + 2) / 4;
                if let Some(fl) = lower_dots.get(&(sx, sy)) {
                    if fl.contains('O') {
                        crosses_ocean = true;
                    }
                    if fl.contains('L') {
                        crosses_lake = true;
                    }
                    if fl.contains('R') {
                        crosses_river = true;
                    }
                }
            }

            if crosses_ocean && !coastline_cross {
                continue;
            }

            let (kind, river_name) = if crosses_ocean {
                (EdgeKind::Inlet, None)
            } else if crosses_lake {
                (EdgeKind::River, Some("Great Lakes".to_string()))
            } else if crosses_river {
                // Classify western vs eastern river system for authentic Flood events.
                let rname = if (x1 + x2) / 2 < 110 {
                    "Columbia/Colorado".to_string()
                } else {
                    "Mississippi/Missouri/Ohio".to_string()
                };
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

    // 7. Parse [demands] -> exact 120 classic demand cards!
    let mut deck: Vec<Card> = Vec::new();
    let mut max_card_id: u16 = 0;
    for line in &demand_lines {
        let p: Vec<&str> = line.split(';').map(|s| s.trim()).collect();
        if p.len() < 10 {
            continue;
        }
        let card_id: u16 = p[0].parse().unwrap_or(max_card_id + 1);
        max_card_id = max_card_id.max(card_id);
        let mut entries: Vec<DemandEntry> = Vec::with_capacity(3);
        for k in 0..3 {
            let cname = p[1 + k * 3];
            let comm_name = p[2 + k * 3];
            let payout: u32 = p[3 + k * 3].parse().unwrap_or(10);
            let Some(city_id) = city_name_to_id.get(&cname.to_ascii_lowercase()) else {
                continue;
            };
            let Some(comm_id) = comm_name_to_id.get(&comm_name.to_ascii_lowercase()) else {
                continue;
            };
            entries.push(DemandEntry {
                commodity: comm_id.clone(),
                city_id: city_id.clone(),
                payout,
            });
        }
        if entries.len() == 3 {
            deck.push(Card::Demand {
                id: card_id,
                demands: [entries[0].clone(), entries[1].clone(), entries[2].clone()],
            });
        }
    }

    // 8. Parse [events] -> authentic event cards!
    for line in &event_lines {
        let p: Vec<&str> = line.split(';').map(|s| s.trim()).collect();
        if p.len() < 7 {
            continue;
        }
        max_card_id += 1;
        let title = p[1].to_string();
        let radius: u8 = p.get(3).and_then(|s| s.parse().ok()).unwrap_or(3);
        let region_code = p.get(4).copied().unwrap_or("");
        let move_effect = p.get(6).copied().unwrap_or("");
        let target_spec = p.get(13).copied().unwrap_or("");

        let target_cities: Vec<String> = target_spec
            .split('|')
            .filter_map(|tok| tok.trim().strip_prefix("City:"))
            .filter_map(|cn| {
                city_name_to_id
                    .get(&cn.trim().to_ascii_lowercase())
                    .cloned()
            })
            .collect();

        let lower_title = title.to_ascii_lowercase();
        let effect = if lower_title.starts_with("derailment") && !target_cities.is_empty() {
            EventEffect::Derailment {
                cities: target_cities,
                radius: radius.max(1),
            }
        } else if lower_title.starts_with("flood") {
            let (river_name, anchor) = if target_spec.contains("Columbia") {
                ("Columbia/Colorado".to_string(), "portland_or".to_string())
            } else {
                (
                    "Mississippi/Missouri/Ohio".to_string(),
                    "st_louis".to_string(),
                )
            };
            let city_id = if cities.iter().any(|c| c.id == anchor) {
                anchor
            } else {
                cities[0].id.clone()
            };
            EventEffect::Flood {
                river_name,
                city_id,
                radius: 18,
            }
        } else if lower_title.starts_with("tax") {
            EventEffect::RailTax
        } else if lower_title.starts_with("strike") {
            let strike_cities = if !target_cities.is_empty() {
                target_cities
            } else if !region_code.is_empty() {
                // Regional strike (e.g. 'C' = Canada): collect all cities in that region!
                cities
                    .iter()
                    .filter(|c| {
                        mp_regions
                            .get(&c.center_mp)
                            .is_some_and(|r| r == region_code)
                    })
                    .map(|c| c.id.clone())
                    .collect()
            } else {
                vec![cities[0].id.clone()]
            };
            EventEffect::Strike {
                cities: strike_cities,
                radius: radius.max(3),
            }
        } else if !target_cities.is_empty() {
            let block_terrain = if move_effect.to_ascii_lowercase().contains("mountains") {
                Some(Terrain::Mountain)
            } else if move_effect.to_ascii_lowercase().contains("clear") {
                Some(Terrain::Clear)
            } else {
                None
            };
            EventEffect::Storm {
                city_id: target_cities[0].clone(),
                radius: radius.max(4),
                block_terrain,
            }
        } else if target_spec.contains("Gulf") {
            EventEffect::Storm {
                city_id: city_name_to_id
                    .get("new orleans")
                    .or_else(|| city_name_to_id.get("houston"))
                    .cloned()
                    .unwrap_or_else(|| cities[0].id.clone()),
                radius: radius.max(5),
                block_terrain: None,
            }
        } else if target_spec.contains("Atlantic") {
            EventEffect::Storm {
                city_id: city_name_to_id
                    .get("new york")
                    .cloned()
                    .unwrap_or_else(|| cities[0].id.clone()),
                radius: radius.max(5),
                block_terrain: None,
            }
        } else if target_spec.contains("Pacific") {
            EventEffect::Storm {
                city_id: city_name_to_id
                    .get("san francisco")
                    .or_else(|| city_name_to_id.get("los angeles"))
                    .cloned()
                    .unwrap_or_else(|| cities[0].id.clone()),
                radius: radius.max(5),
                block_terrain: None,
            }
        } else {
            continue;
        };

        let desc = if target_spec.is_empty() {
            format!("{title} — {move_effect}")
        } else {
            format!("{title} ({target_spec})")
        };
        deck.push(Card::Event {
            id: max_card_id,
            title,
            description: desc,
            effect,
        });
    }

    // 9. Build crisp vector geography directly from the .ebm sub-grid!
    let geography = build_ebm_geography(w, h, &ocean, &lower_dots);

    Ok(MapData {
        id,
        name,
        default_victory_cash: victory_cash,
        default_victory_major_cities: victory_major_cities,
        geography,
        mileposts,
        cities,
        edges,
        commodities,
        deck,
    })
}

fn sub_to_world(sx: i32, sy: i32) -> (f32, f32) {
    ((sx as f32 / 4.0) * SQRT3_OVER_2, sy as f32 / 4.0)
}

fn parse_ebm_coord(token: &str) -> Option<(i32, i32, bool)> {
    let split = token.find(|c: char| c.is_ascii_digit())?;
    let letters = &token[..split];
    let digits = &token[split..];
    if letters.is_empty() || digits.is_empty() {
        return None;
    }
    let is_upper = letters.chars().all(|c| c.is_ascii_uppercase());
    let mut x = 0i32;
    for ch in letters.bytes() {
        let up = ch.to_ascii_uppercase();
        if !up.is_ascii_uppercase() {
            return None;
        }
        x = x * 26 + (up - b'A') as i32;
    }
    let y: i32 = digits.parse().ok()?;
    Some((x, y, is_upper))
}

fn slugify(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut prev_us = false;
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            prev_us = false;
        } else if !prev_us && !out.is_empty() {
            out.push('_');
            prev_us = true;
        }
    }
    out.trim_end_matches('_').to_string()
}

fn short_code(name: &str) -> String {
    let up: String = name
        .chars()
        .filter(|c| c.is_ascii_alphabetic())
        .map(|c| c.to_ascii_uppercase())
        .take(3)
        .collect();
    if up.is_empty() {
        "GDS".to_string()
    } else {
        up
    }
}

/// Trace crisp land contours, lake outlines, rivers, and borders directly from the `.ebm` sub-grid.
fn build_ebm_geography(
    w: usize,
    h: usize,
    ocean: &[bool],
    lower_dots: &HashMap<(i32, i32), String>,
) -> MapGeography {
    let (world_w, world_h) = sub_to_world(w as i32, h as i32);

    // 1. Trace outer land polygon from the `ocean` mask using exact grid boundary edges!
    let land_polygons = trace_mask_contours(w, h, |x, y| !ocean[y * w + x]);

    // 2. Detect enclosed lake polygons from 'L' barrier cells (flood-fill interior pockets).
    let mut lake_barrier = vec![false; w * h];
    let lake_pts: HashSet<(i32, i32)> = lower_dots
        .iter()
        .filter(|(_, fl)| fl.contains('L'))
        .map(|(&pt, _)| pt)
        .collect();
    for &(x, y) in &lake_pts {
        if x >= 0 && y >= 0 && (x as usize) < w && (y as usize) < h {
            lake_barrier[y as usize * w + x as usize] = true;
            for dx in -1..=1 {
                for dy in -1..=1 {
                    if lake_pts.contains(&(x + dx, y + dy)) {
                        let bx = x + dx;
                        if bx >= 0 && (bx as usize) < w {
                            lake_barrier[y as usize * w + bx as usize] = true;
                        }
                    }
                }
            }
        }
    }
    let mut not_lake = vec![false; w * h];
    let mut lq = VecDeque::new();
    for x in 0..w {
        for y in [0, h - 1] {
            let idx = y * w + x;
            if !lake_barrier[idx] && !not_lake[idx] {
                not_lake[idx] = true;
                lq.push_back((x, y));
            }
        }
    }
    for y in 0..h {
        for x in [0, w - 1] {
            let idx = y * w + x;
            if !lake_barrier[idx] && !not_lake[idx] {
                not_lake[idx] = true;
                lq.push_back((x, y));
            }
        }
    }
    while let Some((x, y)) = lq.pop_front() {
        for (dx, dy) in [(1isize, 0isize), (-1, 0), (0, 1), (0, -1)] {
            let nx = x as isize + dx;
            let ny = y as isize + dy;
            if nx >= 0 && ny >= 0 && (nx as usize) < w && (ny as usize) < h {
                let nidx = ny as usize * w + nx as usize;
                if !lake_barrier[nidx] && !not_lake[nidx] {
                    not_lake[nidx] = true;
                    lq.push_back((nx as usize, ny as usize));
                }
            }
        }
    }
    let lake_polygons = trace_mask_contours(w, h, |x, y| !not_lake[y * w + x]);

    // 3. Trace Rivers ('R') and Borders ('Y') into smooth polylines!
    let rivers = trace_flag_polylines(lower_dots, 'R', "River");
    let borders = trace_flag_polylines(lower_dots, 'Y', "Border");

    MapGeography {
        width: world_w,
        height: world_h,
        land_polygons,
        lake_polygons,
        rivers,
        borders,
    }
}

/// Trace closed polygon contours of a boolean mask on `w x h` into world coordinates.
fn trace_mask_contours<F>(w: usize, h: usize, is_inside: F) -> Vec<Vec<[f32; 2]>>
where
    F: Fn(usize, usize) -> bool,
{
    // Collect directed boundary edges (with inside on the right / CW) around all inside cells.
    let mut next_map: HashMap<(i32, i32), Vec<(i32, i32)>> = HashMap::new();
    for y in 0..h {
        for x in 0..w {
            if !is_inside(x, y) {
                continue;
            }
            let xi = x as i32;
            let yi = y as i32;
            if y == 0 || !is_inside(x, y - 1) {
                next_map.entry((xi, yi)).or_default().push((xi + 1, yi));
            }
            if x + 1 == w || !is_inside(x + 1, y) {
                next_map
                    .entry((xi + 1, yi))
                    .or_default()
                    .push((xi + 1, yi + 1));
            }
            if y + 1 == h || !is_inside(x, y + 1) {
                next_map
                    .entry((xi + 1, yi + 1))
                    .or_default()
                    .push((xi, yi + 1));
            }
            if x == 0 || !is_inside(x - 1, y) {
                next_map.entry((xi, yi + 1)).or_default().push((xi, yi));
            }
        }
    }

    let mut used: HashSet<((i32, i32), (i32, i32))> = HashSet::new();
    let mut polys: Vec<Vec<[f32; 2]>> = Vec::new();

    let starts: Vec<(i32, i32)> = next_map.keys().copied().collect();
    for start in starts {
        while let Some(nbs) = next_map.get(&start) {
            let Some(&first_next) = nbs.iter().find(|&&n| !used.contains(&(start, n))) else {
                break;
            };

            let mut loop_pts: Vec<(i32, i32)> = vec![start];
            used.insert((start, first_next));
            let mut cur = first_next;
            let mut prev = start;

            while cur != start {
                loop_pts.push(cur);
                let Some(cands) = next_map.get(&cur) else {
                    break;
                };
                // Prefer continuing straight or turning right cleanly.
                let dx = cur.0 - prev.0;
                let dy = cur.1 - prev.1;
                let picked = cands
                    .iter()
                    .copied()
                    .filter(|&n| !used.contains(&(cur, n)))
                    .min_by_key(|&n| {
                        let ndx = n.0 - cur.0;
                        let ndy = n.1 - cur.1;
                        if (ndx, ndy) == (dx, dy) {
                            0
                        } else {
                            1
                        }
                    });
                let Some(nxt) = picked else {
                    break;
                };
                used.insert((cur, nxt));
                prev = cur;
                cur = nxt;
            }

            if loop_pts.len() >= 12 {
                // Remove collinear vertices & lightly smooth corners for crisp cartographic look.
                let mut simplified: Vec<[f32; 2]> = Vec::new();
                let n = loop_pts.len();
                for i in 0..n {
                    let a = loop_pts[(i + n - 1) % n];
                    let b = loop_pts[i];
                    let c = loop_pts[(i + 1) % n];
                    if (b.0 - a.0) * (c.1 - b.1) != (b.1 - a.1) * (c.0 - b.0) {
                        let (wx, wy) = sub_to_world(b.0, b.1);
                        simplified.push([wx, wy]);
                    }
                }
                if simplified.len() >= 4 {
                    polys.push(simplified);
                }
            }
        }
    }

    polys
}

/// Trace 8-connected sub-grid dots bearing `flag` into clean polylines.
fn trace_flag_polylines(
    lower_dots: &HashMap<(i32, i32), String>,
    flag: char,
    label: &str,
) -> Vec<Polyline> {
    let pts: HashSet<(i32, i32)> = lower_dots
        .iter()
        .filter(|(_, fl)| fl.contains(flag))
        .map(|(&pt, _)| pt)
        .collect();

    let mut used_edges: HashSet<((i32, i32), (i32, i32))> = HashSet::new();
    let mut lines: Vec<Polyline> = Vec::new();
    let mut sorted_pts: Vec<(i32, i32)> = pts.iter().copied().collect();
    sorted_pts.sort_unstable();

    let norm_edge = |a: (i32, i32), b: (i32, i32)| if a < b { (a, b) } else { (b, a) };

    for &start in &sorted_pts {
        for dx in -1..=1 {
            for dy in -1..=1 {
                if dx == 0 && dy == 0 {
                    continue;
                }
                let nb = (start.0 + dx, start.1 + dy);
                if !pts.contains(&nb) {
                    continue;
                }
                let ek = norm_edge(start, nb);
                if used_edges.contains(&ek) {
                    continue;
                }
                // Trace a chain greedily
                used_edges.insert(ek);
                let mut chain = vec![start, nb];
                let mut cur = nb;
                loop {
                    let mut next_pick = None;
                    for ndx in -1..=1 {
                        for ndy in -1..=1 {
                            if ndx == 0 && ndy == 0 {
                                continue;
                            }
                            let cand = (cur.0 + ndx, cur.1 + ndy);
                            if pts.contains(&cand) && !used_edges.contains(&norm_edge(cur, cand)) {
                                next_pick = Some(cand);
                                break;
                            }
                        }
                        if next_pick.is_some() {
                            break;
                        }
                    }
                    let Some(nxt) = next_pick else {
                        break;
                    };
                    used_edges.insert(norm_edge(cur, nxt));
                    chain.push(nxt);
                    cur = nxt;
                }
                let points: Vec<[f32; 2]> = chain
                    .into_iter()
                    .map(|(x, y)| {
                        let (wx, wy) = sub_to_world(x, y);
                        [wx, wy]
                    })
                    .collect();
                lines.push(Polyline {
                    name: label.to_string(),
                    points,
                });
            }
        }
    }

    lines
}
