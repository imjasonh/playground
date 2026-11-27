use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};

pub type MilepostId = u16;
pub type PlayerId = u8;

/// Canonical undirected edge key `(min, max)`.
pub fn edge_key(a: MilepostId, b: MilepostId) -> (MilepostId, MilepostId) {
    if a < b {
        (a, b)
    } else {
        (b, a)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Terrain {
    Clear,
    Mountain,
    Alpine,
    SmallCity,
    MediumCity,
    MajorCity,
}

impl Terrain {
    pub fn build_cost(self) -> u32 {
        match self {
            Terrain::Clear => 1,
            Terrain::Mountain => 2,
            Terrain::Alpine => 5,
            Terrain::SmallCity => 3,
            Terrain::MediumCity => 3,
            Terrain::MajorCity => 5,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CitySize {
    Small,
    Medium,
    Major,
}

impl CitySize {
    pub fn max_players(self) -> Option<usize> {
        match self {
            CitySize::Small => Some(2),
            CitySize::Medium => Some(3),
            CitySize::Major => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    Normal,
    River,
    Inlet,
}

impl EdgeKind {
    pub fn surcharge(self) -> u32 {
        match self {
            EdgeKind::Normal => 0,
            EdgeKind::River => 2,
            EdgeKind::Inlet => 3,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Milepost {
    pub id: MilepostId,
    pub col: u16,
    pub row: u16,
    pub x: f32,
    pub y: f32,
    pub terrain: Terrain,
    pub city_id: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct City {
    pub id: String,
    pub name: String,
    pub size: CitySize,
    pub center_mp: MilepostId,
    pub mileposts: Vec<MilepostId>,
    pub commodities: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeDef {
    pub a: MilepostId,
    pub b: MilepostId,
    pub kind: EdgeKind,
    #[serde(default)]
    pub river_name: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Commodity {
    pub id: String,
    pub name: String,
    pub short: String,
    pub chips: u8,
    pub color: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DemandEntry {
    pub commodity: String,
    pub city_id: String,
    pub payout: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum EventEffect {
    /// Trains within `radius` mileposts of any listed city lose their next turn and drop 1 load.
    Derailment { cities: Vec<String>, radius: u8 },
    /// Washes out bridges (river edges) within `radius` of `city_id` and blocks crossing until next turn.
    Flood {
        river_name: String,
        city_id: String,
        radius: u8,
    },
    /// Trains within `radius` move at half speed; optional terrain blocked for building/moving.
    Storm {
        city_id: String,
        radius: u8,
        block_terrain: Option<Terrain>,
    },
    /// Blocks pickup/delivery/building/movement within `radius` of listed cities for 1 round.
    Strike { cities: Vec<String>, radius: u8 },
    /// Players with >= $50M pay progressive tax (skipped in Fast Mode).
    RailTax,
    /// Persistent bonus demand available to all players until fulfilled.
    HeatingFuelShortage {
        commodity: String,
        target_cities: Vec<String>,
        bonus: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Card {
    Demand {
        id: u16,
        demands: [DemandEntry; 3],
    },
    Event {
        id: u16,
        title: String,
        description: String,
        effect: EventEffect,
    },
}

impl Card {
    pub fn id(&self) -> u16 {
        match self {
            Card::Demand { id, .. } | Card::Event { id, .. } => *id,
        }
    }

    pub fn is_event(&self) -> bool {
        matches!(self, Card::Event { .. })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Polyline {
    pub name: String,
    pub points: Vec<[f32; 2]>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MapGeography {
    pub width: f32,
    pub height: f32,
    pub land_polygons: Vec<Vec<[f32; 2]>>,
    pub lake_polygons: Vec<Vec<[f32; 2]>>,
    pub rivers: Vec<Polyline>,
    pub borders: Vec<Polyline>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MapData {
    pub id: String,
    pub name: String,
    pub default_victory_cash: u32,
    pub default_victory_major_cities: usize,
    pub geography: MapGeography,
    pub mileposts: Vec<Milepost>,
    pub cities: Vec<City>,
    pub edges: Vec<EdgeDef>,
    pub commodities: Vec<Commodity>,
    pub deck: Vec<Card>,
}

impl MapData {
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }
}

/// Runtime index over `MapData` for O(1) lookups and fast pathfinding.
#[derive(Debug, Clone)]
pub struct MapIndex {
    pub data: MapData,
    pub adj: Vec<Vec<(MilepostId, EdgeKind)>>,
    pub edge_map: HashMap<(MilepostId, MilepostId), EdgeDef>,
    pub city_by_id: HashMap<String, usize>,
    pub commodity_by_id: HashMap<String, usize>,
    pub commodity_sources: HashMap<String, Vec<String>>,
    pub major_city_ids: Vec<String>,
}

impl MapIndex {
    pub fn new(data: MapData) -> Self {
        let n = data.mileposts.len();
        let mut adj = vec![Vec::new(); n];
        let mut edge_map = HashMap::with_capacity(data.edges.len());

        for e in &data.edges {
            let key = edge_key(e.a, e.b);
            adj[e.a as usize].push((e.b, e.kind));
            adj[e.b as usize].push((e.a, e.kind));
            edge_map.insert(key, e.clone());
        }

        let mut city_by_id = HashMap::new();
        let mut commodity_sources: HashMap<String, Vec<String>> = HashMap::new();
        let mut major_city_ids = Vec::new();

        for (idx, c) in data.cities.iter().enumerate() {
            city_by_id.insert(c.id.clone(), idx);
            if c.size == CitySize::Major {
                major_city_ids.push(c.id.clone());
            }
            for comm in &c.commodities {
                commodity_sources
                    .entry(comm.clone())
                    .or_default()
                    .push(c.id.clone());
            }
        }

        let mut commodity_by_id = HashMap::new();
        for (idx, c) in data.commodities.iter().enumerate() {
            commodity_by_id.insert(c.id.clone(), idx);
        }

        Self {
            data,
            adj,
            edge_map,
            city_by_id,
            commodity_by_id,
            commodity_sources,
            major_city_ids,
        }
    }

    pub fn milepost(&self, id: MilepostId) -> Option<&Milepost> {
        self.data.mileposts.get(id as usize)
    }

    pub fn city(&self, id: &str) -> Option<&City> {
        self.city_by_id.get(id).map(|&i| &self.data.cities[i])
    }

    pub fn city_at(&self, mp: MilepostId) -> Option<&City> {
        self.milepost(mp)
            .and_then(|m| m.city_id.as_deref())
            .and_then(|cid| self.city(cid))
    }

    pub fn is_same_major_city(&self, a: MilepostId, b: MilepostId) -> bool {
        match (self.city_at(a), self.city_at(b)) {
            (Some(ca), Some(cb)) => ca.size == CitySize::Major && ca.id == cb.id,
            _ => false,
        }
    }

    /// Cost of building track from `from` to `to` (directed because destination terrain determines base cost).
    pub fn build_step_cost(&self, from: MilepostId, to: MilepostId) -> Option<u32> {
        let edge = self.edge_map.get(&edge_key(from, to))?;
        if self.is_same_major_city(from, to) {
            return Some(0);
        }
        let dest = self.milepost(to)?;
        Some(dest.terrain.build_cost() + edge.kind.surcharge())
    }

    /// Shortest hex-hop distance from `city_id`'s mileposts to every milepost within `max_radius`.
    pub fn mileposts_within_radius(&self, city_id: &str, max_radius: u8) -> HashSet<MilepostId> {
        let mut visited = HashSet::new();
        let Some(city) = self.city(city_id) else {
            return visited;
        };
        let mut queue = std::collections::VecDeque::new();
        for &mp in &city.mileposts {
            visited.insert(mp);
            queue.push_back((mp, 0u8));
        }
        while let Some((cur, d)) = queue.pop_front() {
            if d >= max_radius {
                continue;
            }
            for &(next, _) in &self.adj[cur as usize] {
                if visited.insert(next) {
                    queue.push_back((next, d + 1));
                }
            }
        }
        visited
    }

    /// Single-pass Dijkstra computing exact minimum build cost from `sources` to every milepost.
    pub fn build_costs_from<F>(
        &self,
        sources: &[MilepostId],
        owned_edges: &HashSet<(MilepostId, MilepostId)>,
        blocked_edges: &HashSet<(MilepostId, MilepostId)>,
        blocked_nodes: &HashSet<MilepostId>,
        can_enter_city: F,
    ) -> Vec<u32>
    where
        F: Fn(&str) -> bool,
    {
        let n = self.data.mileposts.len();
        let mut dist = vec![u32::MAX; n];
        let mut heap = BinaryHeap::new();

        for &s in sources {
            if (s as usize) < n {
                dist[s as usize] = 0;
                heap.push(StateCost { cost: 0, node: s });
            }
        }

        while let Some(StateCost { cost, node }) = heap.pop() {
            if cost > dist[node as usize] {
                continue;
            }
            if let Some(c) = self.city_at(node) {
                if c.size == CitySize::Major {
                    for &other in &c.mileposts {
                        if other != node && cost < dist[other as usize] {
                            dist[other as usize] = cost;
                            heap.push(StateCost { cost, node: other });
                        }
                    }
                }
            }
            for &(next, _) in &self.adj[node as usize] {
                let ek = edge_key(node, next);
                let is_owned = owned_edges.contains(&ek);
                let same_major = self.is_same_major_city(node, next);
                if !is_owned && !same_major {
                    if blocked_edges.contains(&ek)
                        || blocked_nodes.contains(&node)
                        || blocked_nodes.contains(&next)
                    {
                        continue;
                    }
                    if let Some(dest_city) = self.city_at(next) {
                        if !can_enter_city(&dest_city.id) {
                            continue;
                        }
                    }
                }
                let step = if is_owned || same_major {
                    0
                } else {
                    match self.build_step_cost(node, next) {
                        Some(c) => c,
                        None => continue,
                    }
                };
                let next_cost = cost.saturating_add(step);
                if next_cost < dist[next as usize] {
                    dist[next as usize] = next_cost;
                    heap.push(StateCost {
                        cost: next_cost,
                        node: next,
                    });
                }
            }
        }
        dist
    }

    /// Shortest build path from any node in `sources` to `target` using Dijkstra.
    /// Returns `(ordered_edges, total_cost)` excluding already-owned edges and free major-city internal edges.
    pub fn shortest_build_path<F>(
        &self,
        sources: &[MilepostId],
        target: MilepostId,
        owned_edges: &HashSet<(MilepostId, MilepostId)>,
        blocked_edges: &HashSet<(MilepostId, MilepostId)>,
        blocked_nodes: &HashSet<MilepostId>,
        can_enter_city: F,
    ) -> Option<(Vec<(MilepostId, MilepostId)>, u32)>
    where
        F: Fn(&str) -> bool,
    {
        if sources.is_empty() || (target as usize) >= self.data.mileposts.len() {
            return None;
        }
        let n = self.data.mileposts.len();
        let mut dist = vec![u32::MAX; n];
        let mut prev: Vec<Option<MilepostId>> = vec![None; n];
        let mut heap = BinaryHeap::new();

        for &s in sources {
            if (s as usize) < n {
                dist[s as usize] = 0;
                heap.push(StateCost { cost: 0, node: s });
            }
        }

        // If target is a major city, reaching any milepost of that major city suffices.
        let target_major_id = self
            .city_at(target)
            .filter(|c| c.size == CitySize::Major)
            .map(|c| c.id.as_str());

        let mut reached = None;

        while let Some(StateCost { cost, node }) = heap.pop() {
            if cost > dist[node as usize] {
                continue;
            }
            if node == target
                || target_major_id.is_some_and(|mid| {
                    self.city_at(node)
                        .is_some_and(|c| c.size == CitySize::Major && c.id == mid)
                })
            {
                reached = Some(node);
                break;
            }

            // Free traversal inside a major city red zone.
            if let Some(c) = self.city_at(node) {
                if c.size == CitySize::Major {
                    for &other in &c.mileposts {
                        if other != node && cost < dist[other as usize] {
                            dist[other as usize] = cost;
                            prev[other as usize] = Some(node);
                            heap.push(StateCost { cost, node: other });
                        }
                    }
                }
            }

            for &(next, _) in &self.adj[node as usize] {
                let ek = edge_key(node, next);
                let is_owned = owned_edges.contains(&ek);
                let same_major = self.is_same_major_city(node, next);

                if !is_owned && !same_major {
                    if blocked_edges.contains(&ek)
                        || blocked_nodes.contains(&node)
                        || blocked_nodes.contains(&next)
                    {
                        continue;
                    }
                    if let Some(dest_city) = self.city_at(next) {
                        if !can_enter_city(&dest_city.id) {
                            continue;
                        }
                    }
                }

                let step = if is_owned || same_major {
                    0
                } else {
                    match self.build_step_cost(node, next) {
                        Some(c) => c,
                        None => continue,
                    }
                };
                let next_cost = cost.saturating_add(step);
                if next_cost < dist[next as usize] {
                    dist[next as usize] = next_cost;
                    prev[next as usize] = Some(node);
                    heap.push(StateCost {
                        cost: next_cost,
                        node: next,
                    });
                }
            }
        }

        let end = reached?;
        let total_cost = dist[end as usize];
        let mut chain = Vec::new();
        let mut cur = end;
        while let Some(p) = prev[cur as usize] {
            let ek = edge_key(p, cur);
            if !owned_edges.contains(&ek) && !self.is_same_major_city(p, cur) {
                chain.push((p, cur));
            }
            cur = p;
        }
        chain.reverse();
        Some((chain, total_cost))
    }

    /// Shortest movement path along built tracks (own + optional opponent trackage rights).
    /// Returns `(path_including_start, hops, newly_used_opponents, additional_fee)`.
    #[allow(clippy::too_many_arguments)]
    pub fn shortest_move_path(
        &self,
        start: MilepostId,
        target: MilepostId,
        player_id: PlayerId,
        edge_owners: &HashMap<(MilepostId, MilepostId), Vec<PlayerId>>,
        blocked_edges: &HashSet<(MilepostId, MilepostId)>,
        blocked_nodes: &HashSet<MilepostId>,
        max_hops: u32,
        already_paid_mask: u8,
        max_additional_fee: u32,
        trackage_fee_per_opponent: u32,
    ) -> Option<MovePathResult> {
        if start == target {
            return Some(MovePathResult {
                path: vec![start],
                hops: 0,
                new_opponents: Vec::new(),
                additional_fee: 0,
            });
        }

        // State is (node, paid_mask). Prioritize fewest hops, then lowest additional fee.
        let mut dist: HashMap<(MilepostId, u8), (u32, u32)> = HashMap::new();
        let mut prev: HashMap<(MilepostId, u8), (MilepostId, u8)> = HashMap::new();
        let mut heap = BinaryHeap::new();

        let init = (start, already_paid_mask);
        dist.insert(init, (0, 0));
        heap.push(MoveState {
            hops: 0,
            fee: 0,
            node: start,
            mask: already_paid_mask,
        });

        let mut best_goal: Option<(MilepostId, u8)> = None;

        while let Some(cur) = heap.pop() {
            let key = (cur.node, cur.mask);
            if let Some(&(best_h, best_f)) = dist.get(&key) {
                if (cur.hops, cur.fee) > (best_h, best_f) {
                    continue;
                }
            }
            if cur.node == target {
                best_goal = Some(key);
                break;
            }
            if cur.hops >= max_hops {
                continue;
            }

            for &(next, _) in &self.adj[cur.node as usize] {
                let ek = edge_key(cur.node, next);
                let same_major = self.is_same_major_city(cur.node, next);

                if !same_major
                    && (blocked_edges.contains(&ek)
                        || blocked_nodes.contains(&cur.node)
                        || blocked_nodes.contains(&next))
                {
                    continue;
                }

                let next_hops = cur.hops + 1;
                if next_hops > max_hops {
                    continue;
                }

                // Determine track ownership options for this step.
                if same_major {
                    let nk = (next, cur.mask);
                    let cand = (next_hops, cur.fee);
                    if dist.get(&nk).is_none_or(|&old| cand < old) {
                        dist.insert(nk, cand);
                        prev.insert(nk, key);
                        heap.push(MoveState {
                            hops: next_hops,
                            fee: cur.fee,
                            node: next,
                            mask: cur.mask,
                        });
                    }
                    continue;
                }

                let Some(owners) = edge_owners.get(&ek) else {
                    continue;
                };

                if owners.contains(&player_id) {
                    let nk = (next, cur.mask);
                    let cand = (next_hops, cur.fee);
                    if dist.get(&nk).is_none_or(|&old| cand < old) {
                        dist.insert(nk, cand);
                        prev.insert(nk, key);
                        heap.push(MoveState {
                            hops: next_hops,
                            fee: cur.fee,
                            node: next,
                            mask: cur.mask,
                        });
                    }
                } else {
                    for &opp in owners {
                        let bit = 1u8 << opp;
                        let (next_mask, next_fee) = if (cur.mask & bit) != 0 {
                            (cur.mask, cur.fee)
                        } else {
                            (cur.mask | bit, cur.fee + trackage_fee_per_opponent)
                        };
                        if next_fee > max_additional_fee {
                            continue;
                        }
                        let nk = (next, next_mask);
                        let cand = (next_hops, next_fee);
                        if dist.get(&nk).is_none_or(|&old| cand < old) {
                            dist.insert(nk, cand);
                            prev.insert(nk, key);
                            heap.push(MoveState {
                                hops: next_hops,
                                fee: next_fee,
                                node: next,
                                mask: next_mask,
                            });
                        }
                    }
                }
            }
        }

        let goal = best_goal?;
        let &(hops, additional_fee) = dist.get(&goal)?;
        let mut path = Vec::with_capacity(hops as usize + 1);
        let mut cur = goal;
        path.push(cur.0);
        while let Some(&p) = prev.get(&cur) {
            path.push(p.0);
            cur = p;
        }
        path.reverse();

        let newly_paid_bits = goal.1 & !already_paid_mask;
        let mut new_opponents = Vec::new();
        for opp in 0..8u8 {
            if (newly_paid_bits & (1u8 << opp)) != 0 {
                new_opponents.push(opp);
            }
        }

        Some(MovePathResult {
            path,
            hops,
            new_opponents,
            additional_fee,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MovePathResult {
    pub path: Vec<MilepostId>,
    pub hops: u32,
    pub new_opponents: Vec<PlayerId>,
    pub additional_fee: u32,
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct StateCost {
    cost: u32,
    node: MilepostId,
}

impl Ord for StateCost {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for StateCost {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct MoveState {
    hops: u32,
    fee: u32,
    node: MilepostId,
    mask: u8,
}

impl Ord for MoveState {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .hops
            .cmp(&self.hops)
            .then_with(|| other.fee.cmp(&self.fee))
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for MoveState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
