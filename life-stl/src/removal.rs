//! Post-generate analysis: can a human practically remove the breakaway supports?
//!
//! Heuristics (not a full reachability sim):
//! - **Rest-on-model**: branch ends on a Life roof instead of the bed → often
//!   welded into overhangs and hard/impossible to extract.
//! - **Trapped trunks**: vertical trunk has no clear lateral escape to the
//!   model perimeter through empty cells → support cage inside the sculpture.
//! - **Inaccessible tips**: the empty cell under a tip cannot reach the
//!   perimeter without crossing Life → snap point is in a pocket.
//! - **Dense tip field**: too many contacts per bed area → cleanup nightmare.
//!
//! Score is 0–100 (higher = easier). [`SupportRemovabilityReport::ok`] is the
//! gate used by seed search / CLI exit codes.

use crate::config::RemovalParams;
use crate::support::{Landing, PathKind, RoutedPath, SupportTip};
use crate::volume::{CellKind, Volume};

/// Removability verdict for a support set.
#[derive(Debug, Clone, PartialEq)]
pub struct SupportRemovabilityReport {
    /// 0 = impossible / awful, 100 = trivial (or no supports).
    pub score: f32,
    /// True when score ≥ min and hard-fail conditions are absent.
    pub ok: bool,
    pub tip_count: usize,
    pub trunk_count: usize,
    pub rest_on_model_count: usize,
    pub free_stop_count: usize,
    pub trapped_trunk_count: usize,
    pub inaccessible_tip_count: usize,
    /// Short human reasons (empty when ok).
    pub reasons: Vec<String>,
}

impl Default for SupportRemovabilityReport {
    fn default() -> Self {
        Self {
            score: 100.0,
            ok: true,
            tip_count: 0,
            trunk_count: 0,
            rest_on_model_count: 0,
            free_stop_count: 0,
            trapped_trunk_count: 0,
            inaccessible_tip_count: 0,
            reasons: Vec::new(),
        }
    }
}

/// Analyze routed supports for practical post-print cleanup.
pub fn analyze_removability(
    volume: &Volume,
    tips: &[SupportTip],
    paths: &[RoutedPath],
    cell_mm: f32,
    params: &RemovalParams,
) -> SupportRemovabilityReport {
    if tips.is_empty() && paths.is_empty() {
        return SupportRemovabilityReport::default();
    }

    let mut rest_on_model = 0usize;
    let mut free_stop = 0usize;
    let mut trunk_count = 0usize;
    for p in paths {
        match p.kind {
            PathKind::Trunk => trunk_count += 1,
            PathKind::Branch => match p.landing {
                Landing::RestOnModel => rest_on_model += 1,
                Landing::FreeStop => free_stop += 1,
                Landing::Bed | Landing::TrunkJoin => {}
            },
        }
    }

    let trapped = count_trapped_trunks(volume, paths, cell_mm);
    let inaccessible = count_inaccessible_tips(volume, tips);
    let bed_area = (volume.width * volume.height).max(1) as f32;
    let tip_density = tips.len() as f32 / bed_area; // tips per cell footprint

    let mut score = 100.0f32;
    let mut reasons = Vec::new();

    if rest_on_model > 0 {
        // Rest-on-model branches are double-tapered (needle contact at both
        // ends), so a few are practical to snap off; many still hurt.
        let pen = (12.0 * rest_on_model as f32).min(45.0);
        score -= pen;
        reasons.push(format!(
            "{rest_on_model} support(s) rest on the model instead of the bed \
             (double-tapered, but still extra cleanup)"
        ));
    }
    if free_stop > 0 {
        let pen = (10.0 * free_stop as f32).min(30.0);
        score -= pen;
        reasons.push(format!(
            "{free_stop} support(s) stop in free space above a blockage \
             (may not reach the bed)"
        ));
    }
    if trapped > 0 {
        let pen = (30.0 * trapped as f32).min(60.0);
        score -= pen;
        reasons.push(format!(
            "{trapped} trunk(s) trapped inside Life cavities \
             (no clear lateral escape to the perimeter)"
        ));
    }
    if inaccessible > 0 {
        let frac = inaccessible as f32 / tips.len().max(1) as f32;
        let pen = (20.0 * frac * 100.0 / 15.0).min(40.0); // scale with fraction
        score -= pen;
        reasons.push(format!(
            "{inaccessible}/{} tip contact(s) sit in enclosed pockets \
             (tool cannot reach the snap point)",
            tips.len()
        ));
    }
    // Dense tip field: >0.15 tips/cell is already quite busy on a 16×16 board.
    if tip_density > params.max_tip_density {
        let over = tip_density / params.max_tip_density;
        let pen = (15.0 * (over - 1.0)).min(25.0);
        score -= pen;
        reasons.push(format!(
            "dense tip field ({tip_density:.3} tips/cell > max {:.3})",
            params.max_tip_density
        ));
    }

    score = score.clamp(0.0, 100.0);

    let hard_fail = (!params.allow_rest_on_model && rest_on_model > params.max_rest_on_model)
        || trapped > 0
        || (inaccessible as f32 / tips.len().max(1) as f32) > params.max_inaccessible_tip_fraction;

    let ok = score + 1e-3 >= params.min_score && !hard_fail;

    if !ok && score + 1e-3 < params.min_score {
        reasons.push(format!(
            "removability score {score:.0} below minimum {:.0}",
            params.min_score
        ));
    } else if !ok && reasons.is_empty() {
        reasons.push("support cleanup gate failed".into());
    }

    SupportRemovabilityReport {
        score,
        ok,
        tip_count: tips.len(),
        trunk_count,
        rest_on_model_count: rest_on_model,
        free_stop_count: free_stop,
        trapped_trunk_count: trapped,
        inaccessible_tip_count: inaccessible,
        reasons,
    }
}

/// A trunk is "trapped" if, at mid-height, empty cells around it cannot reach
/// the volume perimeter without crossing Life (4-connected BFS).
fn count_trapped_trunks(volume: &Volume, paths: &[RoutedPath], cell_mm: f32) -> usize {
    let mut n = 0usize;
    for p in paths {
        if p.kind != PathKind::Trunk || p.points.len() < 2 {
            continue;
        }
        let top = p.points[0];
        let bot = *p.points.last().unwrap();
        let mid_z = 0.5 * (top[2] + bot[2]);
        let z_cell =
            ((mid_z / cell_mm).floor() as isize).clamp(0, volume.depth as isize - 1) as usize;
        let cx = ((top[0] / cell_mm).floor() as isize).clamp(0, volume.width as isize - 1) as usize;
        let cy =
            ((top[1] / cell_mm).floor() as isize).clamp(0, volume.height as isize - 1) as usize;
        // Trunk itself should be in empty/non-Life; if Life occupies the cell, trapped.
        if volume.get(cx, cy, z_cell) == CellKind::Life {
            n += 1;
            continue;
        }
        if !empty_reaches_perimeter(volume, cx, cy, z_cell) {
            n += 1;
        }
    }
    n
}

fn count_inaccessible_tips(volume: &Volume, tips: &[SupportTip]) -> usize {
    let mut n = 0usize;
    for tip in tips {
        if tip.cell_z == 0 {
            continue;
        }
        let z = tip.cell_z - 1; // empty cell the tip sits in
        if volume.get(tip.cell_x, tip.cell_y, z) == CellKind::Life {
            n += 1;
            continue;
        }
        if !empty_reaches_perimeter(volume, tip.cell_x, tip.cell_y, z) {
            n += 1;
        }
    }
    n
}

/// 4-connected BFS through non-Life cells on a single Z layer to the border.
fn empty_reaches_perimeter(volume: &Volume, sx: usize, sy: usize, z: usize) -> bool {
    let w = volume.width;
    let h = volume.height;
    if sx >= w || sy >= h || z >= volume.depth {
        return false;
    }
    if volume.get(sx, sy, z) == CellKind::Life {
        return false;
    }
    // Already on perimeter of the grid → reachable for tool access from outside.
    if sx == 0 || sy == 0 || sx + 1 == w || sy + 1 == h {
        return true;
    }

    let mut seen = vec![false; w * h];
    let mut q = std::collections::VecDeque::new();
    let idx = |x: usize, y: usize| y * w + x;
    seen[idx(sx, sy)] = true;
    q.push_back((sx, sy));

    while let Some((x, y)) = q.pop_front() {
        if x == 0 || y == 0 || x + 1 == w || y + 1 == h {
            return true;
        }
        for (nx, ny) in [
            (x.wrapping_sub(1), y),
            (x + 1, y),
            (x, y.wrapping_sub(1)),
            (x, y + 1),
        ] {
            if nx >= w || ny >= h {
                continue;
            }
            let i = idx(nx, ny);
            if seen[i] {
                continue;
            }
            if volume.get(nx, ny, z) == CellKind::Life {
                continue;
            }
            seen[i] = true;
            q.push_back((nx, ny));
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::RemovalParams;
    use crate::support::{Landing, PathKind, RoutedPath, SupportTip};
    use crate::volume::{CellKind, Volume};

    #[test]
    fn no_supports_is_easy() {
        let v = Volume::new(4, 4, 4);
        let r = analyze_removability(&v, &[], &[], 4.0, &RemovalParams::default());
        assert!(r.ok);
        assert_eq!(r.score, 100.0);
    }

    #[test]
    fn few_rest_on_model_pass_many_fail() {
        let v = Volume::new(4, 4, 4);
        let make = |x: f32| {
            (
                SupportTip {
                    cell_x: 1,
                    cell_y: 1,
                    cell_z: 2,
                    tip: [x, 6.0, 8.0],
                },
                RoutedPath {
                    points: vec![[x, 6.0, 8.0], [x, 6.0, 4.2]],
                    kind: PathKind::Branch,
                    shaft_radius_mm: 0.6,
                    landing: Landing::RestOnModel,
                },
            )
        };

        // Default allows up to 2 rest-on-model landings (double-tapered).
        let (t1, p1) = make(6.0);
        let r = analyze_removability(&v, &[t1], &[p1], 4.0, &RemovalParams::default());
        assert!(r.ok, "{:?}", r.reasons);
        assert_eq!(r.rest_on_model_count, 1);
        assert!(r.score < 100.0, "still penalized");

        // Three exceeds max_rest_on_model = 2 → hard fail.
        let pairs: Vec<_> = [2.0f32, 6.0, 10.0].iter().map(|&x| make(x)).collect();
        let tips: Vec<_> = pairs.iter().map(|(t, _)| *t).collect();
        let paths: Vec<_> = pairs.iter().map(|(_, p)| p.clone()).collect();
        let r3 = analyze_removability(&v, &tips, &paths, 4.0, &RemovalParams::default());
        assert!(!r3.ok);
        assert_eq!(r3.rest_on_model_count, 3);

        // Strict setting restores the old behavior.
        let strict = RemovalParams {
            max_rest_on_model: 0,
            ..RemovalParams::default()
        };
        let (t1, p1) = make(6.0);
        let r_strict = analyze_removability(&v, &[t1], &[p1], 4.0, &strict);
        assert!(!r_strict.ok);
    }

    #[test]
    fn enclosed_pocket_tip_is_inaccessible() {
        // 5×5 layer with a ring of Life around an empty center at z=1.
        let mut v = Volume::new(5, 5, 3);
        for y in 0..5 {
            for x in 0..5 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        for y in 1..4 {
            for x in 1..4 {
                if x == 2 && y == 2 {
                    continue;
                }
                v.set(x, y, 1, CellKind::Life);
            }
        }
        // Tip above the pocket center.
        v.set(2, 2, 2, CellKind::Life);
        let tip = SupportTip {
            cell_x: 2,
            cell_y: 2,
            cell_z: 2,
            tip: [10.0, 10.0, 8.0],
        };
        assert_eq!(count_inaccessible_tips(&v, &[tip]), 1);
    }
}
