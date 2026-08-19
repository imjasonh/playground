//! Draw a maze (and prefixes of its solution) into an 800×480 packed 1-bit frame.

use crate::panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};

use super::{Cell, Maze};

/// Pixel layout for a maze on the panel. Independent of how walls were carved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub cols: u16,
    pub rows: u16,
    pub origin_x: u32,
    pub origin_y: u32,
    /// Cell pitch including the north/west wall strip.
    pub cell: u32,
    pub wall: u32,
}

/// Byte-aligned window for a partial refresh (`x` and `width` multiples of 8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteRect {
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
}

impl ByteRect {
    pub fn byte_count(self) -> usize {
        (self.width as usize / 8) * self.height as usize
    }

    /// Intersect with the panel. `None` when the window would be empty.
    pub fn clamped(self) -> Option<Self> {
        if self.x >= PANEL_WIDTH || self.y >= PANEL_HEIGHT {
            return None;
        }
        if self.x % 8 != 0 || self.width % 8 != 0 || self.width == 0 || self.height == 0 {
            return None;
        }
        let width = (self.width.min(PANEL_WIDTH - self.x) / 8) * 8;
        let height = self.height.min(PANEL_HEIGHT - self.y);
        if width == 0 || height == 0 {
            return None;
        }
        Some(Self {
            x: self.x,
            y: self.y,
            width,
            height,
        })
    }
}

/// Center a `cols`×`rows` maze on the panel with thick enough walls for e-ink.
///
/// Cell pitch is the largest square that still fits: this never returns a
/// layout whose bounds exceed the panel, even for very dense grids.
pub fn layout_for(cols: u16, rows: u16) -> Layout {
    const WALL: u32 = 3;
    let cols_u = u32::from(cols.max(2));
    let rows_u = u32::from(rows.max(2));
    let cell_w = (PANEL_WIDTH - WALL) / cols_u;
    let cell_h = (PANEL_HEIGHT - WALL) / rows_u;
    let cell = cell_w.min(cell_h).max(1);
    let wall = WALL.min(cell);
    let total_w = cols_u
        .saturating_mul(cell)
        .saturating_add(wall)
        .min(PANEL_WIDTH);
    let total_h = rows_u
        .saturating_mul(cell)
        .saturating_add(wall)
        .min(PANEL_HEIGHT);
    Layout {
        cols: cols_u as u16,
        rows: rows_u as u16,
        origin_x: (PANEL_WIDTH - total_w) / 2,
        origin_y: (PANEL_HEIGHT - total_h) / 2,
        cell,
        wall,
    }
}

/// Packed 1-bit framebuffer of the empty maze (walls + start/end markers).
pub fn render_empty(maze: &Maze, layout: &Layout) -> Vec<u8> {
    render_progress(maze, layout, &[], 0)
}

/// Packed 1-bit framebuffer of the maze plus the first `shown` cells of `path`.
///
/// `shown == 0` is the empty maze. Only cells on `path` are filled — never a
/// search frontier or a dead end.
pub fn render_progress(maze: &Maze, layout: &Layout, path: &[Cell], shown: usize) -> Vec<u8> {
    let mut frame = vec![0xffu8; FRAME_BYTES];
    paint_maze(&mut frame, maze, layout);
    paint_markers(&mut frame, maze, layout);
    let n = shown.min(path.len());
    if n > 0 {
        paint_path(&mut frame, layout, &path[..n]);
    }
    frame
}

/// Byte-aligned dirty window covering path cells `from..to` (and their connectors).
pub fn dirty_rect(layout: &Layout, path: &[Cell], from: usize, to: usize) -> ByteRect {
    let to = to.min(path.len());
    let from = from.min(to);
    let mut x0 = PANEL_WIDTH;
    let mut y0 = PANEL_HEIGHT;
    let mut x1 = 0u32;
    let mut y1 = 0u32;

    let mut include = |x: u32, y: u32, w: u32, h: u32| {
        if w == 0 || h == 0 {
            return;
        }
        x0 = x0.min(x);
        y0 = y0.min(y);
        x1 = x1.max(x.saturating_add(w));
        y1 = y1.max(y.saturating_add(h));
    };

    if from < to {
        for cell in &path[from..to] {
            let (x, y, w, h) = path_blob(layout, *cell);
            include(x, y, w, h);
        }
        let start_edge = from.saturating_sub(1);
        for pair in path[start_edge..to].windows(2) {
            if let Some((x, y, w, h)) = path_connector(layout, pair[0], pair[1]) {
                include(x, y, w, h);
            }
        }
    }

    if x1 <= x0 || y1 <= y0 {
        return align_byte_rect(layout.origin_x, layout.origin_y, layout.wall, layout.wall);
    }
    const PAD: u32 = 2;
    let x = x0.saturating_sub(PAD);
    let y = y0.saturating_sub(PAD);
    let w = (x1 + PAD).saturating_sub(x);
    let h = (y1 + PAD).saturating_sub(y);
    align_byte_rect(x, y, w, h)
}

/// Copy the packed bytes of `rect` out of a full panel framebuffer.
///
/// Out-of-bounds windows yield an empty buffer instead of panicking.
pub fn crop_packed(frame: &[u8], rect: ByteRect) -> Vec<u8> {
    let Some(rect) = rect.clamped() else {
        return Vec::new();
    };
    if frame.len() != FRAME_BYTES {
        return Vec::new();
    }
    let row_bytes = (PANEL_WIDTH / 8) as usize;
    let x_byte = (rect.x / 8) as usize;
    let w_bytes = (rect.width / 8) as usize;
    let mut out = Vec::with_capacity(rect.byte_count());
    for row in 0..rect.height {
        let y = (rect.y + row) as usize;
        let start = y * row_bytes + x_byte;
        out.extend_from_slice(&frame[start..start + w_bytes]);
    }
    out
}

fn paint_maze(frame: &mut [u8], maze: &Maze, layout: &Layout) {
    debug_assert_eq!(layout.cols, maze.cols);
    debug_assert_eq!(layout.rows, maze.rows);
    let (bx, by, bw, bh) = maze_bounds(layout);
    fill_rect(frame, bx, by, bw, bh, true);
    for y in 0..maze.rows {
        for x in 0..maze.cols {
            let (ix, iy, iw, ih) = interior(layout, Cell::new(x, y));
            fill_rect(frame, ix, iy, iw, ih, false);
            if x + 1 < maze.cols && !maze.has_east_wall(x, y) {
                let (dx, dy, dw, dh) = east_door(layout, Cell::new(x, y));
                fill_rect(frame, dx, dy, dw, dh, false);
            }
            if y + 1 < maze.rows && !maze.has_south_wall(x, y) {
                let (dx, dy, dw, dh) = south_door(layout, Cell::new(x, y));
                fill_rect(frame, dx, dy, dw, dh, false);
            }
        }
    }
}

fn paint_markers(frame: &mut [u8], maze: &Maze, layout: &Layout) {
    let (ix, iy, iw, ih) = interior(layout, maze.start);
    let m = (iw.min(ih) / 3).max(2);
    fill_rect(
        frame,
        ix + (iw.saturating_sub(m)) / 2,
        iy + (ih.saturating_sub(m)) / 2,
        m,
        m,
        true,
    );
    let (ix, iy, iw, ih) = interior(layout, maze.end);
    let m = (iw.min(ih) / 2).max(4);
    let x = ix + (iw.saturating_sub(m)) / 2;
    let y = iy + (ih.saturating_sub(m)) / 2;
    fill_rect(frame, x, y, m, m, true);
    fill_rect(
        frame,
        x + 2,
        y + 2,
        m.saturating_sub(4),
        m.saturating_sub(4),
        false,
    );
}

fn paint_path(frame: &mut [u8], layout: &Layout, path: &[Cell]) {
    for cell in path {
        let (x, y, w, h) = path_blob(layout, *cell);
        fill_rect(frame, x, y, w, h, true);
    }
    for pair in path.windows(2) {
        if let Some((x, y, w, h)) = path_connector(layout, pair[0], pair[1]) {
            fill_rect(frame, x, y, w, h, true);
        }
    }
}

fn maze_bounds(layout: &Layout) -> (u32, u32, u32, u32) {
    let w = u32::from(layout.cols)
        .saturating_mul(layout.cell)
        .saturating_add(layout.wall)
        .min(PANEL_WIDTH.saturating_sub(layout.origin_x));
    let h = u32::from(layout.rows)
        .saturating_mul(layout.cell)
        .saturating_add(layout.wall)
        .min(PANEL_HEIGHT.saturating_sub(layout.origin_y));
    (layout.origin_x, layout.origin_y, w, h)
}

fn interior(layout: &Layout, c: Cell) -> (u32, u32, u32, u32) {
    let x = layout.origin_x + u32::from(c.x) * layout.cell + layout.wall;
    let y = layout.origin_y + u32::from(c.y) * layout.cell + layout.wall;
    let s = layout.cell.saturating_sub(layout.wall);
    (x, y, s, s)
}

fn east_door(layout: &Layout, c: Cell) -> (u32, u32, u32, u32) {
    let x = layout.origin_x + u32::from(c.x + 1) * layout.cell;
    let y = layout.origin_y + u32::from(c.y) * layout.cell + layout.wall;
    (x, y, layout.wall, layout.cell.saturating_sub(layout.wall))
}

fn south_door(layout: &Layout, c: Cell) -> (u32, u32, u32, u32) {
    let x = layout.origin_x + u32::from(c.x) * layout.cell + layout.wall;
    let y = layout.origin_y + u32::from(c.y + 1) * layout.cell;
    (x, y, layout.cell.saturating_sub(layout.wall), layout.wall)
}

fn path_blob(layout: &Layout, c: Cell) -> (u32, u32, u32, u32) {
    let (ix, iy, iw, ih) = interior(layout, c);
    let pw = (iw / 2).max(2);
    let ph = (ih / 2).max(2);
    (
        ix + (iw.saturating_sub(pw)) / 2,
        iy + (ih.saturating_sub(ph)) / 2,
        pw,
        ph,
    )
}

fn path_connector(layout: &Layout, a: Cell, b: Cell) -> Option<(u32, u32, u32, u32)> {
    let (ax, ay, aw, ah) = path_blob(layout, a);
    let (bx, by, bw, bh) = path_blob(layout, b);
    if a.y == b.y {
        let x0 = ax.min(bx) + if ax <= bx { aw } else { bw };
        let x1 = ax.max(bx);
        if x1 <= x0 {
            return None;
        }
        Some((x0, ay.min(by), x1 - x0, ah.min(bh)))
    } else if a.x == b.x {
        let y0 = ay.min(by) + if ay <= by { ah } else { bh };
        let y1 = ay.max(by);
        if y1 <= y0 {
            return None;
        }
        Some((ax.min(bx), y0, aw.min(bw), y1 - y0))
    } else {
        None
    }
}

fn align_byte_rect(x: u32, y: u32, w: u32, h: u32) -> ByteRect {
    let x2 = x.saturating_add(w).min(PANEL_WIDTH);
    let y2 = y.saturating_add(h).min(PANEL_HEIGHT);
    let mut x0 = (x / 8) * 8;
    if x0 >= PANEL_WIDTH {
        x0 = PANEL_WIDTH - 8;
    }
    let mut x1 = x2.div_ceil(8) * 8;
    x1 = x1.min(PANEL_WIDTH).max(x0 + 8);
    let y0 = y.min(PANEL_HEIGHT.saturating_sub(1));
    let y1 = y2.max(y0 + 1).min(PANEL_HEIGHT);
    ByteRect {
        x: x0,
        y: y0,
        width: x1 - x0,
        height: y1 - y0,
    }
}

fn fill_rect(frame: &mut [u8], x: u32, y: u32, w: u32, h: u32, black: bool) {
    if w == 0 || h == 0 {
        return;
    }
    let x1 = x.saturating_add(w).min(PANEL_WIDTH);
    let y1 = y.saturating_add(h).min(PANEL_HEIGHT);
    let x0 = x.min(PANEL_WIDTH);
    let y0 = y.min(PANEL_HEIGHT);
    for py in y0..y1 {
        for px in x0..x1 {
            set_pixel(frame, px, py, black);
        }
    }
}

fn set_pixel(frame: &mut [u8], x: u32, y: u32, black: bool) {
    if x >= PANEL_WIDTH || y >= PANEL_HEIGHT {
        return;
    }
    let row_bytes = (PANEL_WIDTH / 8) as usize;
    let i = y as usize * row_bytes + (x as usize) / 8;
    let bit = 0x80u8 >> (x % 8);
    if black {
        frame[i] &= !bit;
    } else {
        frame[i] |= bit;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::maze::{generate, solve, Cell};

    fn pixel_is_black(frame: &[u8], x: u32, y: u32) -> bool {
        if x >= PANEL_WIDTH || y >= PANEL_HEIGHT {
            return false;
        }
        let row_bytes = (PANEL_WIDTH / 8) as usize;
        let i = y as usize * row_bytes + (x as usize) / 8;
        let bit = 0x80u8 >> (x % 8);
        frame[i] & bit == 0
    }

    fn ink(frame: &[u8]) -> u32 {
        frame.iter().map(|b| (!b).count_ones()).sum()
    }

    #[test]
    fn empty_and_progress_zero_match() {
        let maze = generate(8, 6, 11);
        let layout = layout_for(maze.cols, maze.rows);
        let path = solve(&maze);
        assert_eq!(
            render_empty(&maze, &layout),
            render_progress(&maze, &layout, &path, 0)
        );
    }

    #[test]
    fn frames_are_panel_sized() {
        let maze = generate(8, 6, 3);
        let layout = layout_for(maze.cols, maze.rows);
        assert_eq!(render_empty(&maze, &layout).len(), FRAME_BYTES);
    }

    #[test]
    fn solution_adds_ink_and_leaves_off_path_cells_white() {
        let maze = generate(10, 8, 42);
        let layout = layout_for(maze.cols, maze.rows);
        let path = solve(&maze);
        let empty = render_empty(&maze, &layout);
        let done = render_progress(&maze, &layout, &path, path.len());
        assert!(ink(&done) > ink(&empty));

        let on_path: std::collections::HashSet<_> = path.iter().copied().collect();
        let off = (0..maze.rows)
            .flat_map(|y| (0..maze.cols).map(move |x| Cell::new(x, y)))
            .find(|c| !on_path.contains(c))
            .expect("perfect maze has cells off the unique path");
        let (ix, iy, iw, ih) = interior(&layout, off);
        let cx = ix + iw / 2;
        let cy = iy + ih / 2;
        assert!(
            !pixel_is_black(&done, cx, cy),
            "off-path interior {off:?} should stay white"
        );
        let (sx, sy, sw, sh) = path_blob(&layout, maze.start);
        assert!(pixel_is_black(&done, sx + sw / 2, sy + sh / 2));
    }

    #[test]
    fn progress_is_monotonic() {
        let maze = generate(8, 6, 5);
        let layout = layout_for(maze.cols, maze.rows);
        let path = solve(&maze);
        let mut prev = ink(&render_progress(&maze, &layout, &path, 0));
        let step = 3;
        let mut shown = 0;
        while shown < path.len() {
            shown = (shown + step).min(path.len());
            let now = ink(&render_progress(&maze, &layout, &path, shown));
            assert!(now >= prev, "ink {now} after showing {shown} < {prev}");
            prev = now;
        }
    }

    #[test]
    fn align_byte_rect_pads_to_whole_bytes() {
        let r = align_byte_rect(7, 10, 10, 4);
        assert_eq!(r.x, 0);
        assert_eq!(r.y, 10);
        assert_eq!(r.width % 8, 0);
        assert!(r.x + r.width >= 17);
        assert_eq!(r.height, 4);
    }

    #[test]
    fn crop_packed_matches_byte_count() {
        let maze = generate(6, 4, 1);
        let layout = layout_for(maze.cols, maze.rows);
        let path = solve(&maze);
        let frame = render_progress(&maze, &layout, &path, path.len().min(3));
        let rect = dirty_rect(&layout, &path, 0, path.len().min(3));
        let rect = rect.clamped().expect("dirty window must fit the panel");
        let crop = crop_packed(&frame, rect);
        assert_eq!(crop.len(), rect.byte_count());
    }

    #[test]
    fn layout_fits_the_panel() {
        let layout = layout_for(40, 24);
        let (x, y, w, h) = maze_bounds(&layout);
        assert!(x + w <= PANEL_WIDTH);
        assert!(y + h <= PANEL_HEIGHT);
        assert!(layout.cell > 0);
        assert!(layout.wall > 0);
        assert!(layout.wall <= layout.cell);
    }

    #[test]
    fn layout_never_exceeds_panel_for_dense_grids() {
        for (cols, rows) in [(80, 48), (120, 72), (200, 120), (800, 480)] {
            let layout = layout_for(cols, rows);
            let (x, y, w, h) = maze_bounds(&layout);
            assert!(
                x + w <= PANEL_WIDTH,
                "{cols}x{rows} width {}+{} > {PANEL_WIDTH}",
                x,
                w
            );
            assert!(
                y + h <= PANEL_HEIGHT,
                "{cols}x{rows} height {}+{} > {PANEL_HEIGHT}",
                y,
                h
            );
        }
    }

    #[test]
    fn align_byte_rect_stays_on_the_panel() {
        let r = align_byte_rect(792, 476, 32, 20);
        assert_eq!(r.x % 8, 0);
        assert_eq!(r.width % 8, 0);
        assert!(r.x + r.width <= PANEL_WIDTH);
        assert!(r.y + r.height <= PANEL_HEIGHT);
        assert!(r.width >= 8);
        assert!(r.height >= 1);
        let edge = align_byte_rect(0, PANEL_HEIGHT, 8, 1);
        assert!(edge.y < PANEL_HEIGHT);
        assert!(edge.y + edge.height <= PANEL_HEIGHT);
    }

    #[test]
    fn crop_packed_does_not_panic_on_out_of_bounds() {
        let frame = vec![0xffu8; FRAME_BYTES];
        let crop = crop_packed(
            &frame,
            ByteRect {
                x: 0,
                y: PANEL_HEIGHT,
                width: 8,
                height: 1,
            },
        );
        assert!(crop.is_empty());
        let crop = crop_packed(&frame[0..16], align_byte_rect(0, 0, 8, 1));
        assert!(crop.is_empty());
    }

    #[test]
    fn dirty_rects_are_valid_crops_along_a_full_path() {
        let maze = generate(40, 24, 7);
        let layout = layout_for(maze.cols, maze.rows);
        let path = solve(&maze);
        assert!(!path.is_empty());
        let frame = render_progress(&maze, &layout, &path, path.len());
        for i in 0..path.len() {
            let rect = dirty_rect(&layout, &path, i, i + 1);
            let rect = rect.clamped().expect("dirty window must fit the panel");
            let crop = crop_packed(&frame, rect);
            assert_eq!(crop.len(), rect.byte_count(), "step {i} {rect:?}");
        }
    }
}
