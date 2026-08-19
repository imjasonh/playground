//! Perfect-maze stages: generate, solve, then render.
//!
//! Each stage is a separate module so you can swap the generator, the solver,
//! or the pixel drawing without touching the others. The firmware only animates
//! prefixes of the solver's path — it never paints a search or a wrong route.

mod generate;
mod render;
mod solve;

pub use generate::generate;
pub use render::{
    cells_per_frame, crop_packed, dirty_rect, layout_for, render_empty, render_progress, ByteRect,
    Layout,
};
pub use solve::solve;

/// Baked into the maze firmware ELF so `make flash APP=maze` can refuse a stale image.
pub const MAZE_FIRMWARE_ID: &str = "maze-esp32/0.1";

/// Default maze size; 25×15 cells fill an 800×480 panel with ~3 px walls.
pub const MAZE_COLS: u16 = 25;
pub const MAZE_ROWS: u16 = 15;

/// Target delay between partial refreshes.
pub const TICK_MS: u64 = 1000;

/// Aim to finish the solution in about this many partial frames.
pub const TARGET_FRAMES: usize = 60;

/// Pause on the completed maze before generating the next one.
pub const HOLD_COMPLETE_MS: u64 = 8000;

/// One cell in the maze grid.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Cell {
    pub x: u16,
    pub y: u16,
}

impl Cell {
    pub fn new(x: u16, y: u16) -> Self {
        Self { x, y }
    }

    /// Neighbor in `dir` when that neighbor stays inside `cols`×`rows`.
    pub fn neighbor(self, dir: Dir, cols: u16, rows: u16) -> Option<Cell> {
        let (dx, dy) = dir.delta();
        let x = i32::from(self.x) + dx;
        let y = i32::from(self.y) + dy;
        if x < 0 || y < 0 || x >= i32::from(cols) || y >= i32::from(rows) {
            None
        } else {
            Some(Cell {
                x: x as u16,
                y: y as u16,
            })
        }
    }
}

/// Cardinal direction on the grid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    North,
    East,
    South,
    West,
}

impl Dir {
    pub const ALL: [Dir; 4] = [Dir::North, Dir::East, Dir::South, Dir::West];

    pub fn delta(self) -> (i32, i32) {
        match self {
            Dir::North => (0, -1),
            Dir::East => (1, 0),
            Dir::South => (0, 1),
            Dir::West => (-1, 0),
        }
    }
}

/// Perfect maze: `cols`×`rows` cells, one passage tree, outer walls sealed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Maze {
    pub cols: u16,
    pub rows: u16,
    pub start: Cell,
    pub end: Cell,
    east_walls: Vec<bool>,
    south_walls: Vec<bool>,
}

impl Maze {
    fn sealed(cols: u16, rows: u16, start: Cell, end: Cell) -> Self {
        let cols = cols.max(2);
        let rows = rows.max(2);
        let east = usize::from(cols - 1) * usize::from(rows);
        let south = usize::from(cols) * usize::from(rows - 1);
        Self {
            cols,
            rows,
            start,
            end,
            east_walls: vec![true; east],
            south_walls: vec![true; south],
        }
    }

    /// East wall of cell `(x, y)`, including the outer east boundary.
    pub fn has_east_wall(&self, x: u16, y: u16) -> bool {
        if x >= self.cols || y >= self.rows {
            return true;
        }
        if x + 1 == self.cols {
            return true;
        }
        let i = usize::from(y) * usize::from(self.cols - 1) + usize::from(x);
        self.east_walls[i]
    }

    /// South wall of cell `(x, y)`, including the outer south boundary.
    pub fn has_south_wall(&self, x: u16, y: u16) -> bool {
        if x >= self.cols || y >= self.rows {
            return true;
        }
        if y + 1 == self.rows {
            return true;
        }
        let i = usize::from(y) * usize::from(self.cols) + usize::from(x);
        self.south_walls[i]
    }

    /// True when `a` and `b` are orthogonal neighbors with the shared wall carved.
    pub fn is_open(&self, a: Cell, b: Cell) -> bool {
        if a.x == b.x && a.y.abs_diff(b.y) == 1 {
            let y = a.y.min(b.y);
            !self.has_south_wall(a.x, y)
        } else if a.y == b.y && a.x.abs_diff(b.x) == 1 {
            let x = a.x.min(b.x);
            !self.has_east_wall(x, a.y)
        } else {
            false
        }
    }

    fn knock(&mut self, a: Cell, b: Cell) {
        if a.x == b.x && a.y.abs_diff(b.y) == 1 {
            let y = a.y.min(b.y);
            let i = usize::from(y) * usize::from(self.cols) + usize::from(a.x);
            self.south_walls[i] = false;
        } else if a.y == b.y && a.x.abs_diff(b.x) == 1 {
            let x = a.x.min(b.x);
            let i = usize::from(a.y) * usize::from(self.cols - 1) + usize::from(x);
            self.east_walls[i] = false;
        }
    }

    /// Cells reachable from `c` through carved passages.
    pub fn open_neighbors(&self, c: Cell) -> Vec<Cell> {
        Dir::ALL
            .iter()
            .filter_map(|&dir| {
                let n = c.neighbor(dir, self.cols, self.rows)?;
                self.is_open(c, n).then_some(n)
            })
            .collect()
    }

    fn grid_index(&self, c: Cell) -> usize {
        usize::from(c.y) * usize::from(self.cols) + usize::from(c.x)
    }

    fn cell_count(&self) -> usize {
        usize::from(self.cols) * usize::from(self.rows)
    }
}

/// Solution path from `maze.start` through to `maze.end`.
pub type Path = Vec<Cell>;
