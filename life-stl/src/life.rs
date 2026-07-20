/// A single generation of Conway's Game of Life on a finite grid.
///
/// Edges are **dead** (not toroidal): cells off the grid contribute no
/// neighbors. Callers that need edge-free evolution simulate on a grid padded
/// by the light cone (one cell per generation) and crop afterwards — see
/// `generation_windows` in the crate root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grid {
    width: usize,
    height: usize,
    /// Row-major, `true` = alive.
    cells: Vec<bool>,
}

impl Grid {
    pub fn new(width: usize, height: usize) -> Self {
        assert!(width > 0 && height > 0);
        Self {
            width,
            height,
            cells: vec![false; width * height],
        }
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn height(&self) -> usize {
        self.height
    }

    #[inline]
    fn idx(&self, x: usize, y: usize) -> usize {
        y * self.width + x
    }

    pub fn is_alive(&self, x: usize, y: usize) -> bool {
        self.cells[self.idx(x, y)]
    }

    pub fn set(&mut self, x: usize, y: usize, alive: bool) {
        let i = self.idx(x, y);
        self.cells[i] = alive;
    }

    pub fn live_count(&self) -> usize {
        self.cells.iter().filter(|&&c| c).count()
    }

    fn alive_neighbor_count(&self, x: usize, y: usize) -> u8 {
        let mut n = 0u8;
        for dy in [-1_isize, 0, 1] {
            for dx in [-1_isize, 0, 1] {
                if dx == 0 && dy == 0 {
                    continue;
                }
                let nx = x as isize + dx;
                let ny = y as isize + dy;
                if nx < 0 || ny < 0 || nx >= self.width as isize || ny >= self.height as isize {
                    continue;
                }
                if self.is_alive(nx as usize, ny as usize) {
                    n += 1;
                }
            }
        }
        n
    }

    /// One Conway step (B3/S23).
    pub fn step(&self) -> Self {
        let mut next = Self::new(self.width, self.height);
        for y in 0..self.height {
            for x in 0..self.width {
                let neighbors = self.alive_neighbor_count(x, y);
                let alive = self.is_alive(x, y);
                let next_alive = matches!((alive, neighbors), (true, 2 | 3) | (false, 3));
                next.set(x, y, next_alive);
            }
        }
        next
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blinker_oscillates() {
        let mut g = Grid::new(5, 5);
        // Horizontal blinker centered.
        g.set(1, 2, true);
        g.set(2, 2, true);
        g.set(3, 2, true);
        let g2 = g.step();
        assert!(g2.is_alive(2, 1));
        assert!(g2.is_alive(2, 2));
        assert!(g2.is_alive(2, 3));
        assert_eq!(g2.live_count(), 3);
        let g3 = g2.step();
        assert_eq!(g3, g);
    }

    #[test]
    fn block_still_life() {
        let mut g = Grid::new(4, 4);
        g.set(1, 1, true);
        g.set(1, 2, true);
        g.set(2, 1, true);
        g.set(2, 2, true);
        assert_eq!(g.step(), g);
    }
}
