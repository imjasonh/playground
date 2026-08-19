//! Recursive-backtracker generator. Produces a perfect maze (a spanning tree).

use super::{Cell, Dir, Maze};

/// Carve a perfect `cols`×`rows` maze from `seed`.
///
/// Start is the north-west cell; end is the south-east cell. The same seed
/// always yields the same wall set.
pub fn generate(cols: u16, rows: u16, seed: u64) -> Maze {
    let cols = cols.max(2);
    let rows = rows.max(2);
    let start = Cell::new(0, 0);
    let end = Cell::new(cols - 1, rows - 1);
    let mut maze = Maze::sealed(cols, rows, start, end);
    let mut rng = Rng::new(seed);

    let n = maze.cell_count();
    let mut visited = vec![false; n];
    let mut stack: Vec<Cell> = Vec::with_capacity(n);
    visited[maze.grid_index(start)] = true;
    stack.push(start);

    while let Some(cur) = stack.last().copied() {
        let mut candidates: Vec<Cell> = Dir::ALL
            .iter()
            .filter_map(|&dir| cur.neighbor(dir, cols, rows))
            .filter(|n| !visited[maze.grid_index(*n)])
            .collect();
        if candidates.is_empty() {
            stack.pop();
            continue;
        }
        shuffle(&mut rng, &mut candidates);
        let next = candidates[0];
        maze.knock(cur, next);
        visited[maze.grid_index(next)] = true;
        stack.push(next);
    }
    maze
}

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // xorshift64 rejects a zero state.
        Self(if seed == 0 {
            0x9E37_79B9_7F4A_7C15
        } else {
            seed
        })
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn range(&mut self, n: usize) -> usize {
        if n <= 1 {
            return 0;
        }
        (self.next_u64() % n as u64) as usize
    }
}

fn shuffle<T>(rng: &mut Rng, items: &mut [T]) {
    for i in (1..items.len()).rev() {
        let j = rng.range(i + 1);
        items.swap(i, j);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn carved_internal_walls(maze: &Maze) -> usize {
        let mut n = 0;
        for y in 0..maze.rows {
            for x in 0..maze.cols.saturating_sub(1) {
                if !maze.has_east_wall(x, y) {
                    n += 1;
                }
            }
        }
        for y in 0..maze.rows.saturating_sub(1) {
            for x in 0..maze.cols {
                if !maze.has_south_wall(x, y) {
                    n += 1;
                }
            }
        }
        n
    }

    fn reachable(maze: &Maze) -> usize {
        let n = maze.cell_count();
        let mut seen = vec![false; n];
        let mut stack = vec![maze.start];
        seen[maze.grid_index(maze.start)] = true;
        let mut count = 0;
        while let Some(c) = stack.pop() {
            count += 1;
            for ncell in maze.open_neighbors(c) {
                let i = maze.grid_index(ncell);
                if !seen[i] {
                    seen[i] = true;
                    stack.push(ncell);
                }
            }
        }
        count
    }

    #[test]
    fn same_seed_is_deterministic() {
        let a = generate(12, 8, 0xDEAD_BEEF);
        let b = generate(12, 8, 0xDEAD_BEEF);
        assert_eq!(a, b);
    }

    #[test]
    fn different_seeds_usually_differ() {
        let a = generate(12, 8, 1);
        let b = generate(12, 8, 2);
        assert_ne!(a, b);
    }

    #[test]
    fn perfect_maze_is_a_spanning_tree() {
        let maze = generate(15, 10, 99);
        assert_eq!(carved_internal_walls(&maze), maze.cell_count() - 1);
        assert_eq!(reachable(&maze), maze.cell_count());
        assert!(maze.has_east_wall(maze.cols - 1, 0));
        assert!(maze.has_south_wall(0, maze.rows - 1));
    }

    #[test]
    fn tiny_maze_still_fills_the_grid() {
        let maze = generate(2, 2, 7);
        assert_eq!(maze.cols, 2);
        assert_eq!(maze.rows, 2);
        assert_eq!(reachable(&maze), 4);
        assert_eq!(carved_internal_walls(&maze), 3);
    }

    #[test]
    fn default_panel_size_is_a_spanning_tree() {
        let maze = generate(crate::maze::MAZE_COLS, crate::maze::MAZE_ROWS, 1);
        assert_eq!(carved_internal_walls(&maze), maze.cell_count() - 1);
        assert_eq!(reachable(&maze), maze.cell_count());
    }
}
