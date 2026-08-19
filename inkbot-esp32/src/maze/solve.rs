//! Breadth-first solver. A perfect maze has one route; BFS returns it.

use super::{Maze, Path};

/// Walk `maze.start` to `maze.end` along carved passages.
///
/// Returns an empty path when the end is unreachable (the generator never
/// does that). The path includes both endpoints and no off-route cells.
pub fn solve(maze: &Maze) -> Path {
    let n = maze.cell_count();
    let mut came = vec![None; n];
    let mut seen = vec![false; n];
    let mut queue = std::collections::VecDeque::new();
    let start_i = maze.grid_index(maze.start);
    seen[start_i] = true;
    queue.push_back(maze.start);

    let mut found = false;
    while let Some(cur) = queue.pop_front() {
        if cur == maze.end {
            found = true;
            break;
        }
        for next in maze.open_neighbors(cur) {
            let i = maze.grid_index(next);
            if seen[i] {
                continue;
            }
            seen[i] = true;
            came[i] = Some(cur);
            queue.push_back(next);
        }
    }
    if !found {
        return Vec::new();
    }

    let mut path = Vec::new();
    let mut cur = maze.end;
    loop {
        path.push(cur);
        if cur == maze.start {
            break;
        }
        let Some(prev) = came[maze.grid_index(cur)] else {
            return Vec::new();
        };
        cur = prev;
    }
    path.reverse();
    path
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::maze::{generate, Cell, Maze};

    #[test]
    fn path_runs_start_to_end_on_open_edges() {
        let maze = generate(20, 12, 123);
        let path = solve(&maze);
        assert!(!path.is_empty());
        assert_eq!(path.first().copied(), Some(maze.start));
        assert_eq!(path.last().copied(), Some(maze.end));
        for pair in path.windows(2) {
            assert!(
                maze.is_open(pair[0], pair[1]),
                "solution stepped through a wall {:?} -> {:?}",
                pair[0],
                pair[1]
            );
        }
        let unique = path.len()
            == path
                .iter()
                .copied()
                .collect::<std::collections::HashSet<_>>()
                .len();
        assert!(unique, "solution must not revisit a cell");
    }

    #[test]
    fn sealed_maze_has_no_path_to_a_far_end() {
        let maze = Maze::sealed(4, 4, Cell::new(0, 0), Cell::new(3, 3));
        assert!(solve(&maze).is_empty());
    }

    #[test]
    fn hand_carved_corridor_is_the_only_route() {
        let mut maze = Maze::sealed(3, 1, Cell::new(0, 0), Cell::new(2, 0));
        maze.knock(Cell::new(0, 0), Cell::new(1, 0));
        maze.knock(Cell::new(1, 0), Cell::new(2, 0));
        let path = solve(&maze);
        assert_eq!(
            path,
            vec![Cell::new(0, 0), Cell::new(1, 0), Cell::new(2, 0)]
        );
    }
}
