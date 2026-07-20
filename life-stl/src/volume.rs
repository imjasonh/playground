/// What a voxel represents in the printable volume.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellKind {
    Empty,
    /// Generation-0 bed plate.
    Base,
    /// A live Game of Life cell at this generation.
    Life,
    /// Added so the model is self-supporting under FDM 45° rules.
    Scaffold,
}

impl CellKind {
    pub fn is_solid(self) -> bool {
        !matches!(self, CellKind::Empty)
    }
}

/// Dense XYZ voxel grid (`x` fastest, then `y`, then `z`).
#[derive(Debug, Clone)]
pub struct Volume {
    pub width: usize,
    pub height: usize,
    pub depth: usize,
    cells: Vec<CellKind>,
}

impl Volume {
    pub fn new(width: usize, height: usize, depth: usize) -> Self {
        assert!(width > 0 && height > 0 && depth > 0);
        Self {
            width,
            height,
            depth,
            cells: vec![CellKind::Empty; width * height * depth],
        }
    }

    #[inline]
    fn idx(&self, x: usize, y: usize, z: usize) -> usize {
        (z * self.height + y) * self.width + x
    }

    pub fn get(&self, x: usize, y: usize, z: usize) -> CellKind {
        self.cells[self.idx(x, y, z)]
    }

    pub fn set(&mut self, x: usize, y: usize, z: usize, kind: CellKind) {
        let i = self.idx(x, y, z);
        self.cells[i] = kind;
    }

    /// Set to `kind` only when currently empty (never overwrite Life/Base).
    pub fn fill_empty(&mut self, x: usize, y: usize, z: usize, kind: CellKind) -> bool {
        let i = self.idx(x, y, z);
        if self.cells[i] == CellKind::Empty {
            self.cells[i] = kind;
            true
        } else {
            false
        }
    }

    pub fn is_solid(&self, x: usize, y: usize, z: usize) -> bool {
        self.get(x, y, z).is_solid()
    }

    /// True if any solid exists in the 3×3 Moore neighborhood on layer `z-1`
    /// (or this cell is on z=0). Matches the usual FDM ~45° self-support rule
    /// for cubic voxels of equal size.
    pub fn has_moore_support(&self, x: usize, y: usize, z: usize) -> bool {
        if z == 0 {
            return true;
        }
        let z_below = z - 1;
        for dy in [-1_isize, 0, 1] {
            for dx in [-1_isize, 0, 1] {
                let nx = x as isize + dx;
                let ny = y as isize + dy;
                if nx < 0 || ny < 0 || nx >= self.width as isize || ny >= self.height as isize {
                    continue;
                }
                if self.is_solid(nx as usize, ny as usize, z_below) {
                    return true;
                }
            }
        }
        false
    }

    /// True if the voxel directly underneath is solid (or z==0).
    pub fn has_vertical_support(&self, x: usize, y: usize, z: usize) -> bool {
        z == 0 || self.is_solid(x, y, z - 1)
    }

    pub fn count_kind(&self, kind: CellKind) -> usize {
        self.cells.iter().filter(|&&c| c == kind).count()
    }

    pub fn solid_count(&self) -> usize {
        self.cells.iter().filter(|c| c.is_solid()).count()
    }
}
