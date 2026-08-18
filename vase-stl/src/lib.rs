//! Convert an arbitrary triangle mesh into a solid suitable for FDM
//! **vase / spiral** printing.
//!
//! Vase mode can only extrude a single continuous perimeter per layer, so
//! this crate approximates the input by its **radial envelope**: at each
//! height `z` and angle `θ`, keep the farthest surface hit from a vertical
//! axis. The resulting star-convex solid is lofted into a watertight STL
//! with a flat bottom (and optional open top).

mod convert;
mod envelope;
mod mesh;
mod orient;
mod stl;

pub use convert::{convert, ConvertOptions, ConvertResult, ShellMode};
pub use envelope::{extract_radial_envelope, Contour, Envelope};
pub use mesh::{loft_hollow, loft_solid, loft_solid_open_top, loft_wall, MeshStats};
pub use orient::{choose_up_axis, BoundingBox, UpAxis};
pub use stl::{read_stl, write_stl, TriMesh};
