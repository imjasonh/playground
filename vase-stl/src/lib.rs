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
mod metrics;
mod orient;
mod stl;
mod threemf;
mod validate;

pub use convert::{
    convert, optimize_convert, optimize_convert_with_budget, ConvertOptions, ConvertResult,
    OptimizeTrial, ShellMode,
};
pub use envelope::{
    densify_catmull_rom, extract_radial_envelope, max_layer_step, Contour, Envelope,
};
pub use mesh::{
    loft_hollow, loft_solid, loft_solid_open_top, loft_wall, prepare_loft_envelope, MeshStats,
};
pub use metrics::{compare_envelopes, envelope_volume, EnvelopeMetrics};
pub use orient::{choose_up_axis, BoundingBox, UpAxis};
pub use stl::{read_stl, write_stl, TriMesh};
pub use threemf::write_3mf;
pub use validate::{validate_envelope, VaseValidation};
