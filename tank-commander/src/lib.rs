//! Tank Commander balance and fun simulator.
//!
//! Implements the Skirmish slice of the tabletop rules from
//! <https://github.com/imjasonh/tank-commander> and runs paired heuristic
//! AIs to measure drama and stalemate rates.

pub mod action;
pub mod ai;
pub mod board;
pub mod combat;
pub mod dice;
pub mod game;
pub mod hex;
pub mod metrics;
pub mod scenario;
pub mod sim;
pub mod unit;
pub mod upgrades;
