//! Verified samplers for the OpenDP discrete-distribution primitives (CKS20).
//!
//! Most of the proof functions live in the <sampler>_helper.rs
pub mod bernoulli_rational;
pub mod bernoulli_exp1;
pub mod bernoulli_exp1_helper;
pub mod bernoulli_exp;
pub mod bernoulli_exp_helper;
pub mod exp_rejection;
pub mod exp_rejection_helper;
pub mod geometric_exp;
pub mod geometric_exp_helper;
pub mod geometric_exp_fast;
pub mod geometric_exp_fast_helper;
pub mod discrete_laplace;
pub mod discrete_laplace_helper;
pub mod discrete_gaussian;
pub mod discrete_gaussian_helper;
