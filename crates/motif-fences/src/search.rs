//! Outer-level search: try many (skeleton, coordinate-seed) pairs and
//! keep the best that validates. See `anneal.rs` module docs for why the
//! outer level is multistart over generated skeletons rather than
//! annealing over the graph itself.
//!
//! This module also defines [`SearchRecord`], the machine-readable
//! export format: skeleton + solved coordinates + face structure + the
//! seed that reproduces it. This is the artifact the family-mining half
//! of the task consumes — a run that only reports a number without one
//! of these is not useful for that purpose.

use crate::anneal::{anneal, AnnealParams};
use crate::configuration::Tolerance;
use crate::geometry::Point;
use crate::skeleton::{random_growth, Skeleton};
use serde::{Deserialize, Serialize};

/// One candidate's full machine-readable record: enough to reproduce it
/// (`generator` + `seed` + `anneal_params`) and enough to mine it for
/// structural patterns (`skeleton`, `coords`, `field_areas`) without
/// re-running anything.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchRecord {
    pub n: usize,
    pub generator: String,
    pub seed: u64,
    pub anneal_params: AnnealParams,
    pub skeleton: Skeleton,
    pub coords: Vec<(f64, f64)>,
    /// `None` if the annealed result did not pass
    /// [`Configuration::validate`] (kept for negative-result bookkeeping
    /// / debugging, not for claiming a record).
    pub valid_report: Option<ValidReport>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidReport {
    pub field_areas: Vec<f64>,
    pub total_area: f64,
}

fn to_record(
    n: usize,
    generator: &str,
    seed: u64,
    skeleton: Skeleton,
    coords: Vec<Point>,
    params: AnnealParams,
) -> SearchRecord {
    let config = skeleton.to_configuration(&coords);
    let valid_report = config
        .validate(Tolerance::default())
        .ok()
        .map(|r| ValidReport {
            field_areas: r.field_areas,
            total_area: r.total_area,
        });
    SearchRecord {
        n,
        generator: generator.to_string(),
        seed,
        anneal_params: params,
        skeleton,
        coords: coords.iter().map(|p| (p.x, p.y)).collect(),
        valid_report,
    }
}

/// Anneal one (skeleton, init_coords) pair and package the result.
pub fn run_one(
    n: usize,
    generator: &str,
    seed: u64,
    skeleton: Skeleton,
    init_coords: Vec<Point>,
    params: AnnealParams,
) -> SearchRecord {
    let result = anneal(&skeleton, init_coords, params.clone());
    to_record(n, generator, seed, skeleton, result.coords, params)
}

/// Multistart the random-growth generator for a target `n`: try
/// `attempts` independently-seeded random skeletons (seeds
/// `base_seed..base_seed+attempts`), anneal each, and return every
/// resulting record sorted best-total-area-first (valid records — those
/// that pass `Configuration::validate` — sort ahead of invalid ones
/// regardless of their raw area, since an invalid "area" isn't a real
/// result).
pub fn search_random_growth(
    n: usize,
    attempts: usize,
    base_seed: u64,
    params: AnnealParams,
) -> Vec<SearchRecord> {
    let mut records = search_random_growth_streaming(n, attempts, base_seed, params, |_| {});
    sort_best_first(&mut records);
    records
}

/// Same multistart as [`search_random_growth`], but invokes `on_record`
/// immediately after each attempt instead of buffering all of them
/// until every attempt finishes. Used by the CLI so a long multistart
/// run's progress (and a `kill`ed run's partial results) are visible on
/// stdout as they happen, rather than only after the entire batch
/// completes.
pub fn search_random_growth_streaming(
    n: usize,
    attempts: usize,
    base_seed: u64,
    params: AnnealParams,
    mut on_record: impl FnMut(&SearchRecord),
) -> Vec<SearchRecord> {
    let mut records = Vec::with_capacity(attempts);
    for i in 0..attempts {
        let seed = base_seed + i as u64;
        let (skeleton, init_coords) = random_growth(n, seed);
        let mut p = params.clone();
        p.seed = seed;
        let record = run_one(n, "random_growth", seed, skeleton, init_coords, p);
        on_record(&record);
        records.push(record);
    }
    records
}

fn sort_best_first(records: &mut [SearchRecord]) {
    records.sort_by(|a, b| {
        let key = |r: &SearchRecord| {
            (
                r.valid_report.is_none(), // false (valid) sorts first
                -r.valid_report.as_ref().map(|v| v.total_area).unwrap_or(0.0),
            )
        };
        key(a)
            .0
            .cmp(&key(b).0)
            .then(key(a).1.partial_cmp(&key(b).1).unwrap())
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multistart_on_n3_finds_the_triangle_area() {
        // n=3 has exactly one skeleton up to relabeling (a triangle), so
        // this validates the search plumbing end-to-end against a known
        // record rather than testing generator diversity.
        let params = AnnealParams {
            iterations: 20_000,
            ..AnnealParams::default()
        };
        let records = search_random_growth(3, 8, 1, params);
        let best = &records[0];
        let report = best
            .valid_report
            .as_ref()
            .expect("expected a valid n=3 result");
        assert!(
            (report.total_area - 3f64.sqrt() / 4.0).abs() < 1e-4,
            "total_area = {}",
            report.total_area
        );
    }
}
