pub mod supernova;

use anyhow::anyhow;
use criterion::BenchmarkId;

// TODO: Why Copy and &'static str over String?
#[derive(Clone, Debug, Copy)]
pub(crate) struct BenchParams {
  pub step_size: usize,
  pub date: &'static str,
  pub sha: &'static str,
}
impl BenchParams {
  pub(crate) fn bench_id(&self, name: &str) -> BenchmarkId {
    let output_type = output_type_env().unwrap_or("stdout".into());
    match output_type.as_ref() {
      "pr-comment" => BenchmarkId::new(name, format!("StepCircuitSize-{}", self.step_size)),
      "commit-comment" => {
        let mut short_sha = self.sha.to_owned();
        short_sha.truncate(7);
        BenchmarkId::new(
          format!("ref={}", short_sha),
          format!("{}-NumCons-{}", name, self.step_size),
        )
      }
      // TODO: refine "gh-pages"
      _ => BenchmarkId::new(
        name,
        format!(
          "StepCircuitSize-{}-{}-{}",
          self.step_size, self.sha, self.date
        ),
      ),
    }
  }
}

fn output_type_env() -> anyhow::Result<String> {
  std::env::var("BENCH_OUTPUT").map_err(|e| anyhow!("BENCH_OUTPUT env var isn't set: {e}"))
}

pub(crate) fn noise_threshold_env() -> anyhow::Result<f64> {
  std::env::var("BENCH_NOISE_THRESHOLD")
    .map_err(|e| anyhow!("BENCH_NOISE_THRESHOLD env var isn't set: {e}"))
    .and_then(|nt| {
      nt.parse::<f64>()
        .map_err(|e| anyhow!("Failed to parse noise threshold: {e}"))
    })
}
