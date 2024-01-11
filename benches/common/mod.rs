use anyhow::anyhow;
use criterion::BenchmarkId;

// TODO: Why Copy and &'static str over String?
#[derive(Clone, Debug, Copy)]
pub(crate) struct BenchParams {
  pub step_size: usize,
  pub curve_cycle: &'static str,
  pub date: &'static str,
  pub sha: &'static str,
}
impl BenchParams {
  pub(crate) fn bench_id(&self, name: &str) -> BenchmarkId {
    let output_type = bench_output_env().unwrap_or("stdout".into());
    match output_type.as_ref() {
      "pr-comment" => BenchmarkId::new(name, format!("StepCircuitSize-{}", self.step_size)),
      "commit-comment" => BenchmarkId::new(
        format!("curve-cycle={}", self.curve_cycle),
        format!("{}-StepCircuitSize-{}", name, self.step_size),
      ),
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

fn bench_output_env() -> anyhow::Result<String> {
  std::env::var("ARECIBO_BENCH_OUTPUT").map_err(|e| anyhow!("Bench output env var isn't set: {e}"))
}

pub(crate) fn noise_threshold_env() -> anyhow::Result<f64> {
  std::env::var("ARECIBO_BENCH_NOISE_THRESHOLD")
    .map_err(|e| anyhow!("Noise threshold env var isn't set: {e}"))
    .and_then(|nt| {
      nt.parse::<f64>()
        .map_err(|e| anyhow!("Failed to parse noise threshold: {e}"))
    })
}
