---
title: "chore: some installed deps are not needed"
labels: automated-issue
---

Some dependencies specified in `Cargo.toml` are not needed.

Check the [unused dependencies sanity check]({{env.WORKFLOW_URL}}) workflow for details.

This issue was raised by the workflow at `https://github.com/lurk-lab/ci-workflows/tree/main/.github/workflows/unused-deps.yml`.

> **Note**
> If this is a false positive, please refer to the [`cargo-udeps` docs][cargo-udeps-docs] on how to ignore the dependencies.

[cargo-udeps-docs]: https://github.com/est31/cargo-udeps#ignoring-some-of-the-dependencies
