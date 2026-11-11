# CI workflow (to be moved before publishing)

`build.yml` is the GitHub Actions workflow of this repository: build with the Mathlib cache (after adding swap
space), axiom check of the headline theorems, and `lake comparator`. Move it to `.github/workflows/build.yml` when
publishing (`git mv ci/build.yml .github/workflows/build.yml`, then delete this directory).
