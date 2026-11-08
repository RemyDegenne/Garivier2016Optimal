# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Garivier2016Optimal/`.

**Status.** The statements were set up on 2026-11-08, at the end of phase 1. Six challenges are
proved in the project (Theorem 1, Remark 2, Proposition 6 parts 1 and 2, Theorem 14 with D- and
C-tracking) and five are not yet; comparator has not been run on them.

Each challenge is one file that imports LMLExplore and Mathlib modules only, no project modules
and no sibling helpers.

## The trust story

For each headline theorem `Garivier2016Optimal.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 1 (lower bound on `𝔼[τ_δ]`, for `δ ≤ 1/2`, erratum E1) | `charTime_mul_klBer_le_expectedStoppingTime` |
| Remark 2 (asymptotic lower bound) | `eventually_mul_log_le_expectedStoppingTime` |
| Theorem 5 (the optimal allocation from a scalar equation) | `mem_optAlloc_iff_exists_scalar` |
| Proposition 6 (positivity, continuity, ordering of `w*`) | `pos_of_mem_optAlloc`, `continuousAt_of_mem_optAlloc`, `le_of_mem_optAlloc_of_le` |
| Theorem 10 (the Bernoulli threshold `log(2t(K-1)/δ)`) | `measureReal_glrt_bernoulli_le` |
| Proposition 12 (the threshold `log(C t^α/δ)`, `C` depending on `δ`, erratum E2) | `exists_measureReal_glrt_expFamilyEvidence_le` |
| Proposition 13 (almost sure upper bound) | `stoppingTime_glrt_ne_top_and_limsup_le` |
| Theorem 14 (Track-and-Stop, D- and C-tracking) | `limsup_expectedStoppingTime_trackAndStop_div_log_le`, `limsup_expectedStoppingTime_cTrackAndStop_div_log_le` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, Tau Ceti and Mathlib are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
