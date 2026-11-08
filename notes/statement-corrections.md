# Statement corrections

Errors found after phase 1 in this project's own headline statements, where the paper is right,
with the user's decisions. Errors in the paper are in `notes/paper-errata.md`.

## Theorem 5: at least two arms

- **Statement:** `Garivier2016Optimal.mem_optAlloc_iff_exists_scalar`, as frozen at the end of
  phase 1.
- **Problem:** the statement has no hypothesis that there is an arm other than the best arm `a`,
  and it is false for a single arm: the allocation `1` is optimal, since there are no
  alternatives, while the right-hand side asks for an empty sum equal to `1`. The paper is not
  affected: it leaves `K ≥ 2` implicit, and its statement uses `μ_2`.
- **Evidence:** a derivation of `False` from the statement for one Gaussian arm of variance `1`,
  checked with `lake env lean` (`notes/phase2-decisions.md`, Theorem 5).
- **Found:** round of 2026-11-08 (commit cc669c7), first recorded as erratum E3 of the paper.
- **Decision:** 2026-11-08, add the hypothesis `hb : ∃ b, b ≠ a` and regenerate the challenge.
