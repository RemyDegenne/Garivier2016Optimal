# Errata of "Optimal Best Arm Identification with Fixed Confidence"

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Theorem 1 needs `δ ≤ 1/2`

- **Where:** arXiv:1602.04589v2, Theorem 1 (Section 2.1): "Let `δ ∈ (0, 1)`. For any `δ`-PAC
  strategy and any bandit model `μ ∈ 𝒮`, `𝔼_μ[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)`."
- **Error:** the bound fails for `δ ∈ (1/2, 1)`. With two arms, the strategy that samples one
  observation and then recommends an arm chosen uniformly at random is `δ`-PAC for every
  `δ ≥ 1/2`, with `𝔼_μ[τ_δ] = 1`, while `kl(δ, 1 - δ) → ∞` as `δ → 1`, so that
  `T*(μ) kl(δ, 1 - δ) > 1` for `δ` close to `1`. The proof applies the transportation lemma of
  [KCG16, Lemma 1], whose bound `kl(P_μ(E), P_λ(E)) ≥ kl(1 - δ, δ)` uses
  `P_μ(E) ≥ 1 - δ ≥ δ ≥ P_λ(E)`, that is `δ ≤ 1/2`.
- **Correction:** state Theorem 1 for `δ ∈ (0, 1/2]`. Remark 2 and the asymptotic optimality of
  Theorem 14 are unaffected, since they concern `δ → 0`.
- **Lean:** `Garivier2016Optimal.charTime_mul_klBer_le_expectedStoppingTime` has the hypothesis
  `δ ≤ 1 / 2`, as LMLExplore's `IdentTask.IsDeltaCorrect.charTime_mul_le_expectedStoppingTime`.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement writing, 2026-11-08.
