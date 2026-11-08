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

## E2. Proposition 12's constant depends on `δ`

- **Where:** arXiv:1602.04589v2, Proposition 12 (Section 3.2): "Let `δ ∈ (0, 1)` and `α > 1`. There
  exists a constant `C = C(α, K)` such that whatever the sampling strategy, using Chernoff's
  stopping rule with the threshold `β(t, δ) = log (C t^α / δ)` ensures that for all `μ ∈ 𝒮`,
  `P_μ(τ_δ < ∞, â_{τ_δ} ≠ a*) ≤ δ`", and its proof in Appendix C.
- **Error:** no `C(α, K)` independent of `δ` works for every `δ`; the constant must depend on `δ`.
  The proof bounds the probability of error by
  `∑_t e^{K+1} (β(t, δ)² log t / K)^K e^{-β(t, δ)}`, which for `β(t, δ) = log (C t^α / δ)` is
  `(δ / C) ∑_t (e^{K+1} / K^K) (log² (C t^α / δ) log t)^K / t^α`. The condition it then puts on
  `C`, `∑_t (e^{K+1} / K^K) (log² (C t^α) log t)^K / t^α ≤ C`, drops the `δ` inside the
  logarithm. The sum with the `δ` grows like `log(1/δ)^{2K}` as `δ → 0`, so the `C` the argument
  gives grows with `1/δ`.
- **Correction:** for every `α > 1` and `δ ∈ (0, 1)` there is `C = C(α, K, δ)`: the proof works
  with any `C` such that `∑_t (e^{K+1} / K^K) (log² (C t^α / δ) log t)^K / t^α ≤ C`, which exists
  since the left side grows like a power of `log C`, and can be taken of order `log(1/δ)^{2K}`.
  Consequence: Theorem 14 takes thresholds `log (r(t) / δ)` with `r` independent of `δ`, so the
  remark at the end of Section 4 that combines it with Proposition 12 also needs Theorem 14 for an
  `r` that depends on `δ` with `log r(t) = o(log(1/δ))`, as the corrected `C` does.
- **Lean:** `Garivier2016Optimal.exists_measureReal_glrt_expFamilyEvidence_le` takes `δ` before
  the existential `C`; the constant still depends neither on the family nor on the sampling rule.
- **Kind:** wrong dependence of a constant, from an error in the last step of the proof.
- **Found:** check of the statements against the paper, 2026-11-08.
