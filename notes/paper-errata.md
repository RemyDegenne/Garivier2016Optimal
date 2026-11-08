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
  Its proof (round of 2026-11-08) does not follow Appendix C: it peels the numbers of pulls of each
  arm over dyadic slices and combines the arms by independence in the reward stream model. It
  gives `C = δ exp (c_{α,K} + 2 x_δ)` with `c_{α,K} = 2 K log (2 / (1 - 2^{-α/(2K)}))` and
  `x_δ = log (1/δ) + 2K (1 + log (1 + log (1/δ)))`, so `log (C t^α / δ) = α log t + c_{α,K} + 2 x_δ`,
  for every `α > 0`.
- **Kind:** wrong dependence of a constant, from an error in the last step of the proof.
- **Found:** check of the statements against the paper, 2026-11-08.

## E3. Appendix C.1: the density of the Krichevsky–Trofimov prior

- **Where:** arXiv:1602.04589v2, Appendix C.1 (proof of Theorem 10), the definition
  "`kt(x) = ∫_0^1 1 / √(π u (1 - u)) p_u(x) du`" and the density
  "`h(u) = 1 / √(π u (1 - u)) 𝟙_{[0, 1]}(u)`" of the prior under which `P̃` is defined.
- **Error:** `∫_0^1 du / √(π u (1 - u)) = π / √π = √π ≠ 1`, so `h` is not a probability density,
  and `kt` and `P̃` are not probability distributions. Lemma 11 in Section 3.2 has the right
  normalization, `1 / (π √(u (1 - u)))`, and the appendix itself names the prior
  `Beta(1/2, 1/2)`.
- **Correction:** `h(u) = 1 / (π √(u (1 - u)))` on `(0, 1)`, the density of `Beta(1/2, 1/2)`, as
  in Lemma 11.
- **Lean:** the prior is `betaMeasure (1 / 2) (1 / 2)`
  (`LMLExplore.div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure`,
  `LMLExplore.measure_exists_log_two_mul_mul_lt_klBer_le`).
- **Kind:** typo.
- **Found:** round of 2026-11-08 (the informational threshold, Theorem 10).

## E4. Appendix C.1: an arm without observations

- **Where:** arXiv:1602.04589v2, Appendix C.1 (proof of Theorem 10): "we have that
  `max_{μ'_a ≥ μ'_b} p_{μ'_a}(x^a_t) p_{μ'_b}(x^b_t) ≤ 2t × kt(x^a_t) kt(x^b_t)`, which follows from
  Lemma 11 stated in the main text and the fact that for `n_a, n_b` such that `n_a + n_b ≤ t`,
  `4 √n_a √n_b ≤ 2 (n_a + n_b) ≤ 2t`."
- **Error:** the bound `2 √n` of Lemma 11 fails for `n = 0`: the empty sequence has
  `p_u = kt = 1`, so the ratio is `1 > 2 √0`. When one of the two arms has no observation, the
  product of the two bounds of Lemma 11 is `0`, and the argument as written does not give the
  inequality.
- **Correction:** the inequality holds for `t ≥ 1`: if `n_a = 0`, the ratio of the arm `a` is `1`
  and that of `b` is at most `2 √n_b ≤ 2 n_b ≤ 2t`; if `n_a = n_b = 0`, the product is
  `1 ≤ 2t`. At `t = 0` the statistic vanishes and the stopping rule does not stop.
- **Lean:** `LMLExplore.measure_exists_log_two_mul_mul_lt_klBer_le` bounds each arm with the
  factor `2 √N`, or `1` for an arm without observations, and the product of the two factors by
  `2 n` once one of the arms has an observation. Theorem 10 is unaffected.
- **Kind:** gap in the proof.
- **Found:** round of 2026-11-08 (the informational threshold, Theorem 10).
