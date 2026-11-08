# Blueprint outline: Garivier and Kaufmann 2016

A. Garivier and E. Kaufmann, *Optimal Best Arm Identification with Fixed Confidence*, COLT 2016,
arXiv:1602.04589v2 (1 June 2016), in `source/arXiv-1602.04589v2/`. Citation key `GK16`; the
numbering below is that of this revision, which LMLExplore's citations use too.

## Setting and modelling

- **Models.** Vectors of means `μ : α → ℝ` of arms in one exponential family, the set `𝒮` of
  vectors with a unique best arm. In Lean: a kernel `ν : (α → ℝ) → Kernel α ℝ` with
  `ν μ a = ρ.expFamily id (ρ.natParam id (μ a))`, the family `(ρ, id)` of LMLExplore's
  `Probability/Distributions/ExponentialFamily/`, not degenerate (`∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c`), and
  the task `(baiTask ν id).restrict {μ | ∀ a, μ a ∈ ρ.expFamilyMeans id}`. For Bernoulli arms
  (Theorem 10), `Bandits.bernoulliBandit` of the means clamped to `[0, 1]`, on the means in `(0, 1)`.
- **Strategies.** LMLExplore's identification algorithms `IdentAlg Unit α ℝ α` (sampling rule,
  stopping rule, recommendation), `δ`-correctness `IdentTask.IsDeltaCorrect`, the expected
  stopping time `expectedStoppingTime A (Environment.bandit (ν μ))`, the characteristic time
  `IdentTask.charTime`, the optimal allocations `IdentTask.optAlloc`.
- **Stopping rule.** Chernoff's rule is LMLExplore's GLRT `IdentTask.glrt`. Its statistic is the
  GLR evidence of the family `expFamilyEvidence` (Proposition 12) or the plug-in statistic of the
  empirical means `IdentTask.plugInCost empMean'` (Theorems 10 and 14, Proposition 13). The two agree
  when the empirical means are means of the family; for Bernoulli arms the plug-in statistic is the
  GLR for every empirical mean in `[0, 1]`.
- **Track-and-Stop** is `IdentTask.trackAndStop` (D-tracking) and `IdentTask.cTrackAndStop`
  (C-tracking), tracking `w(μ̂(t))` and recommending `rec(μ̂(t))`, for any measurable `w` and `rec`
  that give an optimal allocation and the best arm on the vectors of means with a unique best arm.

## Results of the paper and where they are

| Result | Content | Where | Lean |
|---|---|---|---|
| Theorem 1 | `𝔼[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)` for `δ`-PAC strategies | LMLExplore (every task) | `charTime_mul_klBer_le_expectedStoppingTime`, for `δ ≤ 1/2` (erratum E1) |
| Remark 2 | `liminf 𝔼[τ_δ] / log (1/δ) ≥ T*(μ)` | LMLExplore | `eventually_mul_log_le_expectedStoppingTime` |
| Lemma 3 | `inf_{Alt} ∑ w_a d(μ_a, λ_a) = min_{a ≠ 1} (w_1 + w_a) I_{w_1/(w_1+w_a)}(μ_1, μ_a)` | LMLExplore | `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf_expFamilyPairCost` |
| Lemma 4 | the pair costs are equal at `w*` | LMLExplore | `LMLExplore.Identification.answerValue_baiTask_restrict_eq_of_mem_optAlloc` |
| Theorem 5 | `w*` from the scalar equation `F(y*) = 1` | uniqueness in LMLExplore; the equation is Identification 3.4 | `mem_optAlloc_iff_exists_scalar` |
| Proposition 6 | `w* > 0`; `w*` continuous; `w*` ordered like the means | 1, 2 in LMLExplore; 3 nowhere | `pos_of_mem_optAlloc`, `continuousAt_of_mem_optAlloc`, `le_of_mem_optAlloc_of_le` |
| Lemma 7 | C-tracking: `N_a(t) ≥ √(t + K²) - 2K`, tracking up to `K (1 + √t)` | LMLExplore | `CTracking.abs_pullCount_sub_sum_le_mul_one_add_sqrt`, `CTracking.sqrt_add_sub_le_pullCount` |
| Lemma 8 | D-tracking: `N_a(t) ≥ (√t - K/2)₊ - 1`, and convergence | LMLExplore | `DTracking.sqrt_sub_sub_one_lt_pullCount`, `DTracking.tendsto_pullCount_div` |
| Proposition 9 | `N_a(t)/t → w*_a` a.s. for C- and D-tracking | LMLExplore, given converging targets | `CTracking.tendsto_pullCount_div`, `DTracking.tendsto_pullCount_div` |
| Theorem 10 | Bernoulli: threshold `log(2t(K-1)/δ)` is `δ`-PAC | Identification 4.2 | `measureReal_glrt_bernoulli_le` |
| Lemma 11 | Krichevsky–Trofimov: `p_u(x)/kt(x) ≤ 2√n` | Identification 4.2 | (prerequisite of Theorem 10) |
| Proposition 12 | threshold `log(C t^α/δ)`, `α > 1`, is `δ`-PAC, with `C` depending on `δ` (erratum E2) | Identification 4.2 (LMLExplore has `K log(2t(t+1)) + x_δ`) | `exists_measureReal_glrt_expFamilyEvidence_le` |
| Proposition 13 | a.s. `limsup τ_δ/log(1/δ) ≤ α T*(μ)` | Identification 4.4 | `stoppingTime_glrt_ne_top_and_limsup_le` |
| Theorem 14 | `limsup 𝔼[τ_δ]/log(1/δ) ≤ α T*(μ)`, C- or D-tracking | LMLExplore (stronger: no `α`) | `limsup_expectedStoppingTime_trackAndStop_div_log_le`, `limsup_expectedStoppingTime_cTrackAndStop_div_log_le` |
| Lemmas 15, 17 | tracking a cumulated sum; tracking a changing sequence | LMLExplore | `Tracking.lean` |
| Lemma 18 | `t ≥ ... ⇒ c₁ t ≥ log(c₂ t^α)` for `α ∈ [1, e/2]` | not needed (LMLExplore's reduction avoids it) | – |
| Lemmas 19, 20 | concentration under tracking; growth of `Z(t)` on `ℰ_T` | LMLExplore | `CTracking/DTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top`, `IdentTask.eventually_expectedStoppingTime_glrt_le` |
| Section 5 | experiments | not formalized | – |
| Appendix F (Theorem 21, Lemma 22) | fixed-budget remarks | not formalized | – |

Lean names without a prefix are in the namespace `Garivier2016Optimal`; the others are LMLExplore's.

## Statement choices

- **Theorem 1** holds for `δ ≤ 1 / 2` only (erratum E1). The Lean statement adds that hypothesis.
- **Proposition 12** holds with a constant `C` that depends on `δ` (erratum E2). The Lean statement
  fixes `δ` before the constant; `C` still depends neither on the family nor on the sampling rule.
- **Theorem 5** is stated as an equivalence in equation form (weights `x` with `x_a = 1`, a common
  value `y` of the pair costs `g_b(x_b)`, and `F`'s equation), not with the inverse functions
  `x_b = g_b⁻¹` and the bisection on `F`.
- **Proposition 6, part 2** is the continuity at `μ` of every selection of the optimal allocations
  near `μ`, since `w*` is a set-valued map in LMLExplore.
- **Theorem 14** is stated with the paper's constant `α T*(μ)`. LMLExplore proves `T*(μ)` for every
  polynomial `r`; the paper's restriction `α ∈ [1, e/2]` is kept as a hypothesis.
- **Propositions 12, 13 and Theorem 10** hold for every sampling rule and every recommendation rule;
  the statements quantify over both.

## Part II prerequisites (library-shaped, for `ForLMLExplore/`)

1. The scalar equation of the optimal allocation (Theorem 5): Identification 3.4.
2. The ordering of the optimal allocation (Proposition 6, part 3): no target, staged.
3. The Krichevsky–Trofimov mixture and the informational threshold for Bernoulli arms
   (Lemma 11, Theorem 10): Identification 4.2.
4. The deviational thresholds `log(C t^α/δ)` (Proposition 12): Identification 4.2.
5. The almost sure sample complexity bound (Proposition 13): Identification 4.4.
