# Paper roadmap: Optimal Best Arm Identification with Fixed Confidence

Paper: RemyDegenne/Garivier2016Optimal · LMLExplore 5113b88ad95f · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-08

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Lower bound for δ-correct strategies [GK16, Theorem 1, Remark 2] | exists | `LMLExplore.Identification.IdentTask.IsDeltaCorrect.charTime_mul_le_expectedStoppingTime` | – | |
| R2 | Closed form of the cost of the alternatives [GK16, Lemma 3] | exists | `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf_expFamilyPairCost` | – | |
| R3 | The pair costs are equal at the optimal allocation [GK16, Lemma 4] | exists | `LMLExplore.Identification.answerValue_baiTask_restrict_eq_of_mem_optAlloc` | – | |
| R4 | Existence and uniqueness of the optimal allocation [GK16, Theorem 5] | exists | `LMLExplore.Identification.exists_optAlloc_baiTask_restrict_eq_singleton` | – | |
| R5 | The optimal allocation from the scalar equation `F(y*) = 1` [GK16, Theorem 5] | target | Identification 3.4 | todo | `ForLMLExplore/Identification/Task/BestArmScalar.lean` |
| R6 | Positivity and continuity of the optimal allocation [GK16, Proposition 6, parts 1–2] | exists | `LMLExplore.Identification.pos_of_mem_optAlloc_baiTask_restrict` | – | |
| R7 | The optimal allocation is ordered like the means [GK16, Proposition 6, part 3] | staged | S1 | todo | `ForLMLExplore/Identification/Task/BestArmOrder.lean` |
| R8 | C-tracking and D-tracking guarantees [GK16, Lemmas 7, 8, 15, 17, Proposition 9] | exists | `LMLExplore.Identification.CTracking.tendsto_pullCount_div` | – | |
| R9 | The Krichevsky–Trofimov mixture and the informational threshold for Bernoulli arms [GK16, Lemma 11, Theorem 10] | target | Identification 4.2 | todo | `ForLMLExplore/Identification/KTThreshold.lean` |
| R10 | The deviational thresholds `log(C t^α/δ)` [GK16, Proposition 12] | target | Identification 4.2 | todo | `ForLMLExplore/Identification/DeviationalThreshold.lean` |
| R11 | The almost sure sample complexity bound of the GLRT [GK16, Proposition 13] | target | Identification 4.4 | todo | `ForLMLExplore/Identification/AlmostSure.lean` |
| R12 | Expected sample complexity of Track-and-Stop [GK16, Theorem 14, Lemmas 19, 20] | exists | `LMLExplore.Identification.IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt` | – | |
| R13 | The paper's statements, specializing the items above to its setting | paper | | todo | `GK2016/Theorem1.lean`, `GK2016/Theorem5.lean`, `GK2016/Proposition6.lean`, `GK2016/Theorem10.lean`, `GK2016/Proposition12.lean`, `GK2016/Proposition13.lean`, `GK2016/Theorem14.lean` |

## Notes

- R1: LMLExplore's lower bound needs `δ ≤ 1/2`, which the paper omits (`notes/paper-errata.md`,
  E1). The asymptotic form of Remark 2 is
  `LMLExplore.Identification.IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`.
- R5: Identification 3.4 asks for the scalar equation whenever the inner infimum has a unique
  minimizer for all weights, in particular for a common family and for Gaussian arms with
  arm-dependent known variances, not only for one exponential family as in the paper.
- R6: continuity is `LMLExplore.Identification.continuousAt_of_mem_optAlloc_baiTask_restrict`.
- R8: D-tracking is `LMLExplore.Identification.DTracking`; LMLExplore's convergence of the
  proportions assumes converging targets, which Proposition 9 obtains from the continuity of `w*`.
- R9: Identification 4.2 asks for the Bernoulli thresholds through the Krichevsky–Trofimov mixture,
  next to the other union-bound thresholds; the mixture bound `sup p_u(x)/kt(x) ≤ 2√n` is a
  prerequisite and belongs with it.
- R10: Identification 4.2 asks for an explicit `C(α, K)`, for arms dominated by any exponential
  families, from the two-sided bound of Layer 1.2; the paper's existential `C` is a consequence.
- R11: Identification 4.4 states it for any statistic with thresholds `log(1/δ) + o(t)`, any
  estimator converging almost surely and proportions converging to a set `W` of allocations, with
  every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`; the paper's `α T*(μ)` is a case.
- R12: LMLExplore proves `𝔼[τ_δ] ≤ c log(1/δ)` for every `c > T*(μ)`, stronger than the paper's
  `α T*(μ)`; the C-tracking form is
  `LMLExplore.Identification.IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`.

## Proposed targets

### S1. Ordering of the optimal allocation of best arm identification

For best arm identification with arms in exponential families with a common family (Identification
3.4), at a vector of means `μ` with unique best arm `a`, prove that the optimal allocation is
ordered like the means on the other arms: if `μ c ≤ μ b < μ a`, then `w*_c(μ) ≤ w*_b(μ)`
[GK16, Proposition 6]. Find the most general form the argument supports: the pair cost
`g_b(x) = d(μ_a, m_b(x)) + x d(μ_b, m_b(x))` decreases in `μ_b` for fixed `x`, so that
`x_b(y) = g_b⁻¹(y)` increases in `μ_b`; the statement then holds for every family in which the
divergence `d(μ_a, ·)` and `d(·, m)` have the monotonicity of Layer 1.4, and for Gaussian arms with
a common variance it is explicit. Place it next to the scalar equation of Identification 3.4.
