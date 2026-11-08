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
| R7 | The optimal allocation is ordered like the means [GK16, Proposition 6, part 3] | staged | S1 | proved | `ForLMLExplore/Identification/Task/BestArmOrder.lean`, `ForLMLExplore/Probability/Distributions/ExponentialFamily/Mean.lean` |
| R8 | C-tracking and D-tracking guarantees [GK16, Lemmas 7, 8, 15, 17, Proposition 9] | exists | `LMLExplore.Identification.CTracking.tendsto_pullCount_div` | – | |
| R9 | The Krichevsky–Trofimov mixture and the informational threshold for Bernoulli arms [GK16, Lemma 11, Theorem 10] | target | Identification 4.2 | todo | `ForLMLExplore/Identification/KTThreshold.lean` |
| R10 | The deviational thresholds `log(C t^α/δ)` [GK16, Proposition 12] | target | Identification 4.2 | todo | `ForLMLExplore/Identification/DeviationalThreshold.lean` |
| R11 | The almost sure sample complexity bound of the GLRT [GK16, Proposition 13] | target | Identification 4.4 | proved | `ForLMLExplore/Identification/AlmostSure.lean`, `ForLMLExplore/SequentialLearning/SumRewards.lean` |
| R12 | Expected sample complexity of Track-and-Stop [GK16, Theorem 14, Lemmas 19, 20] | exists | `LMLExplore.Identification.IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt` | – | |
| R13 | The paper's statements, specializing the items above to its setting | paper | | todo | `GK2016/Basic.lean`, `GK2016/Theorem1.lean`, `GK2016/Theorem5.lean`, `GK2016/Proposition6.lean`, `GK2016/Theorem10.lean`, `GK2016/Proposition12.lean`, `GK2016/Proposition13.lean`, `GK2016/Theorem14.lean` |
| R14 | Continuity of the cost of the alternatives of best arm identification near a model, and openness of its answer sets, for arms in an exponential family | refactor | `LMLExplore.Identification.continuousWithinAt_altCost_baiTask_restrict` | PR #242 | `ForLMLExplore/Identification/Task/BestArm.lean` |

## Notes

- R1: LMLExplore's lower bound needs `δ ≤ 1/2`, which the paper omits (`notes/paper-errata.md`,
  E1). The asymptotic form of Remark 2 is
  `LMLExplore.Identification.IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`.
- R5: Identification 3.4 asks for the scalar equation whenever the inner infimum has a unique
  minimizer for all weights, in particular for a common family and for Gaussian arms with
  arm-dependent known variances, not only for one exponential family as in the paper.
- R5: the paper's Theorem 5 is false for a single arm (`notes/paper-errata.md`, E3), so the
  library statement needs an arm `b ≠ a`, as `betaAnswerValue_baiTask_restrict_pos` does.
- R6: continuity is `LMLExplore.Identification.continuousAt_of_mem_optAlloc_baiTask_restrict`.
- R7: proved without the scalar equation of R5, from the equality of the pair costs at the
  optimal allocation [GK16, Lemma 4] and two monotonicity properties of the pair cost: it
  increases in the weight of the other arm (`strictMonoOn_expFamilyPairCost`), and it decreases
  in the lower mean (`strictAntiOn_expFamilyPairCost_right`, `antitoneOn_expFamilyPairCost_right`,
  in `ForLMLExplore/Probability/Distributions/ExponentialFamily/Mean.lean`; they belong in
  LMLExplore's `Probability/Distributions/ExponentialFamily/Mean.lean`, after
  `strictMonoOn_expFamilyPairCost`). The ordering holds for every statistic `T` and for the
  `β`-optimal allocations of `Identification/Task/TopTwo/BestArm.lean`: for `β > 0`, and strictly
  for `β ∈ (0, 1)`. The optimal allocation is the case `β = w a`, with both the order and the
  strict order as equivalences, `w c ≤ w b ↔ μ c ≤ μ b`.
- R8: D-tracking is `LMLExplore.Identification.DTracking`; LMLExplore's convergence of the
  proportions assumes converging targets, which Proposition 9 obtains from the continuity of `w*`.
- R9: Identification 4.2 asks for the Bernoulli thresholds through the Krichevsky–Trofimov mixture,
  next to the other union-bound thresholds; the mixture bound `sup p_u(x)/kt(x) ≤ 2√n` is a
  prerequisite and belongs with it.
- R10: the constant must depend on `δ`: no `C(α, K)` makes `log(C t^α/δ)` `δ`-correct for every
  `δ` (`notes/paper-errata.md`, E2). Identification 4.2 asks for an explicit `C(α, K)`, for arms
  dominated by any exponential families, from the two-sided bound of Layer 1.2; prove it with an
  explicit `C(α, K, δ)` instead, from which the paper's corrected existential `C` follows.
- R11: Identification 4.4 states it for any statistic with thresholds `log(1/δ) + o(t)`, any
  estimator converging almost surely and proportions converging to a set `W` of allocations, with
  every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`; the paper's `α T*(μ)` is a case.
  `ForLMLExplore/Identification/AlmostSure.lean` proves it so, for the plug-in statistic of any
  estimator into a topological space of models, a compact `W` with `D(·, ·, ¬i)` lower
  semicontinuous at `{θ} × W`, as in `IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le`
  (`IdentTask.ae_eventually_stoppingTime_glrt_le`), with almost sure stopping when the infimum is
  positive (`IdentTask.ae_stoppingTime_glrt_ne_top`). The file is a new LMLExplore file
  `Identification/AlmostSure.lean`, after `Identification/TrackAndStop.lean`; its
  `log_div_le_log_one_div_add_log` and `eventually_log_le_mul_of_isBigO` are the inline steps of
  `IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO`, which can then use them. The
  strong law of large numbers for the empirical means of a run
  (`ae_tendsto_empMean_of_tendsto_pullCount`, from LML's i.i.d. rewards by count) is the
  prerequisite that turns proportions bounded away from zero into the almost sure convergence of
  the empirical means; it goes to LMLExplore's `SequentialLearning/SumRewards.lean`.
  Identification 5.2 asks for the almost sure version of Track-and-Stop's optimality through it.
- R12: LMLExplore proves `𝔼[τ_δ] ≤ c log(1/δ)` for every `c > T*(μ)`, stronger than the paper's
  `α T*(μ)`; the C-tracking form is
  `LMLExplore.Identification.IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`.
- R14: `continuousWithinAt_altCost_baiTask_restrict` is a private lemma of LMLExplore's
  `Identification/Task/BestArm.lean`, and the Track-and-Stop bounds of R12 take its conclusion as a
  hypothesis, so that applying them to best arm identification needs it public. The port makes it
  public, in place, and adds `isOpen_answerSet_baiTask_restrict` next to `isOpen_answerSet_baiTask`:
  for an open set `S` of vectors of means, the models of the task restricted to `S` with unique
  best arm `a` form an open set, which gives the recommendation of `a` near `μ` that the same
  bounds assume.

## Proposed targets

### S1. Ordering of the optimal allocation of best arm identification

For best arm identification with arms in an exponential family (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), at a vector of means `μ` of the family with
unique best arm `a`, prove that the optimal allocation is ordered like the means on the other arms:
for `b, c ≠ a`, `w*_c(μ) ≤ w*_b(μ) ↔ μ c ≤ μ b` and `w*_c(μ) < w*_b(μ) ↔ μ c < μ b`
[GK16, Proposition 6]. Prove it for the `β`-optimal allocations of the Top Two algorithms too, for
`β > 0` (strictly for `β ∈ (0, 1)`), of which the optimal allocation is the case `β = w*_a(μ)`.
The equality of the pair costs at the optimal allocation [GK16, Lemma 4] gives it, with two
monotonicity properties of the pair cost `w_a d(μ a, m) + w_b d(μ b, m)`, where `m` is the
weighted mean: it increases in `w_b`, and it decreases in the lower mean `μ b ≤ μ a`, strictly for
positive weights. The second goes next to `strictMonoOn_expFamilyPairCost` in
`Probability/Distributions/ExponentialFamily/Mean.lean`, and the ordering next to the `β`-optimal
allocations of best arm identification (`Identification/Task/TopTwo/BestArm.lean`). Gaussian arms
with a common variance are a case.
