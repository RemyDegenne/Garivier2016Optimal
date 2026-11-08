/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Probability.Martingale.RateFunction
public import LMLExplore.Probability.Moments.MGF.Dominated

/-!
# Self-normalized deviations of i.i.d. sums on a slice of sample sizes

Let `Z 0, Z 1, …` be i.i.d. real random variables with the law of an integrable `Y`, with rate
function `I` (`LMLExplore.rateFunction Y Q`), and let `μ̂_n = (Z 0 + ⋯ + Z (n - 1)) / n` be the
mean of the first `n` of them. Along the filtration of the past variables, `Z n` is independent of
the past, so its conditional moment generating function is that of `Y`
(`LMLExplore.HasMGFBound.hasCondMGFBound_of_indep`), and the time-uniform Chernoff bound of
`LMLExplore/Probability/Martingale/RateFunction.lean`, with every variable selected, bounds the
deviations of `μ̂_n` above the mean for all `n ≥ a` at once:
`P(∃ n ≥ a, Q[Y] < μ̂_n, r < I(μ̂_n)) ≤ exp (-(a r))`.

On a slice `a ≤ n < b` of sample sizes, the deviation `z ≤ n I(μ̂_n)` forces `I(μ̂_n) > z / b`, on
either side of the mean, so the probability that it happens on the slice is at most
`2 exp (-(a z / b))`. On the dyadic slices `2 ^ k ≤ n < 2 ^ (k + 1)` this is `2 exp (-z / 2)`, the
step of the peeling arguments of `SequentialLearning/RateFunctionDeviation.lean`.

## Main statements

* `ProbabilityTheory.iIndepFun.measure_exists_le_and_gt_and_lt_rateFunction_le`: the bound
  `P(∃ n ≥ a, Q[Y] < μ̂_n, r < I(μ̂_n)) ≤ exp (-(a r))`.
* `ProbabilityTheory.iIndepFun.measure_exists_le_and_lt_and_le_mul_rateFunction_le`: the two-sided
  bound `P(∃ n, a ≤ n < b, z ≤ n I(μ̂_n)) ≤ 2 exp (-(a z / b))` for `z > 0`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10, whose proof peels the sample sizes in the same way.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set

open scoped ENNReal

namespace LMLExplore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {Y : Ω' → ℝ} {Z : ℕ → Ω → ℝ}

/-- **Time-uniform Chernoff bound for i.i.d. sums, with the rate function.** Let `Z 0, Z 1, …` be
independent, each with the law of the integrable `Y`, with rate function `I`, and let `μ̂_n` be the
mean of the first `n` of them. For `a > 0` and `r ≥ 0`, the probability that `μ̂_n` is above the
mean of `Y` with `r < I(μ̂_n)` for some `n ≥ a` is at most `exp (-(a r))`. -/
lemma _root_.ProbabilityTheory.iIndepFun.measure_exists_le_and_gt_and_lt_rateFunction_le
    (h_indep : iIndepFun Z P) (hZm : ∀ i, Measurable (Z i))
    (h_ident : ∀ i, IdentDistrib (Z i) Y P Q) (hY : Integrable Y Q) {a r : ℝ} (ha : 0 < a)
    (hr : 0 ≤ r) :
    P {ω | ∃ n : ℕ, a ≤ n ∧ Q[Y] < (∑ i ∈ range n, Z i ω) / n ∧
      ENNReal.ofReal r < rateFunction Y Q ((∑ i ∈ range n, Z i ω) / n)} ≤
      ENNReal.ofReal (exp (-(a * r))) := by
  -- the filtration of the past variables, of which `Z n` is independent
  let ℱ : Filtration ℕ mΩ :=
    { seq n := ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (Z i) inferInstance
      mono' _ _ hnm := biSup_mono fun i hi ↦ lt_of_lt_of_le hi hnm
      le' _ := iSup₂_le fun i _ ↦ (hZm i).comap_le }
  have hX (n : ℕ) : Measurable[ℱ (n + 1)] (Z n) :=
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (n + 1)) ↦
      MeasurableSpace.comap (Z i) inferInstance) n (Nat.lt_succ_self n))
  have hψ (n : ℕ) : HasCondMGFBound (ℱ n) (ℱ.le n) (Z n) (cgf Y Q)
      (Ici 0 ∩ integrableExpSet Y Q) P := by
    refine HasMGFBound.hasCondMGFBound_of_indep
      (mgfDominatedOn_iff_hasMGFBound.1 (h_ident n).mgfDominatedOn) (hZm n) ?_
    have h := indep_iSup_of_disjoint (fun i ↦ (hZm i).comap_le) h_indep
      (S := {n}) (T := Set.Iio n) (by simp)
    exact (by simpa using h : Indep (MeasurableSpace.comap (Z n) inferInstance)
      (⨆ i ∈ Set.Iio n, MeasurableSpace.comap (Z i) inferInstance) P)
  -- every variable is selected
  have h := measure_exists_le_sum_and_gt_and_lt_rateFunction_le (ℱ := ℱ) (w := fun _ _ ↦ 1) hX hψ
    (fun _ ↦ measurable_const) (fun _ _ ↦ Or.inr rfl) hY ha hr
  simpa using h

/-- **Two-sided deviations of i.i.d. sums on a slice of sample sizes.** Let `Z 0, Z 1, …` be
independent, each with the law of the integrable `Y`, with rate function `I`, and let `μ̂_n` be the
mean of the first `n` of them. For `a > 0` and `z > 0`, the probability that `z ≤ n I(μ̂_n)` for
some `n` with `a ≤ n < b` is at most `2 exp (-(a z / b))`. -/
lemma _root_.ProbabilityTheory.iIndepFun.measure_exists_le_and_lt_and_le_mul_rateFunction_le
    (h_indep : iIndepFun Z P) (hZm : ∀ i, Measurable (Z i))
    (h_ident : ∀ i, IdentDistrib (Z i) Y P Q) (hY : Integrable Y Q) {a b z : ℝ} (ha : 0 < a)
    (hz : 0 < z) :
    P {ω | ∃ n : ℕ, a ≤ n ∧ (n : ℝ) < b ∧
      ENNReal.ofReal z ≤ n * rateFunction Y Q ((∑ i ∈ range n, Z i ω) / n)} ≤
      ENNReal.ofReal (2 * exp (-(a * (z / b)))) := by
  rcases le_or_gt b 0 with hb | hb
  · refine le_of_eq_of_le (b := 0) (measure_eq_zero_iff_ae_notMem.2 ?_) zero_le
    refine ae_of_all _ fun ω ⟨n, han, hnb, _⟩ ↦ ?_
    linarith
  have hr : 0 ≤ z / b := (div_pos hz hb).le
  have h_pos := h_indep.measure_exists_le_and_gt_and_lt_rateFunction_le hZm h_ident hY ha hr
  -- the deviations below the mean are those of `-Z` above the mean of `-Y`
  have h_indep_neg : iIndepFun (fun i ↦ -Z i) P :=
    h_indep.comp (fun _ x ↦ -x) fun _ ↦ measurable_neg
  have h_neg := h_indep_neg.measure_exists_le_and_gt_and_lt_rateFunction_le (Y := -Y)
    (fun i ↦ (hZm i).neg) (fun i ↦ (h_ident i).comp measurable_neg) hY.neg ha hr
  refine (measure_mono fun ω hω ↦ ?_).trans ((measure_union_le _ _).trans
    ((add_le_add h_pos h_neg).trans_eq ?_))
  · obtain ⟨n, han, hnb, hz_le⟩ := hω
    have hn : (0 : ℝ) < n := ha.trans_le han
    -- the rate function exceeds `z / b`
    have h_rate : ENNReal.ofReal (z / b) <
        rateFunction Y Q ((∑ i ∈ range n, Z i ω) / n) := by
      set I := rateFunction Y Q ((∑ i ∈ range n, Z i ω) / n)
      rcases eq_or_ne I ⊤ with hI | hI
      · rw [hI]
        exact ENNReal.ofReal_lt_top
      rw [← ENNReal.ofReal_toReal hI] at hz_le ⊢
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn.le,
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hz_le
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).2 ?_
      rw [div_lt_iff₀ hb]
      have hI0 : 0 < I.toReal := by
        by_contra! h
        nlinarith [ENNReal.toReal_nonneg (a := I)]
      nlinarith
    rcases lt_trichotomy Q[Y] ((∑ i ∈ range n, Z i ω) / n) with h | h | h
    · exact Or.inl ⟨n, han, h, h_rate⟩
    · -- the rate function vanishes at the mean
      rw [← h, rateFunction_integral hY] at hz_le
      simp only [mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hz_le
      linarith
    · refine Or.inr ⟨n, han, ?_, ?_⟩
      · simp only [Pi.neg_apply, sum_neg_distrib, neg_div, integral_neg]
        linarith
      · simpa [neg_div] using h_rate
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    ring_nf

end LMLExplore
