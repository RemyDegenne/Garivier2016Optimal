/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.SequentialLearning.RateFunctionDeviation
public import LMLExplore.SequentialLearning.ExpFamilyDeviation

/-!
# Peeled deviations of the empirical means for rewards dominated by exponential families

If the rewards of each arm `a` are dominated by the member of mean `μ_a` of an exponential family
`(ρ_a, T_a)`, the rate function of the arm is at least the extended divergence `dbar_a(·, μ_a)` of
the family (`MeasureTheory.Measure.expFamilyRate`). The peeled deviation bound of
`SequentialLearning/RateFunctionDeviation.lean` for the rate functions therefore holds for the
generalized likelihood ratio statistic `∑ a, N_a dbar_a(μ̂_a, μ_a)` of the empirical means, as
LMLExplore's `measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le` does for the
union-bound thresholds. It is the deviation inequality behind the thresholds `log (C t ^ p / δ)`
of [GK16, Proposition 12].

## Main statements

* `LMLExplore.measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le`: in a run
  of any algorithm,
  `P(∃ t, 2 (K (η log₂ t + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a, N_a(t) dbar_a(μ̂_a(t), μ_a))` is
  at most `(x / K) ^ K exp (K - x)` for `η > 0` and `x ≥ K`, for rewards dominated by members of
  exponential families.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning

namespace LMLExplore

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {x : ℝ}

/-- **Peeled time-uniform deviations of the empirical means along a run, for rewards dominated by
exponential families** (the deviation inequality of [GK16, Proposition 12]). In a run of any
algorithm against `Environment.bandit ν`, let the rewards of each arm `a` be dominated on
`Set.univ`, in moment generating function, by the member of mean `μ a` of the exponential family
`(ρ a, T a)`, with extended divergence `dbar_a` (`MeasureTheory.Measure.expFamilyRate`). Then for
`η > 0` and `x ≥ K`, with `K` the number of arms, the probability that at some round `t`, the pull
counts `N_a(t)` and the empirical means `μ̂_a(t)` satisfy
`2 (K (η log₂ t + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a, N_a(t) dbar_a(μ̂_a(t), μ a)`, with
`log₂ t = Nat.log 2 t`, is at most `(x / K) ^ K exp (K - x)`. -/
lemma measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    {η : ℝ} (hη : 0 < η) (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (2 * (Fintype.card α *
        (η * Nat.log 2 t + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a, pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the rewards are integrable, and the rate function of each arm is at least `dbar_a(·, μ a)`
  have h_int (a : α) : Integrable id (ν a) := (hν a).integrable (by
    simpa only [Set.univ_inter] using Measure.zero_mem_interior_integrableExpSet_expFamily
      (Measure.natParam_mem_interior_integrableExpSet (hμ a)))
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le h h_int hη hx)
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ht.trans (sum_le_sum fun a _ ↦ ?_)⟩
  rw [Measure.expFamilyRate_def]
  gcongr
  exact ((hν a).mono (Set.subset_univ _)).rateFunction_le _

end LMLExplore
