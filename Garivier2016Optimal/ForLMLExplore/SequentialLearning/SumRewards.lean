/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.SequentialLearning.SumRewards
public import Mathlib.Probability.StrongLaw

/-!
# The strong law of large numbers for the empirical means of a run

In a run of any algorithm against the stochastic environment `Environment.bandit ν`, the rewards
of the successive pulls of an arm `a` are i.i.d. with law `ν a` (LML's
`Bandits.iIndepFun_rewardByCount_add_one_action`, on the product of the probability space with the
stream of rewards). After `N_a(t)` pulls, the empirical mean of `a` is the mean of its first
`N_a(t)` rewards. The strong law of large numbers therefore makes the empirical mean of `a`
converge almost surely to the mean of `ν a`, on the event that `a` is pulled infinitely often.

## Main statements

* `LMLExplore.ae_tendsto_empMean_of_tendsto_pullCount`: almost surely, the empirical mean of every
  arm whose number of pulls tends to infinity converges to the mean of its law.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Filter Topology

namespace LMLExplore

variable {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [DecidableEq α]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- After `t` rounds, the sum of the rewards of the arm `a` is the sum of its first `N_a(t)`
rewards by count. -/
lemma sum_range_rewardByCount_add_one_eq_sumRewards (a : α) (t : ℕ) (ω : Ω × (ℕ → α → ℝ)) :
    ∑ m ∈ range (pullCount A a t ω.1), rewardByCount A R a (m + 1) ω = sumRewards A R a t ω.1 := by
  rw [← sum_rewardByCount_eq_sumRewards a t ω, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [add_comm 1]

variable [Countable α] [MeasurableSingletonClass α]

/-- **The strong law of large numbers for the empirical means** of a run of any algorithm against
the stochastic environment `Environment.bandit ν` with integrable rewards: almost surely, for every
arm `a` pulled infinitely often, the empirical mean of `a` converges to the mean of `ν a`. -/
lemma ae_tendsto_empMean_of_tendsto_pullCount
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a)) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun t ↦ pullCount A a t ω) atTop atTop →
      Tendsto (fun t ↦ empMean A R a t ω) atTop (𝓝 (∫ x, x ∂(ν a))) := by
  rw [ae_all_iff]
  intro a
  -- The rewards by count of `a` are i.i.d. with law `ν a` under `P.prod (streamMeasure ν)`.
  have h_id : IdentDistrib (rewardByCount A R a (0 + 1)) id
      (P.prod (Bandits.streamMeasure ν)) (ν a) :=
    Bandits.identDistrib_rewardByCount_id h a 1 one_ne_zero
  have h_slln := strong_law_ae_real (fun m ↦ rewardByCount A R a (m + 1))
    (h_id.integrable_iff.2 (hν a))
    (fun _ _ hij ↦ (Bandits.iIndepFun_rewardByCount_add_one_action h a).indepFun hij)
    (fun m ↦ (Bandits.hasLaw_rewardByCount_add_one h a m).identDistrib
      (Bandits.hasLaw_rewardByCount_add_one h a 0))
  rw [h_id.integral_eq] at h_slln
  -- The event depends only on the first coordinate.
  filter_upwards [Measure.ae_ae_of_ae_prod h_slln] with ω hω hN
  obtain ⟨s, hs⟩ := hω.exists
  refine (hs.comp hN).congr fun t ↦ ?_
  simp only [Function.comp_apply, empMean]
  rw [← sum_range_rewardByCount_add_one_eq_sumRewards a t (ω, s)]

end LMLExplore
