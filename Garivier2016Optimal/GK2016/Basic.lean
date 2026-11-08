/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop
public import Garivier2016Optimal.ForLMLExplore.Identification.Task.BestArm

/-!
# The setting of [GK16] against the hypotheses of LMLExplore

The paper's arms are the members `ν μ a = ρ.expFamily id (ρ.natParam id (μ a))` of one exponential
family `(ρ, id)`, indexed by their means, and best arm identification is restricted to the vectors
of means of the family. This file proves the hypotheses that LMLExplore's results on best arm
identification and on Track-and-Stop put on the arms and on the recommendation, in this setting,
and the passage from LMLExplore's eventual bounds `f δ ≤ c log (1 / δ)` to the paper's `limsup`.
They are used by the proofs of [GK16, Proposition 13] and [GK16, Theorem 14].

## Main statements

* `Garivier2016Optimal.limsup_div_log_le`: from `f δ ≤ c log (1 / δ)` for small `δ`, for every
  `c > t`, to `limsup_{δ → 0} f δ / log (1 / δ) ≤ t`.
* `Garivier2016Optimal.eventually_mem_M_and_rec_eq`: near a model with unique best arm `a`, the
  vectors of means are models, and the recommendation of the best arm is `a`.
* `Garivier2016Optimal.klDiv_eq_expFamilyDiv`, `Garivier2016Optimal.mgfDominatedOn_expFamily`: the
  hypotheses on the arms.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning LMLExplore
  LMLExplore.Identification Filter Topology Real

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} {mα : MeasurableSpace α} (ν : (α → ℝ) → Kernel α ℝ)
  [∀ μ, IsMarkovKernel (ν μ)] (ρ : Measure ℝ) {μ : α → ℝ}

/-- The bounds `f δ ≤ c log (1 / δ)` for all small enough `δ`, for every `c > t`, give
`limsup_{δ → 0} f δ / log (1 / δ) ≤ t`, the form in which [GK16, Proposition 13] and
[GK16, Theorem 14] state them. -/
lemma limsup_div_log_le {f : ℝ → ℝ≥0∞} {t : ℝ≥0∞}
    (h : ∀ c : ℝ≥0, t < c → ∀ᶠ δ in 𝓝[>] 0, f δ ≤ c * ENNReal.ofReal (log (1 / δ))) :
    limsup (fun δ ↦ f δ / ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤ t := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  obtain ⟨c', hc', hc'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  exact (limsup_le_of_le (h := (h c' hc').mono fun δ hδ ↦ ENNReal.div_le_of_le_mul hδ)).trans
    hc'c.le

/-- Near a vector of means `μ` of the family with unique best arm `a`, the vectors of means are
models of the task, and the recommendation is their unique best arm `a`. -/
lemma eventually_mem_M_and_rec_eq [Finite α] {rec : (α → ℝ) → α}
    (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hrec_best : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      ∀ b ≠ rec μ', μ' b < μ' (rec μ'))
    {a : α} (hμ : ∀ b, μ b ∈ ρ.expFamilyMeans id) (ha : ∀ b ≠ a, μ b < μ a) :
    ∀ᶠ μ' in 𝓝 μ, μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M ∧
      rec μ' = a := by
  have h_mem :
      μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).answerSet a := by
    rw [IdentTask.answerSet_restrict]
    exact ⟨(mem_answerSet_baiTask_iff ν id).2 ha, hμ⟩
  have hS : IsOpen {μ' : α → ℝ | ∀ a, μ' a ∈ ρ.expFamilyMeans id} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun c ↦
      (Measure.isOpen_expFamilyMeans hρ).preimage (continuous_apply c)
  filter_upwards [(isOpen_answerSet_baiTask_restrict ν hS a).mem_nhds h_mem] with μ' hμ'
  have h_best := hμ'
  rw [IdentTask.answerSet_restrict, Set.mem_inter_iff, mem_answerSet_baiTask_iff] at h_best
  rw [IdentTask.mem_answerSet_iff] at hμ'
  refine ⟨hμ'.1, ?_⟩
  by_contra h
  exact lt_asymm (h_best.1 _ h) (hrec_best μ' hμ'.1 a (Ne.symm h))

omit [∀ μ, IsMarkovKernel (ν μ)] in
/-- For arms in the exponential family `(ρ, id)`, the divergence between the arms `b` of two
vectors of means of the family is `d(μ₁ b, μ₂ b)`, the hypothesis on the arms of the results of
`LMLExplore.Identification` on best arm identification. -/
lemma klDiv_eq_expFamilyDiv (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (μ₁ μ₂ : α → ℝ) (h₁ : ∀ b, μ₁ b ∈ ρ.expFamilyMeans id) (h₂ : ∀ b, μ₂ b ∈ ρ.expFamilyMeans id)
    (b : α) : klDiv (ν μ₁ b) (ν μ₂ b) = ENNReal.ofReal (ρ.expFamilyDiv id (μ₁ b) (μ₂ b)) := by
  rw [hν, hν]
  exact Measure.klDiv_expFamily_natParam (h₁ b) (h₂ b)

/-- For arms in the exponential family `(ρ, id)`, each arm is dominated by the member of the family
with its mean, the hypothesis on the arms of the sample complexity bounds of Track-and-Stop. -/
lemma mgfDominatedOn_expFamily (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (b : α) :
    MGFDominatedOn id (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).ν μ b) id
      (ρ.expFamily id (ρ.natParam id (μ b))) Set.univ := by
  rw [IdentTask.ν_restrict, ν_baiTask, hν]
  exact ⟨fun _ _ hY ↦ hY, fun _ _ _ ↦ le_rfl⟩

end Garivier2016Optimal
