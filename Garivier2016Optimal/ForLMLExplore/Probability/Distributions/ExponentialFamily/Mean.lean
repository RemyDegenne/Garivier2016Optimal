/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# The cost of moving two means to their weighted mean, as a function of the lower mean

For an exponential family with divergence `d` and nonnegative weights `w₁, w₂`, the cost
`expFamilyPairCost ρ T μ₁ μ₂ w₁ w₂ = w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving two means to their
weighted mean `m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)` grows as the lower mean `μ₂ ≤ μ₁` moves away from
`μ₁`, strictly when both weights are positive. In best arm identification, this cost is the cost of
the alternatives in which the arm of mean `μ₂` beats the arm of mean `μ₁`, and its monotonicity
orders the optimal allocation like the means [GK16, Proposition 6]
(`LMLExplore/Identification/Task/BestArmOrder.lean`).

The proof compares the costs at the weighted mean `m'` of `μ₁` and the lower mean `μ₂' ≤ μ₂`: the
cost for `μ₂` is at most `w₁ d(μ₁, m') + w₂ d(μ₂, max m' μ₂)`
(`MeasureTheory.Measure.expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv`), and
`d(μ₂, max m' μ₂) ≤ d(μ₂', m')` since `d(·, m')` decreases below `m'`.

## Main statements

* `MeasureTheory.Measure.strictAntiOn_expFamilyPairCost_right`: for positive weights, the cost is
  strictly decreasing in the second mean `μ₂ ≤ μ₁`.
* `MeasureTheory.Measure.antitoneOn_expFamilyPairCost_right`: for nonnegative weights, it is
  decreasing in `μ₂ ≤ μ₁`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2, Proposition 6.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ}

/-- For a mean `μ₁` of the family and positive weights `w₁, w₂`, the cost
`w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving `μ₁` and `μ₂` to their weighted mean `m` is strictly
decreasing in the second mean `μ₂ ≤ μ₁`: the further `μ₂` is below `μ₁`, the more it costs to move
them together. -/
theorem strictAntiOn_expFamilyPairCost_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {μ₁ w₁ w₂ : ℝ}
    (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    StrictAntiOn (fun μ₂ ↦ ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂) (ρ.expFamilyMeans T ∩ Iic μ₁) := by
  rintro μ₂' ⟨hμ₂', hμ₂'₁⟩ μ₂ ⟨hμ₂, hμ₂₁⟩ hlt
  rw [mem_Iic] at hμ₂'₁ hμ₂₁
  have hW : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  -- The weighted mean `m'` of `μ₁` and `μ₂'` is a mean of the family, strictly above `μ₂'`.
  set m' := (w₁ * μ₁ + w₂ * μ₂') / (w₁ + w₂) with hm'_def
  have hm' : m' ∈ ρ.expFamilyMeans T := div_mem_expFamilyMeans hμ₁ hμ₂' hw₁.le hw₂.le hW
  have hm'_gt : μ₂' < m' := by rw [hm'_def, lt_div_iff₀ hW]; nlinarith
  have h_cost : ρ.expFamilyPairCost T μ₁ μ₂' w₁ w₂ =
      w₁ * ρ.expFamilyDiv T μ₁ m' + w₂ * ρ.expFamilyDiv T μ₂' m' := expFamilyPairCost_def ..
  simp only
  rw [h_cost]
  rcases le_total μ₂ m' with hμ₂m | hmμ₂
  · -- `μ₂' < μ₂ ≤ m'`: `d(μ₂, m') < d(μ₂', m')`, since `d(·, m')` decreases below `m'`.
    refine (expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv hT hμ₁ hμ₂ hμ₂₁ hw₁.le
      hw₂.le hm' hm' le_rfl).trans_lt (add_lt_add_right (mul_lt_mul_of_pos_left ?_ hw₂) _)
    exact strictAntiOn_expFamilyDiv_left hT hm' ⟨hμ₂', hlt.le.trans hμ₂m⟩ ⟨hμ₂, hμ₂m⟩ hlt
  · -- `m' ≤ μ₂`: the cost for `μ₂` is at most `w₁ d(μ₁, m') + w₂ d(μ₂, μ₂) = w₁ d(μ₁, m')`.
    have h := expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv hT hμ₁ hμ₂ hμ₂₁ hw₁.le
      hw₂.le hm' hμ₂ hmμ₂
    rw [expFamilyDiv_self, mul_zero, add_zero] at h
    exact h.trans_lt (lt_add_of_pos_right _ (mul_pos hw₂ (expFamilyDiv_pos hμ₂' hm' hm'_gt.ne)))

/-- For a mean `μ₁` of the family and nonnegative weights `w₁, w₂`, the cost
`w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving `μ₁` and `μ₂` to their weighted mean `m` is decreasing in
the second mean `μ₂ ≤ μ₁`; strictly for positive weights (`strictAntiOn_expFamilyPairCost_right`).
-/
theorem antitoneOn_expFamilyPairCost_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {μ₁ w₁ w₂ : ℝ}
    (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    AntitoneOn (fun μ₂ ↦ ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂) (ρ.expFamilyMeans T ∩ Iic μ₁) := by
  rcases hw₁.eq_or_lt with rfl | hw₁
  · intro _ _ _ _ _
    simp [expFamilyPairCost_eq_zero]
  rcases hw₂.eq_or_lt with rfl | hw₂
  · intro _ _ _ _ _
    simp [expFamilyPairCost_eq_zero]
  exact (strictAntiOn_expFamilyPairCost_right hT hμ₁ hw₁ hw₂).antitoneOn

end MeasureTheory.Measure
