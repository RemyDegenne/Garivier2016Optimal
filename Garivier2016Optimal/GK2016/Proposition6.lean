/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm

/-!
# Properties of the optimal allocation [GK16, Proposition 6]

For best arm identification on the vectors of means of an exponential family, at a vector of means
`μ` with a unique best arm `a`:

1. the optimal allocation `w*(μ)` gives a positive proportion to every arm;
2. `w*` is continuous at `μ`: every selection of the optimal allocations near `μ` is continuous
   at `μ`;
3. the optimal allocation is ordered like the means on the other arms: if `μ c ≤ μ b < μ a`, then
   `w*_c(μ) ≤ w*_b(μ)`.

The paper writes part 3 for sorted means, `μ_1 > μ_2 ≥ ⋯ ≥ μ_K` giving `w*_2 ≥ ⋯ ≥ w*_K`. Parts 1
and 2 are in LMLExplore (`pos_of_mem_optAlloc_baiTask_restrict`,
`continuousAt_of_mem_optAlloc_baiTask_restrict`); part 3 is not on any LMLRoadmaps target.

## Main statements

* `Garivier2016Optimal.pos_of_mem_optAlloc`: [GK16, Proposition 6, part 1].
* `Garivier2016Optimal.continuousAt_of_mem_optAlloc`: [GK16, Proposition 6, part 2].
* `Garivier2016Optimal.le_of_mem_optAlloc_of_le`: [GK16, Proposition 6, part 3].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Identification Filter
  Topology

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α} (ν : (α → ℝ) → Kernel α ℝ)
  [∀ μ, IsMarkovKernel (ν μ)] (ρ : Measure ℝ) {μ : α → ℝ} {a : α}

/-- **The optimal allocation is positive** [GK16, Proposition 6, part 1]. For arms in the
exponential family `(ρ, id)` and a vector of means `μ` of the family with unique best arm `a`, the
optimal allocation gives a positive proportion to every arm. -/
theorem pos_of_mem_optAlloc (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (hμ : ∀ b, μ b ∈ ρ.expFamilyMeans id) (ha : ∀ b ≠ a, μ b < μ a) {w : α → ℝ}
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ b, μ' b ∈ ρ.expFamilyMeans id}).optAlloc μ a)
    (b : α) :
    0 < w b :=
  pos_of_mem_optAlloc_baiTask_restrict ν hρ hμ
    (fun μ' hμ' c ↦ by rw [hν, hν]; exact Measure.klDiv_expFamily_natParam (hμ c) (hμ' c)) ha hw b

/-- **The optimal allocation is continuous** [GK16, Proposition 6, part 2]. For arms in the
exponential family `(ρ, id)` and a vector of means `μ` of the family with unique best arm `a`, every
map `w` whose values near `μ` are optimal allocations for `a` is continuous at `μ`. -/
theorem continuousAt_of_mem_optAlloc (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (hμ : ∀ b, μ b ∈ ρ.expFamilyMeans id) (ha : ∀ b ≠ a, μ b < μ a) {w : (α → ℝ) → α → ℝ}
    (hw : ∀ᶠ μ' in 𝓝 μ,
      w μ' ∈ ((baiTask ν id).restrict {μ' | ∀ b, μ' b ∈ ρ.expFamilyMeans id}).optAlloc μ' a) :
    ContinuousAt w μ :=
  continuousAt_of_mem_optAlloc_baiTask_restrict ν hρ
    (fun μ₁ μ₂ h₁ h₂ c ↦ by rw [hν, hν]; exact Measure.klDiv_expFamily_natParam (h₁ c) (h₂ c))
    hμ ha hw

/-- **The optimal allocation is ordered like the means** [GK16, Proposition 6, part 3]. For arms
in the exponential family `(ρ, id)` and a vector of means `μ` of the family with unique best arm
`a`, an arm whose mean is larger, closer to the best, gets a larger optimal proportion: if
`μ c ≤ μ b` for two arms `b, c ≠ a`, then `w c ≤ w b`. -/
theorem le_of_mem_optAlloc_of_le (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (hμ : ∀ b, μ b ∈ ρ.expFamilyMeans id) (ha : ∀ b ≠ a, μ b < μ a) {w : α → ℝ}
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ b, μ' b ∈ ρ.expFamilyMeans id}).optAlloc μ a)
    {b c : α} (hb : b ≠ a) (hc : c ≠ a) (hbc : μ c ≤ μ b) :
    w c ≤ w b := by
  sorry

end Garivier2016Optimal
