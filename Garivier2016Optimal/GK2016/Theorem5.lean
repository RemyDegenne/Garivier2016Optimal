/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm

/-!
# The optimal allocation as the solution of a scalar equation [GK16, Theorem 5]

For best arm identification on the vectors of means `μ` of an exponential family with divergence
`d`, with unique best arm `a`, the optimal allocation is `w*_b = x_b / ∑_c x_c`, where `x_a = 1`
and, for every other arm `b`, `x_b` solves `g_b(x_b) = y*` for the increasing function
`g_b(x) = d(μ_a, m_b(x)) + x d(μ_b, m_b(x))` with `m_b(x) = (μ_a + x μ_b) / (1 + x)`, and `y*` is
the unique solution of `F(y*) = 1` for
`F(y) = ∑_{b ≠ a} d(μ_a, m_b(x_b(y))) / d(μ_b, m_b(x_b(y)))`.

The paper defines `x_b` as the inverse of `g_b` and `F` as a function of `y`, and computes `y*` by
bisection. This file states the characterization in equation form: `w` is the optimal allocation
if and only if `w = x / ∑ x` for weights `x` with `x_a = 1`, `g_b(x_b) = y` for every `b ≠ a` and
some `y`, and `F`'s equation `∑_{b ≠ a} d(μ_a, m_b(x_b)) / d(μ_b, m_b(x_b)) = 1`.

LMLExplore proves that the optimal allocation exists and is unique
(`exists_optAlloc_baiTask_restrict_eq_singleton`); the scalar equation is a target of LMLRoadmaps
(Identification, Layer 3, item 4).

## Main statements

* `Garivier2016Optimal.mem_optAlloc_iff_exists_scalar`: [GK16, Theorem 5].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Identification
  Finset

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (ρ : Measure ℝ) {μ : α → ℝ} {a : α}

/-- **The optimal allocation solves a scalar equation** [GK16, Theorem 5]. For at least two arms
in the exponential family `(ρ, id)` with divergence `d = ρ.expFamilyDiv id` and a vector of means
`μ` of the family with unique best arm `a`, an allocation `w` is optimal if and only if
`w = x / ∑ x` for weights `x` with `x a = 1` and, for some `y` and every arm `b ≠ a`, `x b > 0` and
`d(μ a, m_b) + x b d(μ b, m_b) = y` with `m_b = (μ a + x b μ b) / (1 + x b)`, such that
`∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`. -/
theorem mem_optAlloc_iff_exists_scalar (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' b, ν μ' b = ρ.expFamily id (ρ.natParam id (μ' b)))
    (hμ : ∀ b, μ b ∈ ρ.expFamilyMeans id) (ha : ∀ b ≠ a, μ b < μ a) (hb : ∃ b, b ≠ a)
    {w : α → ℝ} :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ b, μ' b ∈ ρ.expFamilyMeans id}).optAlloc μ a ↔
      ∃ (y : ℝ) (x : α → ℝ), x a = 1 ∧
        (∀ b ≠ a, 0 < x b ∧
          ρ.expFamilyDiv id (μ a) ((μ a + x b * μ b) / (1 + x b)) +
            x b * ρ.expFamilyDiv id (μ b) ((μ a + x b * μ b) / (1 + x b)) = y) ∧
        ∑ b ∈ univ.erase a, ρ.expFamilyDiv id (μ a) ((μ a + x b * μ b) / (1 + x b)) /
          ρ.expFamilyDiv id (μ b) ((μ a + x b * μ b) / (1 + x b)) = 1 ∧
        w = fun b ↦ x b / ∑ c, x c := by
  sorry

end Garivier2016Optimal
