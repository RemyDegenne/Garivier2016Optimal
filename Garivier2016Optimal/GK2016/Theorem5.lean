/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.Identification.Task.BestArmScalar

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
(Identification, Layer 3, item 4). The proof specializes
`LMLExplore.Identification.mem_optAlloc_baiTask_restrict_iff`, which characterizes the optimal
allocation `w` itself: `w a > 0`, the costs `w a d(μ a, m_b) + w b d(μ b, m_b)` of the pairs are
equal, and `F = 1` for the weighted means `m_b` of `w`. By homogeneity, these are the paper's
equations for `x = w / w a`, with `y` the common cost divided by `w a`.

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
  have hν' (μ' : α → ℝ) (hμ' : ∀ c, μ' c ∈ ρ.expFamilyMeans id) (c : α) :
      klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv id (μ c) (μ' c)) := by
    rw [hν, hν]
    exact Measure.klDiv_expFamily_natParam (hμ c) (hμ' c)
  rw [mem_optAlloc_baiTask_restrict_iff ν hρ hμ hν' ha hb]
  constructor
  · -- From `w`, the weights `x = w / w a`.
    rintro ⟨hws, hwa, h_eq, h_sum⟩
    obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hws
    obtain ⟨b₀, hb₀⟩ := hb
    set x : α → ℝ := fun c ↦ w c / w a with hx_def
    have hm (b : α) :
        (μ a + x b * μ b) / (1 + x b) = (w a * μ a + w b * μ b) / (w a + w b) := by
      have hW : w a + w b ≠ 0 := (add_pos_of_pos_of_nonneg hwa (hw0 b)).ne'
      simp only [hx_def]
      field_simp
    have hC (b : α) :
        ρ.expFamilyDiv id (μ a) ((μ a + x b * μ b) / (1 + x b)) +
            x b * ρ.expFamilyDiv id (μ b) ((μ a + x b * μ b) / (1 + x b)) =
          ρ.expFamilyPairCost id (μ a) (μ b) (w a) (w b) / w a := by
      rw [hm, Measure.expFamilyPairCost_def]
      simp only [hx_def]
      field_simp
    refine ⟨ρ.expFamilyPairCost id (μ a) (μ b₀) (w a) (w b₀) / w a, x, div_self hwa.ne',
      fun b hba ↦ ⟨div_pos ((hw0 b).lt_of_ne' fun h0 ↦ ?_) hwa, ?_⟩, ?_, ?_⟩
    · -- An arm `b ≠ a` with `w b = 0` would make the pair `(a, b)` cost nothing.
      have hpos := pos_of_mem_optAlloc_baiTask_restrict ν hρ hμ hν' ha
        (mem_optAlloc_baiTask_restrict_of_sum_div_eq_one ν hρ hμ hν' ha hws hwa h_eq h_sum) b
      exact hpos.ne' h0
    · rw [hC, h_eq b hba b₀ hb₀]
    · simp only [hm]
      exact h_sum
    · funext b
      simp only [hx_def]
      rw [← sum_div, hw1]
      field_simp
  · -- From `x`, the allocation `w = x / ∑ x`.
    rintro ⟨y, x, hxa, hx, h_sum, rfl⟩
    have hx0 (c : α) : 0 < x c := by
      rcases eq_or_ne c a with rfl | hca
      · rw [hxa]
        exact one_pos
      · exact (hx c hca).1
    have : Nonempty α := ⟨a⟩
    set s := ∑ c, x c with hs_def
    have hs : 0 < s := sum_pos (fun c _ ↦ hx0 c) univ_nonempty
    have hm (b : α) : (x a / s * μ a + x b / s * μ b) / (x a / s + x b / s) =
        (μ a + x b * μ b) / (1 + x b) := by
      have hW : 1 + x b ≠ 0 := (add_pos one_pos (hx0 b)).ne'
      rw [hxa]
      field_simp
    have hP {b : α} (hba : b ≠ a) :
        ρ.expFamilyPairCost id (μ a) (μ b) (x a / s) (x b / s) = s⁻¹ * y := by
      rw [div_eq_inv_mul, div_eq_inv_mul, Measure.expFamilyPairCost_mul, hxa,
        Measure.expFamilyPairCost_def, ← (hx b hba).2]
      simp
    refine ⟨mem_simplex_iff.2 ⟨fun c ↦ (div_pos (hx0 c) hs).le, ?_⟩, div_pos (hx0 a) hs,
      fun b hba c hca ↦ by rw [hP hba, hP hca], ?_⟩
    · rw [← sum_div, div_self hs.ne']
    · simp only [hm]
      exact h_sum

end Garivier2016Optimal
