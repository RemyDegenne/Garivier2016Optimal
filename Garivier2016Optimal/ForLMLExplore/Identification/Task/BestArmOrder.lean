/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.TopTwo.BestArm
public import Garivier2016Optimal.ForLMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# The optimal allocation of best arm identification is ordered like the means

For best arm identification with arms in an exponential family with divergence `d`, at a vector
of means `μ` of the family with unique best arm `a`, the optimal allocation `w*(μ, ¬a)` is ordered
like the means on the arms other than `a`: for `b, c ≠ a`, `w*_c ≤ w*_b` if and only if
`μ c ≤ μ b`, and `w*_c < w*_b` if and only if `μ c < μ b` [GK16, Proposition 6]. The same holds
for the `β`-optimal allocations of the Top Two algorithms, for `β > 0` (strictly for `β < 1`).

The paper derives the ordering from its scalar equation [GK16, Theorem 5]. The proof here only
uses the equality of the costs of the pairs at the optimal allocation [GK16, Lemma 4]: if
`μ c ≤ μ b < μ a` and `w b < w c`, then the cost of the pair `(a, b)` at `(w a, w b)` is smaller
than at `(w a, w c)`, since it increases in the weight of `b`
(`MeasureTheory.Measure.strictMonoOn_expFamilyPairCost`), which is at most the cost of the pair
`(a, c)` at `(w a, w c)`, since it decreases in the lower mean
(`MeasureTheory.Measure.antitoneOn_expFamilyPairCost_right`), contradicting their equality.

## Main statements

* `LMLExplore.Identification.le_of_mem_betaOptAlloc_baiTask_restrict_of_le`,
  `LMLExplore.Identification.lt_of_mem_betaOptAlloc_baiTask_restrict_of_lt`: the `β`-optimal
  allocation is ordered like the means, for `β > 0`, and strictly for `β ∈ (0, 1)`.
* `LMLExplore.Identification.le_iff_le_of_mem_optAlloc_baiTask_restrict`,
  `LMLExplore.Identification.lt_iff_lt_of_mem_optAlloc_baiTask_restrict`: the optimal allocation
  is ordered like the means [GK16, Proposition 6].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2, Lemma 4 and Proposition 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {ρ : Measure 𝓨} {T : 𝓨 → ℝ}
  {μ w : α → ℝ} {a b c : α} {β : ℝ}

/-- **The `β`-optimal allocation is ordered like the means.** For arms in an exponential family
(as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the family
with unique best arm `a`, `β > 0` and a `β`-optimal allocation `w` of the answer `a` with the arm
`a`, an arm `b ≠ a` whose mean is at least that of an arm `c ≠ a` gets at least its proportion:
`μ c ≤ μ b` implies `w c ≤ w b`. -/
theorem le_of_mem_betaOptAlloc_baiTask_restrict_of_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : 0 < β)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (hba : b ≠ a) (hca : c ≠ a) (hcb : μ c ≤ μ b) :
    w c ≤ w b := by
  have hw0 := (mem_simplex_iff.1 ((IdentTask.mem_betaOptAlloc_iff _).1 hw).1).1
  have h_eq := expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ hw hw
    hba hca
  -- If `w b < w c`, the pair `(a, b)` costs less at `w b` than at `w c`, which is at most the cost
  -- of the pair `(a, c)` at `w c`.
  refine not_lt.1 fun hbc ↦ h_eq.not_lt ?_
  exact (strictMonoOn_expFamilyPairCost (hμ a) (hμ b) (ha b hba).ne' hβ (Set.mem_Ici.2 (hw0 b))
    (Set.mem_Ici.2 (hw0 c)) hbc).trans_le
    (antitoneOn_expFamilyPairCost_right hT (hμ a) hβ.le (hw0 c) ⟨hμ c, hcb.trans (ha b hba).le⟩
      ⟨hμ b, (ha b hba).le⟩ hcb)

/-- **The `β`-optimal allocation is strictly ordered like the means.** For arms in an exponential
family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the
family with unique best arm `a`, `β ∈ (0, 1)` and a `β`-optimal allocation `w` of the answer `a`
with the arm `a`, an arm `b ≠ a` whose mean is larger than that of an arm `c ≠ a` gets a larger
proportion: `μ c < μ b` implies `w c < w b`. -/
theorem lt_of_mem_betaOptAlloc_baiTask_restrict_of_lt (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : β ∈ Set.Ioo 0 1)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (hba : b ≠ a) (hca : c ≠ a) (hcb : μ c < μ b) :
    w c < w b := by
  have hw0 := (mem_simplex_iff.1 ((IdentTask.mem_betaOptAlloc_iff _).1 hw).1).1
  have hwc := pos_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ hw c
  have h_eq := expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ.1 hw hw
    hba hca
  -- If `w c ≤ w b`, the pair `(a, b)` costs at most as much at `w b` as at `w c`, which is less
  -- than the cost of the pair `(a, c)` at `w c`.
  refine not_le.1 fun hbc ↦ h_eq.not_lt ?_
  exact ((strictMonoOn_expFamilyPairCost (hμ a) (hμ b) (ha b hba).ne' hβ.1).monotoneOn
    (Set.mem_Ici.2 (hw0 b)) (Set.mem_Ici.2 (hw0 c)) hbc).trans_lt
    (strictAntiOn_expFamilyPairCost_right hT (hμ a) hβ.1 hwc
      ⟨hμ c, hcb.le.trans (ha b hba).le⟩ ⟨hμ b, (ha b hba).le⟩ hcb)

/-- The proportion `w a` of the best arm in an optimal allocation is in `(0, 1)` when there is an
arm `b ≠ a`: both `w a` and `w b` are positive and sum to at most `1`. -/
private lemma mem_Ioo_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a)
    (hba : b ≠ a) :
    w a ∈ Set.Ioo 0 1 := by
  classical
  have hpos := pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw
  obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 ((IdentTask.mem_optAlloc_iff _).1 hw).1
  have h_le : w a + w b ≤ 1 := by
    rw [← hw1, ← Finset.sum_pair (f := w) hba.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ ↦ hw0 c
  exact ⟨hpos a, by linarith [hpos b]⟩

/-- **The optimal allocation is ordered like the means** [GK16, Proposition 6]. For arms in an
exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means
`μ` of the family with unique best arm `a` and an optimal allocation `w`, for two arms `b, c ≠ a`,
`w c ≤ w b` if and only if `μ c ≤ μ b`. -/
theorem le_iff_le_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a)
    (hba : b ≠ a) (hca : c ≠ a) :
    w c ≤ w b ↔ μ c ≤ μ b := by
  have hβ := mem_Ioo_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw hba
  have hw' := IdentTask.mem_betaOptAlloc_of_mem_optAlloc _ hw a
  refine ⟨fun h ↦ not_lt.1 fun hbc ↦ ?_, fun h ↦ ?_⟩
  · exact (lt_of_mem_betaOptAlloc_baiTask_restrict_of_lt ν hT hμ hν ha hβ hw' hca hba hbc).not_ge h
  · exact le_of_mem_betaOptAlloc_baiTask_restrict_of_le ν hT hμ hν ha hβ.1 hw' hba hca h

/-- **The optimal allocation is strictly ordered like the means** [GK16, Proposition 6]. For arms
in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of
means `μ` of the family with unique best arm `a` and an optimal allocation `w`, for two arms
`b, c ≠ a`, `w c < w b` if and only if `μ c < μ b`. -/
theorem lt_iff_lt_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a)
    (hba : b ≠ a) (hca : c ≠ a) :
    w c < w b ↔ μ c < μ b := by
  rw [lt_iff_not_ge, lt_iff_not_ge,
    le_iff_le_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw hca hba]

end LMLExplore.Identification
