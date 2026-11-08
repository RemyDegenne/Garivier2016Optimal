/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm

/-!
# Best arm identification near a vector of means of an exponential family

For best arm identification restricted to an open set `S` of vectors of means, the models with
unique best arm `a` form an open set, so that the vectors of means near a model with unique best
arm `a` are models of the restricted task with unique best arm `a`. For arms in an exponential
family, restricted to the vectors of means of the family, and a vector of means `μ` of the family
with unique best arm `a`, `(μ', w) ↦ D(μ', w, ¬a)` is continuous within `univ ×ˢ simplex α` at
`(μ, w)`, for every allocation `w` of the simplex.

The sample complexity bounds of Track-and-Stop (`Identification/TrackAndStop.lean`) take the
continuity, and the recommendation of `a` near `μ`, as hypotheses, so that applying them to best
arm identification needs both. LMLExplore proves the continuity as a private lemma of
`Identification/Task/BestArm.lean`, which its continuity of the value and upper hemicontinuity of
the optimal allocations use. LMLExplore pull request #242 makes that lemma public and adds the
openness, with the statements of this file.

## Main statements

* `LMLExplore.Identification.isOpen_answerSet_baiTask_restrict`: for an open set `S`, the models
  of the task restricted to `S` with unique best arm `a` form an open set.
* `LMLExplore.Identification.continuousWithinAt_altCost_baiTask_restrict`: the continuity of the
  cost of the alternatives at `(μ, w)`, within `univ ×ˢ simplex α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} {a : α}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {ρ : Measure 𝓨} {T : 𝓨 → ℝ}
  {μ w : α → ℝ}

/-- For an open set `S` of vectors of means, the models of best arm identification restricted to
`S` with unique best arm `a` form an open set. -/
lemma isOpen_answerSet_baiTask_restrict [Finite α] {S : Set (α → ℝ)} (hS : IsOpen S) (a : α) :
    IsOpen (((baiTask ν id).restrict S).answerSet a) := by
  rw [IdentTask.answerSet_restrict]
  exact (isOpen_answerSet_baiTask ν a).inter hS

variable [Fintype α]

/-- **Continuity of the cost of the alternatives near a model**, for arms in an exponential family
with divergence `d` (as in `continuousOn_altCost_baiTask_restrict`): at a vector of means `μ` of
the family with unique best arm `a`, `(μ', w) ↦ D(μ', w, ¬a)` is continuous within
`univ ×ˢ simplex α` at `(μ, w)` for every allocation `w` of the simplex. This is the continuity
hypothesis of the continuity of the value and of the upper hemicontinuity of the optimal
allocations (`IdentTask.continuousWithinAt_answerValue`,
`IdentTask.upperHemicontinuousWithinAt_optAlloc`), and of the sample complexity bounds of
Track-and-Stop (`IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`,
`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`). -/
lemma continuousWithinAt_altCost_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) (hw : w ∈ simplex α) :
    ContinuousWithinAt (fun p : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost p.1 p.2 a)
      (Set.univ ×ˢ simplex α) (μ, w) := by
  have h_best : (baiTask ν id).answerSet a ∈ 𝓝 μ :=
    (isOpen_answerSet_baiTask ν a).mem_nhds ((mem_answerSet_baiTask_iff ν id).2 ha)
  have h_nhds : {μ' : α → ℝ | (∀ c, μ' c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ' b ≤ μ' a} ∈ 𝓝 μ :=
    (eventually_all.2 fun c ↦ (continuous_apply c).continuousAt.preimage_mem_nhds
      (expFamilyMeans_mem_nhds hT (hμ c))).and
      (mem_of_superset h_best fun _ hμ' ↦
        apply_le_of_forall_ne_lt ((mem_answerSet_baiTask_iff ν id).1 hμ'))
  have h_mem : {μ' : α → ℝ | (∀ c, μ' c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ' b ≤ μ' a} ×ˢ Set.Ici 0 ∈
      𝓝[Set.univ ×ˢ simplex α] (μ, w) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact prod_mem_prod h_nhds (mem_of_superset self_mem_nhdsWithin simplex_subset_nonneg)
  exact ((continuousOn_altCost_baiTask_restrict ν hT hν a) _
    ⟨mem_of_mem_nhds h_nhds, simplex_subset_nonneg hw⟩).mono_of_mem_nhdsWithin h_mem

end LMLExplore.Identification
