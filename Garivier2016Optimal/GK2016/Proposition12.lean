/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.ExpFamilyThreshold
public import LMLExplore.Identification.Task.BestArm

/-!
# The deviational threshold [GK16, Proposition 12]

For best arm identification on the vectors of means of an exponential family and every exponent
`p > 1`, there is a constant `C`, depending on `p` and the number of arms only, such that whatever
the sampling rule and the recommendation rule, Chernoff's stopping rule with the thresholds
`β(t, δ) = log (C t ^ p / δ)` stops with an arm that is not the best with probability at most `δ`.

The statistic is the generalized likelihood ratio evidence of the family, Chernoff's `Z(t)` of
[GK16, Section 3.2]. LMLExplore has the thresholds `K log (2 t (t + 1)) + x_δ` of [LS, Lemma 33.7]
for the same statistic (`IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le`); the
thresholds `log (C t ^ p / δ)` are a target of LMLRoadmaps (Identification, Layer 4, item 2).

## Main statements

* `Garivier2016Optimal.exists_measureReal_glrt_expFamilyEvidence_le`: [GK16, Proposition 12].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore LMLExplore.Identification Real

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α]

/-- **The deviational threshold** [GK16, Proposition 12]. For every exponent `p > 1` there is a
constant `C > 0` such that, for every exponential family `(ρ, id)` and every `δ ∈ (0, 1)`, whatever
the sampling rule `alg` and the recommendation rule `rec`, Chernoff's stopping rule with the
thresholds `log (C t ^ p / δ)` stops with an arm that is not the best with probability at most
`δ`, on every vector of means of the family with a unique best arm. -/
theorem exists_measureReal_glrt_expFamilyEvidence_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (ρ : Measure ℝ),
      (∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c) →
      (∀ μ a, ν μ a = ρ.expFamily id (ρ.natParam id (μ a))) →
      ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ (alg : Algorithm Unit α ℝ) (rec : (n : ℕ) → Hist Unit α ℝ n → α)
        (hrec : ∀ n, Measurable (rec n))
        (hstop : ∀ n, MeasurableSet {h : Hist Unit α ℝ n |
          ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ)) <
            ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glr
              (expFamilyEvidence (fun _ ↦ ρ) (fun _ ↦ id)) n h (rec n h)}),
        ∀ μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
          (histOutputMeasure
            (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glrt
              (expFamilyEvidence (fun _ ↦ ρ) (fun _ ↦ id)) alg
              (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop)
            (Environment.bandit (ν μ))).real
          {q | q.1 ∈ (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glrt
              (expFamilyEvidence (fun _ ↦ ρ) (fun _ ↦ id)) alg
              (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop).stopSet ∧
            q.2 ∉ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).correct μ} ≤
          δ := by
  sorry

end Garivier2016Optimal
