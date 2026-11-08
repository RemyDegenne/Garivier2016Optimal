/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.LowerBound
public import LMLExplore.Identification.Task.BestArm

/-!
# The lower bound on the sample complexity [GK16, Theorem 1]

For best arm identification on the vectors of means `μ` of an exponential family with a unique best
arm (the set `𝒮` of [GK16, Section 2]), every `δ`-correct strategy has
`𝔼_μ[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)`, where `T*(μ)` is the characteristic time.

The paper states it for every `δ ∈ (0, 1)`; it holds for `δ ≤ 1 / 2` only, and fails beyond: with
two arms and `δ ≥ 1 / 2`, answering an arm chosen uniformly at random, without sampling, is
`δ`-correct with `𝔼[τ] = 0`, while `T*(μ) kl(δ, 1 - δ) > 0` for `δ ≠ 1 / 2`
(`notes/paper-errata.md`, E1).

The bound holds for every identification task
(`IdentTask.IsDeltaCorrect.charTime_mul_le_expectedStoppingTime` in LMLExplore); this file states
the paper's case.

## Main statements

* `Garivier2016Optimal.charTime_mul_klBer_le_expectedStoppingTime`: [GK16, Theorem 1], for
  `δ ≤ 1 / 2`.
* `Garivier2016Optimal.eventually_mul_log_le_expectedStoppingTime`: the asymptotic form of
  [GK16, Remark 2]: for a family of `δ`-correct strategies and every `c < T*(μ)`,
  `𝔼_μ[τ_δ] ≥ c log (1 / δ)` for all small enough `δ`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore LMLExplore.Identification Filter Topology

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)]
  (ρ : Measure ℝ) {μ : α → ℝ}

/-- **Lower bound on the sample complexity** [GK16, Theorem 1]. For best arm identification on the
vectors of means of the exponential family `(ρ, id)` with a unique best arm, every `δ`-correct
strategy `A` with `δ ≤ 1 / 2` has `T*(μ) kl(δ, 1 - δ) ≤ 𝔼_μ[τ]` on every such vector of means `μ`.
The paper states it for `δ ∈ (0, 1)`, see `notes/paper-errata.md`, E1. -/
theorem charTime_mul_klBer_le_expectedStoppingTime {A : IdentAlg Unit α ℝ α} {δ : ℝ}
    (hA : ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).IsDeltaCorrect A δ)
    (hδ : δ ≤ 1 / 2)
    (hμ : μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M) :
    ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ *
        klBer δ (1 - δ) ≤ expectedStoppingTime A (Environment.bandit (ν μ)) := by
  sorry

/-- **Asymptotic lower bound** [GK16, Remark 2]. For a family `A δ` of `δ`-correct strategies for
best arm identification on the vectors of means of the exponential family `(ρ, id)`, and every
`c < T*(μ)`, `𝔼_μ[τ_δ] ≥ c log (1 / δ)` for all small enough `δ`. -/
theorem eventually_mul_log_le_expectedStoppingTime {A : ℝ → IdentAlg Unit α ℝ α}
    (hA : ∀ᶠ δ in 𝓝[>] 0,
      ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).IsDeltaCorrect (A δ) δ)
    (hμ : μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M)
    {c : ℝ≥0∞}
    (hc : c < ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ) :
    ∀ᶠ δ in 𝓝[>] 0, c * ENNReal.ofReal (Real.log (1 / δ)) ≤
      expectedStoppingTime (A δ) (Environment.bandit (ν μ)) := by
  sorry

end Garivier2016Optimal
