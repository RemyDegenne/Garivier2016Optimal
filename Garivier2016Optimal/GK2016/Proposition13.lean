/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.Identification.Task.BestArm

/-!
# The almost sure upper bound [GK16, Proposition 13]

For best arm identification on the vectors of means of an exponential family, let a sampling rule
make the proportions of pulls `N_a(t) / t` converge almost surely to the optimal allocation
`w*(μ)`. With the recommendation of the best empirical arm and Chernoff's stopping rule with the
thresholds `β(t, δ) = log (r(t) / δ)`, for `r(t) = O(t ^ p)` and `p ∈ [1, e / 2]`, the stopping
time `τ_δ` is almost surely finite for every `δ ∈ (0, 1)`, and almost surely
`limsup_{δ → 0} τ_δ / log (1 / δ) ≤ p T*(μ)`.

All the stopping times are read on one run of the sampling rule, which does not depend on `δ`: the
statement is about a sequence `(O, A, Y)` of observations, actions and feedbacks that is a run of
the sampling rule against the bandit. The statistic is the plug-in statistic of the empirical
means, as in `Garivier2016Optimal.limsup_expectedStoppingTime_trackAndStop_div_log_le`.

The almost sure bound is a target of LMLRoadmaps (Identification, Layer 4, item 4).

## Main statements

* `Garivier2016Optimal.stoppingTime_glrt_ne_top_and_limsup_le`: [GK16, Proposition 13].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore LMLExplore.Identification Filter Topology
  Real

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)]
  (ρ : Measure ℝ) {μ : α → ℝ} {p : ℝ} {r : ℕ → ℝ}
  {rec : (α → ℝ) → α} {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ (δ : ℝ) n, MeasurableSet {h : Hist Unit α ℝ n |
    ENNReal.ofReal (log (r n / δ)) <
      ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glr
        (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).plugInCost empMean')
        n h (rec (empMean' n h))}}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **The almost sure upper bound** [GK16, Proposition 13]. Let the arms be in the exponential
family `(ρ, id)`, `rec μ'` be the best arm of every vector of means `μ'` with a unique best arm,
the thresholds be `log (r(t) / δ)` with `r(t) = O(t ^ p)`, `p ∈ [1, e / 2]`, and `(O, A, Y)` be a
run of a sampling rule `alg` on a vector of means `μ` of the family with a unique best arm, whose
proportions of pulls converge almost surely to an optimal allocation `w`. Then for every
`δ ∈ (0, 1)` the stopping time `τ_δ` of Chernoff's stopping rule is almost surely finite, and
almost surely `limsup_{δ → 0} τ_δ / log (1 / δ) ≤ p T*(μ)`. -/
theorem stoppingTime_glrt_ne_top_and_limsup_le (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' a, ν μ' a = ρ.expFamily id (ρ.natParam id (μ' a)))
    (hrec_best : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      ∀ b ≠ rec μ', μ' b < μ' (rec μ'))
    (hp : p ∈ Set.Icc 1 (exp 1 / 2)) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hμ : μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M)
    {w : α → ℝ}
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).optAlloc μ (rec μ))
    (hseq : IsAlgEnvSeq O A Y alg (Environment.bandit (ν μ)) P)
    (hconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (w a))) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glrt
          (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).plugInCost empMean')
          alg (fun n _ ↦ ENNReal.ofReal (log (r n / δ))) (fun n h ↦ rec (empMean' n h)) hrec
          (hstop δ)).stoppingTime O A Y ω ≠ ⊤) ∧
    ∀ᵐ ω ∂P, limsup (fun δ ↦ ENat.toENNReal
        ((((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glrt
          (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).plugInCost empMean')
          alg (fun n _ ↦ ENNReal.ofReal (log (r n / δ))) (fun n h ↦ rec (empMean' n h)) hrec
          (hstop δ)).stoppingTime O A Y ω) / ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤
      ENNReal.ofReal p *
        ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ := by
  sorry

end Garivier2016Optimal
