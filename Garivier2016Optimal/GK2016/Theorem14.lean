/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.GK2016.Basic

/-!
# Asymptotic optimality of Track-and-Stop in expectation [GK16, Theorem 14]

For best arm identification on the vectors of means of an exponential family, Track-and-Stop with
D-tracking or C-tracking of the optimal allocation, the recommendation of the best empirical arm and
Chernoff's stopping rule with thresholds `β(t, δ) = log (r(t) / δ)`, for `r(t) = O(t ^ p)` and
`p ∈ [1, e / 2]`, has `limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ p T*(μ)`.

The statistic of the stopping rule is the plug-in statistic of the empirical means,
`∑ a, N_a d(μ̂_a, λ_a)` minimized over the alternatives, which is Chernoff's statistic `Z(t)` of
[GK16, Section 3.2] when the empirical means are means of the family.

LMLExplore proves more: `𝔼_μ[τ_δ] ≤ c log (1 / δ)` for all small `δ` and every `c > T*(μ)`, whatever
the exponent `p` (`IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt` and
`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`).

## Main statements

* `Garivier2016Optimal.limsup_expectedStoppingTime_trackAndStop_div_log_le`: [GK16, Theorem 14]
  with D-tracking.
* `Garivier2016Optimal.limsup_expectedStoppingTime_cTrackAndStop_div_log_le`: [GK16, Theorem 14]
  with C-tracking.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning LMLExplore
  LMLExplore.Identification Filter Topology Real

open scoped ENNReal NNReal

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)]
  (ρ : Measure ℝ) {μ : α → ℝ} {p : ℝ} {r : ℕ → ℝ}
  {w : (α → ℝ) → α → ℝ} {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)}
  {rec : (α → ℝ) → α} {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ (δ : ℝ) n, MeasurableSet {h : Hist Unit α ℝ n |
    ENNReal.ofReal (log (r n / δ)) <
      ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).glr
        (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).plugInCost empMean')
        n h (rec (empMean' n h))}}

/-- **Asymptotic optimality of Track-and-Stop with D-tracking** [GK16, Theorem 14]. Let the arms be
in the exponential family `(ρ, id)`, the targets `w μ'` be optimal allocations and `rec μ'` the best
arm of every vector of means `μ'` with a unique best arm, and the thresholds be
`log (r(t) / δ)` with `r(t) = O(t ^ p)`, `p ∈ [1, e / 2]`. Then on every vector of means `μ` of
the family with a unique best arm, `limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ p T*(μ)`.

The proof shows the stronger `limsup ≤ T*(μ)`
(`IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`): of the hypothesis
on `p`, it uses only `1 ≤ p`, and the targets `w μ'` need to be allocations only at `μ' = μ`. -/
theorem limsup_expectedStoppingTime_trackAndStop_div_log_le (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' a, ν μ' a = ρ.expFamily id (ρ.natParam id (μ' a)))
    (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      w μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).optAlloc μ' (rec μ'))
    (hrec_best : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      ∀ b ≠ rec μ', μ' b < μ' (rec μ'))
    (hp : p ∈ Set.Icc 1 (exp 1 / 2)) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hμ : μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M) :
    limsup (fun δ ↦ expectedStoppingTime
        (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).trackAndStop empMean' w hw
          (fun n _ ↦ ENNReal.ofReal (log (r n / δ))) rec hrec (hstop δ))
        (Environment.bandit (ν μ)) / ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤
      ENNReal.ofReal p *
        ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ := by
  have hμ' := hμ
  rw [IdentTask.M_restrict, M_baiTask] at hμ'
  obtain ⟨⟨a, ha⟩, hμS⟩ := hμ'
  have h_near := eventually_mem_M_and_rec_eq ν ρ hρ hrec_best hμS ha
  have hw_opt_μ :
      w μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).optAlloc μ a := by
    rw [← h_near.self_of_nhds.2]
    exact hw_opt μ hμ
  have hw_cont : ContinuousAt w μ :=
    continuousAt_of_mem_optAlloc_baiTask_restrict ν hρ (klDiv_eq_expFamilyDiv ν ρ hν) hμS ha
      (h_near.mono fun μ' h ↦ by rw [← h.2]; exact hw_opt μ' h.1)
  -- LMLExplore's bound `𝔼[τ_δ] ≤ c log (1 / δ)` for every `c > T*(μ)`, whatever `p`.
  refine (limsup_div_log_le fun c hc ↦ ?_).trans
    (le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 hp.1))
  have h := IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt
    ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}) (ρ := fun _ ↦ ρ)
    (T := fun _ ↦ id) (hw := hw) (hrec := hrec) (hstop := hstop)
    (β := fun δ n _ ↦ ENNReal.ofReal (log (r n / δ))) (n₀ := 0) (fun _ ↦ hρ) hμS
    (mgfDominatedOn_expFamily ν ρ hν)
    (by rw [IdentTask.correct_restrict]; exact (correct_baiTask_eq_singleton_iff ν id).2 ha)
    hw_opt_μ hw_cont (h_near.mono fun _ h ↦ h.2)
    (continuousWithinAt_altCost_baiTask_restrict ν hρ (klDiv_eq_expFamilyDiv ν ρ hν) hμS ha
      (hw_mem μ)).lowerSemicontinuousWithinAt
    hc hr (Eventually.of_forall fun _ _ _ _ ↦ le_rfl)
  simpa only [IdentTask.ν_restrict, ν_baiTask] using h

/-- **Asymptotic optimality of Track-and-Stop with C-tracking** [GK16, Theorem 14]: the statement of
`limsup_expectedStoppingTime_trackAndStop_div_log_le` for the C-tracking sampling rule.

The proof shows the stronger `limsup ≤ T*(μ)`
(`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`), and of the
hypothesis on `p` it uses only `1 ≤ p`. -/
theorem limsup_expectedStoppingTime_cTrackAndStop_div_log_le (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ' a, ν μ' a = ρ.expFamily id (ρ.natParam id (μ' a)))
    (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      w μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).optAlloc μ' (rec μ'))
    (hrec_best : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M,
      ∀ b ≠ rec μ', μ' b < μ' (rec μ'))
    (hp : p ∈ Set.Icc 1 (exp 1 / 2)) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hμ : μ ∈ ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).M) :
    limsup (fun δ ↦ expectedStoppingTime
        (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).cTrackAndStop empMean' w
          hw (fun n _ ↦ ENNReal.ofReal (log (r n / δ))) rec hrec (hstop δ))
        (Environment.bandit (ν μ)) / ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤
      ENNReal.ofReal p *
        ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ := by
  have hμ' := hμ
  rw [IdentTask.M_restrict, M_baiTask] at hμ'
  obtain ⟨⟨a, ha⟩, hμS⟩ := hμ'
  have h_near := eventually_mem_M_and_rec_eq ν ρ hρ hrec_best hμS ha
  -- LMLExplore's bound `𝔼[τ_δ] ≤ c log (1 / δ)` for every `c > T*(μ)`, whatever `p`.
  refine (limsup_div_log_le fun c hc ↦ ?_).trans
    (le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 hp.1))
  have h := IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt
    ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}) (ρ := fun _ ↦ ρ)
    (T := fun _ ↦ id) (hw := hw) (hrec := hrec) (hstop := hstop)
    (β := fun δ n _ ↦ ENNReal.ofReal (log (r n / δ))) (n₀ := 0) (fun _ ↦ hρ) hμS
    (mgfDominatedOn_expFamily ν ρ hν)
    (by rw [IdentTask.correct_restrict]; exact (correct_baiTask_eq_singleton_iff ν id).2 ha)
    hw_mem (h_near.mono fun μ' h ↦ by rw [← h.2]; exact hw_opt μ' h.1) (h_near.mono fun _ h ↦ h.2)
    (fun _ hv ↦ continuousWithinAt_altCost_baiTask_restrict ν hρ (klDiv_eq_expFamilyDiv ν ρ hν)
      hμS ha hv)
    hc hr (Eventually.of_forall fun _ _ _ _ ↦ le_rfl)
  simpa only [IdentTask.ν_restrict, ν_baiTask] using h

end Garivier2016Optimal
