/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.Identification.Task.BestArm
public import Garivier2016Optimal.ForLMLExplore.Identification.AlmostSure
public import Garivier2016Optimal.ForLMLExplore.SequentialLearning.SumRewards
public import Garivier2016Optimal.GK2016.Basic
public import Garivier2016Optimal.GK2016.Proposition6

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

The proof specializes the almost sure sample complexity of the GLRT for any task and any estimator
(`IdentTask.ae_eventually_stoppingTime_glrt_le` and `IdentTask.ae_stoppingTime_glrt_ne_top`, in
`ForLMLExplore/Identification/AlmostSure.lean`), a target of LMLRoadmaps (Identification, Layer 4,
item 4), with `W = {w}`. The empirical means converge almost surely to `μ` by the strong law of
large numbers (`ae_tendsto_empMean_of_tendsto_pullCount`), since every arm gets a positive
proportion `w b > 0` of the pulls [GK16, Proposition 6]. The cost `D(μ', w', ¬a)` is continuous at
`(μ, w)` (`continuousWithinAt_altCost_baiTask_restrict`), and `D(μ, w, ¬a) = T*(μ)⁻¹` at the optimal
allocation.

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

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The almost sure upper bound** [GK16, Proposition 13]. Let the arms be in the exponential
family `(ρ, id)`, `rec μ'` be the best arm of every vector of means `μ'` with a unique best arm,
the thresholds be `log (r(t) / δ)` with `r(t) = O(t ^ p)`, `p ∈ [1, e / 2]`, and `(O, A, Y)` be a
run of a sampling rule `alg` on a vector of means `μ` of the family with a unique best arm, whose
proportions of pulls converge almost surely to an optimal allocation `w`. Then for every
`δ ∈ (0, 1)` the stopping time `τ_δ` of Chernoff's stopping rule is almost surely finite, and
almost surely `limsup_{δ → 0} τ_δ / log (1 / δ) ≤ p T*(μ)`.

The proof shows the stronger `limsup ≤ T*(μ)`: of the hypothesis on `p`, it uses only `1 ≤ p`.
The instance `[Nonempty α]` of the statement is not used. The binders of the statement are those
of its comparator challenge, in the same order. -/
@[nolint unusedArguments]
theorem stoppingTime_glrt_ne_top_and_limsup_le [Nonempty α] {mα : MeasurableSpace α}
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
    (hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c)
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
  have hμ' := hμ
  rw [IdentTask.M_restrict, M_baiTask] at hμ'
  obtain ⟨⟨a, ha⟩, hμS⟩ := hμ'
  have h_near := eventually_mem_M_and_rec_eq ν ρ hρ hrec_best hμS ha
  rw [h_near.self_of_nhds.2] at hw
  have hw' := (IdentTask.mem_optAlloc_iff _).1 hw
  -- Every arm is pulled a positive proportion `w b` of the time, so that, by the strong law of
  -- large numbers, the empirical means converge almost surely to `μ`.
  have h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ empMean' n (history O A Y n ω)) atTop (𝓝 μ) := by
    have h_int (b : α) : Integrable id (ν μ b) := by
      rw [hν]
      exact Measure.integrable_expFamily (Measure.natParam_mem_interior_integrableExpSet (hμS b))
    filter_upwards [ae_tendsto_empMean_of_tendsto_pullCount hseq h_int, hconv] with ω h_slln h_conv
    refine tendsto_pi_nhds.2 fun b ↦ ?_
    have hN : Tendsto (fun n ↦ pullCount A b n ω) atTop atTop := by
      have h_mul : Tendsto (fun n : ℕ ↦ (pullCount A b n ω : ℝ) / n * n) atTop atTop :=
        (h_conv b).pos_mul_atTop (pos_of_mem_optAlloc ν ρ hρ hν hμS ha hw b)
          tendsto_natCast_atTop_atTop
      refine tendsto_natCast_atTop_iff.1 (h_mul.congr' ?_)
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have h := h_slln b hN
    rw [hν, show ∫ x, x ∂(ρ.expFamily id (ρ.natParam id (μ b))) = μ b from
      Measure.integral_expFamily_natParam (hμS b)] at h
    exact h.congr fun n ↦ empMean_eq_empMean'
  -- The proportions of pulls converge almost surely to `w`.
  have h_prop : ∀ᵐ ω ∂P,
      Tendsto (fun n b ↦ (pullCount A b n ω : ℝ) / n) atTop (𝓝ˢ ({w} : Set (α → ℝ))) := by
    rw [nhdsSet_singleton]
    filter_upwards [hconv] with ω h using tendsto_pi_nhds.2 h
  have h_lsc : ∀ v ∈ ({w} : Set (α → ℝ)), LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).altCost q.1 q.2 a)
      (Set.univ ×ˢ simplex α) (μ, v) := by
    rintro v rfl
    exact (continuousWithinAt_altCost_baiTask_restrict ν hρ (klDiv_eq_expFamilyDiv ν ρ hν) hμS ha
      hw'.1).lowerSemicontinuousWithinAt
  -- At the optimal allocation `w`, `D(μ, w, ¬a) = T*(μ)⁻¹ > 0`.
  have hD : ⨅ v ∈ ({w} : Set (α → ℝ)),
      ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).altCost μ v a =
        (((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).charTime μ)⁻¹ := by
    have hcorrect :
        ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).correct μ = {a} := by
      rw [IdentTask.correct_restrict]
      exact (correct_baiTask_eq_singleton_iff ν id).2 ha
    rw [iInf_singleton, IdentTask.charTime_eq_inv_answerValue _ hcorrect, inv_inv, hw'.2]
  have hpos : 0 < ⨅ v ∈ ({w} : Set (α → ℝ)),
      ((baiTask ν id).restrict {μ' | ∀ a, μ' a ∈ ρ.expFamilyMeans id}).altCost μ v a := by
    rw [iInf_singleton, hw'.2]
    exact answerValue_baiTask_restrict_pos ν hρ hμS (klDiv_eq_expFamilyDiv ν ρ hν μ · hμS) ha
  -- The thresholds are `log (r t / δ) ≤ log (1 / δ) + log (r t)`, with `log (r t) = o(t)`.
  have hf : ∀ ε > 0, ∀ᶠ T in atTop, log (r T) ≤ ε * T :=
    fun _ hε ↦ eventually_log_le_mul_of_isBigO hr hε
  have hβ : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ T ≥ 0, ∀ _ : Hist Unit α ℝ T,
      ENNReal.ofReal (log (r T / δ)) ≤ ENNReal.ofReal (log (1 / δ) + log (r T)) :=
    fun _ hδ _ _ _ ↦ ENNReal.ofReal_le_ofReal (log_div_le_log_one_div_add_log _ hδ.1 hδ.2.le)
  refine ⟨fun δ hδ ↦ ?_, ?_⟩
  · filter_upwards [IdentTask.ae_stoppingTime_glrt_ne_top _ alg empMean' (hrec := hrec)
      (hstop := hstop) isCompact_singleton h_lsc (h_near.mono fun _ h ↦ h.2) hpos h_est h_prop hf
      hβ] with ω hω using hω δ hδ
  · filter_upwards [IdentTask.ae_eventually_stoppingTime_glrt_le _ alg empMean' (hrec := hrec)
      (hstop := hstop) isCompact_singleton h_lsc (h_near.mono fun _ h ↦ h.2) h_est h_prop hf
      (Eventually.mono (Ioo_mem_nhdsGT one_pos) hβ)] with ω hω
    refine (limsup_div_log_le fun c hc ↦ hω c ?_).trans
      (le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 hp.1))
    rwa [hD, inv_inv]

end Garivier2016Optimal
