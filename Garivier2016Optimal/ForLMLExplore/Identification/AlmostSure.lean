/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop

/-!
# Almost sure sample complexity of the GLRT

The almost sure counterpart [GK16, Proposition 13] of the generic sample complexity reduction
`IdentTask.eventually_expectedStoppingTime_glrt_le`. Consider the GLRTs with thresholds
`β δ T h ≤ log (1 / δ) + f T`, where `f T ≤ ε T` eventually for every `ε > 0`.

* **Pathwise.** Along one sequence of histories, if the GLR statistic of the recommended answer
  after `T` rounds is at least `κ T` for all large `T`, with `κ > 0`, the GLRT stops for every
  `δ` at which the thresholds have this form, and its stopping time is at most `c log (1 / δ)` for
  all small `δ`, for every `c > 1 / κ`.
* **Linear growth of the plug-in statistic.** For the plug-in statistic of an estimator `θ̂`, the
  GLR statistic after `T` rounds is `T D(θ̂_T, N(T) / T, ¬i)`. If `θ̂_T → θ`, the proportions of
  pulls `N(T) / T` approach a compact set `W` of allocations, `(θ', w) ↦ D(θ', w, ¬i)` is lower
  semicontinuous at `(θ, w)` for every `w ∈ W`, and the recommendation is `i` near `θ`, then it is
  at least `κ T` for all large `T`, for every `κ < inf_{w ∈ W} D(θ, w, ¬i)`.
* **Almost surely.** If almost surely `θ̂_T → θ` and `N(T) / T` approaches `W`, then almost surely,
  for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, the stopping time at the confidence level `δ` is at
  most `c log (1 / δ)` for all small `δ`, and the GLRT stops at every such `δ` if the infimum is
  positive.

The thresholds `log (r T / δ)` with `r T = O(T ^ p)` of [GK16, Theorem 14] have this form with
`f T = log (r T)`, for `δ ∈ (0, 1]` (`log_div_le_log_one_div_add_log`,
`eventually_log_le_mul_of_isBigO`).

## Main statements

* `IdentTask.stoppingTime_glrt_ne_top_of_eventually_mul_le_glr`,
  `IdentTask.eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr`: the pathwise statements.
* `IdentTask.eventually_mul_le_glr_plugInCost`: the linear growth of the plug-in statistic.
* `IdentTask.ae_eventually_stoppingTime_glrt_le`, `IdentTask.ae_stoppingTime_glrt_ne_top`:
  [GK16, Proposition 13] for any task, any estimator and any thresholds of the form above.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 13.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real Metric

open scoped Topology ENNReal NNReal

namespace LMLExplore.Identification

/-! ### The thresholds `log (r T / δ)` -/

/-- For `δ ∈ (0, 1]`, `log (x / δ) ≤ log (1 / δ) + log x`, with equality for `x ≠ 0`: the
thresholds `log (r T / δ)` are at most `log (1 / δ) + log (r T)`. -/
lemma log_div_le_log_one_div_add_log (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    log (x / δ) ≤ log (1 / δ) + log x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [zero_div, log_zero, add_zero]
    exact log_nonneg (one_le_one_div hδ hδ1)
  · rw [log_div hx hδ.ne', one_div, log_inv]
    linarith

/-- If `r T = O(T ^ p)`, then `log (r T) ≤ ε T` for all large `T`, for every `ε > 0`. -/
lemma eventually_log_le_mul_of_isBigO {r : ℕ → ℝ} {p : ℝ}
    (hr : r =O[atTop] fun T ↦ (T : ℝ) ^ p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, log (r T) ≤ ε * T := by
  obtain ⟨C, hC, hrC⟩ := hr.exists_pos
  have hg : (fun T : ℕ ↦ log C + p * log T) =o[atTop] fun T : ℕ ↦ (T : ℝ) :=
    ((Asymptotics.isLittleO_const_id_atTop (log C)).add
      (isLittleO_log_id_atTop.const_mul_left p)).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [hrC.bound, hg.bound hε, eventually_gt_atTop 0] with T hrT hgT hT
  rcases eq_or_ne (r T) 0 with h | h
  · simp only [h, log_zero]
    positivity
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (rpow_nonneg hT'.le p)] at hrT
  rw [Real.norm_of_nonneg hT'.le] at hgT
  calc log (r T)
  _ = log |r T| := (log_abs _).symm
  _ ≤ log (C * T ^ p) := log_le_log (abs_pos.2 h) hrT
  _ = log C + p * log T := by rw [log_mul hC.ne' (rpow_pos_of_pos hT' p).ne', log_rpow hT']
  _ ≤ ε * T := (le_abs_self _).trans hgT

namespace IdentTask

/-! ### Pathwise: from the linear growth of the GLR statistic to the stopping time -/

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mℐ : MeasurableSpace ℐ} (task : IdentTask α Θ ℐ 𝓨) (Z : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞)
  (alg : Algorithm Unit α 𝓨) (rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ)
  (hrec : ∀ n, Measurable (rec n))
  {Ω : Type*} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {ω : Ω} {κ c : ℝ≥0} {T₀ : ℕ}
  {f : ℕ → ℝ}

/-- **The GLRT stops** along a sequence of histories on which its statistic grows linearly. If the
GLR statistic of the recommended answer after `T` rounds is at least `κ T` for all large `T`, with
`κ > 0`, and the thresholds are `β T h ≤ L + f T` for all large `T`, where `f T ≤ ε T` eventually
for every `ε > 0`, then the stopping time of the GLRT is finite. -/
lemma stoppingTime_glrt_ne_top_of_eventually_mul_le_glr
    {β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr Z n h (rec n h)}) (hκ : 0 < κ)
    (hE : ∀ᶠ T in atTop,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T) {L : ℝ}
    (hβ : ∀ᶠ T in atTop, ∀ h, β T h ≤ ENNReal.ofReal (L + f T)) :
    (task.glrt Z alg β rec hrec hstop).stoppingTime O X Y ω ≠ ⊤ := by
  have hκ' : (0 : ℝ) < κ := hκ
  obtain ⟨T, hET, hfT, hβT, hLT, hT0⟩ := (hE.and ((hf (κ / 2) (by positivity)).and (hβ.and
    (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (2 * L / κ)).and
    (eventually_gt_atTop 0))))).exists
  have hLT' : L < κ / 2 * T := by
    rw [div_lt_iff₀ hκ'] at hLT
    linarith
  refine ne_top_of_le_ne_top (WithTop.coe_ne_top (a := T)) (task.stoppingTime_glrt_le Z alg β rec
    hrec hstop ?_)
  calc β T (history O X Y T ω)
  _ ≤ ENNReal.ofReal (L + f T) := hβT _
  _ < ENNReal.ofReal (κ * T) := by
    refine (ENNReal.ofReal_lt_ofReal_iff (mul_pos hκ' (Nat.cast_pos.2 hT0))).2 ?_
    linarith
  _ = κ * T := by
    rw [ENNReal.ofReal_mul κ.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  _ ≤ _ := hET

/-- **The stopping time of the GLRT at small `δ`** along a sequence of histories on which its
statistic grows linearly (the deterministic step of [GK16, Proposition 13]). Consider the GLRTs with
thresholds `β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀`, where `f T ≤ ε T` eventually for every
`ε > 0`. If the GLR statistic of the recommended answer after `T` rounds is at least `κ T` for all
large `T`, then the stopping time at the confidence level `δ` is at most `c log (1 / δ)` for all
small enough `δ`, for every `c > 1 / κ`. -/
lemma eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr
    {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    (hstop : ∀ δ n, MeasurableSet {h | β δ n h < task.glr Z n h (rec n h)})
    (hE : ∀ᶠ T in atTop,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    (hκc : 1 < κ * c) (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᶠ δ in 𝓝[>] 0, ENat.toENNReal
        ((task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω) ≤
      c * ENNReal.ofReal (log (1 / δ)) := by
  have hκc' : 1 < (κ : ℝ) * c := mod_cast hκc
  have hc : 0 < (c : ℝ) := pos_of_mul_pos_right (one_pos.trans hκc') κ.coe_nonneg
  -- Choose `η` with `1 / c < η < κ`: if `log (1 / δ) ≤ η T`, the threshold is below `κ T`.
  obtain ⟨η, hcη, hηκ⟩ : ∃ η, (c : ℝ)⁻¹ < η ∧ η < κ :=
    exists_between ((inv_lt_iff_one_lt_mul₀' hc).2 (by linarith))
  have hη : 0 < η := (inv_pos.2 hc).trans hcη
  have hκ : 0 < (κ : ℝ) := hη.trans hηκ
  have hηc : 0 < (c : ℝ) - η⁻¹ := sub_pos.2 (inv_lt_of_inv_lt₀ hc hcη)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hf ((κ - η) / 2) (by linarith))
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 hE
  set M := max (max T₀ T₁) (max T₂ 1)
  have hL : Tendsto (fun δ : ℝ ↦ log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [hβ, hL.eventually_ge_atTop ((M + 1) / (c - η⁻¹))] with δ hβδ hLδ
  set L := log (1 / δ)
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ (M + 1) / (c - η⁻¹)).trans hLδ
  -- After `N = max M ⌈L / η⌉` rounds, the stopping condition holds.
  set N := max M ⌈L / η⌉₊
  have hN₀ : T₀ ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := mod_cast (show 1 ≤ N by omega)
  have hLN : L ≤ η * N := by
    rw [← div_le_iff₀' hη]
    exact (Nat.le_ceil _).trans (mod_cast le_max_right _ _)
  have hfN := hT₁ N (by omega)
  have h_stop : (task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω ≤ N := by
    refine task.stoppingTime_glrt_le Z alg (β δ) rec hrec (hstop δ) ?_
    calc β δ N (history O X Y N ω)
    _ ≤ ENNReal.ofReal (L + f N) := hβδ N hN₀ _
    _ < ENNReal.ofReal (κ * N) := by
      refine (ENNReal.ofReal_lt_ofReal_iff (mul_pos hκ (by linarith))).2 ?_
      nlinarith
    _ = κ * N := by
      rw [ENNReal.ofReal_mul κ.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    _ ≤ _ := hT₂ N (by omega)
  -- Hence `τ_δ ≤ N ≤ M + L / η + 1 ≤ c L`.
  calc ENat.toENNReal ((task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω)
  _ ≤ ENat.toENNReal N := ENat.toENNReal_le.2 h_stop
  _ = ENNReal.ofReal N := by rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  _ ≤ ENNReal.ofReal (c * L) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hceil : (⌈L / η⌉₊ : ℝ) ≤ L / η + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hN : (N : ℝ) ≤ M + (L / η + 1) := by
      rw [Nat.cast_max]
      have hM : (0 : ℝ) ≤ M := M.cast_nonneg
      exact max_le (by linarith [div_nonneg hL0 hη.le]) (by linarith)
    rw [div_le_iff₀ hηc] at hLδ
    have : L / η = η⁻¹ * L := by ring
    nlinarith
  _ = c * ENNReal.ofReal L := by rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-! ### The linear growth of the plug-in statistic -/

variable [Fintype α] [DecidableEq α] [TopologicalSpace Θ] (est : (n : ℕ) → Hist Unit α 𝓨 n → Θ)
  {θ : Θ} {i : ℐ} {W : Set (α → ℝ)}

omit [TopologicalSpace Θ] in
/-- After `T ≠ 0` rounds, the proportions of pulls `N(T) / T` are an allocation. -/
lemma pullCount_div_mem_simplex {T : ℕ} (hT : T ≠ 0) :
    (fun a ↦ (pullCount X a T ω : ℝ) / T) ∈ simplex α := by
  refine mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_pullCount, div_self (Nat.cast_ne_zero.2 hT)]

/-- **Linear growth of the plug-in statistic** [GK16, proof of Proposition 13]. Along a sequence of
histories on which the estimates `θ̂_T` converge to `θ` and the proportions of pulls `N(T) / T`
approach a compact set `W` of allocations, let `(θ', w) ↦ D(θ', w, ¬i)` be lower semicontinuous at
`(θ, w)` on the allocations of the simplex for every `w ∈ W`, and let the recommendation be `i`
near `θ`. Then the GLR statistic of the recommendation after `T` rounds is at least `κ T` for all
large `T`, for every `κ < inf_{w ∈ W} D(θ, w, ¬i)`. -/
lemma eventually_mul_le_glr_plugInCost {rec : Θ → ℐ} (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hκ : ∀ w ∈ W, (κ : ℝ≥0∞) < task.altCost θ w i) (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_est : Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W)) :
    ∀ᶠ T in atTop, κ * T ≤ task.glr (task.plugInCost est) T (history O X Y T ω)
      (rec (est T (history O X Y T ω))) := by
  obtain ⟨U, hU, η, hη, hUη⟩ := hW.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt
    h_lsc hκ
  filter_upwards [h_est.eventually_mem (inter_mem hU hrec_eq),
    h_prop.eventually_mem (thickening_mem_nhdsSet W hη), eventually_ne_atTop 0] with T hT hTW hT0
  rw [hT.2, glr_plugInCost_eq_mul task est hT0, mul_comm]
  have h_eq : (fun a ↦ (pullCount' T (history O X Y T ω) a : ℝ) / T) =
      fun a ↦ (pullCount X a T ω : ℝ) / T := by
    simp_rw [pullCount_eq_pullCount' (O := O) (R' := Y)]
  rw [h_eq]
  exact mul_le_mul_right (hUη _ hT.1 _ (pullCount_div_mem_simplex hT0) hTW).le _

/-! ### Almost sure sample complexity -/

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {rec : Θ → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h)}

/-- **Almost sure sample complexity of the GLRT** [GK16, Proposition 13], for every task, every
estimator and every sampling rule. Let `W` be a compact set of allocations such that
`(θ', w) ↦ D(θ', w, ¬i)` is lower semicontinuous at `(θ, w)` on the allocations of the simplex for
every `w ∈ W`, and let the GLRT use the plug-in statistic of the estimator `θ̂` and recommend `i`
near `θ`, with thresholds `β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀` and small `δ`, where
`f T ≤ ε T` eventually for every `ε > 0`. If almost surely `θ̂_T → θ` and the proportions of pulls
`N(T) / T` approach `W`, then almost surely, for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, the
stopping time at the confidence level `δ` is at most `c log (1 / δ)` for all small enough `δ`:
`limsup_{δ → 0} τ_δ / log (1 / δ) ≤ (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`. -/
theorem ae_eventually_stoppingTime_glrt_le {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    {hstop : ∀ δ n, MeasurableSet
      {h | β δ n h < task.glr (task.plugInCost est) n h (rec (est n h))}}
    (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : ∀ᵐ ω ∂P, Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᵐ ω ∂P, ∀ c : ℝ≥0, (⨅ w ∈ W, task.altCost θ w i)⁻¹ < c →
      ∀ᶠ δ in 𝓝[>] 0, ENat.toENNReal ((task.glrt (task.plugInCost est) alg (β δ)
          (fun n h ↦ rec (est n h)) hrec (hstop δ)).stoppingTime O X Y ω) ≤
        c * ENNReal.ofReal (log (1 / δ)) := by
  filter_upwards [h_est, h_prop] with ω h_est h_prop c hc
  obtain ⟨κ, hκ', hκc⟩ := ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt hc
  exact task.eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr (task.plugInCost est) alg
    _ hrec hstop (task.eventually_mul_le_glr_plugInCost est hW h_lsc
      (fun w hw ↦ hκ'.trans_le (iInf₂_le w hw)) hrec_eq h_est h_prop) hκc hf hβ

/-- **The GLRT stops almost surely** [GK16, Proposition 13], for every task, every estimator and
every sampling rule. Under the assumptions of `IdentTask.ae_eventually_stoppingTime_glrt_le`, with
`inf_{w ∈ W} D(θ, w, ¬i) > 0` and thresholds `β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀` and every
`δ` in a set `s`, almost surely the GLRT stops at every confidence level `δ ∈ s`. -/
theorem ae_stoppingTime_glrt_ne_top {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    {hstop : ∀ δ n, MeasurableSet
      {h | β δ n h < task.glr (task.plugInCost est) n h (rec (est n h))}}
    (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i) (hpos : 0 < ⨅ w ∈ W, task.altCost θ w i)
    (h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : ∀ᵐ ω ∂P, Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T) {s : Set ℝ}
    (hβ : ∀ δ ∈ s, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᵐ ω ∂P, ∀ δ ∈ s, (task.glrt (task.plugInCost est) alg (β δ) (fun n h ↦ rec (est n h)) hrec
      (hstop δ)).stoppingTime O X Y ω ≠ ⊤ := by
  obtain ⟨κ, hκ0, hκ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  filter_upwards [h_est, h_prop] with ω h_est h_prop δ hδ
  exact task.stoppingTime_glrt_ne_top_of_eventually_mul_le_glr (task.plugInCost est) alg _ hrec
    (hstop δ) (mod_cast hκ0) (task.eventually_mul_le_glr_plugInCost est hW h_lsc
      (fun w hw ↦ hκ'.trans_le (iInf₂_le w hw)) hrec_eq h_est h_prop) hf
    (eventually_atTop.2 ⟨T₀, fun T hT ↦ hβ δ hδ T hT⟩)

end IdentTask

end LMLExplore.Identification
