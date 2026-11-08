/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.SequentialLearning.ExpFamilyDeviation
public import LMLExplore.Identification.ExpFamilyThreshold
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The deviational thresholds `log (C t ^ p / δ)` of the GLRT for exponential families

Let the models of an identification task be vectors of means `μ : α → ℝ` of `K` arms, and let the
arm `a` be dominated by the member of mean `μ_a` of the exponential family `(ρ a, T a)`. The GLRT
with the generalized likelihood ratio evidence `Z_n(h, λ) = ∑ a, N_a dbar_a(μ̂_a, λ_a)`
(`LMLExplore.Identification.expFamilyEvidence`) stops with an answer that is not correct only if
the evidence against the true model exceeds the threshold at some round. LMLExplore proves the
`δ`-correctness of the thresholds `K log (2 n (n + 1)) + x_δ` [LS, Lemma 33.7]
(`Identification/ExpFamilyThreshold.lean`), which grow like `2 K log n`. This file proves it for
the thresholds `β(n, δ) = log (C n ^ p / δ)` of [GK16, Proposition 12], for every exponent `p > 0`.

The peeled deviation inequality of `SequentialLearning/ExpFamilyDeviation.lean` bounds by
`f(x) = (x / K) ^ K exp (K - x)`, for `x ≥ K`, the probability that the evidence against the true
model exceeds `2 (K (η log₂ n + log (2 / (1 - exp (-η)))) + x)` at some round, for every `η > 0`.
With `η = p log 2 / (2 K)`, these thresholds are at most `p log n + c_{p,K} + 2 x`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, since `log₂ n log 2 ≤ log n`. So the GLRT
with thresholds at least `p log n + c_{p,K} + 2 x` has error probability at most `f(x)`, and with
the level `x_δ` of `Identification/GLR.lean` the thresholds `log (C n ^ p / δ)` are `δ`-correct as
soon as `C ≥ δ exp (c_{p,K} + 2 x_δ)`.

The constant depends on `δ`, through `x_δ = log (1 / δ) + O(log log (1 / δ))`. [GK16] states the
result with a constant `C(α, K)` independent of `δ`, which its proof does not give: the last step
of the proof drops the `δ` inside the logarithm of the condition on `C`. The factor `2` in front
of `x_δ` comes from the ratio `2` of the peeling.

## Main statements

The declarations are in the namespace `LMLExplore.Identification`.

* `IdentTask.measure_exists_lt_expFamilyEvidence_le_of_le`: along a run of any sampling rule, the
  evidence against the true model exceeds thresholds at least
  `2 (K (η log₂ n + log (2 / (1 - exp (-η)))) + x)` at some round with probability at most `f(x)`.
* `IdentTask.measure_exists_lt_expFamilyEvidence_le_of_mul_log_le`: the same for thresholds at
  least `p log n + c_{p,K} + 2 x`.
* `IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le`: the GLRT with
  such thresholds stops with an incorrect answer with probability at most `f(x)`.
* `IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le`:
  [GK16, Proposition 12], with `C ≥ δ exp (c_{p,K} + 2 x_δ)`: the GLRT with the thresholds
  `log (C n ^ p / δ)` stops with an incorrect answer with probability at most `δ`.
* `IdentTask.isDeltaPAC_glrt_expFamilyEvidence_log_mul_rpow_div`: with these thresholds, the GLRT
  is `δ`-PAC as soon as it stops almost surely on every model.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Real

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓧 : Type*} [Fintype α] [DecidableEq α] {m𝓧 : MeasurableSpace 𝓧}
  {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ}

/-- With `η = p log 2 / (2 K)`, the peeled thresholds `2 K (η log₂ n + κ)` are at most
`p log n + 2 K κ`, since `log₂ n log 2 ≤ log n`. -/
private lemma two_mul_card_mul_le {p : ℝ} (hp : 0 < p) {K : ℕ} (hK : K ≠ 0) (n : ℕ) (κ : ℝ) :
    2 * (K * (p * log 2 / (2 * K) * Nat.log 2 n + κ)) ≤ p * log n + 2 * K * κ := by
  have h := Real.natLog_le_logb n 2
  rw [Real.logb, Nat.cast_ofNat, le_div_iff₀ (log_pos one_lt_two)] at h
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK)
  calc 2 * (K * (p * log 2 / (2 * K) * Nat.log 2 n + κ))
  _ = p * (Nat.log 2 n * log 2) + 2 * K * κ := by field_simp
  _ ≤ p * log n + 2 * K * κ := by gcongr

/-- For `C ≥ δ exp (c + 2 x)` and `n ≥ 1`, the threshold `log (C n ^ p / δ)` is at least
`p log n + c + 2 x`. -/
private lemma mul_log_add_le_log_mul_rpow_div {p C δ c x : ℝ} (hδ : 0 < δ)
    (hC : δ * exp (c + 2 * x) ≤ C) {n : ℕ} (hn : n ≠ 0) :
    p * log n + c + 2 * x ≤ log (C * n ^ p / δ) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have h := log_le_log (by positivity) hC
  rw [log_mul hδ.ne' (exp_pos _).ne', log_exp] at h
  rw [log_div (by positivity) hδ.ne', log_mul hC0.ne' (by positivity), log_rpow hn]
  linarith

namespace IdentTask

variable {ℐ : Type*} {mα : MeasurableSpace α} {task : IdentTask α (α → ℝ) ℐ ℝ}
  [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → ℝ} {μ : α → ℝ} {x δ p : ℝ} {β : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}

/-- **Peeled deviation of the generalized likelihood ratio evidence for arms dominated by
exponential families**, along a run of any sampling rule. If the rewards of each arm `a` of the
model `μ` are dominated on `Set.univ`, in moment generating function, by the member of mean `μ a`
of the exponential family `(ρ a, T a)`, then for `η > 0`, a level `x ≥ K` and thresholds `β` at
least `2 (K (η log₂ n + log (2 / (1 - exp (-η)))) + x)` at every round `n ≥ 1`, with
`log₂ n = Nat.log 2 n`, the probability that at some round the evidence against the true model `μ`
exceeds the threshold is at most `(x / K) ^ K exp (K - x)`. -/
lemma measure_exists_lt_expFamilyEvidence_le_of_le {η : ℝ} (hη : 0 < η)
    (hβ : ∀ n, n ≠ 0 → ∀ h, ENNReal.ofReal (2 * (Fintype.card α *
      (η * Nat.log 2 n + log (2 / (1 - exp (-η)))) + x)) ≤ β n h)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, β n (history O A R n ω) < expFamilyEvidence ρ T n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le hseq hμ hν hη hx)
  obtain ⟨n, hn⟩ := hω
  have h_eq : expFamilyEvidence ρ T n (history O A R n ω) μ =
      ∑ a, pullCount A a n ω * (ρ a).expFamilyRate (T a) (empMean A R a n ω) (μ a) := by
    simp only [expFamilyEvidence_def, pullCount_eq_pullCount' (O := O) (R' := R),
      empMean_eq_empMean' (O := O)]
  -- no arm is pulled before the first round, so the evidence vanishes there
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [h_eq] at hn
    simp at hn
  exact ⟨n, (hβ n hn0 _).trans (hn.le.trans_eq h_eq)⟩

/-- **Deviation of the generalized likelihood ratio evidence for arms dominated by exponential
families, for thresholds `p log n + c_{p,K} + 2 x`**, along a run of any sampling rule. If the
rewards of each arm `a` of the model `μ` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for `p > 0`, a
level `x ≥ K` and thresholds `β` at least `p log n + c_{p,K} + 2 x` at every round `n ≥ 1`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, the probability that at some round the
evidence against the true model `μ` exceeds the threshold is at most `(x / K) ^ K exp (K - x)`. -/
lemma measure_exists_lt_expFamilyEvidence_le_of_mul_log_le [Nonempty α] (hp : 0 < p)
    (hβ : ∀ n : ℕ, n ≠ 0 → ∀ h, ENNReal.ofReal (p * log n + 2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) + 2 * x) ≤ β n h)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, β n (history O A R n ω) < expFamilyEvidence ρ T n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  have hη : 0 < p * log 2 / (2 * Fintype.card α) := by
    have := log_pos one_lt_two
    positivity
  refine measure_exists_lt_expFamilyEvidence_le_of_le hη
    (fun n hn h ↦ (ENNReal.ofReal_le_ofReal ?_).trans (hβ n hn h)) hμ hν hseq hx
  linarith [two_mul_card_mul_le hp (Fintype.card_ne_zero (α := α)) n
    (log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))))]

variable {mℐ : MeasurableSpace ℐ} (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ)
  (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for arms dominated by exponential families, with thresholds
`p log n + c_{p,K} + 2 x`**, for every task and every sampling rule. If the rewards of each arm `a`
of an admissible model `μ` are dominated on `Set.univ`, in moment generating function, by the
member of mean `μ a` of the exponential family `(ρ a, T a)`, then for `p > 0`, a level `x ≥ K` and
thresholds `β` at least `p log n + c_{p,K} + 2 x` at every round `n ≥ 1`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, the GLRT with the generalized likelihood
ratio evidence and the thresholds `β` stops with an answer that is not correct for `μ` with
probability at most `(x / K) ^ K exp (K - x)`. -/
lemma measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le [Nonempty α]
    (hp : 0 < p)
    (hβ : ∀ n : ℕ, n ≠ 0 → ∀ h, ENNReal.ofReal (p * log n + 2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) + 2 * x) ≤ β n h)
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr (expFamilyEvidence ρ T) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure (task.glrt (expFamilyEvidence ρ T) alg β rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {q | q.1 ∈ (task.glrt (expFamilyEvidence ρ T) alg β rec hrec hstop).stopSet ∧
          q.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν μ))
  refine (task.measureReal_histOutputMeasure_glrt_le (expFamilyEvidence ρ T) alg _ rec hrec hstop
    hseq hμM hc).trans ?_
  rw [measureReal_def]
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (measure_exists_lt_expFamilyEvidence_le_of_mul_log_le hp hβ hμ hν hseq hx)

/-- **The deviational thresholds of the GLRT for arms dominated by exponential families**
([GK16, Proposition 12], with a constant depending on `δ`), for every task and every sampling rule.
If the rewards of each arm `a` of an admissible model `μ` are dominated on `Set.univ`, in moment
generating function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for
`p > 0`, `δ ∈ (0, 1]` and `C ≥ δ exp (c_{p,K} + 2 x_δ)`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and `x_δ` is the level of
`Identification/GLR.lean`, the GLRT with the generalized likelihood ratio evidence and the
thresholds `log (C n ^ p / δ)` stops with an answer that is not correct for `μ` with probability at
most `δ`. [GK16] states it for `p > 1`, with a constant independent of `δ`. -/
theorem measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le [Nonempty α]
    {C : ℝ} (hp : 0 < p) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : δ * exp (2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) +
        2 * unionBoundLevel (Fintype.card α) δ) ≤ C)
    (hstop : ∀ n : ℕ, MeasurableSet {h | ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ)) <
      task.glr (expFamilyEvidence ρ T) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) :
    (histOutputMeasure (task.glrt (expFamilyEvidence ρ T) alg
          (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {q | q.1 ∈ (task.glrt (expFamilyEvidence ρ T) alg
          (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop).stopSet ∧
          q.2 ∉ task.correct μ} ≤ δ :=
  (measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le rec hrec hp
    (fun _ hn _ ↦ ENNReal.ofReal_le_ofReal (mul_log_add_le_log_mul_rpow_div hδ hC hn)) hstop
    hμM hμ hν hc (card_le_unionBoundLevel hδ hδ1)).trans
    (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)

/-- **The GLRT with the deviational thresholds is `δ`-PAC** ([GK16, Proposition 12], with a
constant depending on `δ`), for every task and every sampling rule. If on every admissible model
`θ` the rewards of each arm `a` are dominated on `Set.univ`, in moment generating function, by the
member of mean `θ a` of the exponential family `(ρ a, T a)`, then for `p > 0`, `δ ∈ (0, 1]` and
`C ≥ δ exp (c_{p,K} + 2 x_δ)`, where `c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, the
GLRT with the generalized likelihood ratio evidence and the thresholds `log (C n ^ p / δ)` is
`δ`-PAC on the task, provided it stops almost surely on every admissible model. -/
theorem isDeltaPAC_glrt_expFamilyEvidence_log_mul_rpow_div [Nonempty α] {C : ℝ} (hp : 0 < p)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : δ * exp (2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) +
        2 * unionBoundLevel (Fintype.card α) δ) ≤ C)
    (hstop : ∀ n : ℕ, MeasurableSet {h | ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ)) <
      task.glr (expFamilyEvidence ρ T) n h (rec n h)})
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt (expFamilyEvidence ρ T) alg
      (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt (expFamilyEvidence ρ T) alg
      (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop) δ := by
  refine task.isDeltaPAC_glrt (expFamilyEvidence ρ T) alg _ rec hrec hstop hc (fun θ hθ ↦ ?_)
    h_stops
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal hδ.le
    ((measure_exists_lt_expFamilyEvidence_le_of_mul_log_le hp
      (fun _ hn _ ↦ ENNReal.ofReal_le_ofReal (mul_log_add_le_log_mul_rpow_div hδ hC hn))
      (hμ θ hθ) (hν θ hθ) (IT.isAlgEnvSeq_trajMeasure alg _)
      (card_le_unionBoundLevel hδ hδ1)).trans ?_)
  exact ENNReal.ofReal_le_ofReal (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)

end IdentTask

end LMLExplore.Identification
