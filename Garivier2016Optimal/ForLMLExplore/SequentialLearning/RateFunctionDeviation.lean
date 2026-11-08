/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.Probability.Martingale.RateFunction
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.SequentialLearning.RateFunctionDeviation

/-!
# Peeled time-uniform deviations of the empirical means, measured by the rate function

Let the rewards of each arm `a` of the stochastic environment `Environment.bandit ν` be integrable,
with Cramér rate function `I_a = rateFunction id (ν a)`, and let `N_a` and `μ̂_a` be the number of
pulls and the empirical mean of `a`. `SequentialLearning/RateFunctionDeviation.lean` of LMLExplore
bounds the probability that `∑ a, N_a(t) I_a(μ̂_a(t))` exceeds `K log (2 t (t + 1)) + x` at some
round `t`, by a union bound over the number of rewards of each arm [LS, Lemma 33.8]. The term
`K log (2 t (t + 1))` grows like `2 K log t`. This file replaces the union bound by a peeling over
the dyadic slices `2 ^ k ≤ s < 2 ^ (k + 1)` of the number of rewards, as in [GC11, Theorem 10],
which makes the term grow like `η log₂ t` per arm, for any `η > 0`, at the price of a factor `2`.

For one arm, in LML's i.i.d. reward stream model, the deviation `z ≤ s I_a(μ̂_s)` happens on the
slice `k` with probability at most `2 exp (-z / 2)`
(`ProbabilityTheory.iIndepFun.measure_exists_le_and_lt_and_le_mul_rateFunction_le`). With the
level `z = 2 (η k + κ_η + y)`, where `κ_η = log (2 / (1 - exp (-η)))`, these probabilities sum to
`exp (-y)` over the slices: `P(∃ s, 2 (η log₂ s + κ_η + y) ≤ s I_a(μ̂_s)) ≤ exp (-y)`, with the
integer logarithm `log₂ s = Nat.log 2 s`. The arms are independent in the stream model, so
[LS, Proposition 33.9] (`LMLExplore.measure_exists_card_mul_add_le_sum_le`), applied to the halves
of the statistics, bounds their joint deviation, and the joint transfer of
`SequentialLearning/SumRewards.lean` turns it into a bound along the run, at all rounds
simultaneously: `P(∃ t, 2 (K (η log₂ t + κ_η) + x) ≤ ∑ a, N_a(t) I_a(μ̂_a(t)))` is at most
`(x / K) ^ K exp (K - x)` for `x ≥ K`. Since `η log₂ t ≤ (η / log 2) log t`, the thresholds
`log (C t ^ p / δ)` of [GK16, Proposition 12] dominate these for every `p > 0`, with `C` depending
on `p`, `K` and `δ` (`Identification/DeviationalThreshold.lean`).

## Main statements

* `LMLExplore.streamMeasure_exists_two_mul_add_le_mul_rateFunction_le`: for an integrable arm in
  the stream model, `P(∃ s, 2 (η log₂ s + κ_η + y) ≤ s I_a(μ̂_s)) ≤ exp (-y)`.
* `LMLExplore.streamMeasure_exists_two_mul_card_mul_add_le_sum_mul_rateFunction_le`: the joint
  deviation over all the arms and all the vectors of numbers of rewards, in the stream model.
* `LMLExplore.measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le`: along a
  run of any algorithm, `P(∃ t, 2 (K (η log₂ t + κ_η) + x) ≤ ∑ a, N_a(t) I_a(μ̂_a(t)))` is at most
  `(x / K) ^ K exp (K - x)` for `x ≥ K`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10, for the peeling.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.8 and Proposition 33.9.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits Filter

open scoped ENNReal Topology

namespace LMLExplore

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-! ### The reward stream model -/

/-- **Peeled time-uniform deviations of the empirical mean of one arm, measured by the rate
function.** In the reward stream model, if the rewards of the arm `a` are integrable, with rate
function `I_a`, then for `η > 0` and `y ≥ 0`, the probability that
`2 (η log₂ s + log (2 / (1 - exp (-η))) + y) ≤ s I_a(μ̂_s)` for some number `s` of rewards, with
`log₂ s = Nat.log 2 s`, is at most `exp (-y)`. -/
lemma streamMeasure_exists_two_mul_add_le_mul_rateFunction_le [Countable α] {a : α}
    (hν : Integrable id (ν a)) {η : ℝ} (hη : 0 < η) {y : ℝ} (hy : 0 ≤ y) :
    streamMeasure ν {ω | ∃ s : ℕ, ENNReal.ofReal (2 * (η * Nat.log 2 s +
        log (2 / (1 - exp (-η))) + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤ ENNReal.ofReal (exp (-y)) := by
  set κ := log (2 / (1 - exp (-η))) with hκ
  have he : exp (-η) < 1 := (exp_lt_exp.2 (neg_lt_zero.2 hη)).trans_eq exp_zero
  have he1 : 0 < 1 - exp (-η) := by linarith
  have hκ0 : 0 < κ := log_pos (by rw [lt_div_iff₀ he1]; linarith [exp_pos (-η)])
  -- the dyadic slice of the numbers of rewards `2 ^ k ≤ s < 2 ^ (k + 1)`
  let E : ℕ → Set (ℕ → α → ℝ) := fun k ↦ {ω | ∃ s : ℕ, (2 : ℝ) ^ k ≤ s ∧ (s : ℝ) < 2 ^ k * 2 ∧
    ENNReal.ofReal (2 * (η * k + κ + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)}
  have hE (k : ℕ) : streamMeasure ν (E k) ≤ ENNReal.ofReal (2 * exp (-(η * k + κ + y))) := by
    have h_indep := iIndepFun_eval_streamMeasure'' ν a
    have h := h_indep.measure_exists_le_and_lt_and_le_mul_rateFunction_le (Y := id) (Q := ν a)
      (fun i ↦ by fun_prop) (fun i ↦ identDistrib_eval_eval_id_streamMeasure ν i a) hν
      (a := 2 ^ k) (b := 2 ^ k * 2) (z := 2 * (η * k + κ + y)) (by positivity) (by positivity)
    refine h.trans_eq ?_
    congr 3
    field_simp
  -- a deviation with `s` rewards is a deviation on the slice of `s`
  have h_sub : {ω : ℕ → α → ℝ | ∃ s : ℕ, ENNReal.ofReal (2 * (η * Nat.log 2 s + κ + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ⊆ ⋃ k, E k := by
    rintro ω ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp only [Nat.log_zero_right, CharP.cast_eq_zero, mul_zero, zero_add, zero_mul,
        nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hs
      linarith
    refine Set.mem_iUnion.2 ⟨Nat.log 2 s, s, ?_, ?_, hs⟩
    · exact_mod_cast Nat.pow_log_le_self 2 hs0
    · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
      rw [Nat.pow_succ] at h
      exact_mod_cast h
  -- the bounds of the slices sum to `exp (-y)`
  have h_sum : HasSum (fun k : ℕ ↦ 2 * exp (-(η * k + κ + y))) (exp (-y)) := by
    have h := (hasSum_exp_neg_add_mul hη 0).mul_left (2 * exp (-(κ + y)))
    convert h using 1
    · ext k
      rw [mul_assoc, ← exp_add]
      push_cast
      ring_nf
    · rw [hκ, neg_add, exp_add, exp_neg (log _), exp_log (by positivity)]
      simp only [CharP.cast_eq_zero, zero_mul, neg_zero, exp_zero]
      field_simp
  calc _ ≤ streamMeasure ν (⋃ k, E k) := measure_mono h_sub
  _ ≤ ∑' k, streamMeasure ν (E k) := measure_iUnion_le _
  _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 * exp (-(η * k + κ + y))) := tsum_le_tsum hE
  _ = ENNReal.ofReal (exp (-y)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) h_sum.summable, h_sum.tsum_eq]

/-- In the reward stream model, if the rewards of the arm `a` are integrable, then almost surely
the statistic `s I_a(μ̂_s)` of the first `s` rewards is finite for every `s`. -/
private lemma streamMeasure_exists_mul_rateFunction_eq_top {a : α} (hν : Integrable id (ν a)) :
    streamMeasure ν {ω | ∃ s : ℕ,
      (s : ℝ≥0∞) * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s) = ∞} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun s ↦ nonpos_iff_eq_zero.1 ?_
  have h_tendsto : Tendsto (fun z : ℝ ↦ ENNReal.ofReal (2 * exp (-z))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_exp_neg_atTop_nhds_zero.const_mul 2)
  refine ge_of_tendsto' h_tendsto fun z ↦ (measure_mono fun ω hω ↦ ?_).trans
    (streamMeasure_le_mul_rateFunction_le hν s z)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hω]
  exact le_top

/-- **Peeled joint time-uniform deviations of the empirical means, measured by the rate
functions**, in the reward stream model. If the rewards of each arm `a` are integrable, with rate
function `I_a`, then for `η > 0` and `x ≥ K`, with `K` the number of arms, the probability that
`2 (K (η log₂ n + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a, s a I_a((∑ i < s a, X_i a) / s a)` for
some numbers of rewards `s : α → ℕ`, with `n = ∑ a, s a` and `log₂ n = Nat.log 2 n`, is at most
`(x / K) ^ K exp (K - x)`. -/
lemma streamMeasure_exists_two_mul_card_mul_add_le_sum_mul_rateFunction_le [Fintype α]
    (hν : ∀ a, Integrable id (ν a)) {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : Fintype.card α ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (2 * (Fintype.card α *
        (η * Nat.log 2 (∑ a, s a) + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the statistic `s I_a(μ̂_s)` of the first `s` rewards `f` of the arm `a`
  set F : α → (ℕ → ℝ) → ℕ → ℝ≥0∞ :=
    fun a f s ↦ s * rateFunction id (ν a) ((∑ i ∈ range s, f i) / s) with hF
  have hFm (a : α) (s : ℕ) : Measurable fun f : ℕ → ℝ ↦ F a f s :=
    measurable_const.mul ((lowerSemicontinuous_rateFunction _ _).measurable.comp (by fun_prop))
  -- the halves of the real statistics of the arms are functions of their independent reward
  -- sequences
  have h_indep : iIndepFun
      (fun a (ω : ℕ → α → ℝ) (s : ℕ) ↦ (F a (fun i ↦ ω i a) s).toReal / 2) (streamMeasure ν) :=
    (iIndepFun_arm_streamMeasure ν).comp (fun a f s ↦ (F a f s).toReal / 2)
      fun a ↦ Measurable.of_eval fun s ↦ (hFm a s).ennreal_toReal.div_const 2
  set g : ℕ → ℝ := fun n ↦ η * Nat.log 2 n + log (2 / (1 - exp (-η))) with hg_def
  have hg : Monotone g := fun m n hmn ↦ by
    simp only [hg_def]
    gcongr
  have hS (a : α) (y : ℝ) (hy : 0 ≤ y) : streamMeasure ν
      {ω | ∃ s : ℕ, g s + y ≤ (F a (fun i ↦ ω i a) s).toReal / 2} ≤
        ENNReal.ofReal (exp (-y)) := by
    refine le_trans (measure_mono fun ω hω ↦ ?_)
      (streamMeasure_exists_two_mul_add_le_mul_rateFunction_le (hν a) hη hy)
    obtain ⟨s, hs⟩ := hω
    refine ⟨s, ENNReal.ofReal_le_of_le_toReal ?_⟩
    simp only [hg_def] at hs
    linarith
  have h_real := measure_exists_card_mul_add_le_sum_le (P := streamMeasure ν)
    (S := fun a s ω ↦ (F a (fun i ↦ ω i a) s).toReal / 2) (g := g) h_indep
    (fun a s ↦ ((hFm a s).comp (by fun_prop)).ennreal_toReal.div_const 2) hg hS hx
  -- outside a null set the statistics are finite, and the event is that of the real statistics
  have h_top : streamMeasure ν {ω | ∃ a, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞} = 0 := by
    rw [Set.ofPred_exists]
    exact measure_iUnion_null fun a ↦ streamMeasure_exists_mul_rateFunction_eq_top (hν a)
  refine le_trans (measure_mono fun ω hω ↦ ?_) ((measure_union_le _ _).trans
    ((add_le_add h_real h_top.le).trans_eq (add_zero _)))
  obtain ⟨s, hs⟩ := hω
  by_cases hω : ∃ a, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞
  · exact Or.inr hω
  push Not at hω
  refine Or.inl ⟨s, ?_⟩
  have h_sum : ∑ a, F a (fun i ↦ ω i a) (s a) ≠ ∞ := ENNReal.sum_ne_top.2 fun a _ ↦ hω a (s a)
  have h := (ENNReal.ofReal_le_iff_le_toReal h_sum).1 hs
  rw [ENNReal.toReal_sum fun a _ ↦ hω a (s a)] at h
  simp only [← Finset.sum_div]
  linarith

/-! ### Runs of an algorithm -/

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {x : ℝ}

/-- **Peeled time-uniform deviations of the empirical means along a run, measured by the rate
functions.** In a run of any algorithm against `Environment.bandit ν`, if the rewards of each arm
`a` are integrable, with rate function `I_a`, then for `η > 0` and `x ≥ K`, with `K` the number of
arms, the probability that at some round `t`, the pull counts `N_a(t)` and the empirical means
`μ̂_a(t)` satisfy `2 (K (η log₂ t + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a, N_a(t) I_a(μ̂_a(t))`,
with `log₂ t = Nat.log 2 t`, is at most `(x / K) ^ K exp (K - x)`. -/
lemma measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a))
    {η : ℝ} (hη : 0 < η) (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (2 * (Fintype.card α *
        (η * Nat.log 2 t + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    ((measure_exists_pullCount_sumRewards_pi_le h fun s y ↦
      ENNReal.ofReal (2 * (Fintype.card α *
        (η * Nat.log 2 (∑ a, s a) + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a, s a * rateFunction id (ν a) (y a / s a)).trans
      (streamMeasure_exists_two_mul_card_mul_add_le_sum_mul_rateFunction_le hν hη hx))
  obtain ⟨t, ht⟩ := hω
  exact ⟨t, by simpa only [sum_pullCount, empMean] using ht⟩

end LMLExplore
