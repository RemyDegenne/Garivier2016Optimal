/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.InformationTheory.KrichevskyTrofimov
public import Garivier2016Optimal.ForLMLExplore.SequentialLearning.LikelihoodRatio
public import LMLExplore.Bandits.Instances
public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# Pairwise deviations of Bernoulli arms through the Krichevsky–Trofimov mixture

Along a run of any algorithm against a Bernoulli bandit with means `p` in `(0, 1)`, for two arms
`a ≠ b` and every `x > 0`,
`P(∃ n, log (2 n x) < N_a(n) d(μ̂_a(n), p_a) + N_b(n) d(μ̂_b(n), p_b)) ≤ 1 / x`,
where `N_c(n)` is the number of pulls of the arm `c` and `μ̂_c(n)` its empirical mean before round
`n`, and `d` is the binary relative entropy. This is the deviation inequality behind the
informational threshold of [GK16, Theorem 10].

The proof [GK16, Appendix C.1] mixes the likelihood ratios of the Bernoulli bandits whose means on
the arms `a` and `b` are `u` and `v`, against the true bandit, over the prior
`Beta(1/2, 1/2) ⊗ Beta(1/2, 1/2)` of `(u, v)`. The mixture is the product of the
Krichevsky–Trofimov likelihood ratios of the two arms, a nonnegative supermartingale with initial
value `1`, so Ville's inequality bounds the probability that it ever reaches `x` by `1 / x`. The
Krichevsky–Trofimov bound [GK16, Lemma 11] bounds `N_c d(μ̂_c, p_c)` by the logarithm of `2 √N_c`
times the likelihood ratio of arm `c`, and `2 √N_a ⋅ 2 √N_b ≤ 2 (N_a + N_b) ≤ 2 n`.

## Main statements

* `LMLExplore.sum_ite_mul_add_one_sub_mul`: the log-likelihood ratio of the observations of an
  arm, `∑_{k < n, A_k = a} (Y_k α + (1 - Y_k) β) = S_a(n) α + (N_a(n) - S_a(n)) β`.
* `LMLExplore.measure_exists_log_two_mul_mul_lt_klBer_le`: the pairwise deviation inequality.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real unitInterval

open scoped ENNReal

namespace LMLExplore

variable {α Ω : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- The sum over the pulls of an arm `a` of a function `Y α + (1 - Y) β` of the observation `Y`,
which is affine in the observation, is `S_a(n) α + (N_a(n) - S_a(n)) β`, where `S_a(n)` is the sum
of the observations of `a` and `N_a(n)` its number of pulls. For Bernoulli observations and
`α = log (q / p)`, `β = log ((1 - q) / (1 - p))`, it is the log-likelihood ratio of the
observations of `a` under the mean `q` against the mean `p`. -/
lemma sum_ite_mul_add_one_sub_mul (a : α) (n : ℕ) (ω : Ω) (x y : ℝ) :
    ∑ k ∈ range n, (if A k ω = a then Y k ω * x + (1 - Y k ω) * y else 0) =
      sumRewards A Y a n ω * x + (pullCount A a n ω - sumRewards A Y a n ω) * y := by
  classical
  have h : ∀ k ∈ range n, (if A k ω = a then Y k ω * x + (1 - Y k ω) * y else 0) =
      (if A k ω = a then Y k ω else 0) * x +
        ((if A k ω = a then (1 : ℝ) else 0) - (if A k ω = a then Y k ω else 0)) * y := by
    intro k _
    split_ifs <;> ring
  rw [sum_congr rfl h, sum_add_distrib, ← sum_mul, ← sum_mul, sum_sub_distrib, sumRewards,
    pullCount, natCast_card_filter]

/-- With observations in `{0, 1}`, the sum of the observations of an arm is a natural number, at
most its number of pulls. -/
private lemma exists_sumRewards_eq_natCast {ω : Ω} (hω : ∀ k, Y k ω ∈ ({0, 1} : Set ℝ)) (a : α)
    (n : ℕ) : ∃ j ≤ pullCount A a n ω, sumRewards A Y a n ω = j := by
  classical
  refine ⟨#(filter (fun k ↦ A k ω = a ∧ Y k ω = 1) (range n)), ?_, ?_⟩
  · exact card_le_card fun k hk ↦ by
      simp only [mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.1⟩
  · rw [sumRewards, natCast_card_filter]
    refine sum_congr rfl fun k _ ↦ ?_
    have hk01 := hω k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk01
    rcases hk01 with h | h <;> by_cases hk : A k ω = a <;> simp [hk, h]

/-- The integral against `Beta(1/2, 1/2)` of the likelihood ratio `(u / p) ^ j ((1 - u) / (1 - p))
^ m`, written as the exponential of the log-likelihood ratio on `(0, 1)`, is the
Krichevsky–Trofimov likelihood ratio `kt(j, m) / (p ^ j (1 - p) ^ m)`. -/
private lemma integral_exp_ite_betaMeasure {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (j m : ℕ) :
    ∫ u, exp (if u ∈ Set.Ioo 0 1 then j * log (u / p) + m * log ((1 - u) / (1 - p)) else 0)
        ∂betaMeasure (1 / 2) (1 / 2) =
      (∫ u, u ^ j * (1 - u) ^ m ∂betaMeasure (1 / 2) (1 / 2)) / (p ^ j * (1 - p) ^ m) := by
  have hp1 : 0 < 1 - p := sub_pos.2 hp.2
  rw [← integral_div]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure (1 / 2) (1 / 2)] with u hu
  have hu1 : 0 < 1 - u := sub_pos.2 hu.2
  rw [ite_eq_left hu, exp_add, ← log_pow, ← log_pow, exp_log (pow_pos (div_pos hu.1 hp.1) _),
    exp_log (pow_pos (div_pos hu1 hp1) _), div_pow, div_pow]
  field_simp

/-- The Krichevsky–Trofimov integral is positive. -/
private lemma integral_pow_mul_one_sub_pow_betaMeasure_pos (j m : ℕ) :
    0 < ∫ u, u ^ j * (1 - u) ^ m ∂betaMeasure (1 / 2) (1 / 2) := by
  rw [integral_pow_mul_one_sub_pow_betaMeasure (by norm_num) (by norm_num)]
  exact div_pos (beta_pos (by positivity) (by positivity)) (beta_pos (by norm_num) (by norm_num))

/-- Per arm: `N d(j / N, p) ≤ log (w Λ)`, with `Λ` the Krichevsky–Trofimov likelihood ratio and
`w = 2 √N`, or `w = 1` for `N = 0`. -/
private lemma mul_klBerReal_le_log {p : ℝ} (hp : p ∈ Set.Ioo 0 1) {j N : ℕ} (hj : j ≤ N) :
    (N : ℝ) * klBerReal (j / N) p ≤
      log ((if N = 0 then 1 else 2 * √(N : ℝ)) *
        ((∫ u, u ^ j * (1 - u) ^ (N - j) ∂betaMeasure (1 / 2) (1 / 2)) /
          (p ^ j * (1 - p) ^ (N - j)))) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : j = 0 := by omega
    rw [integral_pow_mul_one_sub_pow_betaMeasure (by norm_num) (by norm_num)]
    have hB := (beta_pos (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)).ne'
    simp only [Nat.cast_zero, Nat.sub_self, add_zero]
    rw [div_self hB]
    simp
  rw [ite_eq_right hN.ne']
  exact mul_klBerReal_div_le_log_two_mul_sqrt_mul_integral_betaMeasure_div
    (k := j) (m := N - j) (n := N) (by omega) hN hp

/-- `w_a w_b ≤ 2 n` for the weights of `mul_klBerReal_le_log`, when `1 ≤ N_a + N_b ≤ n`. -/
private lemma ite_mul_ite_le {Na Nb n : ℕ} (h1 : 1 ≤ Na + Nb) (hn : Na + Nb ≤ n) :
    (if Na = 0 then 1 else 2 * √(Na : ℝ)) * (if Nb = 0 then 1 else 2 * √(Nb : ℝ)) ≤
      2 * n := by
  have hn' : ((Na : ℝ) + Nb) ≤ n := by exact_mod_cast hn
  have hsa := Real.sq_sqrt (Nat.cast_nonneg Na : (0 : ℝ) ≤ Na)
  have hsb := Real.sq_sqrt (Nat.cast_nonneg Nb : (0 : ℝ) ≤ Nb)
  have ha0 := Real.sqrt_nonneg (Na : ℝ)
  have hb0 := Real.sqrt_nonneg (Nb : ℝ)
  split_ifs with ha hb hb
  · omega
  · subst ha
    have hb1 : (1 : ℝ) ≤ Nb := by exact_mod_cast (by omega : 1 ≤ Nb)
    simp only [CharP.cast_eq_zero, zero_add] at hn'
    nlinarith
  · subst hb
    have ha1 : (1 : ℝ) ≤ Na := by exact_mod_cast (by omega : 1 ≤ Na)
    simp only [CharP.cast_eq_zero, add_zero] at hn'
    nlinarith
  · nlinarith [sq_nonneg (√(Na : ℝ) - √(Nb : ℝ))]

variable [Finite α] [MeasurableSingletonClass α] {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {p : α → I}

/-- **Pairwise deviations of Bernoulli arms** [GK16, proof of Theorem 10]. Along a run of any
algorithm against the Bernoulli bandit with means `p` in `(0, 1)`, for two arms `a ≠ b` and every
`x > 0`, the probability that at some round `n`
`log (2 n x) < N_a(n) d(μ̂_a(n), p_a) + N_b(n) d(μ̂_b(n), p_b)` is at most `1 / x`, where `N_c(n)`
is the number of pulls and `μ̂_c(n)` the empirical mean of the arm `c` before round `n`, and `d`
is the binary relative entropy. -/
theorem measure_exists_log_two_mul_mul_lt_klBer_le
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit (Bandits.bernoulliBandit p)) P)
    (hp : ∀ c, (p c : ℝ) ∈ Set.Ioo 0 1) {a b : α} (hab : a ≠ b) {x : ℝ} (hx : 0 < x) :
    P {ω | ∃ n : ℕ, ENNReal.ofReal (log (2 * n * x)) <
      (pullCount A a n ω : ℝ≥0∞) * klBer (empMean A Y a n ω) (p a) +
        (pullCount A b n ω : ℝ≥0∞) * klBer (empMean A Y b n ω) (p b)} ≤
      ENNReal.ofReal (1 / x) := by
  have := Fintype.ofFinite α
  have := isProbabilityMeasureBeta (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)
  -- the log-likelihood ratio of the bandit with means `u` and `v` on the arms `a` and `b`
  set G : ℝ → ℝ → ℝ → ℝ := fun q r y ↦
    if q ∈ Set.Ioo 0 1 then y * log (q / r) + (1 - y) * log ((1 - q) / (1 - r)) else 0 with hG
  set z : ℝ × ℝ → α → ℝ → ℝ := fun l c y ↦
    (if c = a then G l.1 (p a) y else 0) + (if c = b then G l.2 (p b) y else 0) with hz_def
  have hGm : ∀ r : ℝ, Measurable fun q : ℝ × ℝ ↦ G q.1 r q.2 := fun r ↦
    Measurable.ite (measurableSet_Ioo.preimage measurable_fst) (by fun_prop) measurable_const
  have hz : Measurable fun q : (ℝ × ℝ) × α × ℝ ↦ z q.1 q.2.1 q.2.2 := by
    refine Measurable.add ?_ ?_
    · refine Measurable.ite ((measurableSet_singleton a).preimage
        (measurable_fst.comp measurable_snd)) ?_ measurable_const
      exact (hGm (p a)).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
    · refine Measurable.ite ((measurableSet_singleton b).preimage
        (measurable_fst.comp measurable_snd)) ?_ measurable_const
      exact (hGm (p b)).comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  have hG1 : ∀ q (c : α), ∫⁻ y, ENNReal.ofReal (exp (G q (p c) y)) ∂Ber((1 : ℝ), 0, p c) = 1 := by
    intro q c
    by_cases hq : q ∈ Set.Ioo 0 1
    · simp only [hG, ite_eq_left hq]
      rw [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure,
        lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
      have h1 : 0 < 1 - (p c : ℝ) := sub_pos.2 (hp c).2
      have h2 : 0 < 1 - q := sub_pos.2 hq.2
      simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add]
      rw [exp_log (div_pos hq.1 (hp c).1), exp_log (div_pos h2 h1)]
      simp only [ENNReal.smul_def, smul_eq_mul]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ← ENNReal.ofReal_add (mul_nonneg (NNReal.coe_nonneg _) (div_pos hq.1 (hp c).1).le)
          (mul_nonneg (NNReal.coe_nonneg _) (div_pos h2 h1).le)]
      have h0 : (p c : ℝ) ≠ 0 := (hp c).1.ne'
      simp
      field_simp
      ring
    · simp only [hG, hq, ↓reduceIte]
      simp
  have hle : ∀ l c, ∫⁻ y, ENNReal.ofReal (exp (z l c y)) ∂(Bandits.bernoulliBandit p) c ≤ 1 := by
    intro l c
    rw [Bandits.bernoulliBandit_apply]
    by_cases hca : c = a
    · subst hca
      simp [hz_def, hab, hG1]
    · by_cases hcb : c = b
      · subst hcb
        simp [hz_def, hca, hG1]
      · simp [hz_def, hca, hcb]
  have hV := measure_exists_le_integral_exp_sum_le
    (ρ := (betaMeasure (1 / 2) (1 / 2)).prod (betaMeasure (1 / 2) (1 / 2))) h hz hle hx
  refine le_trans (measure_mono_ae ?_) hV
  have hgood : ∀ᵐ ω ∂P, ∀ k, Y k ω ∈ ({0, 1} : Set ℝ) := by
    refine h.ae_forall_feedback_mem_bandit (by measurability) fun c ↦ ?_
    rw [Bandits.bernoulliBandit_apply, bernoulliMeasure_def, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure ((ae_dirac_iff (by measurability)).2 (by simp)) _,
      Measure.ae_smul_measure ((ae_dirac_iff (by measurability)).2 (by simp)) _⟩
  filter_upwards [hgood] with ω hω hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  -- the numbers of ones
  obtain ⟨ja, hja, hSa⟩ := exists_sumRewards_eq_natCast hω a n
  obtain ⟨jb, hjb, hSb⟩ := exists_sumRewards_eq_natCast hω b n
  set Na := pullCount A a n ω with hNa
  set Nb := pullCount A b n ω with hNb
  -- the mixture is the product of the Krichevsky–Trofimov likelihood ratios
  set Λa := (∫ u, u ^ ja * (1 - u) ^ (Na - ja) ∂betaMeasure (1 / 2) (1 / 2)) /
    ((p a : ℝ) ^ ja * (1 - (p a : ℝ)) ^ (Na - ja)) with hΛa
  set Λb := (∫ u, u ^ jb * (1 - u) ^ (Nb - jb) ∂betaMeasure (1 / 2) (1 / 2)) /
    ((p b : ℝ) ^ jb * (1 - (p b : ℝ)) ^ (Nb - jb)) with hΛb
  have hsum : ∀ l : ℝ × ℝ, ∑ k ∈ range n, z l (A k ω) (Y k ω) =
      (if l.1 ∈ Set.Ioo 0 1 then (ja : ℝ) * log (l.1 / p a) +
          ((Na - ja : ℕ) : ℝ) * log ((1 - l.1) / (1 - p a)) else 0) +
        (if l.2 ∈ Set.Ioo 0 1 then (jb : ℝ) * log (l.2 / p b) +
          ((Nb - jb : ℕ) : ℝ) * log ((1 - l.2) / (1 - p b)) else 0) := by
    intro l
    simp only [hz_def, sum_add_distrib]
    congr 1
    · by_cases hl : l.1 ∈ Set.Ioo 0 1
      · simp only [hG, hl, ↓reduceIte, sum_ite_mul_add_one_sub_mul, hSa, Nat.cast_sub hja]
        rfl
      · simp only [hG, hl, ↓reduceIte, ite_self, sum_const_zero]
    · by_cases hl : l.2 ∈ Set.Ioo 0 1
      · simp only [hG, hl, ↓reduceIte, sum_ite_mul_add_one_sub_mul, hSb, Nat.cast_sub hjb]
        rfl
      · simp only [hG, hl, ↓reduceIte, ite_self, sum_const_zero]
  have hL : ∫ l, exp (∑ k ∈ range n, z l (A k ω) (Y k ω))
      ∂(betaMeasure (1 / 2) (1 / 2)).prod (betaMeasure (1 / 2) (1 / 2)) = Λa * Λb := by
    simp_rw [hsum, exp_add]
    rw [integral_prod_mul (fun u ↦ exp (if u ∈ Set.Ioo 0 1 then (ja : ℝ) * log (u / p a) +
          ((Na - ja : ℕ) : ℝ) * log ((1 - u) / (1 - p a)) else 0))
      (fun v ↦ exp (if v ∈ Set.Ioo 0 1 then (jb : ℝ) * log (v / p b) +
          ((Nb - jb : ℕ) : ℝ) * log ((1 - v) / (1 - p b)) else 0)),
      integral_exp_ite_betaMeasure (hp a), integral_exp_ite_betaMeasure (hp b)]
  rw [hL]
  -- the statistic in real form
  have hmean : ∀ {c : α} {j N : ℕ}, j ≤ N → empMean A Y c n ω = j / N →
      (N : ℝ≥0∞) * klBer (empMean A Y c n ω) (p c) =
        ENNReal.ofReal ((N : ℝ) * klBerReal (j / N) (p c)) := by
    intro c j N hj he
    have hjN : (j : ℝ) / N ∈ Set.Icc 0 1 := ⟨by positivity, div_le_one_of_le₀
      (by exact_mod_cast hj) (Nat.cast_nonneg N)⟩
    have hpc : (p c : ℝ) ∈ Set.Icc 0 1 := ⟨(hp c).1.le, (hp c).2.le⟩
    rw [he, klBer_eq_ofReal_klBerReal hjN hpc (klBer_ne_top (hp c)),
      ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
  have hTa_nonneg : 0 ≤ (Na : ℝ) * klBerReal (ja / Na) (p a) := by
    have hjN : (ja : ℝ) / Na ∈ Set.Icc 0 1 := ⟨by positivity, div_le_one_of_le₀
      (by exact_mod_cast hja) (Nat.cast_nonneg _)⟩
    exact mul_nonneg (Nat.cast_nonneg _) (klBerReal_nonneg hjN ⟨(hp a).1.le, (hp a).2.le⟩
      (klBer_ne_top (hp a)))
  have hTb_nonneg : 0 ≤ (Nb : ℝ) * klBerReal (jb / Nb) (p b) := by
    have hjN : (jb : ℝ) / Nb ∈ Set.Icc 0 1 := ⟨by positivity, div_le_one_of_le₀
      (by exact_mod_cast hjb) (Nat.cast_nonneg _)⟩
    exact mul_nonneg (Nat.cast_nonneg _) (klBerReal_nonneg hjN ⟨(hp b).1.le, (hp b).2.le⟩
      (klBer_ne_top (hp b)))
  rw [hmean hja (by rw [empMean, hSa]), hmean hjb (by rw [empMean, hSb]),
    ← ENNReal.ofReal_add hTa_nonneg hTb_nonneg, ENNReal.ofReal_lt_ofReal_iff'] at hn
  obtain ⟨hlt, hpos⟩ := hn
  -- at least one of the two arms was pulled
  have h1 : 1 ≤ Na + Nb := by
    by_contra h0
    obtain ⟨ha0, hb0⟩ : Na = 0 ∧ Nb = 0 := by omega
    rw [ha0, hb0] at hpos
    simp at hpos
  have hnab : Na + Nb ≤ n := by
    have h2 : ∑ c ∈ ({a, b} : Finset α), pullCount A c n ω ≤ ∑ c, pullCount A c n ω :=
      sum_le_sum_of_subset (subset_univ _)
    rwa [sum_pair hab, sum_pullCount] at h2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1.trans hnab
  have hΛa_pos : 0 < Λa := div_pos (integral_pow_mul_one_sub_pow_betaMeasure_pos _ _)
    (mul_pos (pow_pos (hp a).1 _) (pow_pos (sub_pos.2 (hp a).2) _))
  have hΛb_pos : 0 < Λb := div_pos (integral_pow_mul_one_sub_pow_betaMeasure_pos _ _)
    (mul_pos (pow_pos (hp b).1 _) (pow_pos (sub_pos.2 (hp b).2) _))
  have hwa : 0 < (if Na = 0 then (1 : ℝ) else 2 * √(Na : ℝ)) := by
    split_ifs with h0
    · exact one_pos
    · exact mul_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0))
  have hwb : 0 < (if Nb = 0 then (1 : ℝ) else 2 * √(Nb : ℝ)) := by
    split_ifs with h0
    · exact one_pos
    · exact mul_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0))
  have hTa := mul_klBerReal_le_log (hp a) hja
  have hTb := mul_klBerReal_le_log (hp b) hjb
  rw [← hΛa] at hTa
  rw [← hΛb] at hTb
  have hw := ite_mul_ite_le h1 hnab
  -- `log (2 n x) < log (w_a Λ_a) + log (w_b Λ_b) ≤ log (2 n Λ_a Λ_b)`
  have hlog : log (2 * n * x) < log (2 * n * (Λa * Λb)) := by
    calc log (2 * n * x) < _ := hlt
      _ ≤ _ := add_le_add hTa hTb
      _ = log ((if Na = 0 then (1 : ℝ) else 2 * √(Na : ℝ)) *
          (if Nb = 0 then (1 : ℝ) else 2 * √(Nb : ℝ)) * (Λa * Λb)) := by
        rw [← log_mul (mul_pos hwa hΛa_pos).ne' (mul_pos hwb hΛb_pos).ne']
        ring_nf
      _ ≤ _ := log_le_log (by positivity) (by gcongr)
  rw [log_lt_log_iff (by positivity) (by positivity)] at hlog
  have h2n : 0 < 2 * (n : ℝ) := by positivity
  nlinarith

end LMLExplore
