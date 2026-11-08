/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm

/-!
# The optimal allocation of best arm identification from a scalar equation

For best arm identification with arms in an exponential family with divergence `d`, at a vector
of means `μ` of the family with unique best arm `a`, and with at least one other arm, an allocation
`w` of the simplex is the optimal allocation `w*(μ, ¬a)` if and only if `w a > 0`, the costs
`w a d(μ a, m_b) + w b d(μ b, m_b)` of all the pairs `(a, b)`, `b ≠ a`, are equal, and
`∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where `m_b = (w a μ a + w b μ b) / (w a + w b)` is the
mean of `μ a` and `μ b` weighted by `w` [GK16, Theorem 5]. Written with `x = w / w a`, this is the
scalar equation `F(y) = 1` of [GK16, Theorem 5], for the common value `y` of the costs
`d(μ a, m_b) + x b d(μ b, m_b)`.

Both directions rest on the variational form of the cost of a pair: it is the minimum over the
means `z` of `w a d(μ a, z) + w b d(μ b, z)`, attained at `z = m_b`. So it lies below the linear
function `v ↦ v a d(μ a, m_b) + v b d(μ b, m_b)` of the allocation `v`, with equality at `w`.

* If `w` satisfies the equation and equalizes the costs at the value `D`, then for every
  allocation `v`, a combination of these linear bounds with the weights `1 / d(μ b, m_b)` is
  `v a ∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) + ∑_{b ≠ a} v b = 1`, which is also its value
  `D ∑_{b ≠ a} 1 / d(μ b, m_b)` at `w`. So some pair costs at most `D` at `v`, and `w` is optimal.
* At the optimal allocation, which has positive entries, if the sum `F` differs from `1`, the
  direction `u` with `u a = (∑_{b ≠ a} 1 / d(μ b, m_b)) / (F - 1)` and
  `u a d(μ a, m_b) + u b d(μ b, m_b) = 1` for every `b ≠ a` keeps the sum of the weights. Along it
  the cost of every pair increases, since the cost at `w + t u` exceeds the cost at `w` by at least
  `t (u a d(μ a, m'_b) + u b d(μ b, m'_b))`, for the weighted mean `m'_b` at `w + t u`, which tends
  to `m_b` as `t → 0`. This contradicts the optimality of `w`.

The proof needs no derivative of the divergence, and no inverse of the costs of the pairs, which
the paper uses to reduce the optimization to the scalar equation in `y`.

## Main statements

* `LMLExplore.Identification.sum_div_eq_one_of_mem_optAlloc_baiTask_restrict`: the optimal
  allocation solves the scalar equation [GK16, Theorem 5].
* `LMLExplore.Identification.mem_optAlloc_baiTask_restrict_of_sum_div_eq_one`: an allocation that
  equalizes the costs of the pairs and solves the scalar equation is optimal [GK16, Theorem 5].
* `LMLExplore.Identification.mem_optAlloc_baiTask_restrict_iff`: the characterization of the
  optimal allocation by the scalar equation [GK16, Theorem 5].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2, Theorem 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Finset

open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ}

/-- For nonnegative weights `w₁, w₂`, the cost of moving two means `μ₁, μ₂` of the family to their
weighted mean is at most `w₁ d(μ₁, z) + w₂ d(μ₂, z)` for every mean `z` of the family, whatever the
order of `μ₁` and `μ₂`: it is the minimum of these weighted divergences, so that it is a minimum
of functions linear in the weights. -/
lemma expFamilyPairCost_le_of_mem_expFamilyMeans {μ₁ μ₂ w₁ w₂ z : ℝ}
    (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hz : z ∈ ρ.expFamilyMeans T) :
    ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ ≤
      w₁ * ρ.expFamilyDiv T μ₁ z + w₂ * ρ.expFamilyDiv T μ₂ z := by
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with hW | hW
  · obtain ⟨rfl, rfl⟩ : w₁ = 0 ∧ w₂ = 0 := ⟨by linarith, by linarith⟩
    rw [expFamilyPairCost_eq_zero (Or.inl rfl)]
    simp
  rw [expFamilyPairCost_def]
  exact mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq hw₁ hw₂ (by field_simp)
    (div_mem_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW) hz

/-- For means `μ, μ₁, μ₂` of the family, the divergence `d(μ, m)` from `μ` to the weighted mean
`m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)` is continuous in the weights `(w₁, w₂)` at every pair of
nonnegative weights with `w₁ + w₂ > 0`. -/
lemma continuousAt_expFamilyDiv_div (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {μ μ₁ μ₂ w₁ w₂ : ℝ}
    (hμ : μ ∈ ρ.expFamilyMeans T) (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hW : 0 < w₁ + w₂) :
    ContinuousAt (fun p : ℝ × ℝ ↦ ρ.expFamilyDiv T μ ((p.1 * μ₁ + p.2 * μ₂) / (p.1 + p.2)))
      (w₁, w₂) := by
  have hm := div_mem_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW
  have hd : ContinuousAt (fun q : ℝ × ℝ ↦ ρ.expFamilyDiv T q.1 q.2)
      (μ, (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) :=
    (continuousOn_expFamilyDiv hT).continuousAt
      (prod_mem_nhds (expFamilyMeans_mem_nhds hT hμ) (expFamilyMeans_mem_nhds hT hm))
  have hf : ContinuousAt (fun p : ℝ × ℝ ↦ (μ, (p.1 * μ₁ + p.2 * μ₂) / (p.1 + p.2))) (w₁, w₂) := by
    fun_prop (disch := exact hW.ne')
  exact hd.comp_of_eq hf rfl

end MeasureTheory.Measure

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  {m𝓨 : MeasurableSpace 𝓨} (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]
  {ρ : Measure 𝓨} {T : 𝓨 → ℝ} {μ w : α → ℝ} {a : α}

omit [Fintype α] [DecidableEq α] in
/-- For an allocation `w` with `w a > 0` and an arm `b` with `μ b < μ a`, the mean
`m_b = (w a μ a + w b μ b) / (w a + w b)` differs from `μ b`, so that `d(μ b, m_b) > 0`. -/
private lemma expFamilyDiv_div_pos (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) {b : α}
    (hb : μ b < μ a) (hwa : 0 < w a) (hwb : 0 ≤ w b) :
    0 < ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) := by
  have hW : 0 < w a + w b := add_pos_of_pos_of_nonneg hwa hwb
  refine expFamilyDiv_pos (hμ b) (div_mem_expFamilyMeans (hμ a) (hμ b) hwa.le hwb hW) ?_
  rw [Ne, eq_div_iff hW.ne']
  intro h
  exact mul_ne_zero hwa.ne' (sub_ne_zero.2 hb.ne') (by linear_combination -h)

/-- **The optimal allocation solves the scalar equation** [GK16, Theorem 5]. For arms in an
exponential family with divergence `d` (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`),
a vector of means `μ` of the family with unique best arm `a` and at least one other arm, the optimal
allocation `w` satisfies `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`. -/
lemma sum_div_eq_one_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hb : ∃ b, b ≠ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a) :
    ∑ b ∈ univ.erase a, ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
      ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1 := by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨hws, hwD⟩ := (IdentTask.mem_optAlloc_iff _).1 hw
  obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hws
  have hpos := pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw
  obtain ⟨b₀, hb₀⟩ := hb
  have hmem {b : α} : b ∈ univ.erase a ↔ b ≠ a := by simp
  have hne : (univ.erase a).Nonempty := ⟨b₀, hmem.2 hb₀⟩
  -- The divergences `A b = d(μ a, m_b)` and `B b = d(μ b, m_b) > 0` at `w`.
  set A : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b))
    with hA_def
  set B : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))
    with hB_def
  have hB {b : α} (hba : b ≠ a) : 0 < B b :=
    expFamilyDiv_div_pos hμ (ha b hba) (hpos a) (hw0 b)
  set F := ∑ b ∈ univ.erase a, A b / B b
  set S := ∑ b ∈ univ.erase a, 1 / B b
  have hS : 0 < S := sum_pos (fun b hb ↦ one_div_pos.2 (hB (hmem.1 hb))) hne
  by_contra hF
  have hF1 : F - 1 ≠ 0 := sub_ne_zero.2 hF
  -- The direction `u`, which keeps the sum of the weights and increases every pair to first order.
  set u : α → ℝ := fun c ↦ if c = a then S / (F - 1) else (1 - A c * (S / (F - 1))) / B c
    with hu_def
  have hua : u a = S / (F - 1) := by simp [hu_def]
  have hu_b {b : α} (hba : b ≠ a) : u a * A b + u b * B b = 1 := by
    rw [hua]
    simp only [hu_def, hba, ↓reduceIte]
    field_simp [(hB hba).ne']
    ring
  have hu_sum : ∑ c, u c = 0 := by
    rw [← add_sum_erase _ _ (mem_univ a), hua]
    have h_erase : ∑ c ∈ univ.erase a, u c =
        ∑ c ∈ univ.erase a, (1 / B c - S / (F - 1) * (A c / B c)) := by
      refine sum_congr rfl fun c hc ↦ ?_
      have hca := hmem.1 hc
      simp only [hu_def, hca, ↓reduceIte]
      field_simp [(hB hca).ne']
    rw [h_erase, sum_sub_distrib, ← mul_sum]
    change S / (F - 1) + (S - S / (F - 1) * F) = 0
    field_simp
    ring
  -- The allocations `w + t u`.
  set v : ℝ → α → ℝ := fun t c ↦ w c + t * u c with hv_def
  have hv_cont (c : α) : ContinuousAt (fun t ↦ v t c) 0 := by fun_prop
  -- The cost of the pair `(a, b)` at `w + t u` exceeds its cost at `w` by at least
  -- `t (u a d(μ a, m'_b) + u b d(μ b, m'_b))`, whose second factor tends to `1`.
  set G : α → ℝ → ℝ := fun b t ↦
    u a * ρ.expFamilyDiv T (μ a) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
      u b * ρ.expFamilyDiv T (μ b) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) with hG_def
  have hG_cont {b : α} (hba : b ≠ a) : ContinuousAt (G b) 0 := by
    have hW : 0 < w a + w b := add_pos_of_pos_of_nonneg (hpos a) (hw0 b)
    have hp : ContinuousAt (fun t ↦ (v t a, v t b)) 0 := (hv_cont a).prodMk (hv_cont b)
    have hp0 : (v 0 a, v 0 b) = (w a, w b) := by simp [hv_def]
    exact (continuousAt_const.mul ((continuousAt_expFamilyDiv_div hT (hμ a) (hμ a) (hμ b)
        (hw0 a) (hw0 b) hW).comp_of_eq hp hp0)).add
      (continuousAt_const.mul ((continuousAt_expFamilyDiv_div hT (hμ b) (hμ a) (hμ b)
        (hw0 a) (hw0 b) hW).comp_of_eq hp hp0))
  have hG0 {b : α} (hba : b ≠ a) : G b 0 = 1 := by
    simp only [hG_def, hv_def, zero_mul, add_zero]
    exact hu_b hba
  have h_ev : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ c, 0 < v t c) ∧ ∀ b ∈ univ.erase a, 0 < G b t := by
    refine (eventually_all.2 fun c ↦ (hv_cont c).eventually (lt_mem_nhds ?_)).and
      ((eventually_all_finset _).2 fun b hb ↦
        (hG_cont (hmem.1 hb)).eventually (lt_mem_nhds ?_))
    · simpa [hv_def] using hpos c
    · rw [hG0 (hmem.1 hb)]
      exact one_pos
  obtain ⟨t, ⟨hv_pos, hG_pos⟩, ht⟩ :=
    ((h_ev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  rw [Set.mem_Ioi] at ht
  have hv : v t ∈ simplex α := by
    refine mem_simplex_iff.2 ⟨fun c ↦ (hv_pos c).le, ?_⟩
    simp only [hv_def, sum_add_distrib, ← mul_sum, hu_sum, mul_zero, add_zero, hw1]
  -- Every pair costs more at `w + t u` than at `w`.
  have h_lt {b : α} (hba : b ≠ a) :
      ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) <
        ρ.expFamilyPairCost T (μ a) (μ b) (v t a) (v t b) := by
    have hW : 0 < v t a + v t b := add_pos (hv_pos a) (hv_pos b)
    have h_le := expFamilyPairCost_le_of_mem_expFamilyMeans (hμ a) (hμ b) (hw0 a) (hw0 b)
      (div_mem_expFamilyMeans (hμ a) (hμ b) (hv_pos a).le (hv_pos b).le hW)
    have h_eq : w a * ρ.expFamilyDiv T (μ a) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
        w b * ρ.expFamilyDiv T (μ b) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
          t * G b t = ρ.expFamilyPairCost T (μ a) (μ b) (v t a) (v t b) := by
      rw [expFamilyPairCost_def]
      simp only [hG_def, hv_def]
      ring
    linarith [mul_pos ht (hG_pos b (hmem.2 hba))]
  -- So the cost of the alternatives is larger at `w + t u`, contradicting the optimality of `w`.
  have h_filter : univ.filter (· ≠ a) = univ.erase a := filter_ne' univ a
  have h_top : task.altCost μ w a < ∞ := by
    rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0]
    exact (Finset.inf_le (h_filter ▸ hmem.2 hb₀)).trans_lt ENNReal.ofReal_lt_top
  have h_cost : task.altCost μ w a < task.altCost μ (v t) a := by
    rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' fun c ↦ (hv_pos c).le,
      Finset.lt_inf_iff h_top]
    intro b hb
    have hba := (mem_filter.1 hb).2
    rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0]
    refine (Finset.inf_le hb).trans_lt ((ENNReal.ofReal_lt_ofReal_iff ?_).2 (h_lt hba))
    exact (expFamilyPairCost_nonneg (hμ a) (hμ b) (hw0 a) (hw0 b)).trans_lt (h_lt hba)
  exact (task.altCost_le_answerValue hv).not_gt (hwD ▸ h_cost)

/-- **An allocation solving the scalar equation is optimal** [GK16, Theorem 5]. For arms in an
exponential family with divergence `d` (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`)
and a vector of means `μ` of the family with unique best arm `a`, an allocation `w` of the simplex
with `w a > 0` that equalizes the costs `w a d(μ a, m_b) + w b d(μ b, m_b)` of the pairs `(a, b)`,
`b ≠ a`, and satisfies `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`, is an optimal allocation. -/
lemma mem_optAlloc_baiTask_restrict_of_sum_div_eq_one (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hw : w ∈ simplex α) (hwa : 0 < w a)
    (h_eq : ∀ b ≠ a, ∀ c ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) =
      ρ.expFamilyPairCost T (μ a) (μ c) (w a) (w c))
    (h_sum : ∑ b ∈ univ.erase a,
      ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
        ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1) :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a := by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hw
  have hmem {b : α} : b ∈ univ.erase a ↔ b ≠ a := by simp
  have h_filter : univ.filter (· ≠ a) = univ.erase a := filter_ne' univ a
  -- The sum is not empty, since it equals `1`.
  have hne : (univ.erase a).Nonempty := nonempty_of_sum_ne_zero (h_sum ▸ one_ne_zero)
  obtain ⟨b₀, hb₀⟩ := hne
  set A : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b))
    with hA_def
  set B : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))
    with hB_def
  have hB {b : α} (hba : b ≠ a) : 0 < B b := expFamilyDiv_div_pos hμ (ha b hba) hwa (hw0 b)
  -- For every allocation `x`, the combination of the linear bounds with the weights `1 / B b` is
  -- `x a ∑_{b ≠ a} A b / B b + ∑_{b ≠ a} x b = 1`.
  have h_comb (x : α → ℝ) (hx : ∑ c, x c = 1) :
      ∑ b ∈ univ.erase a, (x a * A b + x b * B b) / B b = 1 := by
    have h : ∀ b ∈ univ.erase a, (x a * A b + x b * B b) / B b = x a * (A b / B b) + x b :=
      fun b hb ↦ by field_simp [(hB (hmem.1 hb)).ne']
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, h_sum, mul_one,
      sum_erase_eq_sub (mem_univ a), hx]
    ring
  -- The common value `D` of the costs of the pairs at `w`.
  set D := ρ.expFamilyPairCost T (μ a) (μ b₀) (w a) (w b₀)
  have hD {b : α} (hba : b ≠ a) : ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) = D :=
    h_eq b hba b₀ (hmem.1 hb₀)
  have hD_sum : ∑ b ∈ univ.erase a, D / B b = 1 := by
    rw [← h_comb w hw1]
    refine sum_congr rfl fun b hb ↦ ?_
    rw [← hD (hmem.1 hb), expFamilyPairCost_def]
  rw [IdentTask.mem_optAlloc_iff_isMaxOn]
  refine ⟨hw, isMaxOn_iff.2 fun v hv ↦ ?_⟩
  obtain ⟨hv0, hv1⟩ := mem_simplex_iff.1 hv
  -- Some pair costs at most `D` at `v`, otherwise the combination of the linear bounds at `v`
  -- would exceed its value `1` at `w`.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (v a) (v b) ≤ D := by
    by_contra! h
    have h_lt : ∑ b ∈ univ.erase a, D / B b <
        ∑ b ∈ univ.erase a, (v a * A b + v b * B b) / B b := by
      refine sum_lt_sum_of_nonempty ⟨b₀, hb₀⟩ fun b hb ↦ ?_
      have hba := hmem.1 hb
      refine div_lt_div_of_pos_right ((h b hba).trans_le ?_) (hB hba)
      exact expFamilyPairCost_le_of_mem_expFamilyMeans (hμ a) (hμ b) (hv0 a) (hv0 b)
        (div_mem_expFamilyMeans (hμ a) (hμ b) (hw0 a) (hw0 b)
          (add_pos_of_pos_of_nonneg hwa (hw0 b)))
    rw [hD_sum, h_comb v hv1] at h_lt
    exact h_lt.false
  rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hv0,
    altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0]
  refine (Finset.inf_le (h_filter ▸ hmem.2 hba)).trans (Finset.le_inf fun c hc ↦ ?_)
  rw [hD (mem_filter.1 hc).2]
  exact ENNReal.ofReal_le_ofReal hb

/-- **The optimal allocation of best arm identification from a scalar equation**
[GK16, Theorem 5]. For arms in an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the family with
unique best arm `a` and at least one other arm, an allocation `w` is optimal if and only if it is
in the simplex, `w a > 0`, the costs `w a d(μ a, m_b) + w b d(μ b, m_b)` of the pairs `(a, b)`,
`b ≠ a`, are equal, and `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`. -/
theorem mem_optAlloc_baiTask_restrict_iff (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hb : ∃ b, b ≠ a) :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a ↔
      w ∈ simplex α ∧ 0 < w a ∧
        (∀ b ≠ a, ∀ c ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) =
          ρ.expFamilyPairCost T (μ a) (μ c) (w a) (w c)) ∧
        ∑ b ∈ univ.erase a,
          ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
            ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1 := by
  refine ⟨fun hw ↦ ⟨((IdentTask.mem_optAlloc_iff _).1 hw).1,
    pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw a, fun b hba c hca ↦ ?_,
    sum_div_eq_one_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hb hw⟩,
    fun ⟨hws, hwa, h_eq, h_sum⟩ ↦
      mem_optAlloc_baiTask_restrict_of_sum_div_eq_one ν hT hμ hν ha hws hwa h_eq h_sum⟩
  have hw0 := (mem_simplex_iff.1 ((IdentTask.mem_optAlloc_iff _).1 hw).1).1
  refine (ENNReal.ofReal_eq_ofReal_iff (expFamilyPairCost_nonneg (hμ a) (hμ b) (hw0 a) (hw0 b))
    (expFamilyPairCost_nonneg (hμ a) (hμ c) (hw0 a) (hw0 c))).1 ?_
  rw [← answerValue_baiTask_restrict_eq_of_mem_optAlloc ν hT hμ hν ha hw hba,
    answerValue_baiTask_restrict_eq_of_mem_optAlloc ν hT hμ hν ha hw hca]

end LMLExplore.Identification
