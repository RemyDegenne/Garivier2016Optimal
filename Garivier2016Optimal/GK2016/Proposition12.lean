/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.Identification.DeviationalThreshold
public import Garivier2016Optimal.GK2016.Basic

/-!
# The deviational threshold [GK16, Proposition 12]

For best arm identification on the vectors of means of an exponential family, every exponent
`p > 1` and every risk `δ ∈ (0, 1)`, there is a constant `C`, depending on `p`, `δ` and the number
of arms only, such that whatever the sampling rule and the recommendation rule, Chernoff's stopping
rule with the thresholds `β(t, δ) = log (C t ^ p / δ)` stops with an arm that is not the best with
probability at most `δ`. The paper claims a `C` that does not depend on `δ`, which its proof does
not give (`notes/paper-errata.md`, E2).

The statistic is the generalized likelihood ratio evidence of the family, Chernoff's `Z(t)` of
[GK16, Section 3.2]. LMLExplore has the thresholds `K log (2 t (t + 1)) + x_δ` of [LS, Lemma 33.7]
for the same statistic (`IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le`), which
grow like `2 K log t`. The proof here is the specialization of
`IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le`
(`ForLMLExplore/Identification/DeviationalThreshold.lean`), which peels the numbers of pulls of each
arm along dyadic slices instead of a union bound, and holds for every task, for arms dominated by
any exponential families and for every `p > 0`, with the constant
`C = δ exp (c_{p,K} + 2 x_δ)`, `c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and `x_δ`
the level of LMLExplore's `Identification/GLR.lean`. The arms of the paper are dominated by the
members of the family with their means (`Garivier2016Optimal.mgfDominatedOn_expFamily`).

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

/-- **The deviational threshold** [GK16, Proposition 12]. For every exponent `p > 1` and every
`δ ∈ (0, 1)` there is a constant `C > 0` such that, for every exponential family `(ρ, id)`, whatever
the sampling rule `alg` and the recommendation rule `rec`, Chernoff's stopping rule with the
thresholds `log (C t ^ p / δ)` stops with an arm that is not the best with probability at most
`δ`, on every vector of means of the family with a unique best arm. The constant depends on `δ`,
unlike the paper's `C(α, K)` (`notes/paper-errata.md`, E2): it is
`C = δ exp (c_{p,K} + 2 x_δ)`, with `c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and
the level `x_δ = log (1 / δ) + 2 K (1 + log (1 + log (1 / δ)))`. The proof uses only `0 < p`,
and not the hypothesis that `id` is not `ρ`-almost everywhere constant. -/
theorem exists_measureReal_glrt_expFamilyEvidence_le {p : ℝ} (hp : 1 < p) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (ρ : Measure ℝ),
      (∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c) →
      (∀ μ a, ν μ a = ρ.expFamily id (ρ.natParam id (μ a))) →
      ∀ (alg : Algorithm Unit α ℝ) (rec : (n : ℕ) → Hist Unit α ℝ n → α)
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
  refine ⟨δ * exp (2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) +
        2 * unionBoundLevel (Fintype.card α) δ), mul_pos hδ.1 (exp_pos _),
    fun ν _ ρ _ hν alg rec hrec hstop μ hμ ↦ ?_⟩
  have hμS : ∀ a, μ a ∈ ρ.expFamilyMeans id := by
    rw [IdentTask.M_restrict] at hμ
    exact hμ.2
  have h := IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le
    (ρ := fun _ ↦ ρ) (T := fun _ ↦ id) (alg := alg) rec hrec (zero_lt_one.trans hp) hδ.1 hδ.2.le
    le_rfl hstop
    hμ hμS (mgfDominatedOn_expFamily ν ρ hν) (Set.toFinite _).measurableSet
  simpa only [IdentTask.ν_restrict, ν_baiTask] using h

end Garivier2016Optimal
