/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Garivier2016Optimal.ForLMLExplore.Identification.KTThreshold
public import LMLExplore.Bandits.Instances
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.Identification.Task.BestArm

/-!
# The informational threshold for Bernoulli arms [GK16, Theorem 10]

For best arm identification with Bernoulli arms, whatever the sampling rule and the recommendation
rule, Chernoff's stopping rule with the thresholds `β(t, δ) = log (2 t (K - 1) / δ)` stops with an
arm that is not the best with probability at most `δ`. The proof [GK16, Appendix C.1] bounds the
maximum likelihood by the Krichevsky–Trofimov mixture [GK16, Lemma 11].

The statistic is the plug-in statistic of the empirical means, `∑ a, N_a kl(μ̂_a, λ_a)` minimized
over the alternatives, which for Bernoulli arms is Chernoff's statistic `Z(t)` of
[GK16, Section 3.2] for all empirical means in `[0, 1]`. The Bernoulli bandit with means `μ` is
`bernoulliBandit` of the means clamped to `[0, 1]`, which changes nothing on the models of the
task, whose means are in `(0, 1)`.

The statement is the specialization of
`LMLExplore.Identification.measureReal_histOutputMeasure_glrt_baiTask_bernoulli_le`, which holds
for every `δ > 0` and all thresholds at least `log (2 t (K - 1) / δ)`
(`ForLMLExplore/Identification/KTThreshold.lean`). The thresholds and the Krichevsky–Trofimov
mixture are a target of LMLRoadmaps (Identification, Layer 4, item 2).

## Main statements

* `Garivier2016Optimal.measureReal_glrt_bernoulli_le`: [GK16, Theorem 10].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning LMLExplore LMLExplore.Identification Real

open scoped ENNReal NNReal unitInterval

namespace Garivier2016Optimal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The informational threshold** [GK16, Theorem 10]. For Bernoulli arms and every
`δ ∈ (0, 1)`, whatever the sampling rule `alg` and the recommendation rule `rec`, Chernoff's
stopping rule with the thresholds `log (2 t (K - 1) / δ)` stops with an arm that is not the best
with probability at most `δ`, on every vector of means in `(0, 1)` with a unique best arm.

The proof uses only `δ > 0`, not `δ < 1`. The instance `[Nonempty α]` of the statement is not
used. The binders of the statement are those of its comparator challenge, in the same order. -/
@[nolint unusedArguments]
theorem measureReal_glrt_bernoulli_le [Nonempty α] {mα : MeasurableSpace α}
    [MeasurableSingletonClass α] {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1)
    (alg : Algorithm Unit α ℝ) (rec : (n : ℕ) → Hist Unit α ℝ n → α)
    (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h : Hist Unit α ℝ n |
      ENNReal.ofReal (log (2 * n * (Fintype.card α - 1) / δ)) <
        ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glr
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') n h (rec n h)})
    {μ : α → ℝ}
    (hμ : μ ∈ ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
      id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).M) :
    (histOutputMeasure
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg
          (fun n _ ↦ ENNReal.ofReal (log (2 * n * (Fintype.card α - 1) / δ))) rec hrec hstop)
        (Environment.bandit
          (Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)))).real
      {q | q.1 ∈ (((baiTask
            (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg
          (fun n _ ↦ ENNReal.ofReal (log (2 * n * (Fintype.card α - 1) / δ))) rec hrec
          hstop).stopSet ∧
        q.2 ∉ ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).correct μ} ≤ δ :=
  measureReal_histOutputMeasure_glrt_baiTask_bernoulli_le hδ.1 alg _ (fun _ _ ↦ le_rfl) rec hrec
    hstop hμ

end Garivier2016Optimal
