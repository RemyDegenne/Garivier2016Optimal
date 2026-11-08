# Phase 2: decisions

Decisions taken in the unattended rounds of `scripts/formalize.sh`, by date.

## 2026-11-08: the specializations of LMLExplore (Theorems 1 and 14, Remark 2, Proposition 6)

- **Area.** The headline results whose prerequisites LMLExplore already proves (PAPER_ROADMAP.md
  R1, R6, R12): Theorem 1, Remark 2, Proposition 6 parts 1 and 2, Theorem 14 with D-tracking and
  with C-tracking. They need no new mathematics, and they fix how the paper's setting (arms
  `ν μ a = ρ.expFamily id (ρ.natParam id (μ a))`) meets LMLExplore's hypotheses, which the other
  results will reuse.
- **The setting against LMLExplore's hypotheses.** LMLExplore's results on best arm
  identification assume `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` on the vectors of means of the family,
  and its Track-and-Stop bounds assume each arm `MGFDominatedOn` the member of the family with its
  mean. With the paper's arms, the first is `Measure.klDiv_expFamily_natParam` and the second is
  reflexivity. LMLExplore has no `MGFDominatedOn.refl`; the anonymous constructor is one line, so
  the paper's file uses it rather than adding a refactor item for it.
- **The continuity of the costs (R14, `refactor`).** Track-and-Stop's bounds in LMLExplore take as
  hypotheses the continuity of `(μ', w) ↦ D(μ', w, ¬a)` at `(μ, w)` within `univ ×ˢ simplex` and
  the recommendation of `a` near `μ`. LMLExplore proves the continuity, but as a private lemma of
  `Identification/Task/BestArm.lean`. `ForLMLExplore/Identification/Task/BestArm.lean` restates it
  publicly, with the same name and proof, and adds `isOpen_answerSet_baiTask_restrict`; the port
  makes the private lemma public in place. A later round opens the refactor pull request.
- **Paper-level helpers in `GK2016/Theorem14.lean`.** Four private lemmas: the passage from
  LMLExplore's eventual bounds `𝔼[τ_δ] ≤ c log (1 / δ)`, for every `c > T*(μ)`, to the paper's
  `limsup`; the recommendation of the best arm near `μ`, from the paper's hypothesis on `rec`; and
  the two bridges above. They name the paper's hypotheses or only translate LMLExplore's stronger
  form into the paper's, so they stay in the paper's folder.
- **Unused hypotheses of the frozen statements.** Theorem 14 holds with `limsup ≤ T*(μ)`, whatever
  `p` (LMLExplore's bound), so of `p ∈ [1, e / 2]` only `1 ≤ p` is used, for
  `T*(μ) ≤ p T*(μ)`. With D-tracking, `hw_mem` is used only at `μ`. The docstrings say so; the
  statements are frozen and stay as they are.
- **Checks.** This session could not run `scripts/check-build.sh`, `scripts/check-forlmlexplore.sh`
  or `python3 scripts/check-blueprint.py` (they need an approval that nobody was there to give).
  It ran what they wrap instead: `lake build Garivier2016Optimal` (only `declaration uses sorry`
  warnings), `lake exe runLinter Garivier2016Optimal`, a search of `ForLMLExplore/` for the
  forbidden constructs, `#print axioms` of the proved results (only `propext`, `Classical.choice`
  and `Quot.sound`), `leanblueprint pdf`, `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`.

## 2026-11-08: the refactor pull request of R14

- **Pull request.** LeanMachineLearning/LMLExplore#242, from the branch
  `refactor/bai-restrict-altcost-continuity` of the fork `RemyDegenne/LMLExplore`, made from
  `upstream/main` (`06af25c`), whose dependency pins are those of the paper's pin `5113b88`.
  `Identification/Task/BestArm.lean` did not change between the two. The fork's clone is
  `.tauceti/LMLExplore`. Its `origin` uses SSH, because pushing over HTTPS has no credentials
  here.
- **Generality.** The pull request states `isOpen_answerSet_baiTask_restrict` for any open set `S`
  of vectors of means, not only for the vectors of means of an exponential family: the proof uses
  only the openness of `S`. The other restricted lemmas of the file take `hS : IsOpen S` in the
  same way. The local copy in `ForLMLExplore/` now has the same statement, so that the bump only
  deletes it. Its use in `GK2016/Theorem14.lean` proves the openness of the vectors of means of
  the family inline, as LMLExplore does in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`.
  `continuousWithinAt_altCost_baiTask_restrict` keeps its name, statement and proof. It only loses
  `private` and gets a fuller docstring.
- **Checks of the pull request.** `scripts/build.sh` in the clone was not run. Linking or copying
  the paper's prebuilt dependencies into the clone (`ln -s`, `cp -r`) needed an approval, and a
  fresh build of Mathlib, Tau Ceti, LML and LMLExplore did not fit in the round. Instead, the
  changed file was compiled with `lake env lean` from the paper's environment, which has the same
  pins, with LMLExplore's `leanOptions` passed as `-D`, `warningAsError` included. It compiled
  with no warnings. A test file with a line over 100 characters failed under the same options,
  which shows that the options were in effect. No other LMLExplore file uses the two names, apart
  from the existing uses of the private lemma in the same file. LMLExplore's CI on the pull
  request builds the whole library.
- **Checks of the round.** As in the previous round: `lake build Garivier2016Optimal` (only the
  five `declaration uses sorry` warnings), `lake exe runLinter Garivier2016Optimal`, a search of
  `ForLMLExplore/` for the forbidden constructs, `leanblueprint pdf`, `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`. No definition in the closure of a headline statement
  changed, so `lake build Comparator` was not needed.

## 2026-11-08: the optimal allocation (Proposition 6 part 3, Theorem 5)

- **Job and area.** Advance. Tag, Refresh and Refactor pull request did not apply: LMLRoadmaps
  `main` is still `d01bdd6b89ce`, and the paper's only pull request, LMLExplore#242 (R14), is
  open with status `PR #242`. The area is the chapter on the optimal allocation, where Theorem 5
  and Proposition 6 part 3 were left. Both depend only on results LMLExplore proves.
- **Proposition 6 part 3 without the scalar equation.** The paper derives the ordering from
  Theorem 5. Here it follows from Lemma 4 alone, which LMLExplore proves, and two monotonicity
  properties of the pair cost `C_b(x) = w_a d(μ a, m) + x d(μ b, m)`:
  - it increases in `x` (`strictMonoOn_expFamilyPairCost`, in LMLExplore);
  - it decreases in the lower mean `μ b ≤ μ a` (new). If `μ c ≤ μ b` and `w b < w c`, then
    `C_b(w b) < C_b(w c) ≤ C_c(w c)`, which contradicts `C_b(w b) = C_c(w c)`.

  So R7 no longer waits for R5, and its proposed target S1 is rewritten to this route.
- **Generality of R7.** The ordering is stated for every statistic `T`, as LMLExplore's results on
  best arm identification are. It also covers the `β`-optimal allocations of
  `Identification/Task/TopTwo/BestArm.lean`: for `β > 0` (`le_of_…_of_le`), and strictly for
  `β ∈ (0, 1)` (`lt_of_…_of_lt`, where `w c > 0` is needed). The optimal allocation is the case
  `β = w a`. The private lemma `mem_Ioo_of_mem_optAlloc_baiTask_restrict` gives `w a ∈ (0, 1)`
  when there is an arm `b ≠ a`. For it, the order and the strict order hold as equivalences
  (`le_iff_le_of_mem_optAlloc_baiTask_restrict`, `lt_iff_lt_of_mem_optAlloc_baiTask_restrict`).
  The paper's statement is the `←` direction of the first.
- **Placement.** The monotonicity in the mean goes to
  `ForLMLExplore/Probability/Distributions/ExponentialFamily/Mean.lean`, the path of the
  LMLExplore file it extends, in its namespace `MeasureTheory.Measure`. The ordering goes to
  `ForLMLExplore/Identification/Task/BestArmOrder.lean`, as in `PAPER_ROADMAP.md`. It imports
  `Identification/Task/TopTwo/BestArm.lean`, where a port would put it. Both files are R7's.
- **Theorem 5 is blocked.** The frozen statement `mem_optAlloc_iff_exists_scalar` has no
  hypothesis that there is an arm other than `a`, and it is false for a single arm. The
  allocation `1` is optimal, since there are no alternatives and `D(μ, w, ¬a) = ⊤` for every `w`.
  The right-hand side asks for an empty sum equal to `1`. The paper leaves `K ≥ 2` implicit
  (`notes/statement-corrections.md`, Theorem 5). The following file compiled with `lake env lean` against the
  library of this commit. It derives `False` from the statement, which is proved with `sorry`:

  ```lean
  import Garivier2016Optimal.GK2016.Theorem5
  import LMLExplore.Bandits.Instances
  import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian

  open MeasureTheory ProbabilityTheory LMLExplore LMLExplore.Identification LMLExplore.Bandits

  example : False := by
    set ρ := gaussianReal 0 1
    have hρ : ∀ c, ¬ id =ᵐ[ρ] fun _ ↦ c := not_ae_eq_const_gaussianReal 0 one_ne_zero
    have hν : ∀ (μ' : Unit → ℝ) b,
        gaussianBandit μ' 1 b = ρ.expFamily id (ρ.natParam id (μ' b)) := by
      intro μ' b
      rw [gaussianBandit_apply, expFamily_natParam_gaussianReal 0 one_ne_zero]
    have hμ : ∀ b : Unit, (0 : Unit → ℝ) b ∈ ρ.expFamilyMeans id :=
      fun _ ↦ mem_expFamilyMeans_gaussianReal 0 one_ne_zero _
    set task := (baiTask (fun μ ↦ gaussianBandit μ 1) id).restrict
      {μ' : Unit → ℝ | ∀ b, μ' b ∈ ρ.expFamilyMeans id}
    have h_alt : task.alt () = ∅ := by
      ext θ
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hθ
      rw [IdentTask.alt_restrict] at hθ
      obtain ⟨b, hb, -⟩ := (mem_alt_baiTask_iff _ _).1 hθ.1
      exact hb rfl
    have h_top (v : Unit → ℝ) : task.altCost 0 v () = ⊤ := by
      rw [IdentTask.altCost_def, h_alt]
      simp
    have h_opt : (fun _ ↦ (1 : ℝ)) ∈ task.optAlloc 0 () := by
      rw [IdentTask.mem_optAlloc_iff_isMaxOn]
      refine ⟨by simp [mem_simplex_iff], fun v _ ↦ ?_⟩
      simp [h_top]
    obtain ⟨y, x, -, -, hF, -⟩ := (Garivier2016Optimal.mem_optAlloc_iff_exists_scalar
      (fun μ ↦ gaussianBandit μ 1) ρ hρ hν hμ (a := ()) (fun b hb ↦ absurd rfl hb)).1 h_opt
    simp at hF
  ```

  The statements are frozen, so this round changes neither the statement nor its challenge. It
  sets the status of Theorem 5 to `blocked` in `formalization.yaml`, with its statement correction, and
  leaves the decision to the user. The fix is the extra hypothesis `∃ b, b ≠ a` (or
  `Nontrivial α`), with a regenerated challenge. With it, the statement is expected to hold
  (not checked in Lean): `⇒` by a first-order optimality argument at the optimal allocation, `⇐`
  by uniqueness of the solution of the system, since `C_b` and
  `x ↦ d(μ a, m_b(x)) / d(μ b, m_b(x))` both increase. That is R5's work, still `todo`.
- **Checks.** This round `scripts/check-build.sh` (4 declarations use `sorry`, no other warning),
  `scripts/check-forlmlexplore.sh` and `python3 scripts/check-blueprint.py` ran without needing
  an approval. Also run: `lake exe runLinter Garivier2016Optimal`, `#print axioms` of the new
  results (only `propext`, `Classical.choice` and `Quot.sound`), `leanblueprint pdf`,
  `leanblueprint web`, `lake exe checkdecls blueprint/lean_decls` and `lake build Comparator`.

## 2026-11-08: the almost sure upper bound (Proposition 13)

- **Job and area.** Advance. Tag, Refresh and Refactor pull request did not apply: LMLRoadmaps
  `main` is still `d01bdd6b89ce`, and the paper's only pull request, LMLExplore#242 (R14), is
  open with status `PR #242`. The area is the sample complexity chapter, where Proposition 13 was
  left (PAPER_ROADMAP.md R11). Its prerequisites in LMLExplore and in this repository were proved:
  the positivity of the optimal allocation, the continuity of the costs (R14) and the
  recommendation near `μ`. Theorem 10 and Proposition 12 need new deviation inequalities (the
  Krichevsky–Trofimov mixture, the union bound of [GK16, Appendix C]), a larger area.
- **Generality of R11.** Identification 4.4 asks for the almost sure reduction "with the same
  statistic, recommendation and thresholds" as its expectation version. It is stated so: for any
  task, the plug-in statistic of any estimator into a topological space of models, a compact set
  `W` of allocations with `D(·, ·, ¬i)` lower semicontinuous at `{θ} × W`, the recommendation `i`
  near `θ`, and thresholds `β δ t h ≤ log (1 / δ) + f t` with `f t = o(t)`. The proportions
  approach `W` in the sense `Tendsto (N(t) / t) atTop (𝓝ˢ W)`, the filter that
  `IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le` uses for the targets. It is split
  into a pathwise statement on the stopping time, given the linear growth of the statistic along
  one sequence of histories, the linear growth of the plug-in statistic from the convergences, and
  the almost sure statements, which apply both pathwise. The rate statement quantifies over every
  `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹` inside the almost sure event. Finiteness needs a positive
  infimum and holds at every `δ` of a set on which the thresholds have this form, for the paper
  `δ ∈ (0, 1)`.
- **The strong law for the empirical means.** LMLExplore had no almost sure convergence of the
  empirical means. LML's rewards by count, on `P.prod (streamMeasure ν)`, are i.i.d. with law
  `ν a` for each arm `a`, and their partial sums are the sums of rewards. Mathlib's
  `strong_law_ae_real` then gives the convergence on the product space, and
  `Measure.ae_ae_of_ae_prod` brings it back to `P`, since the event depends on the first
  coordinate only. The result goes to `ForLMLExplore/SequentialLearning/SumRewards.lean`, the path
  of LMLExplore's file on the empirical means of runs, and is part of R11, whose almost sure
  statements it serves. No LMLRoadmaps item names it, but Identification 5.2 asks for the almost
  sure optimality of Track-and-Stop, which needs it.
- **The paper's statement.** `W = {w}`, the estimator is the vector of empirical means, which
  converges almost surely because `N_b(t) / t → w b > 0` [GK16, Proposition 6] makes every arm
  pulled infinitely often. `D(μ, w, ¬a) = T*(μ)⁻¹` at the optimal allocation, and it is positive.
  The proof gives `limsup ≤ T*(μ)`, which is stronger than `p T*(μ)`: of `p ∈ [1, e / 2]`, only
  `1 ≤ p` is used.
- **The unused `[Nonempty α]`.** The frozen statement has the instance `[Nonempty α]`, which the
  proof does not use. As a section variable, it raised the `unusedSectionVars` warning, which
  `scripts/check-build.sh` rejects, and omitting it would change the statement. The section
  variables from `[Nonempty α]` on became binders of the theorem, in the same order, so that the
  type is the same. A scratch file checked that the type is the same `Expr` as that of the
  comparator challenge, with the same universe names. The theorem has
  `@[nolint unusedArguments]`, since `lake exe runLinter` reports the unused instance otherwise.
- **Shared helpers.** The four private lemmas of `GK2016/Theorem14.lean` that meet the paper's
  setting with LMLExplore's hypotheses (`limsup_div_log_le`, `eventually_mem_M_and_rec_eq`,
  `klDiv_eq_expFamilyDiv`, `mgfDominatedOn_expFamily`) are needed by Proposition 13 too. They
  moved, unchanged and public, to `GK2016/Basic.lean`, which both files import. They name the
  paper's setting, so they stay in the paper's folder.
- **Checks.** `scripts/check-build.sh` (3 declarations use `sorry`, no other warning),
  `lake exe runLinter Garivier2016Optimal`, `scripts/check-forlmlexplore.sh`,
  `python3 scripts/check-blueprint.py`, `#print axioms` of Proposition 13 (only `propext`,
  `Classical.choice` and `Quot.sound`), `leanblueprint pdf`, `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`. No definition in the closure of a headline
  statement changed, so `lake build Comparator` was not needed.

## 2026-11-08: the deviational threshold (Proposition 12)

- **Job and area.** Advance. Tag, Refresh and Refactor pull request did not apply: LMLRoadmaps
  `main` is still `d01bdd6b89ce`, and the paper's only pull request, LMLExplore#242 (R14), is
  open with status `PR #242`. Of the results left, Proposition 12 (R10) and Theorem 10 (R9) each
  need a new deviation inequality. Proposition 12 is the smaller one: LMLExplore already has the
  exponential supermartingales, the self-normalized peeling bounds of [GC11, Theorem 10] and
  [LS, Proposition 33.9]. Theorem 10 needs the Krichevsky–Trofimov mixture bound and a change of
  measure to a Bayesian model, which nothing in LMLExplore provides yet. Theorem 5, unblocked by
  the user's decision of 2026-11-08 (commit `5e45b20`, during this round), is left for a later
  round.
- **Route.** The paper's proof (Appendix C) uses the deviation bound of [Combes14Lip, Theorem 2]
  for the sum over all the arms, which LMLExplore does not have. The corrected statement lets `C`
  depend on `δ`, so a bound of the form `P(∃ t, β(t) < Z(t)) ≤ f(x)` with `f(x) → 0` and
  thresholds `p log t + c + 2 x` suffices. Per arm, the numbers of rewards are peeled over the
  dyadic slices `2 ^ k ≤ s < 2 ^ (k + 1)`. On each slice LMLExplore's time-uniform Chernoff bound
  with the rate function gives `2 exp (-z / 2)`, applied to the i.i.d. stream of the arm with the
  filtration of its past rewards. With levels `2 (η k + κ_η + y)` the slices sum to `exp (-y)`.
  Then [LS, Proposition 33.9] combines the arms, which are independent in the stream model, with
  the monotone function `η log₂ s + κ_η`, and LMLExplore's joint transfer brings the bound to runs.
  LMLExplore's union-bound thresholds `K log (2 t (t + 1)) + x` grow like `2 K log t`, which is
  why they do not give `log (C t ^ p / δ)` for `p < 2 K`. The peeled ones grow like `p log t`
  for any `p > 0`.
- **Generality.** The thresholds hold for every task on vectors of means, for arms dominated by
  any exponential families (each arm with its own family), for every sampling rule and for every
  `p > 0`, with the explicit `C = δ exp (c_{p,K} + 2 x_δ)`, `c_{p,K} =
  2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and LMLExplore's level `x_δ`. Identification 4.2
  asks for an explicit `C(α, K)` independent of `δ` (see E2), and these thresholds are of order
  `2 log (1 / δ)`, a factor 2 from the ratio of the peeling. A ratio `c > 1` in place of `2` would
  give a factor `c`. The KK21 thresholds of the same layer, `log (1 / δ) + O(log log)`, are the
  sharp form and remain to be done. The intermediate statements keep the general `η`
  (`IdentTask.measure_exists_lt_expFamilyEvidence_le_of_le`), so that other threshold shapes can
  reuse them. The i.i.d. slice bounds are stated for any i.i.d. sequence on a standard Borel
  space, as dot-notation lemmas on `iIndepFun`. LML's stream space `ℕ → α → ℝ` is standard Borel
  when `α` is countable.
- **The frozen statement.** It has `1 < p`, of which only `0 < p` is used, and the hypothesis that
  `id` is not `ρ`-almost everywhere constant, which is unused (the docstring says so). Its imports
  changed, so a scratch file elaborated the challenge's statement next to the solution. The types
  are the same `Expr`, with the same universe names, and the axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- **E2.** The erratum says that no `C(α, K)` works. The proof here does not settle that: it gives
  a `C` that grows with `1 / δ`. A heuristic supports the erratum's claim. Boundary crossing
  asymptotics of a centred random walk across `√(2 t (L + α log t))` give a probability of order
  `√L e^{-L}`, which is more than `δ` for `L = log (1 / δ) + O(1)` and small `δ`. The library
  docstring only says that the paper's proof does not give a constant independent of `δ`. The
  erratum's **Lean** entry now records the constant that the proof gives.
- **Placement, and `theorem` or `lemma`.** The four new files are R10's and sit at the paths of the LMLExplore
  files they extend: `Probability/Martingale/RateFunction.lean`,
  `SequentialLearning/RateFunctionDeviation.lean`, `SequentialLearning/ExpFamilyDeviation.lean`,
  and `Identification/DeviationalThreshold.lean`, whose content would go to LMLExplore's
  `Identification/ExpFamilyThreshold.lean`. LMLExplore's private lemma
  `streamMeasure_exists_mul_rateFunction_eq_top` is restated privately in the copy of
  `RateFunctionDeviation.lean`. Only the two library forms of Proposition 12 are `theorem`s, and
  the intermediate results are `lemma`s, following the skill's rule rather than LMLExplore's habit
  of `theorem` for main results.
- **Checks.** `scripts/check-build.sh` (2 declarations use `sorry`, Theorems 5 and 10, no other
  warning), `lake exe runLinter Garivier2016Optimal`, `scripts/check-forlmlexplore.sh`,
  `python3 scripts/check-blueprint.py`, `leanblueprint pdf`, `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`. No definition in the closure of a headline
  statement changed, so `lake build Comparator` was not needed.

## 2026-11-08: the scalar equation (Theorem 5)

- **Job and area.** Advance. Tag, Refresh and Refactor pull request did not apply: LMLRoadmaps
  `main` is still `d01bdd6b89ce`, and the paper's only pull request, LMLExplore#242 (R14), is
  open with status `PR #242`. Of the two results left, Theorem 5 (R5) depends only on what
  LMLExplore proves about the optimal allocation, and the user's decision of 2026-11-08 gave it
  the second arm it needed. Theorem 10 (R9) needs the Krichevsky–Trofimov mixture bound and a
  change of measure to a Bayesian model, a larger area left for a later round.
- **Route.** The paper reduces the optimization to the scalar `y`, through the inverses
  `x_b(y) = g_b⁻¹(y)` of the costs of the pairs, and differentiates `y / (1 + ∑ x_b(y))`. That
  needs the derivative of `g_b`, hence of the divergence, and inverse functions. The proof here
  uses neither. The cost of a pair is the minimum over the means `z` of
  `w a d(μ a, z) + w b d(μ b, z)`. So it is below the linear function `v ↦ v a A_b + v b B_b` of
  the allocation, with `A_b = d(μ a, m_b)` and `B_b = d(μ b, m_b)` at the weighted mean `m_b` of
  `w`, and equal to it at `w`.
  - `⇐` by duality: the combination of the linear bounds with the weights `1 / B_b` is
    `v a F + ∑_{b ≠ a} v b = 1` for every allocation `v`, and `∑_{b ≠ a} D / B_b` at `w`, where
    `D` is the common cost. So some pair costs at most `D` at `v`.
  - `⇒` by a first-order perturbation: if `F ≠ 1`, the direction `u` with
    `u a = (∑_{b ≠ a} 1 / B_b) / (F - 1)` and `u a A_b + u b B_b = 1` keeps the sum of the weights.
    Along it, the cost of every pair grows by at least `t (u a A'_b + u b B'_b)`, at the weighted
    means of `w + t u`, and the second factor tends to `1`. This only needs the continuity of the
    divergence and the positivity of the optimal allocation (LMLExplore). This direction does not
    need Lemma 4, which only gives the equal costs on the right-hand side.
- **The library statement.** `LMLExplore.Identification.mem_optAlloc_baiTask_restrict_iff`
  characterizes the optimal allocation `w` itself: `w` in the simplex, `w a > 0`, equal costs of
  the pairs, and `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`. It holds for every statistic `T`,
  as LMLExplore's results on best arm identification do. The two directions are separate lemmas.
  Only `⇒` needs an arm `b ≠ a`. `⇐` needs `w a > 0`, not the positivity of all the entries. The
  paper's form follows by homogeneity (`expFamilyPairCost_mul`), with `x = w / w a` and `y` the
  common cost divided by `w a`. Identification 3.4 asks for the scalar equation whenever the
  inner infimum has a unique minimizer, for per-arm families too. The argument extends to them,
  given a minimizer continuous in the weights. But LMLExplore has the closed form of the cost of
  the alternatives [GK16, Lemma 3] for one family only, so the statement stays at LMLExplore's
  current generality (PAPER_ROADMAP.md R5).
- **Placement.** The two lemmas on the cost of a pair (`expFamilyPairCost_le_of_mem_expFamilyMeans`,
  `continuousAt_expFamilyDiv_div`), in `MeasureTheory.Measure`, belong in LMLExplore's
  `Probability/Distributions/ExponentialFamily/Mean.lean`. The copy of that file in
  `ForLMLExplore/` is R7's, so to keep the items apart they are in R5's file
  `ForLMLExplore/Identification/Task/BestArmScalar.lean`, and the roadmap note says where they
  go. Only the equivalence is a `theorem`, as in the previous round.
- **Not formalized.** The monotonicity and the limits of `g_b⁻¹` and of `F` as a function of `y`,
  and the bisection. The frozen statement does not ask for them.
- **The frozen statement.** Its file now imports the new library file instead of
  `LMLExplore.Identification.Task.BestArm`. A scratch file elaborated the challenge's statement
  next to the solution: the types are the same `Expr`, with the same universe names, and the
  axioms are `propext`, `Classical.choice` and `Quot.sound`. All its hypotheses are used.
- **Checks.** `scripts/check-build.sh` (1 declaration uses `sorry`, Theorem 10, no other
  warning), `lake exe runLinter Garivier2016Optimal`, `scripts/check-forlmlexplore.sh`,
  `python3 scripts/check-blueprint.py`, `leanblueprint pdf`, `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`. No definition in the closure of a headline
  statement changed, so `lake build Comparator` was not needed.

## 2026-11-08: refresh of the paper roadmap

- **Job.** Refresh. Tag did not apply. LMLRoadmaps `main` is still `d01bdd6b89ce`, so no target
  moved and no `staged` item gained a target. The paper's pull requests to LMLExplore changed:
  LMLExplore#242 (R14) was merged on 2026-11-08 (merge commit `71936e449f5d`), and LMLExplore#246,
  the port of R11 (its `Item: R11` line), was opened.
- **Statuses.** R14 is `merged #242`, R11 is `PR #246`. R14 keeps its tag `refactor` until the
  bump, which moves the pin past the merge, deletes the local copy in
  `ForLMLExplore/Identification/Task/BestArm.lean`, and retags it `exists`. The header is
  unchanged: the LMLExplore pin is still `5113b88ad95f`, and LMLRoadmaps `main` the commit it
  names.
- **Checks.** No Lean, blueprint or statement changed in this round, so none was run.
