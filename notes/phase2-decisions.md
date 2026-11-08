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
  (`notes/paper-errata.md`, E3). The following file compiled with `lake env lean` against the
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
  sets the status of Theorem 5 to `blocked` in `formalization.yaml`, with the erratum E3, and
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
