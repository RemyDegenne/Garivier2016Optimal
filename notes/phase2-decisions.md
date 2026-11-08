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
