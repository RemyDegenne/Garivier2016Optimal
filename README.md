# Garivier2016Optimal

A Lean 4 formalization of *Optimal Best Arm Identification with Fixed Confidence* (Aurélien Garivier
and Emilie Kaufmann, COLT 2016, arXiv:1602.04589v2), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). Made from
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

- Website: https://RemyDegenne.github.io/Garivier2016Optimal/, with the blueprint, the referee site
  and the literature links (which declarations formalize which results of the paper). CI builds it
  on each push to `main`. The literature links are also in `literature/annotations.jsonl`, which
  `scripts/formalize.sh` commits when the paper is formalized and after the final bump.
- The paper: `source/arXiv-1602.04589v2/`; the outline of the formalization: `notes/blueprint-outline.md`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Garivier2016Optimal/GK2016/`, one file per result, listed with their status in
  `formalization.yaml`, and `GK2016/Basic.lean`, the lemmas that meet the paper's setting with
  LMLExplore's hypotheses; comparator challenges in `comparator/`. Since 2026-11-08 every headline
  result is proved, with no `sorry` left in the library.
- Library-shaped material: `Garivier2016Optimal/ForLMLExplore/`, which Tau Ceti workers port to LMLExplore;
  `PAPER_ROADMAP.md` says where each item goes.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). Phase 1 (outline, blueprint,
statements) is done in a Claude Code session. After it, `scripts/formalize.sh`, in a terminal or
tmux, proves the rest and sends the reusable parts to LMLExplore.
