# Singular integer matrices: Lean formalization

Lean 4 + Mathlib formalization of results from the paper in `paper/`
(*How Often Is a Random Integer Matrix Singular?*).

## Status

| Paper result | Lean | Status |
|---|---|---|
| Prop. 2.1: S₂(N) = 2 Σ φ(m) ⌊N/m⌋² − N² | `SingularMatrices/TwoByTwo.lean`, `S2_formula` | compiles |
| Small-N values of S₂ (OEIS A134506) and S₃ (Appendix A) | `SingularMatrices/SmallN.lean` | compiles |
| Section 5: Steps 1–6 give S₃(N) = (J/ζ(3)) N⁶ log N + O(N⁶), with the single-plane estimates, Lemma 5.2 and Lemma 5.4 as hypotheses | `SingularMatrices/ErrorSums.lean`, `main_bound` | compiles |
| Lemma 3.1 (pair form) and the first identity of Lemma 3.2, A(N) = Σ g(m) ⌊N/m⌋² | `SingularMatrices/ThreeByThree.lean`, `S3_split`, `A3count_eq_sum_g` | compiles |
| Rest of Theorem 3.6: grouping pairs by plane, Lemma 3.3, Prop. 3.5, Möbius formula for g(m) | — | next |

## One-time setup

You need the Lean 4 extension for VS Code (it installs `elan` and `lake`).
In Terminal (or the VS Code terminal):

```
cd ~/Library/CloudStorage/OneDrive-WashingtonUniversityinSt.Louis/Repositories/"Claude + Lean"
bash setup.sh
```

The script switches to the Lean version that Mathlib uses, downloads Mathlib
(several GB, into `.lake/`), and checks the proofs. After that, `lake build` rechecks them.
To work interactively, open this folder in VS Code and open a `.lean` file; goals and
errors appear in the Lean Infoview.

If `lake build` reports errors, paste its full output into the chat.

## Note on OneDrive

`.lake/` holds several GB of Mathlib build files, and OneDrive will sync them. To avoid
that, move this folder outside OneDrive (for example to `~/Lean/`) and add the new
location in Cowork.

## Layout

- `SingularMatrices/` — Lean sources; `SingularMatrices.lean` imports them all.
- `paper/` — the paper: LaTeX source, PDF, figures, scripts and data.
- `lakefile.toml`, `lean-toolchain`, `setup.sh` — project configuration.
