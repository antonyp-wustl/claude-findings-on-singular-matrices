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
| Lemma 3.1 (plane form): S₃(N) = N³A(N) + Σ_P L_P I_P | `SingularMatrices/Planes.lean`, `S3_planes` | compiles |
| Prop. 3.5: L_P = qN, I_P = q²N² − D(q,N); D(N,N) = S₂(N) | `SingularMatrices/AxisPlanes.lean`, `axis_plane`, `Dgrid_self` | compiles |
| Lemma 3.2 (Möbius formula for g(m)) | `SingularMatrices/Moebius.lean`, `g3_moebius` | compiles |
| Lemma 3.1 indexed by canonical (primitive, sign-normalized) normals | `SingularMatrices/Canon.lean`, `S3_normals` | compiles |
| Lemma 3.3 (six sign patterns, each plane once), symmetry, and **Theorem 3.6** | `SingularMatrices/Decomposition.lean`, `exact_decomposition` | compiles |
| Section 4: `∫₀¹ log x/(1+x) dx = -π²/12` and Lemma 4.4 (region II, in coordinates `s = a+b-1`, `a`) | `SingularMatrices/LogIntegral.lean`, `SingularMatrices/RegionII.lean`, `regionII` | compiles |
| Section 4: ∫∫ α(a,b)³ da db = 15/2 − 5π²/8 over the quarter-plane (regions I–IV, triangle Fubini for region II), with α given by its piecewise formula | `SingularMatrices/FlatIntegral.lean`, `flat_integral` | compiles |
| Section 4: αpw(a,b) is the area of {(x,y) ∈ [0,1]² : ax + by ≤ 1} | `SingularMatrices/AreaFormula.lean`, `area_eq_αpw` | compiles |
| Section 4: area of the plane section u^⊥ ∩ [0,1]³ (2-dim Euclidean Hausdorff measure) for u = (a,b,−1) is √(1+a²+b²)·αpw(a,b) | `SingularMatrices/SectionArea.lean`, `areaSec_wvec` | compiles |
| Section 4: α(x) on the eight octants (zero on same-sign octants, chart formula, invariance under −x and coordinate swaps) | `SingularMatrices/Octants.lean`, `Frad_ae` | compiles |
| Section 4: integral over one octant = 15/2 − 5π²/8 (substitution (x₀,x₁) = t(a,b), Tonelli) | `SingularMatrices/OctantIntegral.lean`, `octant_lintegral` | compiles |
| Section 4: Lemma 4.1 and **Theorem 4.5**: J = ∫_{S²} α(u)³ dσ(u) = 45 − 15π²/4, σ = surface measure (`volume.toSphere`) | `SingularMatrices/SphereIntegral.lean`, `J_eq` | compiles |
| Section 5: Lemmas 5.1–5.4; Prop. 3.7; Prop. 4.6 | — | later |

Theorem 3.6 is stated with the generic sum over primitive triples `(a, b, c)` with
`a, b, c ≤ N²`, the finite range the paper says suffices, and with `h(1) = 1`,
`h(m) = 2φ(m)` (`hfun`). The right-hand side was checked numerically against brute force for
`N ≤ 5` before formalizing. The Lean file also checks it for `N = 2, 3` with `native_decide`.

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
