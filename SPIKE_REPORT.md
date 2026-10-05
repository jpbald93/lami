# Lami's theorem in Lean 4 + Mathlib: spike report

**Status: done. Builds cleanly with no `sorry` and only the standard axioms.**
Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`. Built on jack (`gmktec`) in `~/lami`, mirrored here with matching sha256 on both sides.

## 0. Prior-art check

Result: I found no existing Lean formalisation of Lami's theorem.

- **Mathlib:** `grep -ri lami Mathlib/` finds nothing relevant. `docs/1000.yaml` has `Q1149522: title: Lami's theorem` with no `decl`/`author` field, so it is listed as open.
- **`gh api search/code?q=Lami+theorem+language:lean`:** 51 hits. All are false positives: TauCeti "PermutationTriple/Passport" (`lam0/lam1/laminf`), ArkLib STIR (author name "Poulami"), lean-auto `LamSystem`, and others.
- **`gh api search/code?q=lami+language:lean`:** 68 hits. Same kind of false positives, plus `LAMI` (a Wasm opcode in phibkro/bang).
- **`gh api search/repositories?q=lami+theorem`:** 2 repos, `rickypatil0007/lami-s-theorem-` (Java) and `shivaphy/Verification-of-Lami-s-Theorem` (HTML). Neither is Lean.
- **`gh api search/repositories?q=lami+lean`:** 1 repo, `SmaniaD/LaminarFamiliesMaximalBinaryTrees`. Not relevant.
- **`gh api search/issues?q=Lami+repo:leanprover-community/mathlib4`:** 0 results.
- **Web search** for "Lami's theorem" Lean 4 formalization Mathlib: 0 results.

Related Mathlib material: `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` and `EuclideanGeometry.law_sin` (Geometry/Euclidean/Triangle.lean:68, :256/265) give the law of sines. There is no statement about equilibrium of forces.

## Files

- `Lami/Basic.lean` (284 lines): all the maths.
- `Lami.lean`: just `import Lami.Basic`.
- `AxCheck.lean`: `#print axioms` for every theorem. It is kept outside the library so the library sources contain no `#print`. Output is in `ax.log`.
- `code/check_lami.py`: numeric check on the VM. Over 100k random equilibrium triples the largest discrepancy was about 9.4e-9 (products, oriented and unoriented, the ratios, and the angle sum of 2π). It also checks the collinear case, where all sines are 0.
- `build.log`, `ax.log`, `start.t`: jack's build output. `start.t` holds the epoch start and end times.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: the scaffold. `.lake/packages` is a symlink on jack to `~/gates/primitive-root-families/.lake/packages`.

## Statements (all in `Lami/Basic.lean`, namespace `Lami`)

Setting for the oriented results: `V` is a real inner product space with `Fact (finrank ℝ V = 2)`, and `o : Orientation ℝ V (Fin 2)`. The unoriented results work in **any** real inner product space `V`; coplanarity is automatic because `F₃ = -(F₁+F₂)`.

### (1) Oriented / signed version

- **`areaForm_cyclic`** (line 27). Hypothesis: `F₁+F₂+F₃=0`. Conclusion: `ω F₁ F₂ = ω F₂ F₃ ∧ ω F₂ F₃ = ω F₃ F₁`. This is pure bilinear algebra.
- **`areaForm_eq_norm_mul_norm_mul_sin_oangle`** (line 36): `ω x y = ‖x‖*‖y‖*sin(o.oangle x y)`. It holds for all `x, y`, including zero. Mathlib did not seem to have this exact lemma; it is proved via `kahler` and `Complex.sin_arg`.
- **`lami_oriented_mul`** (line 49). Hypothesis: equilibrium only. Conclusion: `‖F₂‖‖F₃‖ sin∡(F₂,F₃) = ‖F₃‖‖F₁‖ sin∡(F₃,F₁) = ‖F₁‖‖F₂‖ sin∡(F₁,F₂)`. It holds even in degenerate and collinear cases.
- **`lami_oriented`** (line 100). Hypotheses: equilibrium and `F₁,F₂,F₃ ≠ 0`. Conclusion: `‖F₁‖/sin∡(F₂,F₃) = ‖F₂‖/sin∡(F₃,F₁) = ‖F₃‖/sin∡(F₁,F₂)`, using `Real.Angle.sin (o.oangle …)`.
- **`lami_complex`** (line 111): the same statement for `ℂ` with `Complex.orientation`. It uses `attribute [local instance] Complex.finrank_real_complex_fact in`.
- **`ratio_of_mul`** (line 63): the real-number step from equal products to equal ratios. If every `nᵢ ≠ 0`, then either all `sᵢ = 0` or none is.

### (2) Unoriented, classical form (`InnerProductGeometry.angle`, values in `[0, π]`)

- **`norm_mul_norm_mul_sin_angle`** (line 128): `‖x‖‖y‖ sin∠(x,y) = √(Gram determinant)`.
- **`lami_mul`** (line 134). Hypothesis: equilibrium only. Conclusion: the unoriented product identities. The proof shows all three Gram determinants are equal.
- **`lami`** (line 148). Hypotheses: equilibrium and all forces nonzero. Conclusion: `‖F₁‖/sin α = ‖F₂‖/sin β ∧ ‖F₂‖/sin β = ‖F₃‖/sin γ`.
- **`lami_sin_ne_zero`** (line 158). Hypotheses: as above, plus `angle F₁ F₂ ≠ 0` and `≠ π` (forces not all parallel). Conclusion: all three sines are nonzero.
- **`lami_nondegenerate`** (line 180): the equal ratios together with nonzero denominators. **This is the one to cite for the classical theorem.**
- **`lami_degenerate`** (line 189). Honest degenerate case: if `F₁ ∥ F₂` (angle 0 or π), then all three sines are 0. The equal-ratio statement in `lami` then only holds trivially, because Lean defines `x/0 = 0`.
- **`lami_cross`** (line 211): a division-free form, `‖F₁‖ sin β = ‖F₂‖ sin α`. It needs only `F₃ ≠ 0`.

### (3) Converse (done)

- **`eq_zero_of_areaForm_eq_zero`** (line 235): in 2D, if `ω x y ≠ 0`, `ω s x = 0` and `ω s y = 0`, then `s = 0`. Proved via `inner_mul_areaForm_sub`.
- **`equilibrium_of_areaForm`** (line 247): if the three cyclic area forms are equal and nonzero, then `F₁+F₂+F₃ = 0`.
- **`lami_oriented_converse`** (line 262). Hypotheses: three nonzero forces, nonzero oriented sines, and equal ratios `‖Fᵢ‖/sin∡(opposite)`. Conclusion: `F₁+F₂+F₃ = 0`.
- The docstring notes that the converse fails with unoriented angles. Replacing `F₁` by `-F₁` keeps all the unoriented sines, but breaks equilibrium.
- The "positive multiples" variant is subsumed: the hypotheses are scale-free, so any common scaling of the forces still satisfies them.

### (4) Law of sines

- **`lami_via_law_sin`** (line 220) only re-exports Mathlib's `sin_angle_mul_norm_eq_sin_angle_mul_norm`, the vector law of sines `sin∠(x,y)‖x‖ = sin∠(y,x−y)‖x−y‖`.
- It is **not** used in the proofs, and I did not prove a formal link between Lami's theorem and the force triangle. The main proofs go through area forms and Gram determinants instead.
- Mathematically, the force triangle has sides `‖F₁‖,‖F₂‖,‖F₃‖` and interior angles `π−α, π−β, π−γ`, whose sines equal `sin α, sin β, sin γ`. So Lami's theorem is the law of sines for that triangle.

## Axioms (`ax.log`)

All 15 checked theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## Source hygiene

`grep -nE "sorry|admit|native_decide|axiom |#eval|run_cmd|set_option|macro|elab|syntax|notation|import Lean"` over `Lami.lean` and `Lami/*.lean` finds nothing. The build produced 0 warnings. The only non-proof command in the sources is `attribute [local instance] … in` for the ℂ corollary.

## Build time

- `lake build` of `Lami.Basic` plus `Lami`: about 4 s wall clock (`start.t`: 1790747315 → 1790747319). Mathlib oleans were already built through the shared packages symlink.
- It took four edit/build cycles in total, and the first file was building about 5 min in.

## What remains (optional)

- A proven, not just stated, link to `EuclideanGeometry.law_sin` for the force triangle. This is the triangle with vertices `0, F₁, F₁+F₂`, where the interior angles are `π −` the force angles.
- An affine/point version, with forces as `P → Qᵢ` vectors at a common point.
- An unoriented converse: equal ratios plus a sign or orientation condition, for example all oriented angles having the same sign, implies equilibrium up to the ambiguity noted above.
- Nothing was pushed to git. No network server was started. On jack, only `~/lami` and `/tmp/lami_back.tgz` were created.
