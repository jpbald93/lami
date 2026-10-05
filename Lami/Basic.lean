import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Lami's theorem

Three concurrent forces `F₁ F₂ F₃` in equilibrium (`F₁ + F₂ + F₃ = 0`) satisfy
`‖F₁‖ / sin α = ‖F₂‖ / sin β = ‖F₃‖ / sin γ`, where `α` is the angle between `F₂` and `F₃`,
`β` the angle between `F₃` and `F₁`, and `γ` the angle between `F₁` and `F₂`.

* Oriented version (two-dimensional oriented space, `Orientation.oangle`).
* Unoriented version (`InnerProductGeometry.angle`), valid in any real inner product space.
-/

open scoped Real RealInnerProductSpace

namespace Lami

section Oriented

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- Equilibrium of three forces forces the three cyclic area forms to agree. -/
theorem areaForm_cyclic {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0) :
    o.areaForm F₁ F₂ = o.areaForm F₂ F₃ ∧ o.areaForm F₂ F₃ = o.areaForm F₃ F₁ := by
  have h3 : F₃ = -F₁ - F₂ := by rw [← sub_eq_zero, ← h]; abel
  subst h3
  simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, o.areaForm_apply_self]
  rw [o.areaForm_swap F₂ F₁]
  constructor <;> ring

/-- The area form in terms of norms and the sine of the oriented angle. -/
theorem areaForm_eq_norm_mul_norm_mul_sin_oangle (x y : V) :
    o.areaForm x y = ‖x‖ * ‖y‖ * Real.Angle.sin (o.oangle x y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Orientation.oangle, Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler,
    o.kahler_apply_apply]
  have : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)
  simp [Complex.real_smul]
  field_simp

/-- **Lami's theorem**, oriented product form. No hypotheses beyond equilibrium. -/
theorem lami_oriented_mul {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0) :
    ‖F₂‖ * ‖F₃‖ * Real.Angle.sin (o.oangle F₂ F₃) =
        ‖F₃‖ * ‖F₁‖ * Real.Angle.sin (o.oangle F₃ F₁) ∧
      ‖F₃‖ * ‖F₁‖ * Real.Angle.sin (o.oangle F₃ F₁) =
        ‖F₁‖ * ‖F₂‖ * Real.Angle.sin (o.oangle F₁ F₂) := by
  obtain ⟨h1, h2⟩ := areaForm_cyclic o h
  simp only [← areaForm_eq_norm_mul_norm_mul_sin_oangle]
  exact ⟨h2, (h1.trans h2).symm⟩

end Oriented

/-- Abstract algebra behind the ratio form: from `n₂ n₃ s₁ = n₃ n₁ s₂ = n₁ n₂ s₃` with all
`nᵢ ≠ 0` we get `n₁ / s₁ = n₂ / s₂ = n₃ / s₃` (with Lean's convention `a / 0 = 0`, which is
consistent: either all `sᵢ` vanish or none does). -/
theorem ratio_of_mul {n₁ n₂ n₃ s₁ s₂ s₃ : ℝ} (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (h₃ : n₃ ≠ 0)
    (e₁ : n₂ * n₃ * s₁ = n₃ * n₁ * s₂) (e₂ : n₃ * n₁ * s₂ = n₁ * n₂ * s₃) :
    n₁ / s₁ = n₂ / s₂ ∧ n₂ / s₂ = n₃ / s₃ := by
  by_cases hs : s₁ = 0
  · have hs₂ : s₂ = 0 := by
      subst hs
      have : n₃ * n₁ * s₂ = 0 := by rw [← e₁]; ring
      simpa [h₁, h₃] using this
    have hs₃ : s₃ = 0 := by
      subst hs₂
      have : n₁ * n₂ * s₃ = 0 := by rw [← e₂]; ring
      simpa [h₁, h₂] using this
    simp [hs, hs₂, hs₃]
  · have hs₂ : s₂ ≠ 0 := by
      intro h0; subst h0
      have : n₂ * n₃ * s₁ = 0 := by rw [e₁]; ring
      simp [h₂, h₃, hs] at this
    have hs₃ : s₃ ≠ 0 := by
      intro h0; subst h0
      have : n₃ * n₁ * s₂ = 0 := by rw [e₂]; ring
      simp [h₁, h₃, hs₂] at this
    constructor
    · rw [div_eq_div_iff hs hs₂]
      apply mul_left_cancel₀ h₃
      linear_combination -e₁
    · rw [div_eq_div_iff hs₂ hs₃]
      apply mul_left_cancel₀ h₁
      linear_combination -e₂

section Oriented2

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- **Lami's theorem**, oriented ratio form. -/
theorem lami_oriented {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0) :
    ‖F₁‖ / Real.Angle.sin (o.oangle F₂ F₃) = ‖F₂‖ / Real.Angle.sin (o.oangle F₃ F₁) ∧
      ‖F₂‖ / Real.Angle.sin (o.oangle F₃ F₁) = ‖F₃‖ / Real.Angle.sin (o.oangle F₁ F₂) := by
  obtain ⟨e₁, e₂⟩ := lami_oriented_mul o h
  exact ratio_of_mul (norm_ne_zero_iff.mpr h₁) (norm_ne_zero_iff.mpr h₂)
    (norm_ne_zero_iff.mpr h₃) e₁ e₂

attribute [local instance] Complex.finrank_real_complex_fact in
/-- Lami's theorem for forces given as complex numbers (the plane `ℂ` with its standard
orientation). -/
theorem lami_complex {F₁ F₂ F₃ : ℂ} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0) :
    ‖F₁‖ / Real.Angle.sin (Complex.orientation.oangle F₂ F₃) =
        ‖F₂‖ / Real.Angle.sin (Complex.orientation.oangle F₃ F₁) ∧
      ‖F₂‖ / Real.Angle.sin (Complex.orientation.oangle F₃ F₁) =
        ‖F₃‖ / Real.Angle.sin (Complex.orientation.oangle F₁ F₂) :=
  lami_oriented Complex.orientation h h₁ h₂ h₃

end Oriented2

section Unoriented

open InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `‖x‖ ‖y‖ sin ∠(x, y)` is the square root of the Gram determinant. -/
theorem norm_mul_norm_mul_sin_angle (x y : V) :
    ‖x‖ * ‖y‖ * Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
  rw [← sin_angle_mul_norm_mul_norm]; ring

/-- **Lami's theorem**, unoriented product form, in any real inner product space
(coplanarity is automatic: `F₃ = -(F₁ + F₂)`). No nondegeneracy hypotheses. -/
theorem lami_mul {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0) :
    ‖F₂‖ * ‖F₃‖ * Real.sin (angle F₂ F₃) = ‖F₃‖ * ‖F₁‖ * Real.sin (angle F₃ F₁) ∧
      ‖F₃‖ * ‖F₁‖ * Real.sin (angle F₃ F₁) = ‖F₁‖ * ‖F₂‖ * Real.sin (angle F₁ F₂) := by
  have h3 : F₃ = -F₁ - F₂ := by rw [← sub_eq_zero, ← h]; abel
  subst h3
  simp only [norm_mul_norm_mul_sin_angle]
  constructor <;> congr 1 <;>
    simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
      real_inner_comm F₁ F₂] <;> ring

/-- **Lami's theorem** (classical form, unoriented angles in `[0, π]`):
`‖F₁‖ / sin α = ‖F₂‖ / sin β = ‖F₃‖ / sin γ`.
In the degenerate (all forces parallel) case all three sines vanish, see `lami_degenerate`, and
the equalities hold only trivially via `x / 0 = 0`; use `lami_nondegenerate` for the honest form. -/
theorem lami {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0) :
    ‖F₁‖ / Real.sin (angle F₂ F₃) = ‖F₂‖ / Real.sin (angle F₃ F₁) ∧
      ‖F₂‖ / Real.sin (angle F₃ F₁) = ‖F₃‖ / Real.sin (angle F₁ F₂) := by
  obtain ⟨e₁, e₂⟩ := lami_mul h
  exact ratio_of_mul (norm_ne_zero_iff.mpr h₁) (norm_ne_zero_iff.mpr h₂)
    (norm_ne_zero_iff.mpr h₃) e₁ e₂

/-- If `F₁` and `F₂` are not parallel (`∠(F₁, F₂) ∉ {0, π}`) then all three sines are nonzero,
so the ratios in `lami` are genuine ratios. -/
theorem lami_sin_ne_zero {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0)
    (hγ : angle F₁ F₂ ≠ 0) (hγ' : angle F₁ F₂ ≠ π) :
    Real.sin (angle F₂ F₃) ≠ 0 ∧ Real.sin (angle F₃ F₁) ≠ 0 ∧ Real.sin (angle F₁ F₂) ≠ 0 := by
  have hs : Real.sin (angle F₁ F₂) ≠ 0 := by
    rw [Ne, sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]; tauto
  have n₁ := norm_ne_zero_iff.mpr h₁
  have n₂ := norm_ne_zero_iff.mpr h₂
  have n₃ := norm_ne_zero_iff.mpr h₃
  obtain ⟨e₁, e₂⟩ := lami_mul h
  have hβ : Real.sin (angle F₃ F₁) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e₂
    exact (mul_ne_zero (mul_ne_zero n₁ n₂) hs) e₂.symm
  have hα : Real.sin (angle F₂ F₃) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e₁
    exact (mul_ne_zero (mul_ne_zero n₃ n₁) hβ) e₁.symm
  exact ⟨hα, hβ, hs⟩

/-- **Lami's theorem**, honest nondegenerate form: the three ratios are equal *and* the
denominators are nonzero. -/
theorem lami_nondegenerate {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0)
    (hγ : angle F₁ F₂ ≠ 0) (hγ' : angle F₁ F₂ ≠ π) :
    (Real.sin (angle F₂ F₃) ≠ 0 ∧ Real.sin (angle F₃ F₁) ≠ 0 ∧ Real.sin (angle F₁ F₂) ≠ 0) ∧
      ‖F₁‖ / Real.sin (angle F₂ F₃) = ‖F₂‖ / Real.sin (angle F₃ F₁) ∧
      ‖F₂‖ / Real.sin (angle F₃ F₁) = ‖F₃‖ / Real.sin (angle F₁ F₂) :=
  ⟨lami_sin_ne_zero h h₁ h₂ h₃ hγ hγ', lami h h₁ h₂ h₃⟩

/-- Degenerate case: if `F₁ ∥ F₂` (angle `0` or `π`) then all three sines vanish. -/
theorem lami_degenerate {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0)
    (hγ : angle F₁ F₂ = 0 ∨ angle F₁ F₂ = π) :
    Real.sin (angle F₂ F₃) = 0 ∧ Real.sin (angle F₃ F₁) = 0 ∧ Real.sin (angle F₁ F₂) = 0 := by
  have hs : Real.sin (angle F₁ F₂) = 0 := sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mpr hγ
  have n₁ := norm_ne_zero_iff.mpr h₁
  have n₂ := norm_ne_zero_iff.mpr h₂
  have n₃ := norm_ne_zero_iff.mpr h₃
  obtain ⟨e₁, e₂⟩ := lami_mul h
  rw [hs, mul_zero] at e₂
  have hβ : Real.sin (angle F₃ F₁) = 0 := by
    rcases mul_eq_zero.mp e₂ with h0 | h0
    · exact absurd h0 (mul_ne_zero n₃ n₁)
    · exact h0
  rw [hβ, mul_zero] at e₁
  have hα : Real.sin (angle F₂ F₃) = 0 := by
    rcases mul_eq_zero.mp e₁ with h0 | h0
    · exact absurd h0 (mul_ne_zero n₂ n₃)
    · exact h0
  exact ⟨hα, hβ, hs⟩

/-- Division-free cross-multiplied form: `‖F₁‖ sin β = ‖F₂‖ sin α`, etc. -/
theorem lami_cross {F₁ F₂ F₃ : V} (h : F₁ + F₂ + F₃ = 0) (h₃ : F₃ ≠ 0) :
    ‖F₁‖ * Real.sin (angle F₃ F₁) = ‖F₂‖ * Real.sin (angle F₂ F₃) := by
  obtain ⟨e₁, -⟩ := lami_mul h
  have n₃ := norm_ne_zero_iff.mpr h₃
  apply mul_left_cancel₀ n₃
  linear_combination -e₁

/-- Relation with Mathlib's **law of sines** (`sin_angle_mul_norm_eq_sin_angle_mul_norm`):
Lami's product identity for `F₁, F₂` is the vector law of sines for the force triangle. -/
theorem lami_via_law_sin (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ :=
  sin_angle_mul_norm_eq_sin_angle_mul_norm x y

end Unoriented

section Converse

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- In a 2-dimensional space, a vector with zero area form against two independent vectors
(`ω x y ≠ 0`) is zero. -/
theorem eq_zero_of_areaForm_eq_zero {x y s : V} (hxy : o.areaForm x y ≠ 0)
    (hx : o.areaForm s x = 0) (hy : o.areaForm s y = 0) : s = 0 := by
  have key := o.inner_mul_areaForm_sub s x y
  rw [hx, hy, mul_zero, zero_mul, sub_zero] at key
  have h2 : ‖s‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact h
    · exact absurd h hxy
  simpa using h2

/-- **Converse of Lami's theorem**, area-form version: if the three cyclic area forms agree
and are nonzero, the forces are in equilibrium. -/
theorem equilibrium_of_areaForm {F₁ F₂ F₃ : V}
    (e₁ : o.areaForm F₁ F₂ = o.areaForm F₂ F₃) (e₂ : o.areaForm F₂ F₃ = o.areaForm F₃ F₁)
    (hne : o.areaForm F₁ F₂ ≠ 0) : F₁ + F₂ + F₃ = 0 := by
  apply eq_zero_of_areaForm_eq_zero o hne
  · simp only [map_add, LinearMap.add_apply, o.areaForm_apply_self]
    rw [o.areaForm_swap F₂ F₁]
    linear_combination -e₁ - e₂
  · simp only [map_add, LinearMap.add_apply, o.areaForm_apply_self]
    rw [o.areaForm_swap F₃ F₂]
    linear_combination e₁

/-- **Converse of Lami's theorem**, oriented ratio form: three nonzero forces whose magnitudes
are proportional to the sines of the oriented opposite angles, with those sines nonzero,
are in equilibrium. (Oriented angles are essential: with unoriented angles the converse
fails, e.g. reversing one force.) -/
theorem lami_oriented_converse {F₁ F₂ F₃ : V}
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (h₃ : F₃ ≠ 0)
    (hs₁ : Real.Angle.sin (o.oangle F₂ F₃) ≠ 0) (hs₂ : Real.Angle.sin (o.oangle F₃ F₁) ≠ 0)
    (hs₃ : Real.Angle.sin (o.oangle F₁ F₂) ≠ 0)
    (r₁ : ‖F₁‖ / Real.Angle.sin (o.oangle F₂ F₃) = ‖F₂‖ / Real.Angle.sin (o.oangle F₃ F₁))
    (r₂ : ‖F₂‖ / Real.Angle.sin (o.oangle F₃ F₁) = ‖F₃‖ / Real.Angle.sin (o.oangle F₁ F₂)) :
    F₁ + F₂ + F₃ = 0 := by
  have n₁ := norm_ne_zero_iff.mpr h₁
  have n₂ := norm_ne_zero_iff.mpr h₂
  have n₃ := norm_ne_zero_iff.mpr h₃
  rw [div_eq_div_iff hs₁ hs₂] at r₁
  rw [div_eq_div_iff hs₂ hs₃] at r₂
  apply equilibrium_of_areaForm o
  · rw [areaForm_eq_norm_mul_norm_mul_sin_oangle, areaForm_eq_norm_mul_norm_mul_sin_oangle]
    linear_combination ‖F₁‖ * r₂ + ‖F₃‖ * r₁
  · rw [areaForm_eq_norm_mul_norm_mul_sin_oangle, areaForm_eq_norm_mul_norm_mul_sin_oangle]
    linear_combination -‖F₃‖ * r₁
  · rw [areaForm_eq_norm_mul_norm_mul_sin_oangle]
    exact mul_ne_zero (mul_ne_zero n₁ n₂) hs₃

end Converse

end Lami
