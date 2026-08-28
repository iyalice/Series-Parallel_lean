import SeriesParallel.RealCubeRoot

/-!
# Minimal main-text input

The appendices use only positivity of the diffusion coefficient `a`. The stronger main-text
identity `a = 2 * ζ(3)` is deliberately not imported.
-/

namespace SeriesParallel

/-- The sole datum imported from the main text. -/
structure MainInput where
  /-- The diffusion coefficient denoted by `a` in the paper. -/
  a : ℝ
  /-- This is supplied by the main text's `lem:diffusion-coefficient`. -/
  a_pos : 0 < a

namespace MainInput

/-- `β = (2/a)^(1/3)`, interpreted as the signed real cube root. -/
noncomputable def beta (input : MainInput) : ℝ :=
  Real.cbrt (2 / input.a)

/-- `κ_λ = 2λ/β`. -/
noncomputable def kappa (input : MainInput) (lambda : ℝ) : ℝ :=
  2 * lambda / input.beta

theorem two_div_a_pos (input : MainInput) : 0 < 2 / input.a :=
  div_pos (by norm_num) input.a_pos

theorem beta_pos (input : MainInput) : 0 < input.beta := by
  exact Real.cbrt_pos.mpr input.two_div_a_pos

theorem beta_ne_zero (input : MainInput) : input.beta ≠ 0 :=
  input.beta_pos.ne'

theorem beta_cube (input : MainInput) : input.beta ^ 3 = 2 / input.a := by
  exact Real.cbrt_cube (2 / input.a)

/-- The precise identity used in both profile equations. -/
theorem a_mul_beta_cube (input : MainInput) : input.a * input.beta ^ 3 = 2 := by
  rw [input.beta_cube]
  field_simp [input.a_pos.ne']

end MainInput

end SeriesParallel
