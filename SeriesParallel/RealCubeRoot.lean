import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The real cube root

Mathlib 4.32.1 has the nonnegative real-power API but no signed real cube-root definition.
This file supplies `Real.cbrt` as the signed `1/3` power and proves the two global inverse
identities required by the source. No sign assumption is used in either identity.
-/

namespace Real

/-- The signed real cube root. -/
noncomputable def cbrt (x : ℝ) : ℝ :=
  if x < 0 then -((-x) ^ (1 / 3 : ℝ)) else x ^ (1 / 3 : ℝ)

@[simp]
theorem cbrt_zero : cbrt 0 = 0 := by
  simp [cbrt]

/-- Cubing the real cube root recovers the input, for every real input. -/
@[simp]
theorem cbrt_cube (x : ℝ) : cbrt x ^ 3 = x := by
  by_cases hx : x < 0
  · rw [cbrt, if_pos hx, (show Odd 3 by decide).neg_pow]
    rw [← Real.rpow_mul_natCast (neg_nonneg.mpr hx.le) (1 / 3 : ℝ) 3]
    norm_num
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [cbrt, if_neg hx]
    rw [← Real.rpow_mul_natCast hx0 (1 / 3 : ℝ) 3]
    norm_num

/-- Taking the real cube root of a cube recovers the input, with no sign assumption. -/
@[simp]
theorem cbrt_cube' (x : ℝ) : cbrt (x ^ 3) = x := by
  apply (show Odd 3 by decide).pow_injective
  change cbrt (x ^ 3) ^ 3 = x ^ 3
  rw [cbrt_cube]

/-- Compatibility alias matching the conventional `cube_cbrt` reading. -/
theorem cube_cbrt (x : ℝ) : cbrt (x ^ 3) = x :=
  cbrt_cube' x

/-- The signed real cube root is strictly increasing on all of `ℝ`. -/
theorem strictMono_cbrt : StrictMono cbrt := by
  intro x y hxy
  apply (show Odd 3 by decide).pow_lt_pow.mp
  simpa only [cbrt_cube] using hxy

/-- The signed real cube root is onto. -/
theorem surjective_cbrt : Function.Surjective cbrt := by
  intro x
  exact ⟨x ^ 3, cbrt_cube' x⟩

/-- The signed real cube root is continuous on all of `ℝ`. -/
theorem continuous_cbrt : Continuous cbrt :=
  strictMono_cbrt.monotone.continuous_of_surjective surjective_cbrt

theorem cbrt_pos {x : ℝ} : 0 < cbrt x ↔ 0 < x := by
  rw [← (show Odd 3 by decide).pow_pos_iff, cbrt_cube]

theorem cbrt_nonneg {x : ℝ} : 0 ≤ cbrt x ↔ 0 ≤ x := by
  rw [← (show Odd 3 by decide).pow_nonneg_iff, cbrt_cube]

theorem cbrt_eq_zero {x : ℝ} : cbrt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : ℝ ↦ z ^ 3) h
    simpa only [cbrt_cube, zero_pow (by norm_num : 3 ≠ 0)] using this
  · rintro rfl
    exact cbrt_zero

/-- The signed cube root has at most linear growth.  This deliberately weak bound is the
one needed to apply the finite-horizon global Peano interface to the shooting field. -/
theorem abs_cbrt_le_one_add_abs (x : ℝ) : |cbrt x| ≤ 1 + |x| := by
  let z := |cbrt x|
  have hz : 0 ≤ z := abs_nonneg _
  have hcube : z ^ 3 = |x| := by
    dsimp [z]
    rw [← abs_pow, cbrt_cube]
  by_cases hz_one : z ≤ 1
  · linarith [abs_nonneg x]
  · have hone_le : 1 ≤ z := le_of_not_ge hz_one
    have hprod : 0 ≤ z * (z - 1) * (z + 1) := by positivity
    have hz_cube : z ≤ z ^ 3 := by nlinarith
    rw [hcube] at hz_cube
    linarith

/-- Away from the origin, the derivative of the signed real cube root is the reciprocal
of the derivative of the cubing map. -/
theorem hasDerivAt_cbrt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cbrt (3 * cbrt x ^ 2)⁻¹ x := by
  have hcbrt : cbrt x ≠ 0 := by
    intro h
    exact hx (cbrt_eq_zero.mp h)
  have hcube : HasDerivAt (fun z : ℝ ↦ z ^ 3) (3 * cbrt x ^ 2) (cbrt x) := by
    simpa using hasDerivAt_pow 3 (cbrt x)
  apply hcube.of_local_left_inverse continuous_cbrt.continuousAt
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hcbrt)
  · filter_upwards [] with y
    exact cbrt_cube y

end Real
