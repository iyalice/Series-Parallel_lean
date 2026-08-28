/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.StructuralProperties

/-!
# Adjacent-generation deterministic bounds

This module proves the samplewise comparison between two consecutive generations directly from
the recursive distance and resistance gates.  In particular, the resistance proof uses only the
monotonicity and homogeneity of the positive harmonic gate, proved below by elementary algebra.
-/

@[expose] public section

open MeasureTheory

namespace SeriesParallel.MainText

/-- The positive harmonic gate is coordinatewise monotone. -/
private theorem harmonic_mono {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hac : a ≤ c) (hbd : b ≤ d) :
    a * b / (a + b) ≤ c * d / (c + d) := by
  rw [div_le_div_iff₀ (add_pos ha hb) (add_pos hc hd)]
  have h₁ : 0 ≤ a * c * (d - b) :=
    mul_nonneg (mul_nonneg ha.le hc.le) (sub_nonneg.mpr hbd)
  have h₂ : 0 ≤ b * d * (c - a) :=
    mul_nonneg (mul_nonneg hb.le hd.le) (sub_nonneg.mpr hac)
  nlinarith

/-- Scaling both inputs scales the positive harmonic gate by the same factor. -/
private theorem harmonic_scale (c x y : ℝ) (hc : c ≠ 0) (hxy : x + y ≠ 0) :
    (c * x) * (c * y) / (c * x + c * y) = c * (x * y / (x + y)) := by
  have hscaled : c * x + c * y ≠ 0 := by
    rw [← mul_add]
    exact mul_ne_zero hc hxy
  field_simp [hscaled, hxy]

/-- A factor interval for the two inputs is preserved by the positive harmonic gate. -/
private theorem harmonic_adjacent_bounds {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx' : 0 < x') (hy' : 0 < y') (hxl : (1 / 2 : ℝ) * x ≤ x')
    (hyl : (1 / 2 : ℝ) * y ≤ y') (hxu : x' ≤ 2 * x) (hyu : y' ≤ 2 * y) :
    (1 / 2 : ℝ) * (x * y / (x + y)) ≤ x' * y' / (x' + y') ∧
      x' * y' / (x' + y') ≤ 2 * (x * y / (x + y)) := by
  have hxy : x + y ≠ 0 := (add_pos hx hy).ne'
  constructor
  · rw [← harmonic_scale (1 / 2 : ℝ) x y (by norm_num) hxy]
    exact harmonic_mono (by positivity) (by positivity) hx' hy' hxl hyl
  · rw [← harmonic_scale (2 : ℝ) x y (by norm_num) hxy]
    exact harmonic_mono hx' hy' (by positivity) (by positivity) hxu hyu

/-- Replacing the bottom layer changes distance by a factor in `[1, 2]`. -/
theorem distanceValue_adjacent_bounds (n : ℕ) (environment : Environment) :
    distanceValue n environment ≤ distanceValue (n + 1) environment ∧
      distanceValue (n + 1) environment ≤ 2 * distanceValue n environment := by
  induction n generalizing environment with
  | zero =>
      by_cases hroot : environment root
      · simp [distanceValue_succ, hroot]
      · simp [distanceValue_succ, hroot]
  | succ n ih =>
      rw [distanceValue_succ n environment, distanceValue_succ (n + 1) environment]
      have ihLeft := ih (Environment.subtree [false] environment)
      have ihRight := ih (Environment.subtree [true] environment)
      by_cases hroot : environment root
      · simp only [hroot, if_pos]
        constructor
        · exact Nat.add_le_add ihLeft.1 ihRight.1
        · exact (Nat.add_le_add ihLeft.2 ihRight.2).trans_eq (by omega)
      · simp only [hroot]
        constructor
        · exact min_le_min ihLeft.1 ihRight.1
        · rcases le_total
            (distanceValue n (Environment.subtree [false] environment))
            (distanceValue n (Environment.subtree [true] environment)) with hleft | hright
          · calc
              min (distanceValue (n + 1) (Environment.subtree [false] environment))
                    (distanceValue (n + 1) (Environment.subtree [true] environment))
                  ≤ distanceValue (n + 1) (Environment.subtree [false] environment) :=
                    min_le_left _ _
              _ ≤ 2 * distanceValue n (Environment.subtree [false] environment) := ihLeft.2
              _ = 2 * min (distanceValue n (Environment.subtree [false] environment))
                    (distanceValue n (Environment.subtree [true] environment)) := by
                      rw [min_eq_left hleft]
          · calc
              min (distanceValue (n + 1) (Environment.subtree [false] environment))
                    (distanceValue (n + 1) (Environment.subtree [true] environment))
                  ≤ distanceValue (n + 1) (Environment.subtree [true] environment) :=
                    min_le_right _ _
              _ ≤ 2 * distanceValue n (Environment.subtree [true] environment) := ihRight.2
              _ = 2 * min (distanceValue n (Environment.subtree [false] environment))
                    (distanceValue n (Environment.subtree [true] environment)) := by
                      rw [min_eq_right hright]

/-- Replacing the bottom layer changes resistance by a factor in `[1/2, 2]`. -/
theorem resistanceValue_adjacent_bounds (n : ℕ) (environment : Environment) :
    (1 / 2 : ℝ) * resistanceValue n environment ≤ resistanceValue (n + 1) environment ∧
      resistanceValue (n + 1) environment ≤ 2 * resistanceValue n environment := by
  induction n generalizing environment with
  | zero =>
      by_cases hroot : environment root
      · norm_num [resistanceValue_succ, hroot]
      · norm_num [resistanceValue_succ, hroot]
  | succ n ih =>
      rw [resistanceValue_succ n environment, resistanceValue_succ (n + 1) environment]
      have ihLeft := ih (Environment.subtree [false] environment)
      have ihRight := ih (Environment.subtree [true] environment)
      by_cases hroot : environment root
      · simp only [hroot, if_pos]
        constructor <;> nlinarith [ihLeft.1, ihRight.1, ihLeft.2, ihRight.2]
      · simp only [hroot]
        exact harmonic_adjacent_bounds
          (resistanceValue_pos n (Environment.subtree [false] environment))
          (resistanceValue_pos n (Environment.subtree [true] environment))
          (resistanceValue_pos (n + 1) (Environment.subtree [false] environment))
          (resistanceValue_pos (n + 1) (Environment.subtree [true] environment))
          ihLeft.1 ihRight.1 ihLeft.2 ihRight.2

/-- Clean mode-dependent form of the exact samplewise adjacent-generation comparison. -/
theorem adjacent_Z (mode : Mode) (n : ℕ) (environment : Environment) :
    (if mode = .resistance then (1 / 2 : ℝ) else 1) * Z mode n environment ≤
        Z mode (n + 1) environment ∧
      Z mode (n + 1) environment ≤ 2 * Z mode n environment := by
  cases mode with
  | distance =>
      have h := distanceValue_adjacent_bounds n environment
      simp only [Z, reduceCtorEq, if_false, one_mul]
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  | resistance =>
      simpa [Z] using resistanceValue_adjacent_bounds n environment

/-- Source-facing `2^{-η}` form of the exact samplewise adjacent-generation comparison. -/
theorem adjacent_Z_rpow (mode : Mode) (n : ℕ) (environment : Environment) :
    (2 : ℝ) ^ (-(mode.eta : ℝ)) * Z mode n environment ≤ Z mode (n + 1) environment ∧
      Z mode (n + 1) environment ≤ 2 * Z mode n environment := by
  cases mode with
  | distance => simpa using adjacent_Z .distance n environment
  | resistance => simpa [Real.rpow_neg_one] using adjacent_Z .resistance n environment

/-- Taking logarithms in `adjacent_Z_rpow` bounds every samplewise increment. -/
theorem X_adjacent_bounds (mode : Mode) (n : ℕ) (environment : Environment) :
    -mode.eta * Real.log 2 ≤ X mode (n + 1) environment - X mode n environment ∧
      X mode (n + 1) environment - X mode n environment ≤ Real.log 2 := by
  have hZ := adjacent_Z_rpow mode n environment
  have hn := Z_pos mode n environment
  have hn1 := Z_pos mode (n + 1) environment
  have hfactor : 0 < (2 : ℝ) ^ (-(mode.eta : ℝ)) := by positivity
  constructor
  · have hlog := Real.log_le_log (mul_pos hfactor hn) hZ.1
    rw [Real.log_mul hfactor.ne' hn.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
    change -mode.eta * Real.log 2 ≤
      Real.log (Z mode (n + 1) environment) - Real.log (Z mode n environment)
    linarith
  · have hlog := Real.log_le_log hn1 hZ.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne'] at hlog
    change Real.log (Z mode (n + 1) environment) - Real.log (Z mode n environment) ≤
      Real.log 2
    linarith

/-- The absolute value of each samplewise logarithmic increment is at most `log 2`. -/
theorem abs_X_increment_le_log_two (mode : Mode) (n : ℕ) (environment : Environment) :
    |X mode (n + 1) environment - X mode n environment| ≤ Real.log 2 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hetaLog : mode.eta * Real.log 2 ≤ Real.log 2 :=
    mul_le_of_le_one_left hlog mode.eta_le_one
  rw [abs_le]
  constructor
  · calc
      -Real.log 2 ≤ -(mode.eta * Real.log 2) := neg_le_neg hetaLog
      _ = -mode.eta * Real.log 2 := by ring
      _ ≤ X mode (n + 1) environment - X mode n environment :=
        (X_adjacent_bounds mode n environment).1
  · exact (X_adjacent_bounds mode n environment).2

/-- Iterating the adjacent increment bounds gives the deterministic depth-`n` interval. -/
theorem X_iterated_bounds (mode : Mode) (n : ℕ) (environment : Environment) :
    -mode.eta * n * Real.log 2 ≤ X mode n environment ∧
      X mode n environment ≤ n * Real.log 2 := by
  induction n with
  | zero => simp [X]
  | succ n ih =>
      have hadj := X_adjacent_bounds mode n environment
      constructor
      · calc
          -mode.eta * (n + 1 : ℕ) * Real.log 2 =
              -mode.eta * n * Real.log 2 + -mode.eta * Real.log 2 := by
                push_cast
                ring
          _ ≤ X mode n environment + (X mode (n + 1) environment - X mode n environment) :=
            add_le_add ih.1 hadj.1
          _ = X mode (n + 1) environment := by ring
      · calc
          X mode (n + 1) environment =
              X mode n environment + (X mode (n + 1) environment - X mode n environment) := by
                ring
          _ ≤ n * Real.log 2 + Real.log 2 := add_le_add ih.2 hadj.2
          _ = (n + 1 : ℕ) * Real.log 2 := by
            push_cast
            ring

/-- The mean logarithmic increment under any environment law is bounded by `log 2`. -/
theorem abs_integral_X_increment_le_log_two (p : unitInterval) (mode : Mode) (n : ℕ) :
    |∫ environment, X mode (n + 1) environment ∂environmentMeasure p -
        ∫ environment, X mode n environment ∂environmentMeasure p| ≤ Real.log 2 := by
  rw [← integral_sub (integrable_X p mode (n + 1)) (integrable_X p mode n)]
  have hbound : ∀ᵐ environment ∂environmentMeasure p,
      ‖X mode (n + 1) environment - X mode n environment‖ ≤ Real.log 2 :=
    Filter.Eventually.of_forall fun environment ↦ by
      simpa [Real.norm_eq_abs] using abs_X_increment_le_log_two mode n environment
  have hIntegral := norm_integral_le_of_norm_le_const hbound
  simpa [Real.norm_eq_abs] using hIntegral

end SeriesParallel.MainText
