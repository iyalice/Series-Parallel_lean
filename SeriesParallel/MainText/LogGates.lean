/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic series and parallel gates

This file formalizes the two modes and the deterministic gate identities from the
main text's section on the unified recursion.  The ordinary gates take real inputs,
while positivity is made explicit in every theorem that interprets them as physical
series or parallel combinations.
-/

@[expose] public section

namespace SeriesParallel.MainText

/-- The two values of the parameter `η`: graph distance (`η = 0`) and effective
resistance (`η = 1`). -/
inductive Mode where
  | distance
  | resistance
  deriving DecidableEq, Fintype, Repr

namespace Mode

/-- The natural-number value of the mode parameter. -/
def etaNat : Mode → ℕ
  | distance => 0
  | resistance => 1

/-- The real value of the mode parameter used in logarithmic formulas. -/
def eta (mode : Mode) : ℝ := mode.etaNat

@[simp]
theorem etaNat_distance : Mode.distance.etaNat = 0 := rfl

@[simp]
theorem etaNat_resistance : Mode.resistance.etaNat = 1 := rfl

@[simp]
theorem eta_distance : Mode.distance.eta = 0 := by simp [eta, etaNat]

@[simp]
theorem eta_resistance : Mode.resistance.eta = 1 := by simp [eta, etaNat]

theorem eta_eq_zero_or_one (mode : Mode) : mode.eta = 0 ∨ mode.eta = 1 := by
  cases mode <;> simp

theorem eta_nonneg (mode : Mode) : 0 ≤ mode.eta := by
  cases mode <;> simp

theorem eta_le_one (mode : Mode) : mode.eta ≤ 1 := by
  cases mode <;> simp

end Mode

/-- The ordinary series gate. -/
def seriesGate (x y : ℝ) : ℝ := x + y

/-- The positive-domain parallel gate `Π_η` from `eq:parallel-gate`.

The definition is total on `ℝ`, but its physical interpretation and all logarithmic
bridge theorems explicitly assume positive inputs. -/
noncomputable def parallelGate (mode : Mode) (x y : ℝ) : ℝ :=
  min x y / (1 + min x y / max x y) ^ mode.etaNat

/-- The bounded correction `h(t) = log (1 + exp (-t))`.  The source uses it for
`t ≥ 0`; defining it on all reals makes the gate identities more convenient. -/
noncomputable def h (t : ℝ) : ℝ := Real.log (1 + Real.exp (-t))

/-- The logarithmic series gate `g₊`. -/
noncomputable def logSeriesGate (x y : ℝ) : ℝ :=
  Real.log (Real.exp x + Real.exp y)

/-- The logarithmic parallel gate `g₋^(η)`, by the two cases in the source. -/
noncomputable def logParallelGate (mode : Mode) (x y : ℝ) : ℝ :=
  match mode with
  | .distance => min x y
  | .resistance => -Real.log (Real.exp (-x) + Real.exp (-y))

@[simp]
theorem parallelGate_distance (x y : ℝ) : parallelGate .distance x y = min x y := by
  simp [parallelGate]

@[simp]
theorem parallelGate_resistance (x y : ℝ) :
    parallelGate .resistance x y = min x y / (1 + min x y / max x y) := by
  simp [parallelGate]

@[simp]
theorem logParallelGate_distance (x y : ℝ) :
    logParallelGate .distance x y = min x y := rfl

@[simp]
theorem logParallelGate_resistance (x y : ℝ) :
    logParallelGate .resistance x y = -Real.log (Real.exp (-x) + Real.exp (-y)) := rfl

theorem seriesGate_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < seriesGate x y := by
  exact add_pos hx hy

/-- For positive inputs, the TeX min--max formula for `Π₁` is the usual harmonic
parallel combination. -/
theorem parallelGate_resistance_eq_harmonic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parallelGate .resistance x y = x * y / (x + y) := by
  rcases le_total x y with hxy | hyx
  · rw [parallelGate_resistance, min_eq_left hxy, max_eq_right hxy]
    have hden : 1 + x / y ≠ 0 := (by positivity : 0 < 1 + x / y).ne'
    field_simp [hx.ne', hy.ne', (add_pos hx hy).ne', hden]
    ring
  · rw [parallelGate_resistance, min_eq_right hyx, max_eq_left hyx]
    have hden : 1 + y / x ≠ 0 := (by positivity : 0 < 1 + y / x).ne'
    field_simp [hx.ne', hy.ne', (add_pos hx hy).ne', hden]

theorem parallelGate_pos (mode : Mode) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < parallelGate mode x y := by
  cases mode with
  | distance => simpa using lt_min hx hy
  | resistance =>
      rw [parallelGate_resistance_eq_harmonic hx hy]
      exact div_pos (mul_pos hx hy) (add_pos hx hy)

theorem h_pos (t : ℝ) : 0 < h t := by
  rw [h]
  exact (Real.log_pos_iff (by positivity)).2 (by linarith [Real.exp_pos (-t)])

theorem h_nonneg (t : ℝ) : 0 ≤ h t := (h_pos t).le

/-- On the source domain `t ≥ 0`, the correction is bounded by `log 2`. -/
theorem h_le_log_two {t : ℝ} (ht : 0 ≤ t) : h t ≤ Real.log 2 := by
  apply Real.log_le_log (by positivity)
  have hexp : Real.exp (-t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
  calc
    1 + Real.exp (-t) ≤ 1 + Real.exp 0 := add_le_add le_rfl hexp
    _ = 2 := by rw [Real.exp_zero]; ring

/-- Monotonicity of the logarithmic series gate in its first coordinate. -/
theorem logSeriesGate_mono_left {x₁ x₂ y : ℝ} (hxx : x₁ ≤ x₂) :
    logSeriesGate x₁ y ≤ logSeriesGate x₂ y := by
  apply Real.log_le_log (by positivity)
  exact add_le_add (Real.exp_le_exp.mpr hxx) le_rfl

/-- Monotonicity of the logarithmic series gate in its second coordinate. -/
theorem logSeriesGate_mono_right {x y₁ y₂ : ℝ} (hyy : y₁ ≤ y₂) :
    logSeriesGate x y₁ ≤ logSeriesGate x y₂ := by
  apply Real.log_le_log (by positivity)
  exact add_le_add le_rfl (Real.exp_le_exp.mpr hyy)

theorem monotone_logSeriesGate_left (y : ℝ) : Monotone (fun x ↦ logSeriesGate x y) :=
  fun _ _ ↦ logSeriesGate_mono_left

theorem monotone_logSeriesGate_right (x : ℝ) : Monotone (logSeriesGate x) :=
  fun _ _ ↦ logSeriesGate_mono_right

/-- Resistance parallelism is the negative of series combination after negating both
logarithmic inputs. -/
theorem logParallelGate_resistance_eq_neg_series (x y : ℝ) :
    logParallelGate .resistance x y = -logSeriesGate (-x) (-y) := rfl

/-- Monotonicity of the logarithmic parallel gate in its first coordinate. -/
theorem logParallelGate_mono_left (mode : Mode) {x₁ x₂ y : ℝ} (hxx : x₁ ≤ x₂) :
    logParallelGate mode x₁ y ≤ logParallelGate mode x₂ y := by
  cases mode with
  | distance => exact min_le_min hxx le_rfl
  | resistance =>
      exact neg_le_neg (logSeriesGate_mono_left (neg_le_neg hxx))

/-- Monotonicity of the logarithmic parallel gate in its second coordinate. -/
theorem logParallelGate_mono_right (mode : Mode) {x y₁ y₂ : ℝ} (hyy : y₁ ≤ y₂) :
    logParallelGate mode x y₁ ≤ logParallelGate mode x y₂ := by
  cases mode with
  | distance => exact min_le_min le_rfl hyy
  | resistance =>
      exact neg_le_neg (logSeriesGate_mono_right (neg_le_neg hyy))

theorem monotone_logParallelGate_left (mode : Mode) (y : ℝ) :
    Monotone (fun x ↦ logParallelGate mode x y) :=
  fun _ _ ↦ logParallelGate_mono_left mode

theorem monotone_logParallelGate_right (mode : Mode) (x : ℝ) :
    Monotone (logParallelGate mode x) :=
  fun _ _ ↦ logParallelGate_mono_right mode

/-- Translation covariance of `g₊`. -/
theorem logSeriesGate_translation (x y a : ℝ) :
    logSeriesGate (x + a) (y + a) = a + logSeriesGate x y := by
  have hfactor :
      Real.exp (x + a) + Real.exp (y + a) =
        Real.exp a * (Real.exp x + Real.exp y) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [logSeriesGate, hfactor, Real.log_mul (Real.exp_ne_zero a)]
  · simp [logSeriesGate]
  · positivity

/-- Translation covariance of `g₋^(η)`. -/
theorem logParallelGate_translation (mode : Mode) (x y a : ℝ) :
    logParallelGate mode (x + a) (y + a) = a + logParallelGate mode x y := by
  cases mode with
  | distance => simp [min_add_add_right, add_comm]
  | resistance =>
      rw [logParallelGate_resistance_eq_neg_series,
        show -(x + a) = -x + -a by ring,
        show -(y + a) = -y + -a by ring,
        logSeriesGate_translation]
      rw [logParallelGate_resistance_eq_neg_series]
      ring

/-- The max representation of the logarithmic series gate. -/
theorem logSeriesGate_eq_max_add_h (x y : ℝ) :
    logSeriesGate x y = max x y + h |x - y| := by
  rcases le_total x y with hxy | hyx
  · have habs : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    rw [max_eq_right hxy, habs]
    have hfactor :
        Real.exp x + Real.exp y = Real.exp y * (1 + Real.exp (-(y - x))) := by
      rw [show -(y - x) = x - y by ring, Real.exp_sub]
      field_simp [Real.exp_ne_zero]
      all_goals ring
    rw [logSeriesGate, h, hfactor,
      Real.log_mul (Real.exp_ne_zero y) (by positivity), Real.log_exp]
  · have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyx)
    rw [max_eq_left hyx, habs]
    have hfactor :
        Real.exp x + Real.exp y = Real.exp x * (1 + Real.exp (-(x - y))) := by
      rw [show -(x - y) = y - x by ring, Real.exp_sub]
      field_simp [Real.exp_ne_zero]
    rw [logSeriesGate, h, hfactor,
      Real.log_mul (Real.exp_ne_zero x) (by positivity), Real.log_exp]

/-- The min representation of the logarithmic parallel gate. -/
theorem logParallelGate_eq_min_sub_h (mode : Mode) (x y : ℝ) :
    logParallelGate mode x y = min x y - mode.eta * h |x - y| := by
  cases mode with
  | distance => simp
  | resistance =>
      rw [logParallelGate_resistance_eq_neg_series,
        logSeriesGate_eq_max_add_h]
      simp only [max_neg_neg, neg_sub_neg, Mode.eta_resistance, one_mul]
      rw [abs_sub_comm y x]
      ring

/-- The logarithm of a positive ordinary series combination is `g₊` of the two
input logarithms. -/
theorem log_seriesGate {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (seriesGate x y) = logSeriesGate (Real.log x) (Real.log y) := by
  simp [seriesGate, logSeriesGate, Real.exp_log hx, Real.exp_log hy]

/-- The logarithm of a positive ordinary parallel combination is `g₋^(η)` of
the two input logarithms. -/
theorem log_parallelGate (mode : Mode) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (parallelGate mode x y) =
      logParallelGate mode (Real.log x) (Real.log y) := by
  cases mode with
  | distance =>
      rcases le_total x y with hxy | hyx
      · rw [parallelGate_distance, min_eq_left hxy, logParallelGate_distance,
          min_eq_left (Real.log_le_log hx hxy)]
      · rw [parallelGate_distance, min_eq_right hyx, logParallelGate_distance,
          min_eq_right (Real.log_le_log hy hyx)]
  | resistance =>
      rw [parallelGate_resistance_eq_harmonic hx hy, logParallelGate_resistance]
      simp only [Real.exp_neg, Real.exp_log hx, Real.exp_log hy]
      rw [← Real.log_inv]
      congr 1
      field_simp [hx.ne', hy.ne', (add_pos hx hy).ne']
      all_goals ring

end SeriesParallel.MainText
