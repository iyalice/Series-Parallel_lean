/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.AdjacentBounds

/-!
# Annealed and logarithmic moments

This module introduces the expectation notation used by the main text and proves the basic
finite, positive bounds needed before logarithms and normalized sequences are formed.
-/

@[expose] public section

open MeasureTheory

namespace SeriesParallel.MainText

/-- The first moment `E[Z_n^(η)(p)]`. -/
noncomputable def firstMoment (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment, Z mode n environment ∂environmentMeasure p

/-- The mean logarithm `E[X_n^(η)(p)]`. -/
noncomputable def meanLog (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment, X mode n environment ∂environmentMeasure p

theorem firstMoment_bounds (p : unitInterval) (mode : Mode) (n : ℕ) :
    ((2 : ℝ) ^ n)⁻¹ ≤ firstMoment p mode n ∧
      firstMoment p mode n ≤ (2 : ℝ) ^ n := by
  constructor
  · rw [firstMoment]
    calc
      ((2 : ℝ) ^ n)⁻¹ =
          ∫ _ : Environment, ((2 : ℝ) ^ n)⁻¹ ∂environmentMeasure p := by simp
      _ ≤ ∫ environment, Z mode n environment ∂environmentMeasure p :=
        integral_mono (integrable_const _) (integrable_Z p mode n)
          (fun environment ↦ (Z_global_bounds mode n environment).1)
  · rw [firstMoment]
    calc
      (∫ environment, Z mode n environment ∂environmentMeasure p) ≤
          ∫ _ : Environment, (2 : ℝ) ^ n ∂environmentMeasure p :=
        integral_mono (integrable_Z p mode n) (integrable_const _)
          (fun environment ↦ (Z_global_bounds mode n environment).2)
      _ = (2 : ℝ) ^ n := by simp

theorem firstMoment_pos (p : unitInterval) (mode : Mode) (n : ℕ) :
    0 < firstMoment p mode n :=
  lt_of_lt_of_le (by positivity) (firstMoment_bounds p mode n).1

theorem firstMoment_ne_zero (p : unitInterval) (mode : Mode) (n : ℕ) :
    firstMoment p mode n ≠ 0 :=
  (firstMoment_pos p mode n).ne'

theorem meanLog_bounds (p : unitInterval) (mode : Mode) (n : ℕ) :
    -mode.eta * n * Real.log 2 ≤ meanLog p mode n ∧
      meanLog p mode n ≤ n * Real.log 2 := by
  constructor
  · rw [meanLog]
    calc
      -mode.eta * n * Real.log 2 =
          ∫ _ : Environment, -mode.eta * n * Real.log 2 ∂environmentMeasure p := by simp
      _ ≤ ∫ environment, X mode n environment ∂environmentMeasure p :=
        integral_mono (integrable_const _) (integrable_X p mode n)
          (fun environment ↦ (X_iterated_bounds mode n environment).1)
  · rw [meanLog]
    calc
      (∫ environment, X mode n environment ∂environmentMeasure p) ≤
          ∫ _ : Environment, n * Real.log 2 ∂environmentMeasure p :=
        integral_mono (integrable_X p mode n) (integrable_const _)
          (fun environment ↦ (X_iterated_bounds mode n environment).2)
      _ = n * Real.log 2 := by simp

theorem meanLog_increment_bound (p : unitInterval) (mode : Mode) (n : ℕ) :
    |meanLog p mode (n + 1) - meanLog p mode n| ≤ Real.log 2 := by
  exact abs_integral_X_increment_le_log_two p mode n

/-- The normalized log first moment, indexed by `n+1` to avoid division by zero. -/
noncomputable def normalizedLogFirstMoment
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  Real.log (firstMoment p mode (n + 1)) / (n + 1)

/-- The normalized mean logarithm, indexed by `n+1` to avoid division by zero. -/
noncomputable def normalizedMeanLog
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  meanLog p mode (n + 1) / (n + 1)

end SeriesParallel.MainText
