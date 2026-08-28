/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.RandomModel

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Structural properties of the common-coupling model

This module proves measurability, deterministic bounds, integrability, and the measure-level
resistance duality consequences of the samplewise construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SeriesParallel.MainText

theorem measurable_distanceValue (n : ℕ) : Measurable (distanceValue n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : Environment ↦ (1 : ℕ))
      fun_prop
  | succ n ih =>
      rw [show distanceValue (n + 1) = fun environment ↦
        if environment root then
          distanceValue n (Environment.subtree [false] environment) +
            distanceValue n (Environment.subtree [true] environment)
        else
          min (distanceValue n (Environment.subtree [false] environment))
            (distanceValue n (Environment.subtree [true] environment)) from
          funext (distanceValue_succ n)]
      have hleft :
          Measurable (fun environment ↦ distanceValue n
            (Environment.subtree [false] environment)) :=
        ih.comp (measurable_subtreeShift [false])
      have hright :
          Measurable (fun environment ↦ distanceValue n
            (Environment.subtree [true] environment)) :=
        ih.comp (measurable_subtreeShift [true])
      have hroot : MeasurableSet {environment : Environment | environment root = true} :=
        measurable_coordinate root (measurableSet_singleton true)
      have hmeasurable : Measurable fun environment ↦
        if environment root then
          distanceValue n (Environment.subtree [false] environment) +
            distanceValue n (Environment.subtree [true] environment)
        else
          min (distanceValue n (Environment.subtree [false] environment))
            (distanceValue n (Environment.subtree [true] environment))
          := Measurable.ite hroot (hleft.add hright) (hleft.min hright)
      exact hmeasurable

theorem measurable_resistanceValue (n : ℕ) : Measurable (resistanceValue n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : Environment ↦ (1 : ℝ))
      fun_prop
  | succ n ih =>
      rw [show resistanceValue (n + 1) = fun environment ↦
        if environment root then
          resistanceValue n (Environment.subtree [false] environment) +
            resistanceValue n (Environment.subtree [true] environment)
        else
          resistanceValue n (Environment.subtree [false] environment) *
              resistanceValue n (Environment.subtree [true] environment) /
            (resistanceValue n (Environment.subtree [false] environment) +
              resistanceValue n (Environment.subtree [true] environment)) from
          funext (resistanceValue_succ n)]
      have hleft :
          Measurable (fun environment ↦ resistanceValue n
            (Environment.subtree [false] environment)) :=
        ih.comp (measurable_subtreeShift [false])
      have hright :
          Measurable (fun environment ↦ resistanceValue n
            (Environment.subtree [true] environment)) :=
        ih.comp (measurable_subtreeShift [true])
      have hroot : MeasurableSet {environment : Environment | environment root = true} :=
        measurable_coordinate root (measurableSet_singleton true)
      have hmeasurable : Measurable fun environment ↦
        if environment root then
          resistanceValue n (Environment.subtree [false] environment) +
            resistanceValue n (Environment.subtree [true] environment)
        else
          resistanceValue n (Environment.subtree [false] environment) *
              resistanceValue n (Environment.subtree [true] environment) /
            (resistanceValue n (Environment.subtree [false] environment) +
              resistanceValue n (Environment.subtree [true] environment))
          := Measurable.ite hroot (hleft.add hright)
            ((hleft.mul hright).div (hleft.add hright))
      exact hmeasurable

theorem measurable_Z (mode : Mode) (n : ℕ) : Measurable (Z mode n) := by
  cases mode with
  | distance =>
      exact (measurable_of_countable (fun value : ℕ ↦ (value : ℝ))).comp
        (measurable_distanceValue n)
  | resistance => exact measurable_resistanceValue n

theorem measurable_X (mode : Mode) (n : ℕ) : Measurable (X mode n) :=
  by
    rw [show X mode n = Real.log ∘ Z mode n by rfl]
    exact Real.measurable_log.comp (measurable_Z mode n)

/-- The lower deterministic resistance bound follows from duality and the upper edge bound. -/
theorem inv_two_pow_le_resistanceValue (n : ℕ) (environment : Environment) :
    ((2 : ℝ) ^ n)⁻¹ ≤ resistanceValue n environment := by
  have hupper := Z_le_two_pow .resistance n (complementEnvironment environment)
  simp only [Z] at hupper
  rw [resistanceValue_complement] at hupper
  have htwo : 0 < (2 : ℝ) ^ n := by positivity
  have hinv : 0 < (resistanceValue n environment)⁻¹ :=
    inv_pos.mpr (resistanceValue_pos n environment)
  simpa using (inv_le_inv₀ htwo hinv).2 hupper

/-- Unified deterministic global bounds, equivalent to the iterated adjacent-generation bound. -/
theorem Z_global_bounds (mode : Mode) (n : ℕ) (environment : Environment) :
    ((2 : ℝ) ^ n)⁻¹ ≤ Z mode n environment ∧ Z mode n environment ≤ (2 : ℝ) ^ n := by
  refine ⟨?_, Z_le_two_pow mode n environment⟩
  cases mode with
  | distance =>
      change ((2 : ℝ) ^ n)⁻¹ ≤ (distanceValue n environment : ℝ)
      have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      calc
        ((2 : ℝ) ^ n)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hpow
        _ ≤ distanceValue n environment := by
          exact_mod_cast (randomNetwork n environment).distance_bounds.1
  | resistance => exact inv_two_pow_le_resistanceValue n environment

theorem integrable_Z (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (Z mode n) (environmentMeasure p) := by
  apply Integrable.of_bound (measurable_Z mode n).aestronglyMeasurable ((2 : ℝ) ^ n)
  filter_upwards with environment
  rw [Real.norm_eq_abs, abs_of_pos (Z_pos mode n environment)]
  exact Z_le_two_pow mode n environment

theorem abs_X_le (mode : Mode) (n : ℕ) (environment : Environment) :
    |X mode n environment| ≤ n * Real.log 2 := by
  have hlower := (Z_global_bounds mode n environment).1
  have hupper := (Z_global_bounds mode n environment).2
  have hZ := Z_pos mode n environment
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hlogUpper : X mode n environment ≤ n * Real.log 2 := by
    rw [X, ← Real.log_pow]
    exact Real.log_le_log hZ hupper
  have hlogLower : -(n * Real.log 2) ≤ X mode n environment := by
    rw [X, ← Real.log_pow, ← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hpow) hlower
  rw [abs_le]
  exact ⟨hlogLower, hlogUpper⟩

theorem integrable_X (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (X mode n) (environmentMeasure p) := by
  apply Integrable.of_bound (measurable_X mode n).aestronglyMeasurable (n * Real.log 2)
  filter_upwards with environment
  simpa [Real.norm_eq_abs] using abs_X_le mode n environment

/-- Complementation realizes the parameter change `p ↦ 1-p` at the level of laws. -/
theorem resistanceValue_complement_hasLaw (p : unitInterval) (n : ℕ) :
    HasLaw (fun environment ↦ resistanceValue n (complementEnvironment environment))
      ((environmentMeasure (unitInterval.symm p)).map (resistanceValue n))
      (environmentMeasure p) := by
  refine ⟨((measurable_resistanceValue n).comp
    measurable_complementEnvironment).aemeasurable, ?_⟩
  change (environmentMeasure p).map (resistanceValue n ∘ complementEnvironment) = _
  rw [← Measure.map_map (measurable_resistanceValue n) measurable_complementEnvironment,
    complementEnvironment_map]

/-- The two descendant depth-`n` quantities used at the root are independent. -/
theorem left_right_Z_indep (p : unitInterval) (mode : Mode) (n : ℕ) :
    (fun environment ↦ Z mode n (Environment.subtree [false] environment))
      ⟂ᵢ[environmentMeasure p]
    (fun environment ↦ Z mode n (Environment.subtree [true] environment)) := by
  have hsubtrees :
      subtreeShift [false] ⟂ᵢ[environmentMeasure p] subtreeShift [true] := by
    let left : Level 1 := ⟨[false], by simp⟩
    let right : Level 1 := ⟨[true], by simp⟩
    have hne : left ≠ right := by simp [left, right]
    exact descendantEnvironments_indep p hne
  exact hsubtrees.comp (measurable_Z mode n) (measurable_Z mode n)

end SeriesParallel.MainText
