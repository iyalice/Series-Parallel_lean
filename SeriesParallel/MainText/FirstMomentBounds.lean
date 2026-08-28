/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.ConditionalRefinement
public import SeriesParallel.MainText.Moments

import Mathlib.Probability.Independence.Integration

/-!
# Sharp first-moment bounds

The lower recursion uses the series event at the root.  Its indicator is independent of the
complete family of depth-one descendant environments, so the expectation of the indicator times
the sum of the two descendant values factors exactly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace SeriesParallel.MainText

/-- The depth-one vertex reached by the left edge. -/
private def leftLevelOne : Level 1 := ⟨[false], by simp⟩

/-- The depth-one vertex reached by the right edge. -/
private def rightLevelOne : Level 1 := ⟨[true], by simp⟩

/-- The real-valued indicator of the series choice. -/
private def seriesIndicator (b : Bool) : ℝ := if b then 1 else 0

private theorem measurable_seriesIndicator : Measurable seriesIndicator :=
  measurable_of_finite seriesIndicator

/-- Sum of the two depth-`n` quantities extracted from a depth-one descendant family. -/
private noncomputable def descendantSum
    (mode : Mode) (n : ℕ) (family : Level 1 → Environment) : ℝ :=
  Z mode n (family leftLevelOne) + Z mode n (family rightLevelOne)

private theorem measurable_descendantSum (mode : Mode) (n : ℕ) :
    Measurable (descendantSum mode n) := by
  exact ((measurable_Z mode n).comp (measurable_pi_apply leftLevelOne)).add
    ((measurable_Z mode n).comp (measurable_pi_apply rightLevelOne))

/-- The root coordinate is independent of the full depth-one descendant family. -/
private theorem root_descendantFamily_indep (p : unitInterval) :
    coordinate root ⟂ᵢ[environmentMeasure p] descendantFamily 1 := by
  change Indep
    (MeasurableSpace.comap (coordinate root) inferInstance)
    (MeasurableSpace.comap (descendantFamily 1) inferInstance)
    (environmentMeasure p)
  refine indep_of_indep_of_le (finiteLevelSigma_indep_descendantFamily p 1) ?_ le_rfl
  exact (measurable_coordinate_finiteLevel (n := 1) (w := root) (by simp [root])).comap_le

/-- The root series indicator is independent of the descendant sum. -/
private theorem seriesIndicator_descendantSum_indep
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (fun environment ↦ seriesIndicator (coordinate root environment))
      ⟂ᵢ[environmentMeasure p]
    (fun environment ↦ descendantSum mode n (descendantFamily 1 environment)) := by
  simpa only [Function.comp_def] using
    (root_descendantFamily_indep p).comp measurable_seriesIndicator
      (measurable_descendantSum mode n)

private theorem integrable_seriesIndicator (p : unitInterval) :
    Integrable (fun environment ↦ seriesIndicator (coordinate root environment))
      (environmentMeasure p) := by
  apply Integrable.of_bound
    (measurable_seriesIndicator.comp (measurable_coordinate root)).aestronglyMeasurable 1
  filter_upwards with environment
  cases h : coordinate root environment <;> simp [seriesIndicator, h]

private theorem integrable_Z_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    Integrable (fun environment ↦ Z mode n (Environment.subtree word environment))
      (environmentMeasure p) := by
  have hmeas : Measurable
      (fun environment ↦ Z mode n (Environment.subtree word environment)) := by
    simpa only [Environment.subtree, Function.comp_def] using
      (measurable_Z mode n).comp (measurable_subtreeShift word)
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((2 : ℝ) ^ n)
  filter_upwards with environment
  rw [Real.norm_eq_abs, abs_of_pos (Z_pos mode n _)]
  exact Z_le_two_pow mode n _

private theorem integrable_descendantSum_comp
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ descendantSum mode n (descendantFamily 1 environment))
      (environmentMeasure p) := by
  change Integrable
    ((fun environment ↦ Z mode n (Environment.subtree [false] environment)) +
      fun environment ↦ Z mode n (Environment.subtree [true] environment))
    (environmentMeasure p)
  exact (integrable_Z_subtree p mode n [false]).add
    (integrable_Z_subtree p mode n [true])

private theorem integral_seriesIndicator (p : unitInterval) :
    (∫ environment, seriesIndicator (coordinate root environment) ∂environmentMeasure p) =
      (p : ℝ) := by
  calc
    (∫ environment, seriesIndicator (coordinate root environment) ∂environmentMeasure p) =
        ∫ b, seriesIndicator b ∂bernoulliBool p := by
          simpa only [Function.comp_def] using
            (coordinate_hasLaw p root).integral_comp
              measurable_seriesIndicator.aestronglyMeasurable
    _ = (p : ℝ) := by
      rw [bernoulliBool, integral_bernoulliMeasure]
      simp [seriesIndicator]

private theorem integral_Z_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    (∫ environment, Z mode n (Environment.subtree word environment)
        ∂environmentMeasure p) = firstMoment p mode n := by
  simpa only [firstMoment, Environment.subtree, Function.comp_def] using
    (subtreeShift_hasLaw p word).integral_comp
      (measurable_Z mode n).aestronglyMeasurable

private theorem integral_descendantSum
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, descendantSum mode n (descendantFamily 1 environment)
        ∂environmentMeasure p) = 2 * firstMoment p mode n := by
  rw [show (∫ environment, descendantSum mode n (descendantFamily 1 environment)
      ∂environmentMeasure p) =
      ∫ environment,
        Z mode n (Environment.subtree [false] environment) +
          Z mode n (Environment.subtree [true] environment)
        ∂environmentMeasure p by rfl]
  rw [integral_add (integrable_Z_subtree p mode n [false])
    (integrable_Z_subtree p mode n [true]),
    integral_Z_subtree p mode n [false], integral_Z_subtree p mode n [true]]
  ring

private theorem seriesWeighted_descendantSum_le_succ
    (mode : Mode) (n : ℕ) (environment : Environment) :
    seriesIndicator (coordinate root environment) *
        descendantSum mode n (descendantFamily 1 environment) ≤
      Z mode (n + 1) environment := by
  by_cases hroot : environment root
  · calc
      seriesIndicator (coordinate root environment) *
          descendantSum mode n (descendantFamily 1 environment) =
          Z mode n (Environment.subtree [false] environment) +
            Z mode n (Environment.subtree [true] environment) := by
              simp [seriesIndicator, coordinate, hroot, descendantSum, descendantFamily,
                leftLevelOne, rightLevelOne, Environment.subtree]
      _ ≤ Z mode (n + 1) environment := by
        rw [Z_succ]
        simp [hroot, seriesGate]
  · calc
      seriesIndicator (coordinate root environment) *
          descendantSum mode n (descendantFamily 1 environment) = 0 := by
            simp [seriesIndicator, coordinate, hroot]
      _ ≤ Z mode (n + 1) environment := (Z_pos mode (n + 1) environment).le

/-- One-step lower recursion in source Lemma `lem:first-moment-bounds`. -/
theorem firstMoment_succ_lower_bound (p : unitInterval) (mode : Mode) (n : ℕ) :
    2 * (p : ℝ) * firstMoment p mode n ≤ firstMoment p mode (n + 1) := by
  let rootTerm : Environment → ℝ :=
    fun environment ↦ seriesIndicator (coordinate root environment)
  let descendants : Environment → ℝ :=
    fun environment ↦ descendantSum mode n (descendantFamily 1 environment)
  have hindep : rootTerm ⟂ᵢ[environmentMeasure p] descendants := by
    simpa only [rootTerm, descendants] using seriesIndicator_descendantSum_indep p mode n
  have hfactor :
      (∫ environment, rootTerm environment * descendants environment
          ∂environmentMeasure p) =
        (∫ environment, rootTerm environment ∂environmentMeasure p) *
          ∫ environment, descendants environment ∂environmentMeasure p := by
    exact hindep.integral_fun_mul_eq_mul_integral
      (measurable_seriesIndicator.comp (measurable_coordinate root)).aestronglyMeasurable
      ((measurable_descendantSum mode n).comp
        (measurable_descendantFamily 1)).aestronglyMeasurable
  have hproduct : Integrable (fun environment ↦ rootTerm environment * descendants environment)
      (environmentMeasure p) := by
    change Integrable (rootTerm * descendants) (environmentMeasure p)
    exact hindep.integrable_mul
      (by simpa only [rootTerm] using integrable_seriesIndicator p)
      (by simpa only [descendants] using integrable_descendantSum_comp p mode n)
  calc
    2 * (p : ℝ) * firstMoment p mode n =
        (p : ℝ) * (2 * firstMoment p mode n) := by ring
    _ = (∫ environment, rootTerm environment ∂environmentMeasure p) *
        ∫ environment, descendants environment ∂environmentMeasure p := by
          rw [show (∫ environment, rootTerm environment ∂environmentMeasure p) =
              (p : ℝ) by simpa only [rootTerm] using integral_seriesIndicator p,
            show (∫ environment, descendants environment ∂environmentMeasure p) =
              2 * firstMoment p mode n by
                simpa only [descendants] using integral_descendantSum p mode n]
    _ = ∫ environment, rootTerm environment * descendants environment
        ∂environmentMeasure p := hfactor.symm
    _ ≤ ∫ environment, Z mode (n + 1) environment ∂environmentMeasure p := by
      apply integral_mono hproduct (integrable_Z p mode (n + 1))
      intro environment
      simpa only [rootTerm, descendants] using
        seriesWeighted_descendantSum_le_succ mode n environment
    _ = firstMoment p mode (n + 1) := rfl

/-- The sharp exponential bounds in source Lemma `lem:first-moment-bounds`. -/
theorem firstMoment_geometric_bounds (p : unitInterval) (mode : Mode) (n : ℕ) :
    (2 * (p : ℝ)) ^ n ≤ firstMoment p mode n ∧
      firstMoment p mode n ≤ (2 : ℝ) ^ n := by
  constructor
  · induction n with
    | zero => simp [firstMoment]
    | succ n ih =>
        calc
          (2 * (p : ℝ)) ^ (n + 1) =
              (2 * (p : ℝ)) ^ n * (2 * (p : ℝ)) := by rw [pow_succ]
          _ ≤ firstMoment p mode n * (2 * (p : ℝ)) :=
            mul_le_mul_of_nonneg_right ih (mul_nonneg (by norm_num) p.2.1)
          _ = 2 * (p : ℝ) * firstMoment p mode n := by ring
          _ ≤ firstMoment p mode (n + 1) := firstMoment_succ_lower_bound p mode n
  · exact (firstMoment_bounds p mode n).2

end SeriesParallel.MainText
