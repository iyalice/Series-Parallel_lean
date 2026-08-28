/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.FirstMomentSubmultiplicative
import SeriesParallel.MainText.LogarithmicDrift
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Independence.Integration

/-!
# Normalized second moments and a Paley--Zygmund bound

The exact root recursion gives a closed one-step upper bound for the second moment.
After division by the squared first moment, the resulting affine recurrence is a
contraction whenever `p > 1 / 2`.  Its fixed point supplies a uniform second-moment
bound, and a direct Cauchy--Schwarz argument gives the threshold-one-half
Paley--Zygmund estimate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology unitInterval

namespace SeriesParallel.MainText

/-- The annealed second moment of the depth-`n` network value. -/
noncomputable def secondMoment (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment, Z mode n environment ^ 2 ∂environmentMeasure p

/-- The normalized second moment `E[Z_n^2] / E[Z_n]^2`. -/
noncomputable def normalizedSecondMoment
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  secondMoment p mode n / firstMoment p mode n ^ 2

/-- The unified square coefficient of a parallel gate: `1` or `1 / 4`. -/
noncomputable def parallelSquareConstant (mode : Mode) : ℝ :=
  (4 : ℝ) ^ (-mode.eta)

theorem parallelSquareConstant_eq_rpow (mode : Mode) :
    parallelSquareConstant mode = (4 : ℝ) ^ (-mode.eta) := rfl

@[simp]
theorem parallelSquareConstant_distance :
    parallelSquareConstant .distance = 1 := by
  norm_num [parallelSquareConstant]

@[simp]
theorem parallelSquareConstant_resistance :
    parallelSquareConstant .resistance = 1 / 4 := by
  norm_num [parallelSquareConstant]

theorem parallelSquareConstant_pos (mode : Mode) :
    0 < parallelSquareConstant mode := by
  rw [parallelSquareConstant]
  positivity

/-- Both parallel gates satisfy the same product square bound. -/
theorem parallelGate_sq_le (mode : Mode) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parallelGate mode x y ^ 2 ≤ parallelSquareConstant mode * (x * y) := by
  cases mode with
  | distance =>
      rw [parallelGate_distance, parallelSquareConstant_distance, one_mul]
      rcases le_total x y with hxy | hyx
      · rw [min_eq_left hxy]
        nlinarith
      · rw [min_eq_right hyx]
        nlinarith
  | resistance =>
      rw [parallelGate_resistance_eq_harmonic hx hy]
      rw [parallelSquareConstant_resistance]
      have hsum : 0 < x + y := add_pos hx hy
      field_simp [ne_of_gt hsum]
      nlinarith [sq_nonneg (x - y), mul_pos hx hy]

theorem integrable_Z_sq (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ Z mode n environment ^ 2) (environmentMeasure p) := by
  apply Integrable.of_bound
    ((measurable_Z mode n).pow_const 2).aestronglyMeasurable (((2 : ℝ) ^ n) ^ 2)
  filter_upwards with environment
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (Z_pos mode n environment).le (by positivity)).2
    (Z_le_two_pow mode n environment)

private theorem integrable_Z_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    Integrable (fun environment ↦ Z mode n (Environment.subtree word environment))
      (environmentMeasure p) := by
  simpa only [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p word).integrable_comp_of_integrable
      (integrable_Z p mode n)

private theorem integrable_Z_sq_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    Integrable (fun environment ↦ Z mode n (Environment.subtree word environment) ^ 2)
      (environmentMeasure p) := by
  simpa only [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p word).integrable_comp_of_integrable
      (integrable_Z_sq p mode n)

private theorem integral_Z_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    (∫ environment, Z mode n (Environment.subtree word environment)
        ∂environmentMeasure p) = firstMoment p mode n := by
  simpa only [firstMoment, Environment.subtree, Function.comp_def] using
    (subtreeShift_hasLaw p word).integral_comp
      (measurable_Z mode n).aestronglyMeasurable

private theorem integral_Z_sq_subtree
    (p : unitInterval) (mode : Mode) (n : ℕ) (word : Word) :
    (∫ environment, Z mode n (Environment.subtree word environment) ^ 2
        ∂environmentMeasure p) = secondMoment p mode n := by
  simpa only [secondMoment, Environment.subtree, Function.comp_def] using
    (subtreeShift_hasLaw p word).integral_comp
      ((measurable_Z mode n).pow_const 2).aestronglyMeasurable

theorem integrable_left_mul_right
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦
      Z mode n (Environment.subtree [false] environment) *
        Z mode n (Environment.subtree [true] environment)) (environmentMeasure p) := by
  have hindep := left_right_Z_indep p mode n
  change Integrable
    ((fun environment ↦ Z mode n (Environment.subtree [false] environment)) *
      fun environment ↦ Z mode n (Environment.subtree [true] environment))
    (environmentMeasure p)
  exact hindep.integrable_mul
    (integrable_Z_subtree p mode n [false])
    (integrable_Z_subtree p mode n [true])

theorem integral_left_mul_right
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment,
        Z mode n (Environment.subtree [false] environment) *
          Z mode n (Environment.subtree [true] environment) ∂environmentMeasure p) =
      firstMoment p mode n ^ 2 := by
  rw [(left_right_Z_indep p mode n).integral_fun_mul_eq_mul_integral
    (integrable_Z_subtree p mode n [false]).aestronglyMeasurable
    (integrable_Z_subtree p mode n [true]).aestronglyMeasurable,
    integral_Z_subtree p mode n [false], integral_Z_subtree p mode n [true]]
  ring

theorem secondMoment_nonneg (p : unitInterval) (mode : Mode) (n : ℕ) :
    0 ≤ secondMoment p mode n := by
  rw [secondMoment]
  exact integral_nonneg fun environment ↦ sq_nonneg (Z mode n environment)

private def rootTrueWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 1 else 0

private def rootFalseWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 0 else 1

private theorem measurable_rootTrueWeight : Measurable rootTrueWeight := by
  exact (measurable_of_finite (fun bit : Bool ↦ if bit then (1 : ℝ) else 0)).comp
    (measurable_coordinate root)

private theorem measurable_rootFalseWeight : Measurable rootFalseWeight := by
  exact (measurable_of_finite (fun bit : Bool ↦ if bit then (0 : ℝ) else 1)).comp
    (measurable_coordinate root)

private theorem integrable_rootTrueWeight (p : unitInterval) :
    Integrable rootTrueWeight (environmentMeasure p) := by
  apply Integrable.of_bound measurable_rootTrueWeight.aestronglyMeasurable 1
  filter_upwards with environment
  simp only [rootTrueWeight]
  split <;> norm_num

private theorem integrable_rootFalseWeight (p : unitInterval) :
    Integrable rootFalseWeight (environmentMeasure p) := by
  apply Integrable.of_bound measurable_rootFalseWeight.aestronglyMeasurable 1
  filter_upwards with environment
  simp only [rootFalseWeight]
  split <;> norm_num

private theorem integral_rootTrueWeight (p : unitInterval) :
    (∫ environment, rootTrueWeight environment ∂environmentMeasure p) = (p : ℝ) := by
  let event : Set Environment := {environment | coordinate root environment = true}
  have hevent : MeasurableSet event :=
    (measurableSet_singleton true).preimage (measurable_coordinate root)
  have hfun : rootTrueWeight = event.indicator 1 := by
    funext environment
    by_cases hroot : coordinate root environment <;>
      simp [rootTrueWeight, event, hroot]
  rw [hfun, integral_indicator_one hevent]
  have hmeasure : (environmentMeasure p).real event =
      (bernoulliBool p).real {bit | bit = true} := by
    simpa only [event] using (coordinate_hasLaw p root).measureReal_eq
      (p := fun bit ↦ bit = true) (measurableSet_singleton true)
  calc
    (environmentMeasure p).real event =
        (bernoulliBool p).real {bit | bit = true} := hmeasure
    _ = (bernoulliBool p).real {true} := by congr 1
    _ = (p : ℝ) := bernoulliBool_real_true p

private theorem integral_rootFalseWeight (p : unitInterval) :
    (∫ environment, rootFalseWeight environment ∂environmentMeasure p) =
      1 - (p : ℝ) := by
  let event : Set Environment := {environment | coordinate root environment = false}
  have hevent : MeasurableSet event :=
    (measurableSet_singleton false).preimage (measurable_coordinate root)
  have hfun : rootFalseWeight = event.indicator 1 := by
    funext environment
    by_cases hroot : coordinate root environment <;>
      simp [rootFalseWeight, event, hroot]
  rw [hfun, integral_indicator_one hevent]
  have hmeasure : (environmentMeasure p).real event =
      (bernoulliBool p).real {bit | bit = false} := by
    simpa only [event] using (coordinate_hasLaw p root).measureReal_eq
      (p := fun bit ↦ bit = false) (measurableSet_singleton false)
  calc
    (environmentMeasure p).real event =
        (bernoulliBool p).real {bit | bit = false} := hmeasure
    _ = (bernoulliBool p).real {false} := by congr 1
    _ = 1 - (p : ℝ) := bernoulliBool_real_false p

private noncomputable def seriesSquareDescendants
    (mode : Mode) (n : ℕ) (environment : Environment) : ℝ :=
  (Z mode n (Environment.subtree [false] environment) +
      Z mode n (Environment.subtree [true] environment)) ^ 2

private noncomputable def parallelSquareBound
    (mode : Mode) (n : ℕ) (environment : Environment) : ℝ :=
  parallelSquareConstant mode *
    (Z mode n (Environment.subtree [false] environment) *
      Z mode n (Environment.subtree [true] environment))

private theorem measurable_seriesSquareDescendants (mode : Mode) (n : ℕ) :
    Measurable (seriesSquareDescendants mode n) := by
  change Measurable (fun environment ↦
    (Z mode n (Environment.subtree [false] environment) +
      Z mode n (Environment.subtree [true] environment)) ^ 2)
  exact (((measurable_Z mode n).comp (measurable_subtreeShift [false])).add
    ((measurable_Z mode n).comp (measurable_subtreeShift [true]))).pow_const 2

private theorem measurable_parallelSquareBound (mode : Mode) (n : ℕ) :
    Measurable (parallelSquareBound mode n) := by
  change Measurable (fun environment ↦
    parallelSquareConstant mode *
      (Z mode n (Environment.subtree [false] environment) *
        Z mode n (Environment.subtree [true] environment)))
  exact measurable_const.mul
    (((measurable_Z mode n).comp (measurable_subtreeShift [false])).mul
      ((measurable_Z mode n).comp (measurable_subtreeShift [true])))

private theorem integrable_seriesSquareDescendants
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (seriesSquareDescendants mode n) (environmentMeasure p) := by
  have hleft := integrable_Z_sq_subtree p mode n [false]
  have hright := integrable_Z_sq_subtree p mode n [true]
  have hcross := integrable_left_mul_right p mode n
  rw [show seriesSquareDescendants mode n = fun environment ↦
      Z mode n (Environment.subtree [false] environment) ^ 2 +
        Z mode n (Environment.subtree [true] environment) ^ 2 +
          2 * (Z mode n (Environment.subtree [false] environment) *
            Z mode n (Environment.subtree [true] environment)) by
    funext environment
    simp only [seriesSquareDescendants]
    ring]
  exact (hleft.add hright).add (hcross.const_mul 2)

private theorem integrable_parallelSquareBound
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (parallelSquareBound mode n) (environmentMeasure p) := by
  rw [show parallelSquareBound mode n = fun environment ↦
      parallelSquareConstant mode *
        (Z mode n (Environment.subtree [false] environment) *
          Z mode n (Environment.subtree [true] environment)) by rfl]
  exact (integrable_left_mul_right p mode n).const_mul (parallelSquareConstant mode)

private theorem integral_seriesSquareDescendants
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, seriesSquareDescendants mode n environment
        ∂environmentMeasure p) =
      2 * secondMoment p mode n + 2 * firstMoment p mode n ^ 2 := by
  have hleft := integrable_Z_sq_subtree p mode n [false]
  have hright := integrable_Z_sq_subtree p mode n [true]
  have hcross := integrable_left_mul_right p mode n
  rw [show seriesSquareDescendants mode n = fun environment ↦
      Z mode n (Environment.subtree [false] environment) ^ 2 +
        Z mode n (Environment.subtree [true] environment) ^ 2 +
          2 * (Z mode n (Environment.subtree [false] environment) *
            Z mode n (Environment.subtree [true] environment)) by
    funext environment
    simp only [seriesSquareDescendants]
    ring]
  change (∫ environment,
      (Z mode n (Environment.subtree [false] environment) ^ 2 +
        Z mode n (Environment.subtree [true] environment) ^ 2) +
          2 * (Z mode n (Environment.subtree [false] environment) *
            Z mode n (Environment.subtree [true] environment))
      ∂environmentMeasure p) =
    2 * secondMoment p mode n + 2 * firstMoment p mode n ^ 2
  calc
    (∫ environment,
        (Z mode n (Environment.subtree [false] environment) ^ 2 +
          Z mode n (Environment.subtree [true] environment) ^ 2) +
            2 * (Z mode n (Environment.subtree [false] environment) *
              Z mode n (Environment.subtree [true] environment))
        ∂environmentMeasure p) =
        (∫ environment,
          Z mode n (Environment.subtree [false] environment) ^ 2 +
            Z mode n (Environment.subtree [true] environment) ^ 2
          ∂environmentMeasure p) +
          ∫ environment,
            2 * (Z mode n (Environment.subtree [false] environment) *
              Z mode n (Environment.subtree [true] environment))
            ∂environmentMeasure p :=
      integral_add (hleft.add hright) (hcross.const_mul 2)
    _ = ((∫ environment, Z mode n (Environment.subtree [false] environment) ^ 2
            ∂environmentMeasure p) +
          ∫ environment, Z mode n (Environment.subtree [true] environment) ^ 2
            ∂environmentMeasure p) +
        2 * ∫ environment,
          Z mode n (Environment.subtree [false] environment) *
            Z mode n (Environment.subtree [true] environment)
          ∂environmentMeasure p := by
      rw [integral_add hleft hright, integral_const_mul]
    _ = 2 * secondMoment p mode n + 2 * firstMoment p mode n ^ 2 := by
      rw [integral_Z_sq_subtree p mode n [false],
        integral_Z_sq_subtree p mode n [true], integral_left_mul_right p mode n]
      ring

private theorem integral_parallelSquareBound
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, parallelSquareBound mode n environment
        ∂environmentMeasure p) =
      parallelSquareConstant mode * firstMoment p mode n ^ 2 := by
  rw [show parallelSquareBound mode n = fun environment ↦
      parallelSquareConstant mode *
        (Z mode n (Environment.subtree [false] environment) *
          Z mode n (Environment.subtree [true] environment)) by rfl,
    integral_const_mul, integral_left_mul_right p mode n]

private theorem rootTrue_seriesSquare_indep
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    rootTrueWeight ⟂ᵢ[environmentMeasure p] seriesSquareDescendants mode n := by
  have hrootMeasurable : Measurable (fun bit : Bool ↦ if bit then (1 : ℝ) else 0) :=
    measurable_of_finite _
  have hgate : Measurable (fun environments : Environment × Environment ↦
      (Z mode n environments.1 + Z mode n environments.2) ^ 2) :=
    (((measurable_Z mode n).comp measurable_fst).add
      ((measurable_Z mode n).comp measurable_snd)).pow_const 2
  have hindep := (root_subtrees_indep p).comp hrootMeasurable hgate
  have hrootEq : rootTrueWeight =
      (fun environment ↦ if coordinate root environment then (1 : ℝ) else 0) := by
    funext environment
    rfl
  have hgateEq : seriesSquareDescendants mode n = fun environment ↦
      (Z mode n (Environment.subtree [false] environment) +
        Z mode n (Environment.subtree [true] environment)) ^ 2 := by
    funext environment
    rfl
  rw [hrootEq, hgateEq]
  simpa only [Function.comp_def] using hindep

private theorem rootFalse_parallelSquare_indep
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    rootFalseWeight ⟂ᵢ[environmentMeasure p] parallelSquareBound mode n := by
  have hrootMeasurable : Measurable (fun bit : Bool ↦ if bit then (0 : ℝ) else 1) :=
    measurable_of_finite _
  have hgate : Measurable (fun environments : Environment × Environment ↦
      parallelSquareConstant mode *
        (Z mode n environments.1 * Z mode n environments.2)) :=
    measurable_const.mul
      (((measurable_Z mode n).comp measurable_fst).mul
        ((measurable_Z mode n).comp measurable_snd))
  have hindep := (root_subtrees_indep p).comp hrootMeasurable hgate
  have hrootEq : rootFalseWeight =
      (fun environment ↦ if coordinate root environment then (0 : ℝ) else 1) := by
    funext environment
    rfl
  have hgateEq : parallelSquareBound mode n = fun environment ↦
      parallelSquareConstant mode *
        (Z mode n (Environment.subtree [false] environment) *
          Z mode n (Environment.subtree [true] environment)) := by
    funext environment
    rfl
  rw [hrootEq, hgateEq]
  simpa only [Function.comp_def] using hindep

private theorem integral_rootTrue_mul_seriesSquare
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, rootTrueWeight environment *
        seriesSquareDescendants mode n environment ∂environmentMeasure p) =
      (p : ℝ) *
        (2 * secondMoment p mode n + 2 * firstMoment p mode n ^ 2) := by
  rw [(rootTrue_seriesSquare_indep p mode n).integral_fun_mul_eq_mul_integral
    measurable_rootTrueWeight.aestronglyMeasurable
    (measurable_seriesSquareDescendants mode n).aestronglyMeasurable,
    integral_rootTrueWeight p, integral_seriesSquareDescendants p mode n]

private theorem integral_rootFalse_mul_parallelSquare
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, rootFalseWeight environment *
        parallelSquareBound mode n environment ∂environmentMeasure p) =
      (1 - (p : ℝ)) *
        (parallelSquareConstant mode * firstMoment p mode n ^ 2) := by
  rw [(rootFalse_parallelSquare_indep p mode n).integral_fun_mul_eq_mul_integral
    measurable_rootFalseWeight.aestronglyMeasurable
    (measurable_parallelSquareBound mode n).aestronglyMeasurable,
    integral_rootFalseWeight p, integral_parallelSquareBound p mode n]

private theorem integrable_rootTrue_mul_seriesSquare
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ rootTrueWeight environment *
      seriesSquareDescendants mode n environment) (environmentMeasure p) := by
  have hindep := rootTrue_seriesSquare_indep p mode n
  change Integrable (rootTrueWeight * seriesSquareDescendants mode n)
    (environmentMeasure p)
  exact hindep.integrable_mul (integrable_rootTrueWeight p)
    (integrable_seriesSquareDescendants p mode n)

private theorem integrable_rootFalse_mul_parallelSquare
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ rootFalseWeight environment *
      parallelSquareBound mode n environment) (environmentMeasure p) := by
  have hindep := rootFalse_parallelSquare_indep p mode n
  change Integrable (rootFalseWeight * parallelSquareBound mode n) (environmentMeasure p)
  exact hindep.integrable_mul (integrable_rootFalseWeight p)
    (integrable_parallelSquareBound p mode n)

private theorem Z_succ_sq_le_weighted_bounds
    (mode : Mode) (n : ℕ) (environment : Environment) :
    Z mode (n + 1) environment ^ 2 ≤
      rootTrueWeight environment * seriesSquareDescendants mode n environment +
        rootFalseWeight environment * parallelSquareBound mode n environment := by
  rw [Z_succ]
  by_cases hroot : environment root
  · rw [if_pos hroot]
    simp [rootTrueWeight, rootFalseWeight, coordinate, hroot,
      seriesSquareDescendants, seriesGate]
  · rw [if_neg hroot]
    simpa [rootTrueWeight, rootFalseWeight, coordinate, hroot, parallelSquareBound] using
      parallelGate_sq_le mode
        (Z_pos mode n (Environment.subtree [false] environment))
        (Z_pos mode n (Environment.subtree [true] environment))

/-- The exact one-step second-moment estimate from the two root gates. -/
theorem secondMoment_succ_le (p : unitInterval) (mode : Mode) (n : ℕ) :
    secondMoment p mode (n + 1) ≤
      2 * (p : ℝ) * secondMoment p mode n +
        (2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode) *
          firstMoment p mode n ^ 2 := by
  have htrue := integrable_rootTrue_mul_seriesSquare p mode n
  have hfalse := integrable_rootFalse_mul_parallelSquare p mode n
  calc
    secondMoment p mode (n + 1) =
        ∫ environment, Z mode (n + 1) environment ^ 2 ∂environmentMeasure p := rfl
    _ ≤ ∫ environment,
          rootTrueWeight environment * seriesSquareDescendants mode n environment +
            rootFalseWeight environment * parallelSquareBound mode n environment
          ∂environmentMeasure p := by
      apply integral_mono (integrable_Z_sq p mode (n + 1)) (htrue.add hfalse)
      exact Z_succ_sq_le_weighted_bounds mode n
    _ = (∫ environment, rootTrueWeight environment *
            seriesSquareDescendants mode n environment ∂environmentMeasure p) +
          ∫ environment, rootFalseWeight environment *
            parallelSquareBound mode n environment ∂environmentMeasure p :=
      integral_add htrue hfalse
    _ = 2 * (p : ℝ) * secondMoment p mode n +
          (2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode) *
            firstMoment p mode n ^ 2 := by
      rw [integral_rootTrue_mul_seriesSquare,
        integral_rootFalse_mul_parallelSquare]
      ring

/-- The fixed point of the normalized second-moment affine recurrence. -/
noncomputable def secondMomentBoundConstant (p : unitInterval) (mode : Mode) : ℝ :=
  (2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode) /
    (2 * (p : ℝ) * (2 * (p : ℝ) - 1))

theorem secondMomentBoundConstant_eq (p : unitInterval) (mode : Mode) :
    secondMomentBoundConstant p mode =
      (2 * (p : ℝ) + (1 - (p : ℝ)) * (4 : ℝ) ^ (-mode.eta)) /
        (2 * (p : ℝ) * (2 * (p : ℝ) - 1)) := rfl

theorem normalizedSecondMoment_nonneg
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    0 ≤ normalizedSecondMoment p mode n := by
  rw [normalizedSecondMoment]
  exact div_nonneg (secondMoment_nonneg p mode n) (sq_nonneg _)

theorem secondMomentBoundConstant_pos
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) :
    0 < secondMomentBoundConstant p mode := by
  rw [secondMomentBoundConstant]
  have hp0 : 0 < (p : ℝ) := lt_trans (by norm_num) hp
  have hpGap : 0 < 2 * (p : ℝ) - 1 := by linarith
  have hnumerator :
      0 < 2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode := by
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hp0)
      (mul_nonneg (sub_nonneg.mpr p.2.2) (parallelSquareConstant_pos mode).le)
  exact div_pos hnumerator (mul_pos (mul_pos (by norm_num) hp0) hpGap)

theorem one_le_secondMomentBoundConstant
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) :
    1 ≤ secondMomentBoundConstant p mode := by
  rw [secondMomentBoundConstant]
  have hp0 : 0 < (p : ℝ) := lt_trans (by norm_num) hp
  have hpGap : 0 < 2 * (p : ℝ) - 1 := by linarith
  have hdenom : 0 < 2 * (p : ℝ) * (2 * (p : ℝ) - 1) :=
    mul_pos (mul_pos (by norm_num) hp0) hpGap
  rw [le_div_iff₀ hdenom]
  have hfactor :
      0 ≤ (1 - (p : ℝ)) * (4 * (p : ℝ) + parallelSquareConstant mode) :=
    mul_nonneg (sub_nonneg.mpr p.2.2)
      (add_nonneg (mul_nonneg (by norm_num) hp0.le)
        (parallelSquareConstant_pos mode).le)
  nlinarith

theorem secondMomentBoundConstant_fixedPoint
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) :
    secondMomentBoundConstant p mode =
      secondMomentBoundConstant p mode / (2 * (p : ℝ)) +
        (2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode) /
          (4 * (p : ℝ) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := (lt_trans (by norm_num) hp).ne'
  have hpGap : 2 * (p : ℝ) - 1 ≠ 0 := by linarith
  rw [secondMomentBoundConstant]
  field_simp
  ring

@[simp]
theorem secondMoment_zero (p : unitInterval) (mode : Mode) :
    secondMoment p mode 0 = 1 := by
  simp [secondMoment]

@[simp]
theorem normalizedSecondMoment_zero (p : unitInterval) (mode : Mode) :
    normalizedSecondMoment p mode 0 = 1 := by
  simp [normalizedSecondMoment, secondMoment, firstMoment]

/-- The normalized affine recurrence obtained from the first- and second-moment bounds. -/
theorem normalizedSecondMoment_succ_le
    (p : unitInterval) (mode : Mode) (n : ℕ) (hp : 0 < (p : ℝ)) :
    normalizedSecondMoment p mode (n + 1) ≤
      normalizedSecondMoment p mode n / (2 * (p : ℝ)) +
        (2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode) /
          (4 * (p : ℝ) ^ 2) := by
  let m := firstMoment p mode n
  let mnext := firstMoment p mode (n + 1)
  let q := secondMoment p mode n
  let qnext := secondMoment p mode (n + 1)
  let a := 2 * (p : ℝ) + (1 - (p : ℝ)) * parallelSquareConstant mode
  have hm : 0 < m := firstMoment_pos p mode n
  have hmnext : 0 < mnext := firstMoment_pos p mode (n + 1)
  have hlower : 2 * (p : ℝ) * m ≤ mnext := by
    simpa only [m, mnext] using firstMoment_succ_lower_bound p mode n
  have hsquare : (2 * (p : ℝ) * m) ^ 2 ≤ mnext ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) hp.le) hm.le) hmnext.le).2
      hlower
  have ha : 0 ≤ a := by
    exact add_nonneg (mul_nonneg (by norm_num) hp.le)
      (mul_nonneg (sub_nonneg.mpr p.2.2) (parallelSquareConstant_pos mode).le)
  have haffine : 0 ≤ q / m ^ 2 / (2 * (p : ℝ)) + a / (4 * (p : ℝ) ^ 2) := by
    exact add_nonneg
      (div_nonneg (div_nonneg (secondMoment_nonneg p mode n) (sq_nonneg m))
        (mul_nonneg (by norm_num) hp.le))
      (div_nonneg ha (mul_nonneg (by norm_num) (sq_nonneg (p : ℝ))))
  change qnext / mnext ^ 2 ≤
    q / m ^ 2 / (2 * (p : ℝ)) + a / (4 * (p : ℝ) ^ 2)
  rw [div_le_iff₀ (sq_pos_of_pos hmnext)]
  calc
    qnext ≤ 2 * (p : ℝ) * q + a * m ^ 2 := by
      simpa only [qnext, q, a, m] using secondMoment_succ_le p mode n
    _ = (q / m ^ 2 / (2 * (p : ℝ)) + a / (4 * (p : ℝ) ^ 2)) *
          (2 * (p : ℝ) * m) ^ 2 := by
      field_simp [hp.ne', hm.ne']
      ring
    _ ≤ (q / m ^ 2 / (2 * (p : ℝ)) + a / (4 * (p : ℝ) ^ 2)) *
          mnext ^ 2 := mul_le_mul_of_nonneg_left hsquare haffine

/-- For `p > 1 / 2`, all normalized second moments lie below the affine fixed point. -/
theorem normalizedSecondMoment_le_bound
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) (n : ℕ) :
    normalizedSecondMoment p mode n ≤ secondMomentBoundConstant p mode := by
  induction n with
  | zero =>
      simpa using one_le_secondMomentBoundConstant p mode hp
  | succ n ih =>
      have hp0 : 0 < (p : ℝ) := lt_trans (by norm_num) hp
      calc
        normalizedSecondMoment p mode (n + 1) ≤
            normalizedSecondMoment p mode n / (2 * (p : ℝ)) +
              (2 * (p : ℝ) +
                  (1 - (p : ℝ)) * parallelSquareConstant mode) /
                (4 * (p : ℝ) ^ 2) :=
          normalizedSecondMoment_succ_le p mode n hp0
        _ ≤ secondMomentBoundConstant p mode / (2 * (p : ℝ)) +
              (2 * (p : ℝ) +
                  (1 - (p : ℝ)) * parallelSquareConstant mode) /
                (4 * (p : ℝ) ^ 2) := by
          have hdenom : 0 ≤ 2 * (p : ℝ) := mul_nonneg (by norm_num) hp0.le
          exact add_le_add (div_le_div_of_nonneg_right ih hdenom) le_rfl
        _ = secondMomentBoundConstant p mode :=
          (secondMomentBoundConstant_fixedPoint p mode hp).symm

/-- Equivalent unnormalized uniform second-moment estimate. -/
theorem secondMoment_le_bound_mul_firstMoment_sq
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) (n : ℕ) :
    secondMoment p mode n ≤
      secondMomentBoundConstant p mode * firstMoment p mode n ^ 2 := by
  have hbound := normalizedSecondMoment_le_bound p mode hp n
  change secondMoment p mode n / firstMoment p mode n ^ 2 ≤
    secondMomentBoundConstant p mode at hbound
  exact (div_le_iff₀ (sq_pos_of_pos (firstMoment_pos p mode n))).mp hbound

theorem secondMoment_pos (p : unitInterval) (mode : Mode) (n : ℕ) :
    0 < secondMoment p mode n := by
  let lower := ((2 : ℝ) ^ n)⁻¹
  have hlowerPos : 0 < lower := by
    simp only [lower]
    positivity
  calc
    0 < lower ^ 2 := sq_pos_of_pos hlowerPos
    _ = ∫ _ : Environment, lower ^ 2 ∂environmentMeasure p := by simp
    _ ≤ ∫ environment, Z mode n environment ^ 2 ∂environmentMeasure p := by
      apply integral_mono (integrable_const _) (integrable_Z_sq p mode n)
      intro environment
      exact (sq_le_sq₀ hlowerPos.le (Z_pos mode n environment).le).2
        (Z_global_bounds mode n environment).1
    _ = secondMoment p mode n := rfl

private theorem integral_mul_sq_le_integral_sq_mul_integral_sq
    {alpha : Type*} [MeasurableSpace alpha] {μ : Measure alpha}
    (f g : alpha → ℝ)
    (hfSq : Integrable (fun x ↦ f x ^ 2) μ)
    (hgSq : Integrable (fun x ↦ g x ^ 2) μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hfSqPos : 0 < ∫ x, f x ^ 2 ∂μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  let A := ∫ x, f x ^ 2 ∂μ
  let B := ∫ x, g x ^ 2 ∂μ
  let C := ∫ x, f x * g x ∂μ
  have hquadEq : (fun x ↦ (A * g x - C * f x) ^ 2) = fun x ↦
      (A ^ 2 * g x ^ 2 + (-2 * A * C) * (f x * g x)) + C ^ 2 * f x ^ 2 := by
    funext x
    ring
  have hfirst : Integrable (fun x ↦ A ^ 2 * g x ^ 2) μ := hgSq.const_mul _
  have hmiddle : Integrable (fun x ↦ (-2 * A * C) * (f x * g x)) μ :=
    hfg.const_mul _
  have hlast : Integrable (fun x ↦ C ^ 2 * f x ^ 2) μ := hfSq.const_mul _
  have hintegral :
      (∫ x, (A * g x - C * f x) ^ 2 ∂μ) =
        (A ^ 2 * B + (-2 * A * C) * C) + C ^ 2 * A := by
    rw [hquadEq]
    calc
      (∫ x,
          (A ^ 2 * g x ^ 2 + (-2 * A * C) * (f x * g x)) +
            C ^ 2 * f x ^ 2 ∂μ) =
          (∫ x, A ^ 2 * g x ^ 2 + (-2 * A * C) * (f x * g x) ∂μ) +
            ∫ x, C ^ 2 * f x ^ 2 ∂μ :=
        integral_add (hfirst.add hmiddle) hlast
      _ = ((∫ x, A ^ 2 * g x ^ 2 ∂μ) +
            ∫ x, (-2 * A * C) * (f x * g x) ∂μ) +
          ∫ x, C ^ 2 * f x ^ 2 ∂μ := by
        rw [integral_add hfirst hmiddle]
      _ = (A ^ 2 * B + (-2 * A * C) * C) + C ^ 2 * A := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hnonneg : 0 ≤ ∫ x, (A * g x - C * f x) ^ 2 ∂μ :=
    integral_nonneg fun x ↦ sq_nonneg (A * g x - C * f x)
  rw [hintegral] at hnonneg
  change C ^ 2 ≤ A * B
  have hA : 0 < A := hfSqPos
  nlinarith

/-- The event that `Z_n` is at least one half of its first moment. -/
noncomputable def halfMeanEvent
    (p : unitInterval) (mode : Mode) (n : ℕ) : Set Environment :=
  {environment | firstMoment p mode n / 2 ≤ Z mode n environment}

theorem measurableSet_halfMeanEvent
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    MeasurableSet (halfMeanEvent p mode n) := by
  exact measurableSet_le measurable_const (measurable_Z mode n)

private noncomputable def halfMeanTruncation
    (p : unitInterval) (mode : Mode) (n : ℕ) : Environment → ℝ :=
  (halfMeanEvent p mode n).indicator (Z mode n)

private theorem integrable_halfMeanTruncation
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (halfMeanTruncation p mode n) (environmentMeasure p) := by
  exact (integrable_Z p mode n).indicator (measurableSet_halfMeanEvent p mode n)

private theorem Z_le_halfMean_add_truncation
    (p : unitInterval) (mode : Mode) (n : ℕ) (environment : Environment) :
    Z mode n environment ≤ firstMoment p mode n / 2 +
      halfMeanTruncation p mode n environment := by
  by_cases hmem : environment ∈ halfMeanEvent p mode n
  · rw [halfMeanTruncation, Set.indicator_of_mem hmem]
    linarith [firstMoment_pos p mode n]
  · rw [halfMeanTruncation, Set.indicator_of_notMem hmem, add_zero]
    simp only [halfMeanEvent, Set.mem_setOf_eq] at hmem
    exact le_of_lt (lt_of_not_ge hmem)

private theorem half_firstMoment_le_integral_truncation
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    firstMoment p mode n / 2 ≤
      ∫ environment, halfMeanTruncation p mode n environment ∂environmentMeasure p := by
  have htrunc := integrable_halfMeanTruncation p mode n
  have hmono : firstMoment p mode n ≤
      ∫ environment,
        firstMoment p mode n / 2 + halfMeanTruncation p mode n environment
        ∂environmentMeasure p := by
    calc
      firstMoment p mode n =
          ∫ environment, Z mode n environment ∂environmentMeasure p := rfl
      _ ≤ ∫ environment,
            firstMoment p mode n / 2 + halfMeanTruncation p mode n environment
            ∂environmentMeasure p := by
        apply integral_mono (integrable_Z p mode n) ((integrable_const _).add htrunc)
        exact Z_le_halfMean_add_truncation p mode n
  have hadd :
      (∫ environment,
          firstMoment p mode n / 2 + halfMeanTruncation p mode n environment
          ∂environmentMeasure p) =
        (∫ _ : Environment, firstMoment p mode n / 2 ∂environmentMeasure p) +
          ∫ environment, halfMeanTruncation p mode n environment
            ∂environmentMeasure p :=
    integral_add (integrable_const _) htrunc
  rw [hadd] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  linarith

private theorem integral_truncation_sq_le_secondMoment_mul_probability
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, halfMeanTruncation p mode n environment
        ∂environmentMeasure p) ^ 2 ≤
      secondMoment p mode n * (environmentMeasure p).real (halfMeanEvent p mode n) := by
  let indicator : Environment → ℝ :=
    (halfMeanEvent p mode n).indicator (fun _ ↦ 1)
  have hevent := measurableSet_halfMeanEvent p mode n
  have hindicator : Integrable indicator (environmentMeasure p) := by
    exact (integrable_const 1).indicator hevent
  have hindicatorSqEq : (fun environment ↦ indicator environment ^ 2) = indicator := by
    funext environment
    by_cases hmem : environment ∈ halfMeanEvent p mode n <;>
      simp [indicator, hmem]
  have hindicatorSq : Integrable (fun environment ↦ indicator environment ^ 2)
      (environmentMeasure p) := by
    rw [hindicatorSqEq]
    exact hindicator
  have hproductEq :
      (fun environment ↦ Z mode n environment * indicator environment) =
        halfMeanTruncation p mode n := by
    funext environment
    by_cases hmem : environment ∈ halfMeanEvent p mode n <;>
      simp [indicator, halfMeanTruncation, hmem]
  have hproduct : Integrable (fun environment ↦ Z mode n environment *
      indicator environment) (environmentMeasure p) := by
    rw [hproductEq]
    exact integrable_halfMeanTruncation p mode n
  have hcs := integral_mul_sq_le_integral_sq_mul_integral_sq
    (Z mode n) indicator (integrable_Z_sq p mode n) hindicatorSq hproduct
    (by simpa only [secondMoment] using secondMoment_pos p mode n)
  have hindicatorIntegral :
      (∫ environment, indicator environment ∂environmentMeasure p) =
        (environmentMeasure p).real (halfMeanEvent p mode n) := by
    have hindicatorEq : indicator =
        (halfMeanEvent p mode n).indicator (1 : Environment → ℝ) := by
      funext environment
      rfl
    rw [hindicatorEq]
    exact integral_indicator_one hevent
  rw [hproductEq, hindicatorSqEq, hindicatorIntegral] at hcs
  simpa only [secondMoment] using hcs

/-- Paley--Zygmund at threshold `1 / 2`, using the uniform fixed-point bound. -/
theorem paleyZygmund_half
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) (n : ℕ) :
    1 / (4 * secondMomentBoundConstant p mode) ≤
      (environmentMeasure p).real (halfMeanEvent p mode n) := by
  let m := firstMoment p mode n
  let q := secondMoment p mode n
  let K := secondMomentBoundConstant p mode
  let probability := (environmentMeasure p).real (halfMeanEvent p mode n)
  let truncatedMean :=
    ∫ environment, halfMeanTruncation p mode n environment ∂environmentMeasure p
  have hm : 0 < m := firstMoment_pos p mode n
  have hK : 0 < K := secondMomentBoundConstant_pos p mode hp
  have hprobability : 0 ≤ probability := measureReal_nonneg
  have hhalf : m / 2 ≤ truncatedMean := by
    simpa only [m, truncatedMean] using half_firstMoment_le_integral_truncation p mode n
  have htruncatedMean : 0 ≤ truncatedMean :=
    le_trans (div_nonneg hm.le (by norm_num)) hhalf
  have hsquares : (m / 2) ^ 2 ≤ truncatedMean ^ 2 :=
    (sq_le_sq₀ (div_nonneg hm.le (by norm_num)) htruncatedMean).2 hhalf
  have hcs : truncatedMean ^ 2 ≤ q * probability := by
    simpa only [truncatedMean, q, probability] using
      integral_truncation_sq_le_secondMoment_mul_probability p mode n
  have hfirst : (m / 2) ^ 2 ≤ q * probability := hsquares.trans hcs
  have hqBound : q ≤ K * m ^ 2 := by
    simpa only [q, K, m] using secondMoment_le_bound_mul_firstMoment_sq p mode hp n
  have hproduct : q * probability ≤ (K * m ^ 2) * probability :=
    mul_le_mul_of_nonneg_right hqBound hprobability
  have hmain : m ^ 2 / 4 ≤ (K * m ^ 2) * probability := by
    calc
      m ^ 2 / 4 = (m / 2) ^ 2 := by ring
      _ ≤ q * probability := hfirst
      _ ≤ (K * m ^ 2) * probability := hproduct
  have hscaled : (1 : ℝ) / 4 ≤ K * probability := by
    calc
      (1 : ℝ) / 4 = (m ^ 2 / 4) / m ^ 2 := by
        field_simp [hm.ne']
      _ ≤ ((K * m ^ 2) * probability) / m ^ 2 :=
        div_le_div_of_nonneg_right hmain (sq_nonneg m)
      _ = K * probability := by
        field_simp [hm.ne']
  change 1 / (4 * K) ≤ probability
  rw [div_le_iff₀ (mul_pos (by norm_num) hK)]
  nlinarith

/-- Source-facing event form of the threshold-one-half Paley--Zygmund estimate. -/
theorem paleyZygmund_half_probability_lower_bound
    (p : unitInterval) (mode : Mode) (hp : 1 / 2 < (p : ℝ)) (n : ℕ) :
    1 / (4 * secondMomentBoundConstant p mode) ≤
      (environmentMeasure p).real
        {environment | firstMoment p mode n / 2 ≤ Z mode n environment} := by
  simpa only [halfMeanEvent] using paleyZygmund_half p mode hp n

end SeriesParallel.MainText
