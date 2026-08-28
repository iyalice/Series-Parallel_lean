/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.StructuralProperties

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic

/-!
# The logarithmic drift identity

This module upgrades the samplewise logarithmic recursion to an exact law under the canonical
Bernoulli environment and proves the source drift identity.  The independent copy is realized by
the depth-one left and right subtrees in the common environment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SeriesParallel.MainText

/-- The non-root word obtained by adjoining a first left/right bit. -/
private def nonRootWord (q : Bool × Word) : Word := q.1 :: q.2

private theorem nonRootWord_injective : Function.Injective nonRootWord := by
  rintro ⟨b, u⟩ ⟨c, v⟩ h
  simp only [nonRootWord, List.cons.injEq] at h
  exact Prod.ext h.1 h.2

/-- The root coordinate is independent of the joint process of all non-root coordinates. -/
private theorem root_descendantCoordinates_indep (p : unitInterval) :
    coordinate root ⟂ᵢ[environmentMeasure p]
      (fun environment q ↦ coordinate (nonRootWord q) environment) := by
  apply IndepFun.indepFun_process (measurable_coordinate root)
    (fun q ↦ measurable_coordinate (nonRootWord q))
  intro I
  let T : Finset Word := I.image nonRootWord
  have hdisjoint : Disjoint ({root} : Finset Word) T := by
    rw [Finset.disjoint_left]
    intro w hwRoot hwT
    rw [Finset.mem_singleton] at hwRoot
    subst w
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hwT
    simp [root, nonRootWord] at hq
  have hcoordinates := (coordinates_iIndep p).indepFun_finset
    ({root} : Finset Word) T hdisjoint measurable_coordinate
  let selectRoot : ((w : ({root} : Finset Word)) → Bool) → Bool :=
    fun values ↦ values ⟨root, Finset.mem_singleton_self root⟩
  let includeDescendant (q : I) : T :=
    ⟨nonRootWord q.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩
  let selectDescendants : ((w : T) → Bool) → ((q : I) → Bool) :=
    fun values q ↦ values (includeDescendant q)
  have hselectRoot : Measurable selectRoot := measurable_pi_apply _
  have hselectDescendants : Measurable selectDescendants :=
    measurable_pi_iff.mpr fun q ↦ measurable_pi_apply (includeDescendant q)
  change (fun environment ↦ environment root) ⟂ᵢ[environmentMeasure p]
    (fun environment (q : I) ↦ environment (nonRootWord q.1))
  simpa [selectRoot, selectDescendants, includeDescendant, coordinate, Function.comp_def] using
    hcoordinates.comp hselectRoot hselectDescendants

/-- The root choice is independent of the pair of complete descendant environments. -/
theorem root_subtrees_indep (p : unitInterval) :
    coordinate root ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        (Environment.subtree [false] environment, Environment.subtree [true] environment)) := by
  let collectSubtrees : ((Bool × Word) → Bool) → Environment × Environment :=
    fun values ↦ (fun word ↦ values (false, word), fun word ↦ values (true, word))
  have hcollect : Measurable collectSubtrees := by
    apply Measurable.prod
    · exact measurable_pi_iff.mpr fun word ↦ measurable_pi_apply (false, word)
    · exact measurable_pi_iff.mpr fun word ↦ measurable_pi_apply (true, word)
  change coordinate root ⟂ᵢ[environmentMeasure p]
    (fun environment ↦
      ((fun word ↦ environment (false :: word)), fun word ↦ environment (true :: word)))
  simpa [collectSubtrees, nonRootWord, coordinate, Function.comp_def] using
    (root_descendantCoordinates_indep p).comp measurable_id hcollect

/-- The two depth-`n` logarithmic descendants are independent copies. -/
theorem left_right_X_indep (p : unitInterval) (mode : Mode) (n : ℕ) :
    (fun environment ↦ X mode n (Environment.subtree [false] environment))
      ⟂ᵢ[environmentMeasure p]
    (fun environment ↦ X mode n (Environment.subtree [true] environment)) := by
  simpa [X, Function.comp_def] using
    (left_right_Z_indep p mode n).comp Real.measurable_log Real.measurable_log

/-- The root choice is independent of the ordered pair of logarithmic descendants. -/
theorem root_left_right_X_indep (p : unitInterval) (mode : Mode) (n : ℕ) :
    coordinate root ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        (X mode n (Environment.subtree [false] environment),
          X mode n (Environment.subtree [true] environment))) := by
  have hpair : Measurable (fun environments : Environment × Environment ↦
      (X mode n environments.1, X mode n environments.2)) :=
    ((measurable_X mode n).comp measurable_fst).prod
      ((measurable_X mode n).comp measurable_snd)
  simpa [Function.comp_def] using (root_subtrees_indep p).comp measurable_id hpair

/-- The depth-`n` logarithmic variable has its canonical pushforward law. -/
theorem X_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw (X mode n) ((environmentMeasure p).map (X mode n)) (environmentMeasure p) :=
  ⟨(measurable_X mode n).aemeasurable, rfl⟩

/-- The left logarithmic descendant has the original depth-`n` law. -/
theorem left_X_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw (fun environment ↦ X mode n (Environment.subtree [false] environment))
      ((environmentMeasure p).map (X mode n)) (environmentMeasure p) := by
  simpa [Environment.subtree, Function.comp_def] using
    (X_hasLaw p mode n).comp (subtreeShift_hasLaw p [false])

/-- The right logarithmic descendant has the original depth-`n` law. -/
theorem right_X_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw (fun environment ↦ X mode n (Environment.subtree [true] environment))
      ((environmentMeasure p).map (X mode n)) (environmentMeasure p) := by
  simpa [Environment.subtree, Function.comp_def] using
    (X_hasLaw p mode n).comp (subtreeShift_hasLaw p [true])

/-- The ordered descendant pair has the product of two copies of the depth-`n` law. -/
theorem left_right_X_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw
      (fun environment ↦
        (X mode n (Environment.subtree [false] environment),
          X mode n (Environment.subtree [true] environment)))
      (((environmentMeasure p).map (X mode n)).prod
        ((environmentMeasure p).map (X mode n)))
      (environmentMeasure p) := by
  have hleft : Measurable
      (fun environment ↦ X mode n (Environment.subtree [false] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [false])
  have hright : Measurable
      (fun environment ↦ X mode n (Environment.subtree [true] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [true])
  refine ⟨(hleft.prod hright).aemeasurable, ?_⟩
  rw [(left_right_X_indep p mode n).map_prod_eq_prod_map_map
    hleft.aemeasurable hright.aemeasurable, (left_X_hasLaw p mode n).map_eq,
    (right_X_hasLaw p mode n).map_eq]

/-- The root and the two logarithmic descendants have Bernoulli-times-product law. -/
theorem root_left_right_X_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw
      (fun environment ↦
        (coordinate root environment,
          (X mode n (Environment.subtree [false] environment),
            X mode n (Environment.subtree [true] environment))))
      ((bernoulliBool p).prod
        (((environmentMeasure p).map (X mode n)).prod
          ((environmentMeasure p).map (X mode n))))
      (environmentMeasure p) := by
  have hroot := measurable_coordinate root
  have hleft : Measurable
      (fun environment ↦ X mode n (Environment.subtree [false] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [false])
  have hright : Measurable
      (fun environment ↦ X mode n (Environment.subtree [true] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [true])
  have hpair : Measurable (fun environment ↦
      (X mode n (Environment.subtree [false] environment),
        X mode n (Environment.subtree [true] environment))) :=
    hleft.prod hright
  refine ⟨(hroot.prod hpair).aemeasurable, ?_⟩
  rw [(root_left_right_X_indep p mode n).map_prod_eq_prod_map_map
    hroot.aemeasurable hpair.aemeasurable, (coordinate_hasLaw p root).map_eq,
    (left_right_X_hasLaw p mode n).map_eq]

private theorem measurable_logSeriesGate_pair :
    Measurable (fun values : ℝ × ℝ ↦ logSeriesGate values.1 values.2) := by
  simp only [logSeriesGate]
  fun_prop

private theorem measurable_logParallelGate_pair (mode : Mode) :
    Measurable (fun values : ℝ × ℝ ↦ logParallelGate mode values.1 values.2) := by
  cases mode with
  | distance =>
      simp only [logParallelGate]
      fun_prop
  | resistance =>
      simp only [logParallelGate]
      fun_prop

private theorem measurable_logRecursionGate (mode : Mode) :
    Measurable (fun values : Bool × (ℝ × ℝ) ↦
      if values.1 then logSeriesGate values.2.1 values.2.2
      else logParallelGate mode values.2.1 values.2.2) := by
  have htrue : MeasurableSet {values : Bool × (ℝ × ℝ) | values.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  exact Measurable.ite htrue
    (measurable_logSeriesGate_pair.comp measurable_snd)
    ((measurable_logParallelGate_pair mode).comp measurable_snd)

/-- Exact law form of the unified logarithmic RDE, with canonical independent copies. -/
theorem X_succ_hasLaw (p : unitInterval) (mode : Mode) (n : ℕ) :
    HasLaw (X mode (n + 1))
      (((bernoulliBool p).prod
        (((environmentMeasure p).map (X mode n)).prod
          ((environmentMeasure p).map (X mode n)))).map
        (fun values : Bool × (ℝ × ℝ) ↦
          if values.1 then logSeriesGate values.2.1 values.2.2
          else logParallelGate mode values.2.1 values.2.2))
      (environmentMeasure p) := by
  let triple : Environment → Bool × (ℝ × ℝ) := fun environment ↦
    (coordinate root environment,
      (X mode n (Environment.subtree [false] environment),
        X mode n (Environment.subtree [true] environment)))
  let gate : Bool × (ℝ × ℝ) → ℝ := fun values ↦
    if values.1 then logSeriesGate values.2.1 values.2.2
    else logParallelGate mode values.2.1 values.2.2
  have htriple := root_left_right_X_hasLaw p mode n
  have hgate : Measurable gate := measurable_logRecursionGate mode
  have hgateLaw : HasLaw gate
      (((bernoulliBool p).prod
        (((environmentMeasure p).map (X mode n)).prod
          ((environmentMeasure p).map (X mode n)))).map gate)
      ((bernoulliBool p).prod
        (((environmentMeasure p).map (X mode n)).prod
          ((environmentMeasure p).map (X mode n)))) :=
    ⟨hgate.aemeasurable, rfl⟩
  have hcomp := hgateLaw.comp htriple
  apply hcomp.congr
  filter_upwards with environment
  rw [X_succ]
  rfl

private theorem weighted_log_gates (p : unitInterval) (mode : Mode) (x y : ℝ) :
    (p : ℝ) * logSeriesGate x y + (1 - (p : ℝ)) * logParallelGate mode x y =
      (x + y) / 2 + ((p : ℝ) - 1 / 2) * |x - y| +
        ((p : ℝ) - mode.eta * (1 - (p : ℝ))) * h |x - y| := by
  rw [logSeriesGate_eq_max_add_h, logParallelGate_eq_min_sub_h]
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [max_eq_left hyx, min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

private theorem integrable_left_X (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ X mode n (Environment.subtree [false] environment))
      (environmentMeasure p) := by
  simpa [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p [false]).integrable_comp_of_integrable
      (integrable_X p mode n)

private theorem integrable_right_X (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦ X mode n (Environment.subtree [true] environment))
      (environmentMeasure p) := by
  simpa [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p [true]).integrable_comp_of_integrable
      (integrable_X p mode n)

private theorem integrable_h_abs_descendant_sub (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦
      h |X mode n (Environment.subtree [false] environment) -
        X mode n (Environment.subtree [true] environment)|) (environmentMeasure p) := by
  have hleft : Measurable
      (fun environment ↦ X mode n (Environment.subtree [false] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [false])
  have hright : Measurable
      (fun environment ↦ X mode n (Environment.subtree [true] environment)) :=
    (measurable_X mode n).comp (measurable_subtreeShift [true])
  have hgap : Measurable (fun environment ↦
      |X mode n (Environment.subtree [false] environment) -
        X mode n (Environment.subtree [true] environment)|) :=
    continuous_abs.measurable.comp (hleft.sub hright)
  have hmeas : Measurable (fun environment ↦
      h |X mode n (Environment.subtree [false] environment) -
        X mode n (Environment.subtree [true] environment)|) := by
    simp only [h]
    exact Real.measurable_log.comp
      (measurable_const.add (Real.measurable_exp.comp hgap.neg))
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.log 2) ?_
  filter_upwards with environment
  rw [Real.norm_eq_abs, abs_of_nonneg (h_nonneg _)]
  exact h_le_log_two (abs_nonneg _)

private theorem integrable_series_descendants (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦
      logSeriesGate (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) (environmentMeasure p) := by
  rw [show (fun environment ↦
      logSeriesGate (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) =
      (fun environment ↦
        max (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) +
            h |X mode n (Environment.subtree [false] environment) -
              X mode n (Environment.subtree [true] environment)|) by
        funext environment
        exact logSeriesGate_eq_max_add_h _ _]
  exact (integrable_left_X p mode n).sup (integrable_right_X p mode n) |>.add
    (integrable_h_abs_descendant_sub p mode n)

private theorem integrable_parallel_descendants (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (fun environment ↦
      logParallelGate mode (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) (environmentMeasure p) := by
  rw [show (fun environment ↦
      logParallelGate mode (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) =
      (fun environment ↦
        min (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) -
            mode.eta * h |X mode n (Environment.subtree [false] environment) -
              X mode n (Environment.subtree [true] environment)|) by
        funext environment
        exact logParallelGate_eq_min_sub_h mode _ _]
  exact (integrable_left_X p mode n).inf (integrable_right_X p mode n) |>.sub
    ((integrable_h_abs_descendant_sub p mode n).const_mul mode.eta)

private def rootTrueWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 1 else 0

private def rootFalseWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 0 else 1

private theorem measurable_rootTrueWeight : Measurable rootTrueWeight := by
  exact (measurable_of_finite (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
    (measurable_coordinate root)

private theorem measurable_rootFalseWeight : Measurable rootFalseWeight := by
  exact (measurable_of_finite (fun b : Bool ↦ if b then (0 : ℝ) else 1)).comp
    (measurable_coordinate root)

private theorem integral_rootTrueWeight (p : unitInterval) :
    ∫ environment, rootTrueWeight environment ∂environmentMeasure p = (p : ℝ) := by
  let s : Set Environment := {environment | coordinate root environment = true}
  have hs : MeasurableSet s :=
    (measurableSet_singleton true).preimage (measurable_coordinate root)
  have hfun : rootTrueWeight = s.indicator 1 := by
    funext environment
    by_cases hroot : coordinate root environment
    · simp [rootTrueWeight, s, hroot]
    · simp [rootTrueWeight, s, hroot]
  rw [hfun, integral_indicator_one hs]
  have hmeasure : (environmentMeasure p).real s =
      (bernoulliBool p).real {b | b = true} := by
    simpa only [s] using (coordinate_hasLaw p root).measureReal_eq
      (p := fun b ↦ b = true) (measurableSet_singleton true)
  calc
    (environmentMeasure p).real s = (bernoulliBool p).real {b | b = true} := hmeasure
    _ = (bernoulliBool p).real {true} := by
      congr 1
    _ = (p : ℝ) := bernoulliBool_real_true p

private theorem integral_rootFalseWeight (p : unitInterval) :
    ∫ environment, rootFalseWeight environment ∂environmentMeasure p = 1 - (p : ℝ) := by
  let s : Set Environment := {environment | coordinate root environment = false}
  have hs : MeasurableSet s :=
    (measurableSet_singleton false).preimage (measurable_coordinate root)
  have hfun : rootFalseWeight = s.indicator 1 := by
    funext environment
    by_cases hroot : coordinate root environment
    · simp [rootFalseWeight, s, hroot]
    · simp [rootFalseWeight, s, hroot]
  rw [hfun, integral_indicator_one hs]
  have hmeasure : (environmentMeasure p).real s =
      (bernoulliBool p).real {b | b = false} := by
    simpa only [s] using (coordinate_hasLaw p root).measureReal_eq
      (p := fun b ↦ b = false) (measurableSet_singleton false)
  calc
    (environmentMeasure p).real s = (bernoulliBool p).real {b | b = false} := hmeasure
    _ = (bernoulliBool p).real {false} := by
      congr 1
    _ = 1 - (p : ℝ) := bernoulliBool_real_false p

private theorem rootTrue_series_indep (p : unitInterval) (mode : Mode) (n : ℕ) :
    rootTrueWeight ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        logSeriesGate (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment))) := by
  change (fun environment ↦ if coordinate root environment then (1 : ℝ) else 0)
    ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        logSeriesGate (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)))
  simpa only [Function.comp_def] using (root_left_right_X_indep p mode n).comp
    (measurable_of_finite (fun b : Bool ↦ if b then (1 : ℝ) else 0))
    measurable_logSeriesGate_pair

private theorem rootFalse_parallel_indep (p : unitInterval) (mode : Mode) (n : ℕ) :
    rootFalseWeight ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        logParallelGate mode (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment))) := by
  change (fun environment ↦ if coordinate root environment then (0 : ℝ) else 1)
    ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        logParallelGate mode (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)))
  simpa only [Function.comp_def] using (root_left_right_X_indep p mode n).comp
    (measurable_of_finite (fun b : Bool ↦ if b then (0 : ℝ) else 1))
    (measurable_logParallelGate_pair mode)

private theorem integral_rootTrue_mul_series (p : unitInterval) (mode : Mode) (n : ℕ) :
    ∫ environment, rootTrueWeight environment *
        logSeriesGate (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p =
      (p : ℝ) * ∫ environment,
        logSeriesGate (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p := by
  have hpair : Measurable (fun environment ↦
      (X mode n (Environment.subtree [false] environment),
        X mode n (Environment.subtree [true] environment))) :=
    ((measurable_X mode n).comp (measurable_subtreeShift [false])).prod
      ((measurable_X mode n).comp (measurable_subtreeShift [true]))
  rw [(rootTrue_series_indep p mode n).integral_fun_mul_eq_mul_integral
    measurable_rootTrueWeight.aestronglyMeasurable
    (measurable_logSeriesGate_pair.comp hpair).aestronglyMeasurable,
    integral_rootTrueWeight]

private theorem integral_rootFalse_mul_parallel
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    ∫ environment, rootFalseWeight environment *
        logParallelGate mode (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p =
      (1 - (p : ℝ)) * ∫ environment,
        logParallelGate mode (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p := by
  have hpair : Measurable (fun environment ↦
      (X mode n (Environment.subtree [false] environment),
        X mode n (Environment.subtree [true] environment))) :=
    ((measurable_X mode n).comp (measurable_subtreeShift [false])).prod
      ((measurable_X mode n).comp (measurable_subtreeShift [true]))
  rw [(rootFalse_parallel_indep p mode n).integral_fun_mul_eq_mul_integral
    measurable_rootFalseWeight.aestronglyMeasurable
    ((measurable_logParallelGate_pair mode).comp hpair).aestronglyMeasurable,
    integral_rootFalseWeight]

private theorem integral_X_succ_eq_weighted_gates
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    ∫ environment, X mode (n + 1) environment ∂environmentMeasure p =
      (p : ℝ) * ∫ environment,
        logSeriesGate (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p +
      (1 - (p : ℝ)) * ∫ environment,
        logParallelGate mode (X mode n (Environment.subtree [false] environment))
          (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p := by
  have htrueBound : ∀ᵐ environment ∂environmentMeasure p,
      ‖rootTrueWeight environment‖ ≤ (1 : ℝ) := Filter.Eventually.of_forall fun environment ↦ by
    simp only [rootTrueWeight]
    split <;> norm_num
  have hfalseBound : ∀ᵐ environment ∂environmentMeasure p,
      ‖rootFalseWeight environment‖ ≤ (1 : ℝ) := Filter.Eventually.of_forall fun environment ↦ by
    simp only [rootFalseWeight]
    split <;> norm_num
  have htrueIntegrable : Integrable (fun environment ↦ rootTrueWeight environment *
      logSeriesGate (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) (environmentMeasure p) :=
    (integrable_series_descendants p mode n).bdd_mul
      measurable_rootTrueWeight.aestronglyMeasurable htrueBound
  have hfalseIntegrable : Integrable (fun environment ↦ rootFalseWeight environment *
      logParallelGate mode (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))) (environmentMeasure p) :=
    (integrable_parallel_descendants p mode n).bdd_mul
      measurable_rootFalseWeight.aestronglyMeasurable hfalseBound
  calc
    ∫ environment, X mode (n + 1) environment ∂environmentMeasure p =
        ∫ environment,
          (rootTrueWeight environment *
              logSeriesGate (X mode n (Environment.subtree [false] environment))
                (X mode n (Environment.subtree [true] environment)) +
            rootFalseWeight environment *
              logParallelGate mode (X mode n (Environment.subtree [false] environment))
                (X mode n (Environment.subtree [true] environment)))
          ∂environmentMeasure p := by
      apply integral_congr_ae
      filter_upwards with environment
      rw [X_succ]
      by_cases hroot : coordinate root environment
      · change environment root = true at hroot
        simp [rootTrueWeight, rootFalseWeight, coordinate, hroot]
      · change ¬environment root = true at hroot
        simp [rootTrueWeight, rootFalseWeight, coordinate, hroot]
    _ = (∫ environment, rootTrueWeight environment *
          logSeriesGate (X mode n (Environment.subtree [false] environment))
            (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p) +
        ∫ environment, rootFalseWeight environment *
          logParallelGate mode (X mode n (Environment.subtree [false] environment))
            (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p :=
      integral_add htrueIntegrable hfalseIntegrable
    _ = _ := by
      rw [integral_rootTrue_mul_series, integral_rootFalse_mul_parallel]

private theorem integral_left_X_eq (p : unitInterval) (mode : Mode) (n : ℕ) :
    ∫ environment, X mode n (Environment.subtree [false] environment)
        ∂environmentMeasure p =
      ∫ environment, X mode n environment ∂environmentMeasure p := by
  exact (left_X_hasLaw p mode n).integral_eq.trans (X_hasLaw p mode n).integral_eq.symm

private theorem integral_right_X_eq (p : unitInterval) (mode : Mode) (n : ℕ) :
    ∫ environment, X mode n (Environment.subtree [true] environment)
        ∂environmentMeasure p =
      ∫ environment, X mode n environment ∂environmentMeasure p := by
  exact (right_X_hasLaw p mode n).integral_eq.trans (X_hasLaw p mode n).integral_eq.symm

/-- `lem:logarithmic-drift`: the exact mean drift, with the independent copy realized by the
left and right depth-one subtrees. -/
theorem logarithmic_drift (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, X mode (n + 1) environment ∂environmentMeasure p) -
        ∫ environment, X mode n environment ∂environmentMeasure p =
      ((p : ℝ) - 1 / 2) *
          ∫ environment,
            |X mode n (Environment.subtree [false] environment) -
              X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p +
        ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
          ∫ environment,
            h |X mode n (Environment.subtree [false] environment) -
              X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p := by
  have hleft := integrable_left_X p mode n
  have hright := integrable_right_X p mode n
  have habs : Integrable (fun environment ↦
      |X mode n (Environment.subtree [false] environment) -
        X mode n (Environment.subtree [true] environment)|) (environmentMeasure p) :=
    (hleft.sub hright).abs
  have hcorrection := integrable_h_abs_descendant_sub p mode n
  have hseries := integrable_series_descendants p mode n
  have hparallel := integrable_parallel_descendants p mode n
  have hseriesScaled := hseries.const_mul (p : ℝ)
  have hparallelScaled := hparallel.const_mul (1 - (p : ℝ))
  have hmean : Integrable (fun environment ↦
      (X mode n (Environment.subtree [false] environment) +
        X mode n (Environment.subtree [true] environment)) / 2) (environmentMeasure p) :=
    (hleft.add hright).div_const 2
  have habsScaled := habs.const_mul ((p : ℝ) - 1 / 2)
  have hcorrectionScaled := hcorrection.const_mul
    ((p : ℝ) - mode.eta * (1 - (p : ℝ)))
  have hsplitOuter :
      (∫ environment,
          ((X mode n (Environment.subtree [false] environment) +
              X mode n (Environment.subtree [true] environment)) / 2 +
            ((p : ℝ) - 1 / 2) *
              |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)|) +
            ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
              h |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)|
          ∂environmentMeasure p) =
        (∫ environment,
          (X mode n (Environment.subtree [false] environment) +
              X mode n (Environment.subtree [true] environment)) / 2 +
            ((p : ℝ) - 1 / 2) *
              |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)|
          ∂environmentMeasure p) +
        ∫ environment, ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
          h |X mode n (Environment.subtree [false] environment) -
            X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p := by
    simpa only [Pi.add_apply] using
      integral_add (hmean.add habsScaled) hcorrectionScaled
  have hsplitInner :
      (∫ environment,
          (X mode n (Environment.subtree [false] environment) +
              X mode n (Environment.subtree [true] environment)) / 2 +
            ((p : ℝ) - 1 / 2) *
              |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)|
          ∂environmentMeasure p) =
        (∫ environment,
          (X mode n (Environment.subtree [false] environment) +
            X mode n (Environment.subtree [true] environment)) / 2
          ∂environmentMeasure p) +
        ∫ environment, ((p : ℝ) - 1 / 2) *
          |X mode n (Environment.subtree [false] environment) -
            X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p := by
    simpa only [Pi.add_apply] using integral_add hmean habsScaled
  have hmeanEvaluation :
      (∫ environment,
        (X mode n (Environment.subtree [false] environment) +
          X mode n (Environment.subtree [true] environment)) / 2
        ∂environmentMeasure p) =
      ((∫ environment, X mode n (Environment.subtree [false] environment)
          ∂environmentMeasure p) +
        ∫ environment, X mode n (Environment.subtree [true] environment)
          ∂environmentMeasure p) / 2 := by
    rw [integral_div, integral_add hleft hright]
  have habsEvaluation :
      (∫ environment, ((p : ℝ) - 1 / 2) *
        |X mode n (Environment.subtree [false] environment) -
          X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p) =
      ((p : ℝ) - 1 / 2) *
        ∫ environment,
          |X mode n (Environment.subtree [false] environment) -
            X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p := by
    rw [integral_const_mul]
  have hcorrectionEvaluation :
      (∫ environment, ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
        h |X mode n (Environment.subtree [false] environment) -
          X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p) =
      ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
        ∫ environment,
          h |X mode n (Environment.subtree [false] environment) -
            X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p := by
    rw [integral_const_mul]
  rw [integral_X_succ_eq_weighted_gates]
  calc
    ((p : ℝ) * ∫ environment,
          logSeriesGate (X mode n (Environment.subtree [false] environment))
            (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p +
        (1 - (p : ℝ)) * ∫ environment,
          logParallelGate mode (X mode n (Environment.subtree [false] environment))
            (X mode n (Environment.subtree [true] environment)) ∂environmentMeasure p) -
        ∫ environment, X mode n environment ∂environmentMeasure p =
      (∫ environment,
          ((p : ℝ) *
              logSeriesGate (X mode n (Environment.subtree [false] environment))
                (X mode n (Environment.subtree [true] environment)) +
            (1 - (p : ℝ)) *
              logParallelGate mode (X mode n (Environment.subtree [false] environment))
                (X mode n (Environment.subtree [true] environment)))
          ∂environmentMeasure p) -
        ∫ environment, X mode n environment ∂environmentMeasure p := by
      rw [integral_add hseriesScaled hparallelScaled, integral_const_mul,
        integral_const_mul]
    _ = (∫ environment,
          ((X mode n (Environment.subtree [false] environment) +
              X mode n (Environment.subtree [true] environment)) / 2 +
            ((p : ℝ) - 1 / 2) *
              |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)| +
            ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
              h |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)|)
          ∂environmentMeasure p) -
        ∫ environment, X mode n environment ∂environmentMeasure p := by
      congr 1
      apply integral_congr_ae
      filter_upwards with environment
      exact weighted_log_gates p mode
        (X mode n (Environment.subtree [false] environment))
        (X mode n (Environment.subtree [true] environment))
    _ = (((∫ environment, X mode n (Environment.subtree [false] environment)
              ∂environmentMeasure p) +
            ∫ environment, X mode n (Environment.subtree [true] environment)
              ∂environmentMeasure p) / 2 +
          ((p : ℝ) - 1 / 2) *
            ∫ environment,
              |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p +
          ((p : ℝ) - mode.eta * (1 - (p : ℝ))) *
            ∫ environment,
              h |X mode n (Environment.subtree [false] environment) -
                X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p) -
        ∫ environment, X mode n environment ∂environmentMeasure p := by
      rw [hsplitOuter, hsplitInner, hmeanEvaluation, habsEvaluation,
        hcorrectionEvaluation]
    _ = _ := by
      rw [integral_left_X_eq, integral_right_X_eq]
      ring

end SeriesParallel.MainText
