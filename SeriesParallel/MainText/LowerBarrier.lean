/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.HardEdgeConsistency
import SeriesParallel.MainText.RemainingParameters
import SeriesParallel.MainText.UpperBarrier

/-!
# The subcritical lower barrier

This file restores the CDF iteration omitted from the source TeX.  The analytic
hard-edge construction enters only through a global one-step barrier hypothesis;
the probability-law iteration, expectation comparison, and resistance duality are
proved here without any additional interface.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology unitInterval

namespace SeriesParallel.MainText

open SeriesParallel.Appendix

/-! ## The translated lower-barrier induction -/

/-- A global pointwise lower barrier iterates against the exact resistance law.

With `shift = -s`, the hypothesis reads
`cdf barrier (x + s) <= cdfOperator p barrier x`, and the conclusion is the
source statement `F_n(x) >= cdf barrier (x + n * s)`.
-/
theorem lowerBarrier_CDF_translation_induction
    (p : Set.Icc (0 : ℝ) 1) (barrier : Measure ℝ)
    [IsProbabilityMeasure barrier] {shift : ℝ}
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x - shift) ≤
        cdfOperator p barrier x) :
    ∀ n : ℕ,
      CDFOrdered (translateLaw (n * shift) barrier)
        (resistanceGenerationLaw p n) := by
  have honeStep : CDFOrdered (translateLaw shift barrier)
      (oneStepLaw p barrier) :=
    cdfOrdered_translate_oneStep_of_barrier p barrier hglobal
  intro n
  rw [resistanceGenerationLaw_eq_iterated]
  exact cdfOrdered_iteratedOneStepLaw p barrier (Measure.dirac 0)
    hinitial honeStep n

/-- The CDF induction in the literal negative-shift notation of the source. -/
theorem lowerBarrier_CDF_negative_shift_induction
    (p : Set.Icc (0 : ℝ) 1) (barrier : Measure ℝ)
    [IsProbabilityMeasure barrier] {s : ℝ}
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + s) ≤
        cdfOperator p barrier x) (n : ℕ) :
    CDFOrdered (translateLaw (-(n : ℝ) * s) barrier)
      (resistanceGenerationLaw p n) := by
  have hiteration := lowerBarrier_CDF_translation_induction p barrier
    hinitial (shift := -s) (by
      intro x
      simpa only [sub_neg_eq_add] using hglobal x) n
  convert hiteration using 1
  ring_nf

/-! ## CDF order gives the finite-level expectation upper bound -/

/-- The translated CDF lower barrier bounds the resistance mean logarithm from above. -/
theorem meanLog_resistance_le_lowerBarrier
    (p : Set.Icc (0 : ℝ) 1) (barrier : Measure ℝ)
    [IsProbabilityMeasure barrier] (hbarrier : Integrable id barrier)
    {shift : ℝ} (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x - shift) ≤
        cdfOperator p barrier x) (n : ℕ) :
    meanLog p .resistance n ≤
      (∫ x, x ∂barrier) + n * shift := by
  letI : IsProbabilityMeasure (resistanceGenerationLaw p n) :=
    resistanceGenerationLaw_isProbabilityMeasure p n
  letI : IsProbabilityMeasure (translateLaw (n * shift) barrier) :=
    translateLaw_isProbabilityMeasure (n * shift) barrier
  have htranslated := integrable_id_translateLaw hbarrier (n * shift)
  have hprocess := integrable_id_resistanceGenerationLaw p n
  have horder := lowerBarrier_CDF_translation_induction p barrier
    hinitial hglobal n
  have hexpectation := integral_id_mono_of_CDFOrdered horder
    htranslated hprocess
  rw [integral_id_resistanceGenerationLaw,
    integral_id_translateLaw hbarrier] at hexpectation
  linarith

/-- Negative-shift form of the finite-level expectation comparison. -/
theorem meanLog_resistance_le_lowerBarrier_negative_shift
    (p : Set.Icc (0 : ℝ) 1) (barrier : Measure ℝ)
    [IsProbabilityMeasure barrier] (hbarrier : Integrable id barrier)
    {s : ℝ} (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + s) ≤
        cdfOperator p barrier x) (n : ℕ) :
    meanLog p .resistance n ≤
      (∫ x, x ∂barrier) - n * s := by
  have hbound := meanLog_resistance_le_lowerBarrier p barrier hbarrier
    hinitial (shift := -s) (by
      intro x
      simpa only [sub_neg_eq_add] using hglobal x) n
  convert hbound using 1
  ring_nf

/-- Normalized finite-generation form, indexed by `n + 1` as in `normalizedMeanLog`. -/
theorem normalizedMeanLog_resistance_le_lowerBarrier
    (p : Set.Icc (0 : ℝ) 1) (barrier : Measure ℝ)
    [IsProbabilityMeasure barrier] (hbarrier : Integrable id barrier)
    {shift : ℝ} (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x - shift) ≤
        cdfOperator p barrier x) (n : ℕ) :
    normalizedMeanLog p .resistance n ≤
      shift + (∫ x, x ∂barrier) / ((n : ℝ) + 1) := by
  rw [normalizedMeanLog]
  have hmean := meanLog_resistance_le_lowerBarrier p barrier hbarrier
    hinitial hglobal (n + 1)
  have hdenom : 0 < (n : ℝ) + 1 := by positivity
  calc
    meanLog p .resistance (n + 1) / ((n : ℝ) + 1) ≤
        ((∫ x, x ∂barrier) + ((n : ℝ) + 1) * shift) /
          ((n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      simpa only [Nat.cast_add, Nat.cast_one] using hmean
    _ = shift + (∫ x, x ∂barrier) / ((n : ℝ) + 1) := by
      field_simp
      ring_nf

/-! ## The strict-subcritical speed consequence -/

/-- Any integrable translated lower barrier bounds the strict-subcritical speed.

The hard-edge analysis is deliberately represented by `hglobal`, a theorem
parameter rather than a new project interface.
-/
theorem vR_le_of_lowerBarrier_subcritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (barrier : Measure ℝ) [IsProbabilityMeasure barrier]
    (hbarrier : Integrable id barrier) {shift : ℝ}
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x - shift) ≤
        cdfOperator (modelParameter p) barrier x) :
    vR p ≤ shift := by
  let barrierMean := ∫ x, x ∂barrier
  have hlimit : Tendsto
      (normalizedMeanLog (modelParameter p) .resistance)
      atTop (nhds (vR p)) :=
    normalizedMeanLog_resistance_tendsto_vR_subcritical hpMem hp
  have hvanish : Tendsto
      (fun n : ℕ ↦ barrierMean / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul barrierMean
  have hupper : Tendsto
      (fun n : ℕ ↦ shift + barrierMean / ((n : ℝ) + 1))
      atTop (nhds shift) := by
    simpa using tendsto_const_nhds.add hvanish
  apply le_of_tendsto_of_tendsto' hlimit hupper
  intro n
  exact normalizedMeanLog_resistance_le_lowerBarrier
    (modelParameter p) barrier hbarrier hinitial hglobal n

/-! ## Finite-level resistance complement bridge -/

/-- Complementing a real model parameter negates every finite-level resistance mean. -/
theorem meanLog_resistance_modelParameter_complement
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    meanLog (modelParameter (1 - p)) .resistance n =
      -meanLog (modelParameter p) .resistance n := by
  rw [modelParameter_one_sub hp]
  exact meanLog_resistance_symm (modelParameter p) n

/-- The same complement identity after the source normalization by `n + 1`. -/
theorem normalizedMeanLog_resistance_modelParameter_complement
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    normalizedMeanLog (modelParameter (1 - p)) .resistance n =
      -normalizedMeanLog (modelParameter p) .resistance n := by
  rw [modelParameter_one_sub hp]
  exact normalizedMeanLog_resistance_symm (modelParameter p) n

/-- A subcritical lower-barrier expectation bound becomes a finite-level lower bound at the
complementary resistance parameter. -/
theorem lowerBarrier_complement_meanLog_bound
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (barrier : Measure ℝ) [IsProbabilityMeasure barrier]
    (hbarrier : Integrable id barrier) {s : ℝ}
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + s) ≤
        cdfOperator (modelParameter p) barrier x) (n : ℕ) :
    n * s - (∫ x, x ∂barrier) ≤
      meanLog (modelParameter (1 - p)) .resistance n := by
  have hsub := meanLog_resistance_le_lowerBarrier_negative_shift
    (modelParameter p) barrier hbarrier hinitial hglobal n
  rw [meanLog_resistance_modelParameter_complement hp]
  linarith

/-! ## The near-critical fixed-parameter inequalities -/

/-- A positive `epsilon` with `epsilon^3 <= 1/2` gives a valid strict-subcritical
Bernoulli parameter `1/2 - epsilon^3`. -/
theorem half_sub_cube_mem_unitInterval {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hcube : epsilon ^ 3 ≤ 1 / 2) :
    1 / 2 - epsilon ^ 3 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · linarith
  · have hcubePos : 0 < epsilon ^ 3 := pow_pos hepsilon 3
    linarith

/-- The global hard-edge lower barrier implies the fixed-`epsilon` negative speed bound. -/
theorem vR_half_sub_cube_le_neg_kappa_sq_of_lowerBarrier
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (barrier : Measure ℝ) [IsProbabilityMeasure barrier]
    (hbarrier : Integrable id barrier)
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3)) barrier x) :
    vR (1 / 2 - epsilon ^ 3) ≤ -kappa * epsilon ^ 2 := by
  have hpMem := half_sub_cube_mem_unitInterval hepsilon hcube
  have hp : 1 / 2 - epsilon ^ 3 < (1 / 2 : ℝ) := by
    have hcubePos : 0 < epsilon ^ 3 := pow_pos hepsilon 3
    linarith
  apply vR_le_of_lowerBarrier_subcritical hpMem hp barrier hbarrier
    hinitial (shift := -kappa * epsilon ^ 2)
  intro x
  convert hglobal x using 1
  ring_nf

/-- Finite-level complementarity transfers the same hard-edge hypothesis to the positive
side before any limiting argument is used. -/
theorem half_add_cube_lower_meanLog_of_lowerBarrier
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (barrier : Measure ℝ) [IsProbabilityMeasure barrier]
    (hbarrier : Integrable id barrier)
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3)) barrier x)
    (n : ℕ) :
    n * (kappa * epsilon ^ 2) - (∫ x, x ∂barrier) ≤
      meanLog (modelParameter (1 / 2 + epsilon ^ 3))
        .resistance n := by
  have hpMem := half_sub_cube_mem_unitInterval hepsilon hcube
  have hbound := lowerBarrier_complement_meanLog_bound hpMem barrier
    hbarrier hinitial hglobal n
  convert hbound using 1
  ring_nf

/-- Resistance duality turns the subcritical negative bound into the matching
supercritical positive lower bound. -/
theorem kappa_sq_le_vR_half_add_cube_of_lowerBarrier
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (barrier : Measure ℝ) [IsProbabilityMeasure barrier]
    (hbarrier : Integrable id barrier)
    (hinitial : CDFOrdered barrier (Measure.dirac 0))
    (hglobal : ∀ x : ℝ,
      ProbabilityTheory.cdf barrier (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3)) barrier x) :
    kappa * epsilon ^ 2 ≤ vR (1 / 2 + epsilon ^ 3) := by
  have hpMem := half_sub_cube_mem_unitInterval hepsilon hcube
  have hsub := vR_half_sub_cube_le_neg_kappa_sq_of_lowerBarrier
    hepsilon hcube barrier hbarrier hinitial hglobal
  have hdual := vR_one_sub (1 / 2 - epsilon ^ 3) hpMem
  have hneg := neg_le_neg hsub
  have hneg' : kappa * epsilon ^ 2 ≤
      -vR (1 / 2 - epsilon ^ 3) := by
    linarith
  calc
    kappa * epsilon ^ 2 ≤ -vR (1 / 2 - epsilon ^ 3) := hneg'
    _ = vR (1 - (1 / 2 - epsilon ^ 3)) := hdual.symm
    _ = vR (1 / 2 + epsilon ^ 3) := by ring_nf

/-! ## Assembly with the concrete hard-edge law -/

/-- The source CDF induction for the density-defined hard-edge law.  The analytic
three-region estimate is the explicit hypothesis `hglobal`.
-/
theorem hardEdge_lowerBarrier_CDF_translation_induction
    (p : Set.Icc (0 : ℝ) 1) {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hglobal : ∀ x : ℝ,
      hardEdgeScaledCDF Psi epsilon
          (x + kappa * epsilon ^ 2) ≤
        cdfOperator p
          (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x)
    (n : ℕ) :
    CDFOrdered
      (translateLaw (-(n : ℝ) * (kappa * epsilon ^ 2))
        (hardEdgeScaledLaw diffusionMainInput W Psi epsilon))
      (resistanceGenerationLaw p n) := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  apply lowerBarrier_CDF_negative_shift_induction p
    (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
    (hardEdgeScaledLaw_initial_CDFOrdered hprofile hepsilon)
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon)
    (x + kappa * epsilon ^ 2)]
  exact hglobal x

/-- The concrete hard-edge CDF order gives the finite-level source expectation
inequality `E X_n <= E Z_epsilon - n * kappa * epsilon^2`.
-/
theorem meanLog_resistance_le_hardEdge_lowerBarrier
    (p : Set.Icc (0 : ℝ) 1) {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hglobal : ∀ x : ℝ,
      hardEdgeScaledCDF Psi epsilon
          (x + kappa * epsilon ^ 2) ≤
        cdfOperator p
          (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x)
    (n : ℕ) :
    meanLog p .resistance n ≤
      (∫ x, x ∂hardEdgeScaledLaw diffusionMainInput W Psi epsilon) -
        n * (kappa * epsilon ^ 2) := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  apply meanLog_resistance_le_lowerBarrier_negative_shift p
    (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
    (integrable_id_hardEdgeScaledLaw hprofile hepsilon)
    (hardEdgeScaledLaw_initial_CDFOrdered hprofile hepsilon)
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon)
    (x + kappa * epsilon ^ 2)]
  exact hglobal x

/-- `vR(1/2-epsilon^3) <= -kappa*epsilon^2` from the concrete hard-edge law and
the global one-step barrier theorem.
-/
theorem vR_half_sub_cube_le_neg_kappa_sq
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (hglobal : ∀ x : ℝ,
      hardEdgeScaledCDF Psi epsilon
          (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3))
          (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x) :
    vR (1 / 2 - epsilon ^ 3) ≤ -kappa * epsilon ^ 2 := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  apply vR_half_sub_cube_le_neg_kappa_sq_of_lowerBarrier
    hepsilon hcube
    (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
    (integrable_id_hardEdgeScaledLaw hprofile hepsilon)
    (hardEdgeScaledLaw_initial_CDFOrdered hprofile hepsilon)
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon)
    (x + kappa * epsilon ^ 2)]
  exact hglobal x

/-- Finite-level resistance complement bridge for the concrete hard-edge lower
barrier, before passage to the speed.
-/
theorem half_add_cube_lower_meanLog_hardEdge
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (hglobal : ∀ x : ℝ,
      hardEdgeScaledCDF Psi epsilon
          (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3))
          (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x)
    (n : ℕ) :
    n * (kappa * epsilon ^ 2) -
        (∫ x, x ∂hardEdgeScaledLaw diffusionMainInput W Psi epsilon) ≤
      meanLog (modelParameter (1 / 2 + epsilon ^ 3))
        .resistance n := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  apply half_add_cube_lower_meanLog_of_lowerBarrier hepsilon hcube
    (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
    (integrable_id_hardEdgeScaledLaw hprofile hepsilon)
    (hardEdgeScaledLaw_initial_CDFOrdered hprofile hepsilon)
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon)
    (x + kappa * epsilon ^ 2)]
  exact hglobal x

/-- The concrete hard-edge lower barrier and resistance duality give the positive-side
fixed-`epsilon` speed lower bound.
-/
theorem kappa_sq_le_vR_half_add_cube
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon)
    (hcube : epsilon ^ 3 ≤ 1 / 2)
    (hglobal : ∀ x : ℝ,
      hardEdgeScaledCDF Psi epsilon
          (x + kappa * epsilon ^ 2) ≤
        cdfOperator (modelParameter (1 / 2 - epsilon ^ 3))
          (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x) :
    kappa * epsilon ^ 2 ≤ vR (1 / 2 + epsilon ^ 3) := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  apply kappa_sq_le_vR_half_add_cube_of_lowerBarrier
    hepsilon hcube
    (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
    (integrable_id_hardEdgeScaledLaw hprofile hepsilon)
    (hardEdgeScaledLaw_initial_CDFOrdered hprofile hepsilon)
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon)
    (x + kappa * epsilon ^ 2)]
  exact hglobal x

end SeriesParallel.MainText
