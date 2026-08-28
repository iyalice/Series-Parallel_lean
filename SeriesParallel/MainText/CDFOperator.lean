/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeriesParallel formalization contributors
-/
module

public import SeriesParallel.MainText.LogGates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.CDF
public import Mathlib.Topology.UnitInterval

/-!
# The exact resistance CDF operator

This file defines the independent-copy series and resistance-parallel laws as pushforwards of
`mu.prod mu`.  Their Bernoulli mixture is the one-step resistance law.  The CDF convention is the
source convention

`mu (Set.Iic x) = ENNReal.ofReal (F x)`.

The nested integrals `Iminus` and `Iplus` are also recorded.  The algebraic passage from the two
series/parallel CDF formulas to the exact operator identity is proved here.  The analytic
two-dimensional change-of-variables argument establishing those formulas is deliberately not
asserted in this foundational module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace SeriesParallel.MainText

/-! ## Probability laws and their CDFs -/

/-- A probability measure with the source's exact closed-left-ray CDF convention. -/
def IsProbabilityLawOfCDF (F : ℝ → ℝ) (mu : Measure ℝ) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ x, mu (Iic x) = ENNReal.ofReal (F x)

/-- Mathlib's CDF satisfies the source's `Iic` convention exactly. -/
theorem cdf_isProbabilityLaw (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityLawOfCDF (ProbabilityTheory.cdf mu) mu := by
  exact ⟨inferInstance, fun x ↦ (ProbabilityTheory.ofReal_cdf mu x).symm⟩

/-- Joint measurability of the logarithmic series gate on a pair of inputs. -/
theorem measurable_logSeriesGate_pair :
    Measurable (fun z : ℝ × ℝ ↦ logSeriesGate z.1 z.2) := by
  unfold logSeriesGate
  fun_prop

/-- Joint measurability of the logarithmic resistance-parallel gate. -/
theorem measurable_logResistanceParallelGate_pair :
    Measurable (fun z : ℝ × ℝ ↦ logParallelGate .resistance z.1 z.2) := by
  simp only [logParallelGate_resistance]
  fun_prop

/-- The law of the logarithmic series gate applied to two independent copies with law `mu`. -/
noncomputable def seriesLaw (mu : Measure ℝ) : Measure ℝ :=
  (mu.prod mu).map fun z ↦ logSeriesGate z.1 z.2

/-- The law of the logarithmic resistance-parallel gate applied to two independent copies. -/
noncomputable def parallelLaw (mu : Measure ℝ) : Measure ℝ :=
  (mu.prod mu).map fun z ↦ logParallelGate .resistance z.1 z.2

/-- The series pushforward of a probability law is again a probability law. -/
theorem seriesLaw_isProbabilityMeasure (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (seriesLaw mu) := by
  exact Measure.isProbabilityMeasure_map measurable_logSeriesGate_pair.aemeasurable

/-- The resistance-parallel pushforward of a probability law is again a probability law. -/
theorem parallelLaw_isProbabilityMeasure (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (parallelLaw mu) := by
  exact Measure.isProbabilityMeasure_map measurable_logResistanceParallelGate_pair.aemeasurable

/-- The real-valued CDF `S_F` of the series pushforward law. -/
noncomputable def seriesCDF (mu : Measure ℝ) : ℝ → ℝ :=
  ProbabilityTheory.cdf (seriesLaw mu)

/-- The real-valued CDF `P_F` of the resistance-parallel pushforward law. -/
noncomputable def parallelCDF (mu : Measure ℝ) : ℝ → ℝ :=
  ProbabilityTheory.cdf (parallelLaw mu)

theorem seriesLaw_hasCDF (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityLawOfCDF (seriesCDF mu) (seriesLaw mu) := by
  letI : IsProbabilityMeasure (seriesLaw mu) := seriesLaw_isProbabilityMeasure mu
  exact cdf_isProbabilityLaw (seriesLaw mu)

theorem parallelLaw_hasCDF (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityLawOfCDF (parallelCDF mu) (parallelLaw mu) := by
  letI : IsProbabilityMeasure (parallelLaw mu) := parallelLaw_isProbabilityMeasure mu
  exact cdf_isProbabilityLaw (parallelLaw mu)

/-! ## One-step Bernoulli mixture -/

/-- The one-step resistance law: choose the series gate with probability `p` and the
resistance-parallel gate with probability `1 - p`. -/
noncomputable def oneStepLaw (p : unitInterval) (mu : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (p : ℝ) • seriesLaw mu +
    ENNReal.ofReal (1 - (p : ℝ)) • parallelLaw mu

/-- The source's real-valued CDF operator `T_p`. -/
noncomputable def cdfOperator (p : unitInterval) (mu : Measure ℝ) (x : ℝ) : ℝ :=
  (p : ℝ) * seriesCDF mu x + (1 - (p : ℝ)) * parallelCDF mu x

/-- The Bernoulli mixture has total mass one. -/
theorem oneStepLaw_isProbabilityMeasure (p : unitInterval) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (oneStepLaw p mu) := by
  letI : IsProbabilityMeasure (seriesLaw mu) := seriesLaw_isProbabilityMeasure mu
  letI : IsProbabilityMeasure (parallelLaw mu) := parallelLaw_isProbabilityMeasure mu
  constructor
  simp only [oneStepLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]
  simp

/-- The one-step measure has exactly the CDF given by `cdfOperator`. -/
theorem oneStepLaw_hasCDF (p : unitInterval) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsProbabilityLawOfCDF (cdfOperator p mu) (oneStepLaw p mu) := by
  letI : IsProbabilityMeasure (seriesLaw mu) := seriesLaw_isProbabilityMeasure mu
  letI : IsProbabilityMeasure (parallelLaw mu) := parallelLaw_isProbabilityMeasure mu
  refine ⟨oneStepLaw_isProbabilityMeasure p mu, ?_⟩
  intro x
  rw [oneStepLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    (seriesLaw_hasCDF mu).2 x, (parallelLaw_hasCDF mu).2 x]
  unfold cdfOperator
  have hseriesNonneg : 0 ≤ seriesCDF mu x := ProbabilityTheory.cdf_nonneg (seriesLaw mu) x
  have hparallelNonneg : 0 ≤ parallelCDF mu x :=
    ProbabilityTheory.cdf_nonneg (parallelLaw mu) x
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_add
    (mul_nonneg p.2.1 hseriesNonneg)
    (mul_nonneg (sub_nonneg.mpr p.2.2) hparallelNonneg),
    ENNReal.ofReal_mul p.2.1, ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]

/-! ## Translations -/

/-- Translation of a CDF, with the source sign convention `tau_a F (x) = F (x - a)`. -/
def translateCDF (a : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ := F (x - a)

/-- Push a law forward by the random-variable translation `x ↦ x + a`. -/
noncomputable def translateLaw (a : ℝ) (mu : Measure ℝ) : Measure ℝ :=
  mu.map fun x ↦ x + a

theorem translateLaw_isProbabilityMeasure (a : ℝ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (translateLaw a mu) := by
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Translating the random variable by `a` translates its CDF by `tau_a`. -/
theorem translateLaw_hasCDF {F : ℝ → ℝ} {mu : Measure ℝ}
    (hmu : IsProbabilityLawOfCDF F mu) (a : ℝ) :
    IsProbabilityLawOfCDF (translateCDF a F) (translateLaw a mu) := by
  letI : IsProbabilityMeasure mu := hmu.1
  refine ⟨translateLaw_isProbabilityMeasure a mu, ?_⟩
  intro x
  rw [translateLaw, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpreimage : (fun y : ℝ ↦ y + a) ⁻¹' Iic x = Iic (x - a) := by
    ext y
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro hy <;> linarith
  rw [hpreimage, hmu.2]
  rfl

/-- The mathlib CDF of a translated probability law has the source translation sign. -/
theorem cdf_translateLaw (a : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (ProbabilityTheory.cdf (translateLaw a mu) : ℝ → ℝ) =
      translateCDF a (ProbabilityTheory.cdf mu) := by
  letI : IsProbabilityMeasure (translateLaw a mu) := translateLaw_isProbabilityMeasure a mu
  funext x
  unfold translateCDF
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  unfold Measure.real translateLaw
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro hy <;> linarith

/-! ## Translation covariance of the gates and the operator -/

theorem seriesLaw_translate (a : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    seriesLaw (translateLaw a mu) = translateLaw a (seriesLaw mu) := by
  unfold seriesLaw translateLaw
  rw [Measure.map_prod_map mu mu (by fun_prop) (by fun_prop)]
  rw [Measure.map_map measurable_logSeriesGate_pair (by fun_prop)]
  rw [Measure.map_map (by fun_prop) measurable_logSeriesGate_pair]
  apply Measure.map_congr
  filter_upwards with z
  rcases z with ⟨x, y⟩
  simpa only [Function.comp_apply, Prod.map, add_comm] using
    logSeriesGate_translation x y a

theorem parallelLaw_translate (a : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    parallelLaw (translateLaw a mu) = translateLaw a (parallelLaw mu) := by
  unfold parallelLaw translateLaw
  rw [Measure.map_prod_map mu mu (by fun_prop) (by fun_prop)]
  rw [Measure.map_map measurable_logResistanceParallelGate_pair (by fun_prop)]
  rw [Measure.map_map (by fun_prop) measurable_logResistanceParallelGate_pair]
  apply Measure.map_congr
  filter_upwards with z
  rcases z with ⟨x, y⟩
  simpa only [Function.comp_apply, Prod.map, add_comm] using
    logParallelGate_translation .resistance x y a

/-- Translation covariance of the one-step probability law. -/
theorem oneStepLaw_translate (p : unitInterval) (a : ℝ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    oneStepLaw p (translateLaw a mu) = translateLaw a (oneStepLaw p mu) := by
  unfold oneStepLaw
  rw [seriesLaw_translate, parallelLaw_translate]
  unfold translateLaw
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul]

theorem seriesCDF_translate (a : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    seriesCDF (translateLaw a mu) = translateCDF a (seriesCDF mu) := by
  letI : IsProbabilityMeasure (seriesLaw mu) := seriesLaw_isProbabilityMeasure mu
  unfold seriesCDF
  rw [seriesLaw_translate]
  exact cdf_translateLaw a (seriesLaw mu)

theorem parallelCDF_translate (a : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    parallelCDF (translateLaw a mu) = translateCDF a (parallelCDF mu) := by
  letI : IsProbabilityMeasure (parallelLaw mu) := parallelLaw_isProbabilityMeasure mu
  unfold parallelCDF
  rw [parallelLaw_translate]
  exact cdf_translateLaw a (parallelLaw mu)

/-- Translation covariance `T_p (tau_a F) = tau_a (T_p F)` for the law-based CDF operator. -/
theorem cdfOperator_translate (p : unitInterval) (a : ℝ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    cdfOperator p (translateLaw a mu) = translateCDF a (cdfOperator p mu) := by
  funext x
  unfold cdfOperator translateCDF
  rw [congrFun (seriesCDF_translate a mu) x, congrFun (parallelCDF_translate a mu) x]
  rfl

/-! ## The density integrals and the exact algebraic identity -/

/-- The crossing integral below the threshold in the series formula. -/
noncomputable def Iminus (rho : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r, rho (x - s) * rho (x - s - r)

/-- The crossing integral above the threshold in the resistance-parallel formula. -/
noncomputable def Iplus (rho : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r, rho (x + s) * rho (x + s + r)

/-- Once the two series/parallel CDF formulas are available, the exact CDF operator identity is
pure algebra.  No analytic change of variables is hidden in this theorem. -/
theorem exact_cdf_operator_of_series_parallel (p : unitInterval) (mu : Measure ℝ)
    (F rho : ℝ → ℝ) (delta x : ℝ)
    (hp : (p : ℝ) = 1 / 2 + delta)
    (hseries : seriesCDF mu x = F x ^ 2 - 2 * Iminus rho x)
    (hparallel : parallelCDF mu x = 2 * F x - F x ^ 2 + 2 * Iplus rho x) :
    cdfOperator p mu x - F x =
      Iplus rho x - Iminus rho x - 2 * delta * F x * (1 - F x) -
        2 * delta * (Iplus rho x + Iminus rho x) := by
  unfold cdfOperator
  rw [hseries, hparallel, hp]
  ring

end SeriesParallel.MainText
