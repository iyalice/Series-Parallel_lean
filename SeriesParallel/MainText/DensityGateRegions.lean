/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.CDFOperator

import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Density formulas for the logarithmic gate regions

This module supplies the analytic part of the exact CDF recursion.  The two affine
changes of variables are factored into translations, sign changes, swaps, and Haar
shears, so their preservation of planar Lebesgue measure is proved rather than assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Interval unitInterval

namespace SeriesParallel.MainText

/-! ## Density laws -/

/-- The absolutely continuous law with nonnegative real density `rho`. -/
noncomputable def densityLaw (rho : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (rho x))

/-- A nonnegative density of integral one defines a probability measure. -/
theorem densityLaw_isProbabilityMeasure (rho : ℝ → ℝ) (hrho : Integrable rho)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∫ x, rho x = 1) :
    IsProbabilityMeasure (densityLaw rho) := by
  constructor
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho (ae_of_all _ hrho_nonneg), hrho_mass]
  simp

private theorem densityLaw_prod (rho : ℝ → ℝ) (hrho_meas : Measurable rho)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) :
    (densityLaw rho).prod (densityLaw rho) =
      (volume.prod volume).withDensity
        (fun z ↦ ENNReal.ofReal (rho z.1 * rho z.2)) := by
  rw [densityLaw, prod_withDensity (hrho_meas.ennreal_ofReal)
    (hrho_meas.ennreal_ofReal)]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (hrho_nonneg z.1)]

private theorem integrable_densityProduct (rho : ℝ → ℝ) (hrho : Integrable rho) :
    Integrable (fun z : ℝ × ℝ ↦ rho z.1 * rho z.2) (volume.prod volume) :=
  hrho.mul_prod hrho

private theorem densityProduct_measureReal (rho : ℝ → ℝ) (hrho_meas : Measurable rho)
    (hrho : Integrable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) :
    ((densityLaw rho).prod (densityLaw rho)).real s =
      ∫ z in s, rho z.1 * rho z.2 ∂(volume.prod volume) := by
  rw [densityLaw_prod rho hrho_meas hrho_nonneg, measureReal_def,
    withDensity_apply _ hs]
  have hint : Integrable (fun z : ℝ × ℝ ↦ rho z.1 * rho z.2)
      ((volume.prod volume).restrict s) :=
    (integrable_densityProduct rho hrho).restrict
  have hnonneg : ∀ᵐ z ∂((volume.prod volume).restrict s), 0 ≤ rho z.1 * rho z.2 :=
    ae_of_all _ fun z ↦ mul_nonneg (hrho_nonneg z.1) (hrho_nonneg z.2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]

/-! ## Unit-Jacobian affine parametrizations -/

/-- Series crossing coordinates `(r,s) ↦ (x-s,x-s-r)`. -/
def seriesCrossingEquiv (x : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun z := (x - z.2, x - z.2 - z.1)
  invFun z := (z.1 - z.2, x - z.1)
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  measurable_toFun :=
    (measurable_const.sub measurable_snd).prodMk
      ((measurable_const.sub measurable_snd).sub measurable_fst)
  measurable_invFun :=
    (measurable_fst.sub measurable_snd).prodMk
      (measurable_const.sub measurable_fst)

/-- Parallel crossing coordinates `(r,s) ↦ (x+s,x+s+r)`. -/
def parallelCrossingEquiv (x : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun z := (x + z.2, x + z.2 + z.1)
  invFun z := (z.2 - z.1, z.1 - x)
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  measurable_toFun :=
    (measurable_const.add measurable_snd).prodMk
      ((measurable_const.add measurable_snd).add measurable_fst)
  measurable_invFun :=
    (measurable_snd.sub measurable_fst).prodMk
      (measurable_fst.sub measurable_const)

/-- The series crossing parametrization preserves planar Lebesgue measure. -/
theorem seriesCrossingEquiv_measurePreserving (x : ℝ) :
    MeasurePreserving (seriesCrossingEquiv x) (volume.prod volume)
      (volume.prod volume) := by
  let hswap := Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  let hshear := measurePreserving_prod_add (volume : Measure ℝ) volume
  let hrotate := measurePreserving_add_prod_neg (volume : Measure ℝ) volume
  let hnegPair := hrotate.comp (hrotate.comp hrotate)
  let htranslate := measurePreserving_add_left (volume : Measure ℝ) x
  have h := (htranslate.prod htranslate).comp
    (hnegPair.comp (hshear.comp hswap))
  convert h using 1
  ext z <;> rcases z with ⟨r, s⟩ <;>
    dsimp [seriesCrossingEquiv, Function.comp_apply] <;> ring

/-- The parallel crossing parametrization preserves planar Lebesgue measure. -/
theorem parallelCrossingEquiv_measurePreserving (x : ℝ) :
    MeasurePreserving (parallelCrossingEquiv x) (volume.prod volume)
      (volume.prod volume) := by
  let hswap := Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  let hshear := measurePreserving_prod_add (volume : Measure ℝ) volume
  let htranslate := measurePreserving_add_left (volume : Measure ℝ) x
  have h := (htranslate.prod htranslate).comp (hshear.comp hswap)
  convert h using 1
  ext z <;> rcases z with ⟨r, s⟩
  · rfl
  ·
    dsimp [parallelCrossingEquiv, Function.comp_apply]
    ring

/-! ## Parameter and gate regions -/

/-- Parameters for the strict series crossing event. -/
def seriesParameterRegion : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 < h z.1}

/-- Parameters for the parallel crossing event. -/
def parallelParameterRegion : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 < z.2 ∧ z.2 ≤ h z.1}

/-- One ordered half of the series crossing event. -/
def seriesCrossingRegion (x : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ≤ z.1 ∧ z.1 ≤ x ∧ x < logSeriesGate z.1 z.2}

/-- One ordered half of the resistance-parallel crossing event. -/
def parallelCrossingRegion (x : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ z.2 ∧ x < z.1 ∧ logParallelGate .resistance z.1 z.2 ≤ x}

theorem measurableSet_seriesParameterRegion : MeasurableSet seriesParameterRegion := by
  have hz1 : Measurable (fun z : ℝ × ℝ ↦ z.1) := measurable_fst
  have hz2 : Measurable (fun z : ℝ × ℝ ↦ z.2) := measurable_snd
  have hzero : Measurable (fun _ : ℝ × ℝ ↦ (0 : ℝ)) := measurable_const
  have hh : Measurable (fun z : ℝ × ℝ ↦ h z.1) := by
    unfold h
    fun_prop
  change MeasurableSet ({z : ℝ × ℝ | 0 ≤ z.1} ∩
    ({z : ℝ × ℝ | 0 ≤ z.2} ∩ {z : ℝ × ℝ | z.2 < h z.1}))
  exact (measurableSet_le hzero hz1).inter
    ((measurableSet_le hzero hz2).inter (measurableSet_lt hz2 hh))

theorem measurableSet_parallelParameterRegion : MeasurableSet parallelParameterRegion := by
  have hz1 : Measurable (fun z : ℝ × ℝ ↦ z.1) := measurable_fst
  have hz2 : Measurable (fun z : ℝ × ℝ ↦ z.2) := measurable_snd
  have hzero : Measurable (fun _ : ℝ × ℝ ↦ (0 : ℝ)) := measurable_const
  have hh : Measurable (fun z : ℝ × ℝ ↦ h z.1) := by
    unfold h
    fun_prop
  change MeasurableSet ({z : ℝ × ℝ | 0 ≤ z.1} ∩
    ({z : ℝ × ℝ | 0 < z.2} ∩ {z : ℝ × ℝ | z.2 ≤ h z.1}))
  exact (measurableSet_le hzero hz1).inter
    ((measurableSet_lt hzero hz2).inter (measurableSet_le hz2 hh))

theorem measurableSet_seriesCrossingRegion (x : ℝ) :
    MeasurableSet (seriesCrossingRegion x) := by
  have hz1 : Measurable (fun z : ℝ × ℝ ↦ z.1) := measurable_fst
  have hz2 : Measurable (fun z : ℝ × ℝ ↦ z.2) := measurable_snd
  have hx : Measurable (fun _ : ℝ × ℝ ↦ x) := measurable_const
  change MeasurableSet ({z : ℝ × ℝ | z.2 ≤ z.1} ∩
    ({z : ℝ × ℝ | z.1 ≤ x} ∩
      {z : ℝ × ℝ | x < logSeriesGate z.1 z.2}))
  exact (measurableSet_le hz2 hz1).inter
    ((measurableSet_le hz1 hx).inter
      (measurableSet_lt hx measurable_logSeriesGate_pair))

theorem measurableSet_parallelCrossingRegion (x : ℝ) :
    MeasurableSet (parallelCrossingRegion x) := by
  have hz1 : Measurable (fun z : ℝ × ℝ ↦ z.1) := measurable_fst
  have hz2 : Measurable (fun z : ℝ × ℝ ↦ z.2) := measurable_snd
  have hx : Measurable (fun _ : ℝ × ℝ ↦ x) := measurable_const
  change MeasurableSet ({z : ℝ × ℝ | z.1 ≤ z.2} ∩
    ({z : ℝ × ℝ | x < z.1} ∩
      {z : ℝ × ℝ | logParallelGate .resistance z.1 z.2 ≤ x}))
  exact (measurableSet_le hz1 hz2).inter
    ((measurableSet_lt hx hz1).inter
      (measurableSet_le measurable_logResistanceParallelGate_pair hx))

theorem seriesCrossingEquiv_preimage (x : ℝ) :
    seriesCrossingEquiv x ⁻¹' seriesCrossingRegion x = seriesParameterRegion := by
  ext z
  change
    ((x - z.2 - z.1 ≤ x - z.2) ∧ (x - z.2 ≤ x) ∧
      x < logSeriesGate (x - z.2) (x - z.2 - z.1)) ↔
      0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 < h z.1
  constructor
  · rintro ⟨hvu, hux, hxg⟩
    have hr : 0 ≤ z.1 := by simpa [seriesCrossingEquiv] using hvu
    have hs : 0 ≤ z.2 := by simpa [seriesCrossingEquiv] using hux
    rw [logSeriesGate_eq_max_add_h, max_eq_left hvu,
      abs_of_nonneg (sub_nonneg.mpr hvu)] at hxg
    refine ⟨hr, hs, ?_⟩
    have harg : x - z.2 - (x - z.2 - z.1) = z.1 := by ring
    rw [harg] at hxg
    linarith
  · rintro ⟨hr, hs, hsh⟩
    have hvu : x - z.2 - z.1 ≤ x - z.2 := by linarith
    have hux : x - z.2 ≤ x := by linarith
    refine ⟨hvu, hux, ?_⟩
    rw [logSeriesGate_eq_max_add_h, max_eq_left hvu,
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    have harg : x - z.2 - (x - z.2 - z.1) = z.1 := by ring
    rw [harg]
    linarith

theorem parallelCrossingEquiv_preimage (x : ℝ) :
    parallelCrossingEquiv x ⁻¹' parallelCrossingRegion x = parallelParameterRegion := by
  ext z
  change
    ((x + z.2 ≤ x + z.2 + z.1) ∧ (x < x + z.2) ∧
      logParallelGate .resistance (x + z.2) (x + z.2 + z.1) ≤ x) ↔
      0 ≤ z.1 ∧ 0 < z.2 ∧ z.2 ≤ h z.1
  constructor
  · rintro ⟨huv, hxu, hgx⟩
    have hr : 0 ≤ z.1 := by simpa [parallelCrossingEquiv] using huv
    have hs : 0 < z.2 := by simpa [parallelCrossingEquiv] using hxu
    rw [logParallelGate_eq_min_sub_h, min_eq_left huv, Mode.eta_resistance,
      one_mul, abs_of_nonpos (sub_nonpos.mpr huv)] at hgx
    refine ⟨hr, hs, ?_⟩
    simpa [parallelCrossingEquiv] using hgx
  · rintro ⟨hr, hs, hsh⟩
    have huv : x + z.2 ≤ x + z.2 + z.1 := by linarith
    have hxu : x < x + z.2 := by linarith
    refine ⟨huv, hxu, ?_⟩
    rw [logParallelGate_eq_min_sub_h, min_eq_left huv, Mode.eta_resistance,
      one_mul, abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa [parallelCrossingEquiv] using hsh

/-! ## The two parameter integrals -/

private theorem integrable_seriesParameterIntegrand (rho : ℝ → ℝ)
    (hrho : Integrable rho) (x : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ rho (x - z.2) * rho (x - z.2 - z.1))
      (volume.prod volume) := by
  have hbase := integrable_densityProduct rho hrho
  have hcomp :=
    (seriesCrossingEquiv_measurePreserving x).integrable_comp_emb
      (seriesCrossingEquiv x).measurableEmbedding |>.2 hbase
  convert hcomp using 1
  ext z
  rfl

private theorem integrable_parallelParameterIntegrand (rho : ℝ → ℝ)
    (hrho : Integrable rho) (x : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ rho (x + z.2) * rho (x + z.2 + z.1))
      (volume.prod volume) := by
  have hbase := integrable_densityProduct rho hrho
  have hcomp :=
    (parallelCrossingEquiv_measurePreserving x).integrable_comp_emb
      (parallelCrossingEquiv x).measurableEmbedding |>.2 hbase
  convert hcomp using 1
  ext z
  rfl

/-- `Iminus` is the planar density integral over its exact parameter region. -/
theorem Iminus_eq_integral_seriesParameterRegion (rho : ℝ → ℝ)
    (hrho : Integrable rho) (x : ℝ) :
    Iminus rho x =
      ∫ z in seriesParameterRegion,
        rho (x - z.2) * rho (x - z.2 - z.1) ∂(volume.prod volume) := by
  let f : ℝ × ℝ → ℝ :=
    fun z ↦ rho (x - z.2) * rho (x - z.2 - z.1)
  have hf : Integrable f (volume.prod volume) :=
    integrable_seriesParameterIntegrand rho hrho x
  have hfi : Integrable (seriesParameterRegion.indicator f)
      (volume.prod volume) :=
    hf.indicator measurableSet_seriesParameterRegion
  rw [← integral_indicator measurableSet_seriesParameterRegion]
  rw [integral_prod _ hfi]
  unfold Iminus
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0 ≤ r
  · rw [Set.indicator_of_mem (mem_Ici.mpr hr)]
    rw [intervalIntegral.integral_of_le (h_nonneg r)]
    rw [← integral_Ico_eq_integral_Ioc]
    rw [← integral_indicator measurableSet_Ico]
    apply integral_congr_ae
    filter_upwards with s
    simp only [f, seriesParameterRegion, Set.indicator_apply]
    congr 1
    simp only [mem_Ico]
    simp [hr]
  · rw [Set.indicator_of_notMem (fun hmem ↦ hr (mem_Ici.mp hmem))]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards with s
    simp [seriesParameterRegion, hr]

/-- `Iplus` is the planar density integral over its exact parameter region. -/
theorem Iplus_eq_integral_parallelParameterRegion (rho : ℝ → ℝ)
    (hrho : Integrable rho) (x : ℝ) :
    Iplus rho x =
      ∫ z in parallelParameterRegion,
        rho (x + z.2) * rho (x + z.2 + z.1) ∂(volume.prod volume) := by
  let f : ℝ × ℝ → ℝ :=
    fun z ↦ rho (x + z.2) * rho (x + z.2 + z.1)
  have hf : Integrable f (volume.prod volume) :=
    integrable_parallelParameterIntegrand rho hrho x
  have hfi : Integrable (parallelParameterRegion.indicator f)
      (volume.prod volume) :=
    hf.indicator measurableSet_parallelParameterRegion
  rw [← integral_indicator measurableSet_parallelParameterRegion]
  rw [integral_prod _ hfi]
  unfold Iplus
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0 ≤ r
  · rw [Set.indicator_of_mem (mem_Ici.mpr hr)]
    rw [intervalIntegral.integral_of_le (h_nonneg r)]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with s
    simp only [f, parallelParameterRegion, Set.indicator_apply]
    congr 1
    simp only [mem_Ioc]
    simp [hr]
  · rw [Set.indicator_of_notMem (fun hmem ↦ hr (mem_Ici.mp hmem))]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards with s
    simp [parallelParameterRegion, hr]

private theorem seriesParameter_integral_eq_crossing (rho : ℝ → ℝ)
    (x : ℝ) :
    (∫ z in seriesParameterRegion,
        rho (x - z.2) * rho (x - z.2 - z.1) ∂(volume.prod volume)) =
      ∫ z in seriesCrossingRegion x,
        rho z.1 * rho z.2 ∂(volume.prod volume) := by
  let g : ℝ × ℝ → ℝ := fun z ↦ rho z.1 * rho z.2
  have hchange :=
    (seriesCrossingEquiv_measurePreserving x).integral_comp
      (seriesCrossingEquiv x).measurableEmbedding
      ((seriesCrossingRegion x).indicator g)
  have hindicator :
      (fun z ↦ (seriesCrossingRegion x).indicator g
        ((seriesCrossingEquiv x) z)) =
        seriesParameterRegion.indicator
          (fun z ↦ rho (x - z.2) * rho (x - z.2 - z.1)) := by
    funext z
    rw [← Set.indicator_comp_right]
    rw [seriesCrossingEquiv_preimage]
    rfl
  rw [hindicator, integral_indicator measurableSet_seriesParameterRegion,
    integral_indicator (measurableSet_seriesCrossingRegion x)] at hchange
  simpa only [g] using hchange

private theorem parallelParameter_integral_eq_crossing (rho : ℝ → ℝ)
    (x : ℝ) :
    (∫ z in parallelParameterRegion,
        rho (x + z.2) * rho (x + z.2 + z.1) ∂(volume.prod volume)) =
      ∫ z in parallelCrossingRegion x,
        rho z.1 * rho z.2 ∂(volume.prod volume) := by
  let g : ℝ × ℝ → ℝ := fun z ↦ rho z.1 * rho z.2
  have hchange :=
    (parallelCrossingEquiv_measurePreserving x).integral_comp
      (parallelCrossingEquiv x).measurableEmbedding
      ((parallelCrossingRegion x).indicator g)
  have hindicator :
      (fun z ↦ (parallelCrossingRegion x).indicator g
        ((parallelCrossingEquiv x) z)) =
        parallelParameterRegion.indicator
          (fun z ↦ rho (x + z.2) * rho (x + z.2 + z.1)) := by
    funext z
    rw [← Set.indicator_comp_right]
    rw [parallelCrossingEquiv_preimage]
    rfl
  rw [hindicator, integral_indicator measurableSet_parallelParameterRegion,
    integral_indicator (measurableSet_parallelCrossingRegion x)] at hchange
  simpa only [g] using hchange

/-- `Iminus` is exactly one ordered series-crossing probability. -/
theorem Iminus_eq_seriesCrossing_measureReal (rho : ℝ → ℝ)
    (hrho_meas : Measurable rho) (hrho : Integrable rho)
    (hrho_nonneg : ∀ y, 0 ≤ rho y) (x : ℝ) :
    Iminus rho x =
      ((densityLaw rho).prod (densityLaw rho)).real
        (seriesCrossingRegion x) := by
  rw [Iminus_eq_integral_seriesParameterRegion rho hrho x]
  rw [seriesParameter_integral_eq_crossing]
  exact (densityProduct_measureReal rho hrho_meas hrho hrho_nonneg
    (measurableSet_seriesCrossingRegion x)).symm

/-- `Iplus` is exactly one ordered resistance-parallel crossing probability. -/
theorem Iplus_eq_parallelCrossing_measureReal (rho : ℝ → ℝ)
    (hrho_meas : Measurable rho) (hrho : Integrable rho)
    (hrho_nonneg : ∀ y, 0 ≤ rho y) (x : ℝ) :
    Iplus rho x =
      ((densityLaw rho).prod (densityLaw rho)).real
        (parallelCrossingRegion x) := by
  rw [Iplus_eq_integral_parallelParameterRegion rho hrho x]
  rw [parallelParameter_integral_eq_crossing]
  exact (densityProduct_measureReal rho hrho_meas hrho hrho_nonneg
    (measurableSet_parallelCrossingRegion x)).symm

/-! ## Event partitions and exact CDF formulas -/

private def diagonalRegion : Set (ℝ × ℝ) :=
  {z | z.1 = z.2}

private def seriesGateRegion (x : ℝ) : Set (ℝ × ℝ) :=
  {z | logSeriesGate z.1 z.2 ≤ x}

private def parallelGateRegion (x : ℝ) : Set (ℝ × ℝ) :=
  {z | logParallelGate .resistance z.1 z.2 ≤ x}

private def lowerCoordinateRegion (x : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ x ∨ z.2 ≤ x}

private theorem measurableSet_diagonalRegion : MeasurableSet diagonalRegion :=
  measurableSet_eq_fun measurable_fst measurable_snd

private theorem measurableSet_seriesGateRegion (x : ℝ) :
    MeasurableSet (seriesGateRegion x) :=
  measurableSet_le measurable_logSeriesGate_pair measurable_const

private theorem measurableSet_parallelGateRegion (x : ℝ) :
    MeasurableSet (parallelGateRegion x) :=
  measurableSet_le measurable_logResistanceParallelGate_pair measurable_const

private theorem measurableSet_lowerCoordinateRegion (x : ℝ) :
    MeasurableSet (lowerCoordinateRegion x) := by
  exact (measurableSet_le measurable_fst measurable_const).union
    (measurableSet_le measurable_snd measurable_const)

private theorem densityLaw_prod_diagonal_zero (rho : ℝ → ℝ)
    [IsProbabilityMeasure (densityLaw rho)] :
    ((densityLaw rho).prod (densityLaw rho)) diagonalRegion = 0 := by
  letI : NullSingletonClass (densityLaw rho) := by
    unfold densityLaw
    infer_instance
  rw [Measure.prod_apply measurableSet_diagonalRegion]
  simp [diagonalRegion]

private theorem logSeriesGate_comm (u v : ℝ) :
    logSeriesGate u v = logSeriesGate v u := by
  unfold logSeriesGate
  rw [add_comm]

private theorem logResistanceParallelGate_comm (u v : ℝ) :
    logParallelGate .resistance u v =
      logParallelGate .resistance v u := by
  simp only [logParallelGate_resistance]
  rw [add_comm]

private theorem le_logSeriesGate_left (u v : ℝ) :
    u ≤ logSeriesGate u v := by
  rw [logSeriesGate_eq_max_add_h]
  linarith [le_max_left u v, h_nonneg |u - v|]

private theorem le_logSeriesGate_right (u v : ℝ) :
    v ≤ logSeriesGate u v := by
  rw [logSeriesGate_eq_max_add_h]
  linarith [le_max_right u v, h_nonneg |u - v|]

private theorem logResistanceParallelGate_le_left (u v : ℝ) :
    logParallelGate .resistance u v ≤ u := by
  rw [logParallelGate_eq_min_sub_h]
  simp only [Mode.eta_resistance, one_mul]
  linarith [min_le_left u v, h_nonneg |u - v|]

private theorem logResistanceParallelGate_le_right (u v : ℝ) :
    logParallelGate .resistance u v ≤ v := by
  rw [logParallelGate_eq_min_sub_h]
  simp only [Mode.eta_resistance, one_mul]
  linarith [min_le_right u v, h_nonneg |u - v|]

private theorem series_crossing_partition (x : ℝ) :
    (seriesCrossingRegion x \ diagonalRegion) ∪
      (Prod.swap ⁻¹' (seriesCrossingRegion x \ diagonalRegion)) =
      (((Iic x ×ˢ Iic x) \ seriesGateRegion x) \ diagonalRegion) := by
  ext z
  rcases z with ⟨u, v⟩
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_preimage, Set.mem_prod,
    Set.mem_setOf_eq, Prod.swap_prod_mk, mem_Iic, seriesCrossingRegion,
    diagonalRegion, seriesGateRegion]
  change
    (((v ≤ u ∧ u ≤ x ∧ x < logSeriesGate u v) ∧ u ≠ v) ∨
      ((u ≤ v ∧ v ≤ x ∧ x < logSeriesGate v u) ∧ v ≠ u)) ↔
      (((u ≤ x ∧ v ≤ x) ∧ ¬logSeriesGate u v ≤ x) ∧ u ≠ v)
  rw [logSeriesGate_comm v u]
  constructor
  · rintro (⟨⟨hvu, hux, hxg⟩, hne⟩ | ⟨⟨huv, hvx, hxg⟩, hne⟩)
    · exact ⟨⟨⟨hux, hvu.trans hux⟩, not_le.mpr hxg⟩, hne⟩
    · exact ⟨⟨⟨huv.trans hvx, hvx⟩, not_le.mpr hxg⟩, hne.symm⟩
  · rintro ⟨⟨⟨hux, hvx⟩, hxg⟩, hne⟩
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact Or.inr ⟨⟨huv.le, hvx, lt_of_not_ge hxg⟩, hne.symm⟩
    · exact Or.inl ⟨⟨hvu.le, hux, lt_of_not_ge hxg⟩, hne⟩

private theorem parallel_crossing_partition (x : ℝ) :
    (parallelCrossingRegion x \ diagonalRegion) ∪
      (Prod.swap ⁻¹' (parallelCrossingRegion x \ diagonalRegion)) =
      (((parallelGateRegion x \ lowerCoordinateRegion x) \ diagonalRegion)) := by
  ext z
  rcases z with ⟨u, v⟩
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_preimage,
    Set.mem_setOf_eq, Prod.swap_prod_mk, parallelCrossingRegion,
    diagonalRegion, parallelGateRegion, lowerCoordinateRegion]
  change
    (((u ≤ v ∧ x < u ∧ logParallelGate .resistance u v ≤ x) ∧
        u ≠ v) ∨
      ((v ≤ u ∧ x < v ∧ logParallelGate .resistance v u ≤ x) ∧
        v ≠ u)) ↔
      (((logParallelGate .resistance u v ≤ x ∧ ¬(u ≤ x ∨ v ≤ x))) ∧
        u ≠ v)
  rw [logResistanceParallelGate_comm v u]
  constructor
  · rintro (⟨⟨huv, hxu, hgx⟩, hne⟩ | ⟨⟨hvu, hxv, hgx⟩, hne⟩)
    · exact ⟨⟨hgx, not_or_intro (not_le.mpr hxu) (not_le.mpr (hxu.trans_le huv))⟩,
        hne⟩
    · exact ⟨⟨hgx, not_or_intro (not_le.mpr (hxv.trans_le hvu)) (not_le.mpr hxv)⟩,
        hne.symm⟩
  · rintro ⟨⟨hgx, hnot⟩, hne⟩
    have hxu : x < u := lt_of_not_ge fun hux ↦ hnot (Or.inl hux)
    have hxv : x < v := lt_of_not_ge fun hvx ↦ hnot (Or.inr hvx)
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact Or.inl ⟨⟨huv.le, hxu, hgx⟩, hne⟩
    · exact Or.inr ⟨⟨hvu.le, hxv, hgx⟩, hne.symm⟩

private theorem crossing_halves_disjoint (s : Set (ℝ × ℝ))
    (hs : ∀ z ∈ s, z.2 ≤ z.1) :
    Disjoint (s \ diagonalRegion)
      (Prod.swap ⁻¹' (s \ diagonalRegion)) := by
  rw [Set.disjoint_left]
  intro z hz hswap
  have hle := hs z hz.1
  have hle' := hs z.swap hswap.1
  have heq : z.1 = z.2 := le_antisymm hle' hle
  exact hz.2 heq

private theorem crossing_halves_disjoint' (s : Set (ℝ × ℝ))
    (hs : ∀ z ∈ s, z.1 ≤ z.2) :
    Disjoint (s \ diagonalRegion)
      (Prod.swap ⁻¹' (s \ diagonalRegion)) := by
  rw [Set.disjoint_left]
  intro z hz hswap
  have hle := hs z hz.1
  have hle' := hs z.swap hswap.1
  have heq : z.1 = z.2 := le_antisymm hle hle'
  exact hz.2 heq

private theorem series_crossing_difference_measureReal (rho : ℝ → ℝ)
    [IsProbabilityMeasure (densityLaw rho)] (x : ℝ) :
    ((densityLaw rho).prod (densityLaw rho)).real
        ((Iic x ×ˢ Iic x) \ seriesGateRegion x) =
      2 * ((densityLaw rho).prod (densityLaw rho)).real
        (seriesCrossingRegion x) := by
  let mu := densityLaw rho
  let nu := mu.prod mu
  letI : IsProbabilityMeasure mu := inferInstance
  letI : IsProbabilityMeasure nu := inferInstance
  have hdiag : nu diagonalRegion = 0 := densityLaw_prod_diagonal_zero rho
  have hcross : MeasurableSet (seriesCrossingRegion x \ diagonalRegion) :=
    (measurableSet_seriesCrossingRegion x).diff measurableSet_diagonalRegion
  have hswap :
      nu.real (Prod.swap ⁻¹' (seriesCrossingRegion x \ diagonalRegion)) =
        nu.real (seriesCrossingRegion x \ diagonalRegion) :=
    (Measure.measurePreserving_swap (μ := mu) (ν := mu)).measureReal_preimage
      hcross.nullMeasurableSet
  have htrim :
      nu.real (seriesCrossingRegion x \ diagonalRegion) =
        nu.real (seriesCrossingRegion x) := by
    unfold Measure.real
    rw [measure_sdiff_null hdiag]
  have hdisjoint :
      Disjoint (seriesCrossingRegion x \ diagonalRegion)
        (Prod.swap ⁻¹' (seriesCrossingRegion x \ diagonalRegion)) :=
    crossing_halves_disjoint _ fun z hz ↦ hz.1
  have hunion := measureReal_union (μ := nu) hdisjoint
    (hcross.preimage measurable_swap)
  calc
    nu.real ((Iic x ×ˢ Iic x) \ seriesGateRegion x) =
        nu.real (((Iic x ×ˢ Iic x) \ seriesGateRegion x) \
          diagonalRegion) := by
      unfold Measure.real
      rw [measure_sdiff_null hdiag]
    _ = nu.real ((seriesCrossingRegion x \ diagonalRegion) ∪
        (Prod.swap ⁻¹' (seriesCrossingRegion x \ diagonalRegion))) := by
      rw [series_crossing_partition]
    _ = nu.real (seriesCrossingRegion x \ diagonalRegion) +
        nu.real (Prod.swap ⁻¹' (seriesCrossingRegion x \ diagonalRegion)) := hunion
    _ = 2 * nu.real (seriesCrossingRegion x) := by
      rw [hswap, htrim]
      ring

private theorem parallel_crossing_difference_measureReal (rho : ℝ → ℝ)
    [IsProbabilityMeasure (densityLaw rho)] (x : ℝ) :
    ((densityLaw rho).prod (densityLaw rho)).real
        (parallelGateRegion x \ lowerCoordinateRegion x) =
      2 * ((densityLaw rho).prod (densityLaw rho)).real
        (parallelCrossingRegion x) := by
  let mu := densityLaw rho
  let nu := mu.prod mu
  letI : IsProbabilityMeasure mu := inferInstance
  letI : IsProbabilityMeasure nu := inferInstance
  have hdiag : nu diagonalRegion = 0 := densityLaw_prod_diagonal_zero rho
  have hcross : MeasurableSet (parallelCrossingRegion x \ diagonalRegion) :=
    (measurableSet_parallelCrossingRegion x).diff measurableSet_diagonalRegion
  have hswap :
      nu.real (Prod.swap ⁻¹' (parallelCrossingRegion x \ diagonalRegion)) =
        nu.real (parallelCrossingRegion x \ diagonalRegion) :=
    (Measure.measurePreserving_swap (μ := mu) (ν := mu)).measureReal_preimage
      hcross.nullMeasurableSet
  have htrim :
      nu.real (parallelCrossingRegion x \ diagonalRegion) =
        nu.real (parallelCrossingRegion x) := by
    unfold Measure.real
    rw [measure_sdiff_null hdiag]
  have hdisjoint :
      Disjoint (parallelCrossingRegion x \ diagonalRegion)
        (Prod.swap ⁻¹' (parallelCrossingRegion x \ diagonalRegion)) :=
    crossing_halves_disjoint' _ fun z hz ↦ hz.1
  have hunion := measureReal_union (μ := nu) hdisjoint
    (hcross.preimage measurable_swap)
  calc
    nu.real (parallelGateRegion x \ lowerCoordinateRegion x) =
        nu.real ((parallelGateRegion x \ lowerCoordinateRegion x) \
          diagonalRegion) := by
      unfold Measure.real
      rw [measure_sdiff_null hdiag]
    _ = nu.real ((parallelCrossingRegion x \ diagonalRegion) ∪
        (Prod.swap ⁻¹' (parallelCrossingRegion x \ diagonalRegion))) := by
      rw [parallel_crossing_partition]
    _ = nu.real (parallelCrossingRegion x \ diagonalRegion) +
        nu.real (Prod.swap ⁻¹' (parallelCrossingRegion x \ diagonalRegion)) := hunion
    _ = 2 * nu.real (parallelCrossingRegion x) := by
      rw [hswap, htrim]
      ring

private theorem seriesCDF_eq_gateRegion_measureReal (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    seriesCDF mu x = (mu.prod mu).real (seriesGateRegion x) := by
  letI : IsProbabilityMeasure (seriesLaw mu) :=
    seriesLaw_isProbabilityMeasure mu
  unfold seriesCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold seriesLaw
  rw [map_measureReal_apply measurable_logSeriesGate_pair measurableSet_Iic]
  rfl

private theorem parallelCDF_eq_gateRegion_measureReal (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    parallelCDF mu x = (mu.prod mu).real (parallelGateRegion x) := by
  letI : IsProbabilityMeasure (parallelLaw mu) :=
    parallelLaw_isProbabilityMeasure mu
  unfold parallelCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold parallelLaw
  rw [map_measureReal_apply measurable_logResistanceParallelGate_pair
    measurableSet_Iic]
  rfl

private theorem seriesGateRegion_subset_square (x : ℝ) :
    seriesGateRegion x ⊆ Iic x ×ˢ Iic x := by
  rintro ⟨u, v⟩ hg
  exact ⟨(le_logSeriesGate_left u v).trans hg,
    (le_logSeriesGate_right u v).trans hg⟩

private theorem lowerCoordinateRegion_subset_parallelGateRegion (x : ℝ) :
    lowerCoordinateRegion x ⊆ parallelGateRegion x := by
  rintro ⟨u, v⟩ (hu | hv)
  · exact (logResistanceParallelGate_le_left u v).trans hu
  · exact (logResistanceParallelGate_le_right u v).trans hv

private theorem product_Iic_measureReal (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    (mu.prod mu).real (Iic x ×ˢ Iic x) =
      ProbabilityTheory.cdf mu x ^ 2 := by
  unfold Measure.real
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  change mu.real (Iic x) * mu.real (Iic x) = _
  rw [← ProbabilityTheory.cdf_eq_real mu x]
  ring

private theorem lowerCoordinateRegion_measureReal (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    (mu.prod mu).real (lowerCoordinateRegion x) =
      2 * ProbabilityTheory.cdf mu x -
        ProbabilityTheory.cdf mu x ^ 2 := by
  let nu := mu.prod mu
  letI : IsProbabilityMeasure nu := inferInstance
  have hcomp : (lowerCoordinateRegion x)ᶜ = Ioi x ×ˢ Ioi x := by
    ext z
    rcases z with ⟨u, v⟩
    simp only [lowerCoordinateRegion, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_prod, mem_Ioi]
    push Not
    rfl
  have htail : mu.real (Ioi x) = 1 - ProbabilityTheory.cdf mu x := by
    rw [← Set.compl_Iic]
    rw [measureReal_compl measurableSet_Iic, probReal_univ]
    rw [← ProbabilityTheory.cdf_eq_real mu x]
  have hprod : nu.real (Ioi x ×ˢ Ioi x) =
      (1 - ProbabilityTheory.cdf mu x) ^ 2 := by
    unfold Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    change mu.real (Ioi x) * mu.real (Ioi x) = _
    rw [htail]
    ring
  have hcomplement :=
    measureReal_compl (μ := nu) (measurableSet_lowerCoordinateRegion x)
  rw [hcomp, hprod, probReal_univ] at hcomplement
  linarith

/-- Exact series CDF formula for an absolutely continuous probability density. -/
theorem seriesCDF_density_formula (rho : ℝ → ℝ)
    (hrho_meas : Measurable rho) (hrho : Integrable rho)
    (hrho_nonneg : ∀ y, 0 ≤ rho y) (hrho_mass : ∫ y, rho y = 1)
    (x : ℝ) :
    seriesCDF (densityLaw rho) x =
      ProbabilityTheory.cdf (densityLaw rho) x ^ 2 -
        2 * Iminus rho x := by
  letI : IsProbabilityMeasure (densityLaw rho) :=
    densityLaw_isProbabilityMeasure rho hrho hrho_nonneg hrho_mass
  let nu := (densityLaw rho).prod (densityLaw rho)
  letI : IsProbabilityMeasure nu := inferInstance
  rw [seriesCDF_eq_gateRegion_measureReal]
  have hdiff := measureReal_sdiff (μ := nu)
    (seriesGateRegion_subset_square x)
    (measurableSet_seriesGateRegion x)
  have hcross := series_crossing_difference_measureReal rho x
  rw [← Iminus_eq_seriesCrossing_measureReal rho hrho_meas hrho
    hrho_nonneg x] at hcross
  have hsquare := product_Iic_measureReal (densityLaw rho) x
  rw [hsquare] at hdiff
  linarith

/-- Exact resistance-parallel CDF formula for an absolutely continuous density. -/
theorem parallelCDF_density_formula (rho : ℝ → ℝ)
    (hrho_meas : Measurable rho) (hrho : Integrable rho)
    (hrho_nonneg : ∀ y, 0 ≤ rho y) (hrho_mass : ∫ y, rho y = 1)
    (x : ℝ) :
    parallelCDF (densityLaw rho) x =
      2 * ProbabilityTheory.cdf (densityLaw rho) x -
        ProbabilityTheory.cdf (densityLaw rho) x ^ 2 +
          2 * Iplus rho x := by
  letI : IsProbabilityMeasure (densityLaw rho) :=
    densityLaw_isProbabilityMeasure rho hrho hrho_nonneg hrho_mass
  let nu := (densityLaw rho).prod (densityLaw rho)
  letI : IsProbabilityMeasure nu := inferInstance
  rw [parallelCDF_eq_gateRegion_measureReal]
  have hdiff := measureReal_sdiff (μ := nu)
    (lowerCoordinateRegion_subset_parallelGateRegion x)
    (measurableSet_lowerCoordinateRegion x)
  have hcross := parallel_crossing_difference_measureReal rho x
  rw [← Iplus_eq_parallelCrossing_measureReal rho hrho_meas hrho
    hrho_nonneg x] at hcross
  have hbase := lowerCoordinateRegion_measureReal (densityLaw rho) x
  rw [hbase] at hdiff
  linarith

/-- The exact biased CDF operator, now with the two density formulas discharged. -/
theorem exact_cdf_operator_density (p : unitInterval) (rho : ℝ → ℝ)
    (delta x : ℝ) (hrho_meas : Measurable rho)
    (hrho : Integrable rho) (hrho_nonneg : ∀ y, 0 ≤ rho y)
    (hrho_mass : ∫ y, rho y = 1) (hp : (p : ℝ) = 1 / 2 + delta) :
    cdfOperator p (densityLaw rho) x -
        ProbabilityTheory.cdf (densityLaw rho) x =
      Iplus rho x - Iminus rho x -
        2 * delta * ProbabilityTheory.cdf (densityLaw rho) x *
          (1 - ProbabilityTheory.cdf (densityLaw rho) x) -
        2 * delta * (Iplus rho x + Iminus rho x) := by
  apply exact_cdf_operator_of_series_parallel p (densityLaw rho)
    (ProbabilityTheory.cdf (densityLaw rho)) rho delta x hp
  · exact seriesCDF_density_formula rho hrho_meas hrho hrho_nonneg
      hrho_mass x
  · exact parallelCDF_density_formula rho hrho_meas hrho hrho_nonneg
      hrho_mass x

end SeriesParallel.MainText
