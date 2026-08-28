import SeriesParallel.MainTextInterface
import SeriesParallel.ManualInterfaces
import SeriesParallel.Appendix.SubcriticalW
import SeriesParallel.Appendix.EndpointAsymptotics
import SeriesParallel.Appendix.LinearBranchRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# Full-line and hard-edge profiles

This file records the source-facing objects and conclusions of
`cor:wave-relative-derivatives` and `cor:subcritical-profile`.  In particular, the
hard-edge profile uses derivatives within `[0,∞)` at zero; its zero extension is
not incorrectly asserted to be two-sided differentiable there.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-! ## Integral coordinates and phase equations -/

/-- The positive reciprocal speed in the full-line integral coordinate. -/
noncomputable def fullLineCoordinateIntegrand (input : MainInput) (W : ℝ → ℝ)
    (s : ℝ) : ℝ :=
  (input.beta * W (1 - s))⁻¹

/-- `eq:full-line-profile-coordinate`: the coordinate `Θ_λ` before inversion. -/
noncomputable def fullLineCoordinate (input : MainInput) (W : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ s in (1 / 2 : ℝ)..v, fullLineCoordinateIntegrand input W s

/-- The positive reciprocal speed in the hard-edge integral coordinate. -/
noncomputable def halfLineCoordinateIntegrand (input : MainInput) (W : ℝ → ℝ)
    (s : ℝ) : ℝ :=
  (input.beta * W s)⁻¹

/-- The half-line coordinate `z(v)` used in the proof of
`cor:subcritical-profile`. -/
noncomputable def halfLineCoordinate (input : MainInput) (W : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..v, halfLineCoordinateIntegrand input W s

/-- Every canonical shooting transform is smooth in the open interval. -/
theorem WSolution_contDiffOn_infty_interior (lambda : ℝ) (hlambda : 0 < lambda) :
    ContDiffOn ℝ ∞ (WSolution lambda hlambda) openUnitInterval := by
  apply ManualInterfaces.MI09_ode_regularity_bootstrap_infty
    (positiveWField lambda) positiveWFieldDomain openUnitInterval
      (WSolution lambda hlambda)
  · exact isOpen_positiveWFieldDomain
  · exact positiveWField_contDiffOn lambda
  · exact isOpen_Ioo
  · intro u hu
    exact WSolution_pos lambda hlambda u hu
  · intro u hu
    exact WSolution_hasDerivAt_positiveWField lambda hlambda hu

/-- Smoothness and positivity of the full-line coordinate integrand. -/
theorem fullLineCoordinateIntegrand_contDiffOn {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) :
    ContDiffOn ℝ ∞ (fullLineCoordinateIntegrand input W) openUnitInterval := by
  have hreflect : ContDiffOn ℝ ∞ (fun s : ℝ ↦ 1 - s) openUnitInterval :=
    (contDiff_const.sub contDiff_id).contDiffOn
  have hmaps : MapsTo (fun s : ℝ ↦ 1 - s) openUnitInterval openUnitInterval := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hcomp : ContDiffOn ℝ ∞ (W ∘ fun s : ℝ ↦ 1 - s) openUnitInterval :=
    hW.comp hreflect hmaps
  have hprod : ContDiffOn ℝ ∞
      (fun s : ℝ ↦ input.beta * W (1 - s)) openUnitInterval := by
    simpa only [Function.comp_apply] using contDiffOn_const.mul hcomp
  have hinv := hprod.inv fun s hs ↦
    mul_ne_zero input.beta_ne_zero (hpos (1 - s) (hmaps hs)).ne'
  exact hinv

/-- Smoothness and positivity of the hard-edge coordinate integrand in `(0,1)`. -/
theorem halfLineCoordinateIntegrand_contDiffOn {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) :
    ContDiffOn ℝ ∞ (halfLineCoordinateIntegrand input W) openUnitInterval := by
  have hprod : ContDiffOn ℝ ∞ (fun s : ℝ ↦ input.beta * W s) openUnitInterval :=
    contDiffOn_const.mul hW
  exact hprod.inv fun s hs ↦ mul_ne_zero input.beta_ne_zero (hpos s hs).ne'

/-- One-sided smoothness of the hard-edge coordinate integrand, including `s=0`. -/
theorem halfLineCoordinateIntegrand_contDiffOn_Ico {input : MainInput}
    {W : ℝ → ℝ} (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    ContDiffOn ℝ ∞ (halfLineCoordinateIntegrand input W) (Ico (0 : ℝ) 1) := by
  have hprod : ContDiffOn ℝ ∞ (fun s : ℝ ↦ input.beta * W s) (Ico (0 : ℝ) 1) :=
    contDiffOn_const.mul hW
  exact hprod.inv fun s hs ↦ mul_ne_zero input.beta_ne_zero (hpos s hs).ne'

private theorem uIcc_zero_subset_Ico {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) :
    uIcc (0 : ℝ) v ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  rw [uIcc_of_le hv.1] at hx
  exact ⟨hx.1, hx.2.trans_lt hv.2⟩

/-- FTC at positive points of the hard-edge coordinate. -/
theorem halfLineCoordinate_hasDerivAt {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) {v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (halfLineCoordinate input W)
      (halfLineCoordinateIntegrand input W v) v := by
  have hsmooth := halfLineCoordinateIntegrand_contDiffOn_Ico
    (input := input) hW hpos
  have hcontinuous := hsmooth.continuousOn
  have hvIco : v ∈ Ico (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
  have hint : IntervalIntegrable (halfLineCoordinateIntegrand input W) volume 0 v :=
    (hcontinuous.mono (uIcc_zero_subset_Ico hvIco)).intervalIntegrable
  have hinterior : Ioo (0 : ℝ) 1 ⊆ Ico (0 : ℝ) 1 := fun _ hx ↦ ⟨hx.1.le, hx.2⟩
  have hcontinuousAt : ContinuousAt (halfLineCoordinateIntegrand input W) v :=
    (hcontinuous.mono hinterior).continuousAt (isOpen_Ioo.mem_nhds hv)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hcontinuous.mono hinterior) v hv) hcontinuousAt

/-- Right derivative of the hard-edge coordinate at its finite endpoint. -/
theorem halfLineCoordinate_hasDerivWithinAt_zero {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    HasDerivWithinAt (halfLineCoordinate input W)
      (halfLineCoordinateIntegrand input W 0) (Ici 0) 0 := by
  have hsmooth := halfLineCoordinateIntegrand_contDiffOn_Ico
    (input := input) hW hpos
  have hcontinuous := hsmooth.continuousOn
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  have hrightMem : Ico (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ico_mem_nhdsGT zero_lt_one
  have hsourceLe : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico (0 : ℝ) 1] (0 : ℝ) := by
    refine le_inf inf_le_left ?_
    exact le_principal_iff.mpr hrightMem
  have hcontinuousRight : ContinuousWithinAt
      (halfLineCoordinateIntegrand input W) (Ioi 0) 0 :=
    (hcontinuous 0 hzero).mono_left hsourceLe
  have hmeas : StronglyMeasurableAtFilter (halfLineCoordinateIntegrand input W)
      (𝓝[>] (0 : ℝ)) volume := by
    exact ⟨Ico (0 : ℝ) 1, hrightMem,
      hcontinuous.aestronglyMeasurable measurableSet_Ico⟩
  have hraw := intervalIntegral.integral_hasDerivWithinAt_right
    (a := (0 : ℝ)) (b := (0 : ℝ)) (s := Ici (0 : ℝ)) (t := Ioi (0 : ℝ))
    (f := halfLineCoordinateIntegrand input W) (by simp) hmeas hcontinuousRight
  change HasDerivWithinAt
    (fun u : ℝ ↦ ∫ x in (0 : ℝ)..u, halfLineCoordinateIntegrand input W x)
      (halfLineCoordinateIntegrand input W 0) (Ici 0) 0
  exact hraw

/-- The hard-edge coordinate is one-sided `C∞` on `[0,1)`. -/
theorem halfLineCoordinate_contDiffOn_Ico {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    ContDiffOn ℝ ∞ (halfLineCoordinate input W) (Ico (0 : ℝ) 1) := by
  have hsmooth := halfLineCoordinateIntegrand_contDiffOn_Ico
    (input := input) hW hpos
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ico (0 : ℝ) 1)]
  constructor
  · intro v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hvpos
    · exact (halfLineCoordinate_hasDerivWithinAt_zero hW hpos).differentiableWithinAt.mono
        (fun _ hx ↦ hx.1)
    · exact (halfLineCoordinate_hasDerivAt hW hpos ⟨hvpos, hv.2⟩).differentiableAt
        |>.differentiableWithinAt
  · apply hsmooth.congr
    intro v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hvpos
    · exact ((halfLineCoordinate_hasDerivWithinAt_zero hW hpos).mono
        (fun _ hx ↦ hx.1)).derivWithin (uniqueDiffOn_Ico (0 : ℝ) 1 0 hv)
    · exact ((halfLineCoordinate_hasDerivAt hW hpos ⟨hvpos, hv.2⟩).hasDerivWithinAt)
        |>.derivWithin (uniqueDiffOn_Ico (0 : ℝ) 1 v hv)

private theorem uIcc_half_subset_openUnit {v : ℝ} (hv : v ∈ openUnitInterval) :
    uIcc (1 / 2 : ℝ) v ⊆ openUnitInterval := by
  intro x hx
  by_cases hhalf : (1 / 2 : ℝ) ≤ v
  · rw [uIcc_of_le hhalf] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, hv.2]⟩
  · have hvhalf : v ≤ (1 / 2 : ℝ) := le_of_not_ge hhalf
    rw [uIcc_of_ge hvhalf] at hx
    exact ⟨by linarith [hx.1, hv.1], by linarith [hx.2]⟩

/-- FTC for the full-line integral coordinate at every interior point. -/
theorem fullLineCoordinate_hasDerivAt {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) {v : ℝ}
    (hv : v ∈ openUnitInterval) :
    HasDerivAt (fullLineCoordinate input W)
      (fullLineCoordinateIntegrand input W v) v := by
  have hsmooth := fullLineCoordinateIntegrand_contDiffOn (input := input) hW hpos
  have hcontinuous := hsmooth.continuousOn
  have hint : IntervalIntegrable (fullLineCoordinateIntegrand input W) volume
      (1 / 2 : ℝ) v :=
    (hcontinuous.mono (uIcc_half_subset_openUnit hv)).intervalIntegrable
  have hcontinuousAt : ContinuousAt (fullLineCoordinateIntegrand input W) v :=
    hcontinuous.continuousAt (isOpen_Ioo.mem_nhds hv)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcontinuous v hv) hcontinuousAt

/-- The integral coordinate is smooth on `(0,1)`. -/
theorem fullLineCoordinate_contDiffOn {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) :
    ContDiffOn ℝ ∞ (fullLineCoordinate input W) openUnitInterval := by
  change ContDiffOn ℝ ∞ (fullLineCoordinate input W) (Ioo (0 : ℝ) 1)
  apply (contDiffOn_infty_iff_deriv_of_isOpen (𝕜 := ℝ)
    (f := fullLineCoordinate input W) isOpen_Ioo).2
  constructor
  · intro v hv
    exact (fullLineCoordinate_hasDerivAt hW hpos hv).differentiableAt.differentiableWithinAt
  · have hsmooth := fullLineCoordinateIntegrand_contDiffOn (input := input) hW hpos
    exact hsmooth.congr fun v hv ↦ (fullLineCoordinate_hasDerivAt hW hpos hv).deriv

theorem fullLineCoordinate_deriv_pos {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) {v : ℝ}
    (hv : v ∈ openUnitInterval) :
    0 < deriv (fullLineCoordinate input W) v := by
  rw [(fullLineCoordinate_hasDerivAt hW hpos hv).deriv]
  unfold fullLineCoordinateIntegrand
  exact inv_pos.mpr (mul_pos input.beta_pos (hpos (1 - v) ⟨by linarith [hv.2],
    by linarith [hv.1]⟩))

@[simp]
theorem fullLineCoordinate_half (input : MainInput) (W : ℝ → ℝ) :
    fullLineCoordinate input W (1 / 2) = 0 := by
  simp [fullLineCoordinate]

/-- Reflection sends a right-hand approach to zero to a left-hand approach to one. -/
theorem tendsto_one_sub_nhdsGT_zero_nhdsLT_one :
    Tendsto (fun s : ℝ ↦ 1 - s) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hfull : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have ht : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 (0 : ℝ))
          (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub tendsto_id
      simpa only [sub_zero] using ht
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    show 1 - s < 1
    linarith

/-- A correct logarithmic-divergence lemma at the left endpoint.  In contrast to the
old MI17 admission, this includes continuity and strict positivity on every truncated
interval, so every Bochner interval integral used below is genuinely integrable. -/
theorem logarithmicIntegralDivergenceLeft_of_continuousOn_pos
    (f : ℝ → ℝ) (c s₀ : ℝ) (hc : 0 < c) (hs₀ : 0 < s₀)
    (hcontinuous : ContinuousOn f (Ioc 0 s₀))
    (hpos : ∀ s ∈ Ioc (0 : ℝ) s₀, 0 < f s)
    (hequiv : (fun s ↦ f s) ~[𝓝[>] (0 : ℝ)] (fun s ↦ c * s)) :
    Tendsto (fun v ↦ ∫ s in s₀..v, (f s)⁻¹) (𝓝[>] (0 : ℝ)) atBot := by
  have hdenom : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_ne_zero hc.ne' hs.ne'
  have hratio : Tendsto (fun s ↦ f s / (c * s)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hdenom).mp hequiv
  have hratio_lt : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s / (c * s) < 2 :=
    hratio.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  rcases (mem_nhdsGT_iff_exists_Ioo_subset.mp hratio_lt) with ⟨d, hd, hbound⟩
  let δ : ℝ := min d (s₀ / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hd (half_pos hs₀)
  have hδd : δ ≤ d := min_le_left _ _
  have hδs₀ : δ < s₀ :=
    (min_le_right d (s₀ / 2)).trans_lt (half_lt_self hs₀)
  have hf_upper : ∀ s ∈ Ioo (0 : ℝ) δ, f s ≤ 2 * c * s := by
    intro s hs
    have hratio_s : f s / (c * s) < 2 := hbound ⟨hs.1, hs.2.trans_le hδd⟩
    have hcs : 0 < c * s := mul_pos hc hs.1
    have := (div_lt_iff₀ hcs).mp hratio_s
    nlinarith
  let C : ℝ := ∫ s in δ..s₀, (f s)⁻¹
  have hcomparison : ∀ v ∈ Ioo (0 : ℝ) δ,
      (∫ s in s₀..v, (f s)⁻¹) ≤
        (2 * c)⁻¹ * Real.log v +
          (-((2 * c)⁻¹ * Real.log δ) - C) := by
    intro v hv
    have hvδ : v ≤ δ := hv.2.le
    have hvpos : 0 < v := hv.1
    have hfint : IntervalIntegrable (fun s ↦ (f s)⁻¹) volume v δ := by
      apply (hcontinuous.mono ?_).inv₀ ?_ |>.intervalIntegrable
      · intro s hs
        simp only [uIcc_of_le hvδ] at hs
        exact ⟨hvpos.trans_le hs.1, hs.2.trans hδs₀.le⟩
      · intro s hs
        simp only [uIcc_of_le hvδ] at hs
        exact (hpos s ⟨hvpos.trans_le hs.1, hs.2.trans hδs₀.le⟩).ne'
    have hgint : IntervalIntegrable (fun s : ℝ ↦ (2 * c * s)⁻¹) volume v δ := by
      apply ((continuous_const.mul continuous_id).continuousOn.inv₀ ?_).intervalIntegrable
      intro s hs
      simp only [uIcc_of_le hvδ] at hs
      exact mul_ne_zero (mul_ne_zero (by norm_num) hc.ne') (hvpos.trans_le hs.1).ne'
    have hmono : (∫ s in v..δ, (2 * c * s)⁻¹) ≤
        ∫ s in v..δ, (f s)⁻¹ := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hvδ hgint hfint
      intro s hs
      have hspos : 0 < s := hvpos.trans hs.1
      have hfpos : 0 < f s := hpos s ⟨hspos, (hs.2.trans hδs₀).le⟩
      rw [inv_le_inv₀ (mul_pos (mul_pos (by norm_num) hc) hspos) hfpos]
      exact hf_upper s ⟨hspos, hs.2⟩
    have hmodel : (∫ s in v..δ, (2 * c * s)⁻¹) =
        (2 * c)⁻¹ * (Real.log δ - Real.log v) := by
      calc
        (∫ s in v..δ, (2 * c * s)⁻¹) =
            ∫ s in v..δ, (2 * c)⁻¹ * s⁻¹ := by
              apply intervalIntegral.integral_congr
              intro s _
              by_cases hs : s = 0
              · simp [hs]
              · field_simp [hc.ne', hs]
        _ =
            (2 * c)⁻¹ * ∫ s in v..δ, s⁻¹ := by
              rw [intervalIntegral.integral_const_mul]
        _ = (2 * c)⁻¹ * Real.log (δ / v) := by
              rw [integral_inv_of_pos hvpos hδ]
        _ = (2 * c)⁻¹ * (Real.log δ - Real.log v) := by
              rw [Real.log_div hδ.ne' hvpos.ne']
    have hadd : (∫ s in v..s₀, (f s)⁻¹) =
        (∫ s in v..δ, (f s)⁻¹) + C := by
      dsimp only [C]
      exact (intervalIntegral.integral_add_adjacent_intervals hfint
        ((hcontinuous.mono (fun s hs ↦ by
            simp only [uIcc_of_le hδs₀.le] at hs
            exact ⟨hδ.trans_le hs.1, hs.2⟩)).inv₀
          (fun s hs ↦ by
            simp only [uIcc_of_le hδs₀.le] at hs
            exact (hpos s ⟨hδ.trans_le hs.1, hs.2⟩).ne')).intervalIntegrable).symm
    rw [intervalIntegral.integral_symm, hadd]
    rw [hmodel] at hmono
    nlinarith
  have hlimit : Tendsto
      (fun v : ℝ ↦ (2 * c)⁻¹ * Real.log v +
        (-((2 * c)⁻¹ * Real.log δ) - C))
      (𝓝[>] (0 : ℝ)) atBot := by
    have hscale : 0 < (2 * c)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hc)
    exact tendsto_atBot_add_const_right _ _
      (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hscale)
  have hcomparison_eventually : ∀ᶠ v in 𝓝[>] (0 : ℝ),
      (∫ s in s₀..v, (f s)⁻¹) ≤
        (2 * c)⁻¹ * Real.log v + (-((2 * c)⁻¹ * Real.log δ) - C) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with v hv
    exact hcomparison v hv
  exact tendsto_atBot_mono' _ hcomparison_eventually hlimit

/-- The corresponding correct right-endpoint statement, proved by reflecting
`s ↦ 1-s` and applying the left-endpoint comparison theorem. -/
theorem logarithmicIntegralDivergenceRight_of_continuousOn_pos
    (f : ℝ → ℝ) (c s₀ : ℝ) (hc : 0 < c) (hs₀ : s₀ < 1)
    (hcontinuous : ContinuousOn f (Ico s₀ 1))
    (hpos : ∀ s ∈ Ico s₀ (1 : ℝ), 0 < f s)
    (hequiv : (fun s ↦ f s) ~[𝓝[<] (1 : ℝ)] (fun s ↦ c * (1 - s))) :
    Tendsto (fun v ↦ ∫ s in s₀..v, (f s)⁻¹) (𝓝[<] (1 : ℝ)) atTop := by
  let g : ℝ → ℝ := fun r ↦ f (1 - r)
  have hgcontinuous : ContinuousOn g (Ioc 0 (1 - s₀)) := by
    exact hcontinuous.comp (continuousOn_const.sub continuousOn_id) fun r hr ↦
      ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hgpos : ∀ r ∈ Ioc (0 : ℝ) (1 - s₀), 0 < g r := by
    intro r hr
    exact hpos (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hgequiv : (fun r ↦ g r) ~[𝓝[>] (0 : ℝ)] (fun r ↦ c * r) := by
    have hcomp := hequiv.comp_tendsto tendsto_one_sub_nhdsGT_zero_nhdsLT_one
    refine hcomp.congr ?_ ?_
    all_goals
      intro r
      simp only [g, Function.comp_apply, Pi.sub_apply]
      ring
  have hleft := logarithmicIntegralDivergenceLeft_of_continuousOn_pos
    g c (1 - s₀) hc (sub_pos.mpr hs₀) hgcontinuous hgpos hgequiv
  have hcomp := hleft.comp tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  change Tendsto (fun v ↦ ∫ s in (1 - s₀)..(1 - v), (g s)⁻¹)
    (𝓝[<] (1 : ℝ)) atBot at hcomp
  have hneg : Tendsto
      (fun v ↦ -((fun r ↦ ∫ s in (1 - s₀)..r, (g s)⁻¹) (1 - v)))
      (𝓝[<] (1 : ℝ)) atTop := by
    rw [← tendsto_neg_atBot_iff]
    simpa only [neg_neg] using hcomp
  convert hneg using 1
  funext v
  dsimp only [g]
  rw [intervalIntegral.integral_comp_sub_left (fun s ↦ (f s)⁻¹) 1]
  have hv : (1 : ℝ) - (1 - v) = v := by ring
  have hs₀' : (1 : ℝ) - (1 - s₀) = s₀ := by ring
  rw [hv, hs₀']
  exact intervalIntegral.integral_symm v s₀

/-- The left logarithmic divergence of `Θ`, obtained from the linear branch at `u=1`. -/
theorem fullLineCoordinate_tendsto_atBot {input : MainInput} {lambda : ℝ}
    {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hlinear : HasLinearBranchAtOne lambda W) :
    Tendsto (fullLineCoordinate input W) (𝓝[>] (0 : ℝ)) atBot := by
  have hcomp := hlinear.comp_tendsto tendsto_one_sub_nhdsGT_zero_nhdsLT_one
  have hbeta : (fun _ : ℝ ↦ input.beta) ~[𝓝[>] (0 : ℝ)]
      (fun _ : ℝ ↦ input.beta) := IsEquivalent.refl
  have hmul := hbeta.mul hcomp
  have hequiv : (fun s : ℝ ↦ input.beta * W (1 - s)) ~[𝓝[>] (0 : ℝ)]
      (fun s : ℝ ↦ (input.beta / lambda) * s) := by
    refine hmul.congr ?_ ?_
    · intro s
      simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]
      field_simp [hlambda.ne']
      ring
    · intro s
      simp only [Function.comp_apply, Pi.mul_apply]
      field_simp [hlambda.ne']
      ring
  have hltOne : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (show ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Iio 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hcontinuous : ContinuousOn (fun s : ℝ ↦ input.beta * W (1 - s))
      (Ioc 0 (1 / 2)) := by
    exact continuousOn_const.mul (hW.continuousOn.comp
      (continuousOn_const.sub continuousOn_id) fun s hs ↦
        ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hpositive : ∀ s ∈ Ioc (0 : ℝ) (1 / 2), 0 < input.beta * W (1 - s) := by
    intro s hs
    exact mul_pos input.beta_pos (hpos (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  change Tendsto (fun v : ℝ ↦
    ∫ s in (1 / 2 : ℝ)..v, (input.beta * W (1 - s))⁻¹) (𝓝[>] (0 : ℝ)) atBot
  exact logarithmicIntegralDivergenceLeft_of_continuousOn_pos
    (fun s : ℝ ↦ input.beta * W (1 - s)) (input.beta / lambda) (1 / 2)
    (div_pos input.beta_pos hlambda) (by norm_num) hcontinuous hpositive hequiv

/-- The right logarithmic divergence of `Θ`, obtained from the linear branch at `u=0`. -/
theorem fullLineCoordinate_tendsto_atTop {input : MainInput} {lambda : ℝ}
    {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hlinear : HasLinearBranchAtZero lambda W) :
    Tendsto (fullLineCoordinate input W) (𝓝[<] (1 : ℝ)) atTop := by
  have hcomp := hlinear.comp_tendsto tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  have hbeta : (fun _ : ℝ ↦ input.beta) ~[𝓝[<] (1 : ℝ)]
      (fun _ : ℝ ↦ input.beta) := IsEquivalent.refl
  have hmul := hbeta.mul hcomp
  have hequiv : (fun s : ℝ ↦ input.beta * W (1 - s)) ~[𝓝[<] (1 : ℝ)]
      (fun s : ℝ ↦ (input.beta / lambda) * (1 - s)) := by
    refine hmul.congr ?_ ?_
    · intro s
      simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]
      field_simp [hlambda.ne']
    · intro s
      simp only [Function.comp_apply, Pi.mul_apply]
      field_simp [hlambda.ne']
  have hgtZero : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s :=
    (show ∀ᶠ s in 𝓝 (1 : ℝ), s ∈ Ioi 0 from
      Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hcontinuous : ContinuousOn (fun s : ℝ ↦ input.beta * W (1 - s))
      (Ico (1 / 2) 1) := by
    exact continuousOn_const.mul (hW.continuousOn.comp
      (continuousOn_const.sub continuousOn_id) fun s hs ↦
        ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hpositive : ∀ s ∈ Ico (1 / 2 : ℝ) 1, 0 < input.beta * W (1 - s) := by
    intro s hs
    exact mul_pos input.beta_pos (hpos (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  change Tendsto (fun v : ℝ ↦
    ∫ s in (1 / 2 : ℝ)..v, (input.beta * W (1 - s))⁻¹) (𝓝[<] (1 : ℝ)) atTop
  exact logarithmicIntegralDivergenceRight_of_continuousOn_pos
    (fun s : ℝ ↦ input.beta * W (1 - s)) (input.beta / lambda) (1 / 2)
    (div_pos input.beta_pos hlambda) (by norm_num) hcontinuous hpositive hequiv

private theorem inverse_tendsto_atBot_zero {theta inverse : ℝ → ℝ}
    (hmaps : ∀ z, inverse z ∈ Ioo (0 : ℝ) 1)
    (hleftInverse : ∀ v ∈ Ioo (0 : ℝ) 1, inverse (theta v) = v)
    (hstrict : StrictMono inverse) :
    Tendsto inverse atBot (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun z ↦ ha.trans (hmaps z).1
  · intro b hb
    let e : ℝ := min b 1 / 2
    have hminpos : 0 < min b (1 : ℝ) := lt_min hb zero_lt_one
    have hepos : 0 < e := by
      dsimp only [e]
      positivity
    have heltOne : e < 1 := by
      have hminle : min b (1 : ℝ) ≤ 1 := min_le_right _ _
      dsimp only [e]
      nlinarith
    have heltB : e < b := by
      have hminle : min b (1 : ℝ) ≤ b := min_le_left _ _
      dsimp only [e]
      nlinarith
    filter_upwards [eventually_lt_atBot (theta e)] with z hz
    calc
      inverse z < inverse (theta e) := hstrict hz
      _ = e := hleftInverse e ⟨hepos, heltOne⟩
      _ < b := heltB

private theorem inverse_tendsto_atTop_one {theta inverse : ℝ → ℝ}
    (hmaps : ∀ z, inverse z ∈ Ioo (0 : ℝ) 1)
    (hleftInverse : ∀ v ∈ Ioo (0 : ℝ) 1, inverse (theta v) = v)
    (hstrict : StrictMono inverse) :
    Tendsto inverse atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let e : ℝ := (max a 0 + 1) / 2
    have hmaxlt : max a (0 : ℝ) < 1 := max_lt ha zero_lt_one
    have hepos : 0 < e := by
      have hmaxnonneg : 0 ≤ max a (0 : ℝ) := le_max_right _ _
      dsimp only [e]
      nlinarith
    have heltOne : e < 1 := by
      dsimp only [e]
      nlinarith
    have haelt : a < e := by
      have hale : a ≤ max a (0 : ℝ) := le_max_left _ _
      dsimp only [e]
      nlinarith
    filter_upwards [eventually_gt_atTop (theta e)] with z hz
    calc
      a < e := haelt
      _ = inverse (theta e) := (hleftInverse e ⟨hepos, heltOne⟩).symm
      _ < inverse z := hstrict hz
  · intro b hb
    exact Filter.Eventually.of_forall fun z ↦ (hmaps z).2.trans hb

/-- Right-hand side of `eq:Phi-phase-definition`. -/
noncomputable def wavePhaseRhs (input : MainInput) (W Phi : ℝ → ℝ) (z : ℝ) : ℝ :=
  input.beta * W (1 - Phi z)

/-- Right-hand side of `eq:Psi-subcritical-definition`. -/
noncomputable def hardEdgePhaseRhs (input : MainInput) (W Psi : ℝ → ℝ) (z : ℝ) : ℝ :=
  input.beta * W (Psi z)

/-- A normalized full-line solution of the phase equation, with exactly the source's
range, smoothness, monotonicity, normalization, and two endpoint limits. -/
def IsNormalizedWaveProfile (input : MainInput) (W Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ Phi ∧
    StrictMono Phi ∧
    (∀ z, Phi z ∈ Ioo (0 : ℝ) 1) ∧
    Phi 0 = 1 / 2 ∧
    (∀ z, HasDerivAt Phi (wavePhaseRhs input W Phi z) z) ∧
    Tendsto Phi atBot (𝓝 0) ∧
    Tendsto Phi atTop (𝓝 1)

/-- A half-line solution of the hard-edge phase equation.  The derivative at zero is
the right derivative within `[0,∞)`. -/
def IsNormalizedHardEdgeProfile (input : MainInput) (W Psi : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ Psi (Ici 0) ∧
    StrictMonoOn Psi (Ici 0) ∧
    MapsTo Psi (Ici 0) (Ico 0 1) ∧
    Psi 0 = 0 ∧
    HasDerivWithinAt Psi (hardEdgePhaseRhs input W Psi 0) (Ici 0) 0 ∧
    (∀ z ∈ Ioi (0 : ℝ), HasDerivAt Psi (hardEdgePhaseRhs input W Psi z) z) ∧
    Tendsto Psi atTop (𝓝 1)

/-- The exact B3 uniqueness predicate.  "Increasing" is represented by `Monotone`;
strict increase follows internally from positivity of the phase right-hand side. -/
def IsExactWaveProfile (input : MainInput) (W Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ Phi ∧
    Monotone Phi ∧
    (∀ z, Phi z ∈ Ioo (0 : ℝ) 1) ∧
    Phi 0 = 1 / 2 ∧
    (∀ z, HasDerivAt Phi (wavePhaseRhs input W Phi z) z) ∧
    Tendsto Phi atBot (𝓝 0) ∧
    Tendsto Phi atTop (𝓝 1)

/-- The exact B4 uniqueness predicate.  It records only the monotone half-line phase
data stated in the source; one-sided smoothness and strict increase are derived. -/
def IsExactHardEdgeProfile (input : MainInput) (W Psi : ℝ → ℝ) : Prop :=
  MonotoneOn Psi (Ici 0) ∧
    MapsTo Psi (Ici 0) (Ico 0 1) ∧
    Psi 0 = 0 ∧
    HasDerivWithinAt Psi (hardEdgePhaseRhs input W Psi 0) (Ici 0) 0 ∧
    (∀ z ∈ Ioi (0 : ℝ), HasDerivAt Psi (hardEdgePhaseRhs input W Psi z) z) ∧
    Tendsto Psi atTop (𝓝 1)

theorem IsNormalizedWaveProfile.toExact {input : MainInput} {W Phi : ℝ → ℝ}
    (h : IsNormalizedWaveProfile input W Phi) : IsExactWaveProfile input W Phi := by
  exact ⟨h.1, h.2.1.monotone, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem IsExactWaveProfile.strictMono {input : MainInput} {W Phi : ℝ → ℝ}
    (h : IsExactWaveProfile input W Phi)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) : StrictMono Phi := by
  apply strictMono_of_hasDerivAt_pos h.2.2.2.2.1
  intro z
  unfold wavePhaseRhs
  exact mul_pos input.beta_pos (hpos (1 - Phi z)
    ⟨by linarith [(h.2.2.1 z).2], by linarith [(h.2.2.1 z).1]⟩)

theorem IsExactWaveProfile.toNormalized {input : MainInput} {W Phi : ℝ → ℝ}
    (h : IsExactWaveProfile input W Phi)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u) :
    IsNormalizedWaveProfile input W Phi := by
  exact ⟨h.1, h.strictMono hpos, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem IsNormalizedHardEdgeProfile.toExact {input : MainInput}
    {W Psi : ℝ → ℝ} (h : IsNormalizedHardEdgeProfile input W Psi) :
    IsExactHardEdgeProfile input W Psi := by
  exact ⟨h.2.1.monotoneOn, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem IsExactHardEdgeProfile.strictMonoOn {input : MainInput}
    {W Psi : ℝ → ℝ} (h : IsExactHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    StrictMonoOn Psi (Ici (0 : ℝ)) := by
  have hcontinuous : ContinuousOn Psi (Ici (0 : ℝ)) := by
    intro z hz
    rcases eq_or_lt_of_le (mem_Ici.mp hz) with rfl | hzpos
    · exact h.2.2.2.1.continuousWithinAt
    · exact (h.2.2.2.2.1 z hzpos).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hcontinuous
  rw [interior_Ici]
  intro z hz
  rw [(h.2.2.2.2.1 z hz).deriv]
  unfold hardEdgePhaseRhs
  exact mul_pos input.beta_pos (hpos (Psi z) (h.2.1 (mem_Ici.mpr hz.le)))

/-- The normalized full-line phase exists uniquely once both endpoint branches of `W`
are linear.  This is the inverse-coordinate part of B3. -/
theorem existsUnique_normalizedWaveProfile_of_linear_branches {input : MainInput}
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hzero : HasLinearBranchAtZero lambda W)
    (hone : HasLinearBranchAtOne lambda W) :
    ∃! Phi : ℝ → ℝ, IsNormalizedWaveProfile input W Phi := by
  let theta : ℝ → ℝ := fullLineCoordinate input W
  have hsmooth : ContDiffOn ℝ ∞ theta (Ioo (0 : ℝ) 1) :=
    fullLineCoordinate_contDiffOn hW hpos
  have hderiv : ∀ v ∈ Ioo (0 : ℝ) 1, 0 < deriv theta v := by
    intro v hv
    exact fullLineCoordinate_deriv_pos hW hpos hv
  have hleft : Tendsto theta (𝓝[>] (0 : ℝ)) atBot :=
    fullLineCoordinate_tendsto_atBot hlambda hW hpos hone
  have hright : Tendsto theta (𝓝[<] (1 : ℝ)) atTop :=
    fullLineCoordinate_tendsto_atTop hlambda hW hpos hzero
  rcases ManualInterfaces.MI08_open_interval_global_inverse theta
      (show (0 : ℝ) < 1 by norm_num) hsmooth hderiv hleft hright with
    ⟨Phi, hmaps, hleftInverse, hrightInverse, hPhiSmooth, hPhiDeriv⟩
  have hPhiRange : ∀ z, Phi z ∈ Ioo (0 : ℝ) 1 := by
    intro z
    exact hmaps (Set.mem_univ z)
  have hPhiPhase : ∀ z, HasDerivAt Phi (wavePhaseRhs input W Phi z) z := by
    intro z
    have htheta := fullLineCoordinate_hasDerivAt (input := input) hW hpos
      (hPhiRange z)
    have hraw := hPhiDeriv z
    apply hraw.congr_deriv
    rw [htheta.deriv]
    unfold fullLineCoordinateIntegrand wavePhaseRhs
    rw [inv_inv]
  have hPhiStrict : StrictMono Phi := by
    apply strictMono_of_hasDerivAt_pos hPhiPhase
    intro z
    unfold wavePhaseRhs
    exact mul_pos input.beta_pos (hpos (1 - Phi z) ⟨by linarith [(hPhiRange z).2],
      by linarith [(hPhiRange z).1]⟩)
  have hPhiZero : Phi 0 = 1 / 2 := by
    have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    have hcoordinateHalf : theta (1 / 2 : ℝ) = 0 := by
      change fullLineCoordinate input W (1 / 2 : ℝ) = 0
      exact fullLineCoordinate_half input W
    have hinverseHalf := hleftInverse (1 / 2 : ℝ) hhalf
    rw [hcoordinateHalf] at hinverseHalf
    exact hinverseHalf
  have hPhiLeft : Tendsto Phi atBot (𝓝 0) :=
    inverse_tendsto_atBot_zero hPhiRange hleftInverse hPhiStrict
  have hPhiRight : Tendsto Phi atTop (𝓝 1) :=
    inverse_tendsto_atTop_one hPhiRange hleftInverse hPhiStrict
  refine ⟨Phi, ⟨hPhiSmooth, hPhiStrict, hPhiRange, hPhiZero, hPhiPhase,
    hPhiLeft, hPhiRight⟩, ?_⟩
  intro Psi hPsi
  have hPsiRange : ∀ z, Psi z ∈ Ioo (0 : ℝ) 1 := hPsi.2.2.1
  have hPsiPhase : ∀ z, HasDerivAt Psi (wavePhaseRhs input W Psi z) z :=
    hPsi.2.2.2.2.1
  let error : ℝ → ℝ := fun z ↦ theta (Psi z) - z
  have herrorDeriv : ∀ z, HasDerivAt error 0 z := by
    intro z
    have htheta := fullLineCoordinate_hasDerivAt (input := input) hW hpos
      (hPsiRange z)
    have hcomp := htheta.comp z (hPsiPhase z)
    have honeDeriv : HasDerivAt (fun z : ℝ ↦ theta (Psi z)) 1 z := by
      apply hcomp.congr_deriv
      unfold fullLineCoordinateIntegrand wavePhaseRhs
      have hne : input.beta * W (1 - Psi z) ≠ 0 :=
        mul_ne_zero input.beta_ne_zero
          (hpos (1 - Psi z) ⟨by linarith [(hPsiRange z).2],
            by linarith [(hPsiRange z).1]⟩).ne'
      exact inv_mul_cancel₀ hne
    change HasDerivAt ((fun x : ℝ ↦ theta (Psi x)) - id) 0 z
    simpa only [sub_self] using honeDeriv.sub (hasDerivAt_id z)
  have herrorDiff : Differentiable ℝ error := fun z ↦ (herrorDeriv z).differentiableAt
  have herrorDerivEq : ∀ z, deriv error z = 0 := fun z ↦ (herrorDeriv z).deriv
  funext z
  have hconst := is_const_of_deriv_eq_zero herrorDiff herrorDerivEq z 0
  have hcoordinate : theta (Psi z) = z := by
    have hPsiZero : Psi 0 = 1 / 2 := hPsi.2.2.2.1
    have herrorZero : error 0 = 0 := by
      have hcoordinateHalf : theta (1 / 2 : ℝ) = 0 := by
        change fullLineCoordinate input W (1 / 2 : ℝ) = 0
        exact fullLineCoordinate_half input W
      simp only [error, hPsiZero, hcoordinateHalf, sub_zero]
    have : error z = 0 := hconst.trans herrorZero
    dsimp only [error] at this
    linarith
  calc
    Psi z = Phi (theta (Psi z)) := (hleftInverse (Psi z) (hPsiRange z)).symm
    _ = Phi z := by rw [hcoordinate]

/-- Exact source-facing B3 existence and uniqueness.  Candidate profiles are assumed
only monotone, as in the source; strict monotonicity is derived from the phase ODE. -/
theorem existsUnique_exactWaveProfile_of_linear_branches {input : MainInput}
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hzero : HasLinearBranchAtZero lambda W)
    (hone : HasLinearBranchAtOne lambda W) :
    ∃! Phi : ℝ → ℝ, IsExactWaveProfile input W Phi := by
  rcases existsUnique_normalizedWaveProfile_of_linear_branches hlambda hW hpos hzero hone with
    ⟨Phi, hPhi, hunique⟩
  refine ⟨Phi, hPhi.toExact, ?_⟩
  intro Psi hPsi
  exact hunique Psi (hPsi.toNormalized hpos)

/-- The zero extension of the hard-edge CDF to the whole real line. -/
noncomputable def hardEdgeCDF (Psi : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z < 0 then 0 else Psi z

/-- The full-line density `q=Φ'`, represented by the phase-equation expression. -/
noncomputable def waveDensity (input : MainInput) (W Phi : ℝ → ℝ) (z : ℝ) : ℝ :=
  input.beta * W (1 - Phi z)

/-- The half-line density `q_λ=Ψ_λ'`, including its right-hand value at zero. -/
noncomputable def hardEdgeDensity (input : MainInput) (W Psi : ℝ → ℝ) (z : ℝ) : ℝ :=
  input.beta * W (Psi z)

/-! ## Exact differentiated identities -/

/-- The first differentiated full-line density from the proof of B3. -/
noncomputable def waveDensityD1 (input : MainInput) (W W1 Phi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  -input.beta ^ 2 * W (1 - Phi z) * W1 (1 - Phi z)

/-- The second differentiated full-line density. -/
noncomputable def waveDensityD2 (input : MainInput) (W W1 W2 Phi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  input.beta ^ 3 * W (1 - Phi z) *
    (W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z))

/-- The third differentiated full-line density. -/
noncomputable def waveDensityD3 (input : MainInput) (W W1 W2 W3 Phi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  -input.beta ^ 4 * W (1 - Phi z) *
    (W1 (1 - Phi z) ^ 3 +
      4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
      W (1 - Phi z) ^ 2 * W3 (1 - Phi z))

/-- The first differentiated half-line density from the proof of B4. -/
noncomputable def hardEdgeDensityD1 (input : MainInput) (W W1 Psi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  input.beta ^ 2 * W (Psi z) * W1 (Psi z)

/-- The second differentiated half-line density. -/
noncomputable def hardEdgeDensityD2 (input : MainInput) (W W1 W2 Psi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  input.beta ^ 3 * W (Psi z) *
    (W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z))

/-- The third differentiated half-line density. -/
noncomputable def hardEdgeDensityD3 (input : MainInput) (W W1 W2 W3 Psi : ℝ → ℝ)
    (z : ℝ) : ℝ :=
  input.beta ^ 4 * W (Psi z) *
    (W1 (Psi z) ^ 3 + 4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
      W (Psi z) ^ 2 * W3 (Psi z))

/-- The source's identity `q'=-β²WW'` on the full-line profile. -/
theorem waveDensity_hasDerivAt {input : MainInput} {W W1 Phi : ℝ → ℝ} {z : ℝ}
    (hPhi : HasDerivAt Phi (waveDensity input W Phi z) z)
    (hW : HasDerivAt W (W1 (1 - Phi z)) (1 - Phi z)) :
    HasDerivAt (waveDensity input W Phi) (waveDensityD1 input W W1 Phi z) z := by
  have hinner : HasDerivAt (fun x : ℝ ↦ 1 - Phi x)
      (-waveDensity input W Phi z) z := by
    simpa using hPhi.const_sub 1
  have hcomp := hW.comp z hinner
  have hmul := hcomp.const_mul input.beta
  have h' : HasDerivAt (fun x : ℝ ↦ input.beta * W (1 - Phi x))
      (waveDensityD1 input W W1 Phi z) z := by
    apply hmul.congr_deriv
    simp only [waveDensity, waveDensityD1]
    ring
  exact h'

/-- The source's identity `q'=β²WW'` on the hard-edge profile. -/
theorem hardEdgeDensity_hasDerivAt {input : MainInput} {W W1 Psi : ℝ → ℝ} {z : ℝ}
    (hPsi : HasDerivAt Psi (hardEdgeDensity input W Psi z) z)
    (hW : HasDerivAt W (W1 (Psi z)) (Psi z)) :
    HasDerivAt (hardEdgeDensity input W Psi)
      (hardEdgeDensityD1 input W W1 Psi z) z := by
  have hcomp := hW.comp z hPsi
  have hmul := hcomp.const_mul input.beta
  have h' : HasDerivAt (fun x : ℝ ↦ input.beta * W (Psi x))
      (hardEdgeDensityD1 input W W1 Psi z) z := by
    apply hmul.congr_deriv
    simp only [hardEdgeDensity, hardEdgeDensityD1]
    ring
  exact h'

/-- One-sided form of `q'=β²WW'`, used at the hard edge `z=0`. -/
theorem hardEdgeDensity_hasDerivWithinAt {input : MainInput} {W Psi : ℝ → ℝ}
    {z dW : ℝ} (hPsi : HasDerivWithinAt Psi (hardEdgeDensity input W Psi z)
      (Ici 0) z) (hmaps : MapsTo Psi (Ici 0) (Ici 0))
    (hW : HasDerivWithinAt W dW (Ici 0) (Psi z)) :
    HasDerivWithinAt (hardEdgeDensity input W Psi)
      (input.beta ^ 2 * W (Psi z) * dW) (Ici 0) z := by
  have hcomp := hW.comp z hPsi hmaps
  have hmul := hcomp.const_mul input.beta
  have h' : HasDerivWithinAt (fun x : ℝ ↦ input.beta * W (Psi x))
      (input.beta ^ 2 * W (Psi z) * dW) (Ici 0) z := by
    apply hmul.congr_deriv
    simp only [hardEdgeDensity]
    ring
  exact h'

/-- Differentiating the full-line first-derivative expression gives the source's
second-derivative expression. -/
theorem waveDensityD1_hasDerivAt {input : MainInput} {W W1 W2 Phi : ℝ → ℝ}
    {z : ℝ} (hPhi : HasDerivAt Phi (waveDensity input W Phi z) z)
    (hW : HasDerivAt W (W1 (1 - Phi z)) (1 - Phi z))
    (hW1 : HasDerivAt W1 (W2 (1 - Phi z)) (1 - Phi z)) :
    HasDerivAt (waveDensityD1 input W W1 Phi)
      (waveDensityD2 input W W1 W2 Phi z) z := by
  have hinner : HasDerivAt (fun x : ℝ ↦ 1 - Phi x)
      (-waveDensity input W Phi z) z := by
    simpa using hPhi.const_sub 1
  have hproduct := (hW.comp z hinner).mul (hW1.comp z hinner)
  have hscaled := hproduct.const_mul (-input.beta ^ 2)
  have h' : HasDerivAt (fun x : ℝ ↦ -input.beta ^ 2 *
      ((W ∘ fun y : ℝ ↦ 1 - Phi y) * (W1 ∘ fun y : ℝ ↦ 1 - Phi y)) x)
      (waveDensityD2 input W W1 W2 Phi z) z := by
    apply hscaled.congr_deriv
    simp only [Function.comp_apply, waveDensity, waveDensityD2]
    ring
  convert h' using 1
  funext x
  unfold waveDensityD1
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- Differentiating the half-line first-derivative expression gives the source's
second-derivative expression. -/
theorem hardEdgeDensityD1_hasDerivAt {input : MainInput} {W W1 W2 Psi : ℝ → ℝ}
    {z : ℝ} (hPsi : HasDerivAt Psi (hardEdgeDensity input W Psi z) z)
    (hW : HasDerivAt W (W1 (Psi z)) (Psi z))
    (hW1 : HasDerivAt W1 (W2 (Psi z)) (Psi z)) :
    HasDerivAt (hardEdgeDensityD1 input W W1 Psi)
      (hardEdgeDensityD2 input W W1 W2 Psi z) z := by
  have hproduct := (hW.comp z hPsi).mul (hW1.comp z hPsi)
  have hscaled := hproduct.const_mul (input.beta ^ 2)
  have h' : HasDerivAt
      (fun x : ℝ ↦ input.beta ^ 2 * ((W ∘ Psi) * (W1 ∘ Psi)) x)
      (hardEdgeDensityD2 input W W1 W2 Psi z) z := by
    apply hscaled.congr_deriv
    simp only [Function.comp_apply, hardEdgeDensity, hardEdgeDensityD2]
    ring
  convert h' using 1
  funext x
  unfold hardEdgeDensityD1
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- Differentiating the full-line second-derivative expression gives the source's
third-derivative expression. -/
theorem waveDensityD2_hasDerivAt {input : MainInput} {W W1 W2 W3 Phi : ℝ → ℝ}
    {z : ℝ} (hPhi : HasDerivAt Phi (waveDensity input W Phi z) z)
    (hW : HasDerivAt W (W1 (1 - Phi z)) (1 - Phi z))
    (hW1 : HasDerivAt W1 (W2 (1 - Phi z)) (1 - Phi z))
    (hW2 : HasDerivAt W2 (W3 (1 - Phi z)) (1 - Phi z)) :
    HasDerivAt (waveDensityD2 input W W1 W2 Phi)
      (waveDensityD3 input W W1 W2 W3 Phi z) z := by
  let inner : ℝ → ℝ := fun x ↦ 1 - Phi x
  have hinner : HasDerivAt inner (-waveDensity input W Phi z) z := by
    simpa [inner] using hPhi.const_sub 1
  have hWc := hW.comp z hinner
  have hW1c := hW1.comp z hinner
  have hW2c := hW2.comp z hinner
  have hbracket := (hW1c.pow 2).add (hWc.mul hW2c)
  have hscaled := (hWc.mul hbracket).const_mul (input.beta ^ 3)
  have h' : HasDerivAt
      (fun x : ℝ ↦ input.beta ^ 3 *
        (((W ∘ inner) * ((W1 ∘ inner) ^ 2 + (W ∘ inner) * (W2 ∘ inner))) x))
      (waveDensityD3 input W W1 W2 W3 Phi z) z := by
    apply hscaled.congr_deriv
    simp only [inner, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      waveDensity, waveDensityD3]
    ring
  convert h' using 1
  funext x
  unfold waveDensityD2
  simp only [inner, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  ring

/-- Differentiating the half-line second-derivative expression gives the source's
third-derivative expression. -/
theorem hardEdgeDensityD2_hasDerivAt {input : MainInput} {W W1 W2 W3 Psi : ℝ → ℝ}
    {z : ℝ} (hPsi : HasDerivAt Psi (hardEdgeDensity input W Psi z) z)
    (hW : HasDerivAt W (W1 (Psi z)) (Psi z))
    (hW1 : HasDerivAt W1 (W2 (Psi z)) (Psi z))
    (hW2 : HasDerivAt W2 (W3 (Psi z)) (Psi z)) :
    HasDerivAt (hardEdgeDensityD2 input W W1 W2 Psi)
      (hardEdgeDensityD3 input W W1 W2 W3 Psi z) z := by
  have hWc := hW.comp z hPsi
  have hW1c := hW1.comp z hPsi
  have hW2c := hW2.comp z hPsi
  have hbracket := (hW1c.pow 2).add (hWc.mul hW2c)
  have hscaled := (hWc.mul hbracket).const_mul (input.beta ^ 3)
  have h' : HasDerivAt
      (fun x : ℝ ↦ input.beta ^ 3 *
        (((W ∘ Psi) * ((W1 ∘ Psi) ^ 2 + (W ∘ Psi) * (W2 ∘ Psi))) x))
      (hardEdgeDensityD3 input W W1 W2 W3 Psi z) z := by
    apply hscaled.congr_deriv
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      hardEdgeDensity, hardEdgeDensityD3]
    ring
  convert h' using 1
  funext x
  unfold hardEdgeDensityD2
  simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  ring

/-! ## Phase and profile equations -/

theorem IsNormalizedWaveProfile.deriv_eq_waveDensity {input : MainInput}
    {W Phi : ℝ → ℝ} (h : IsNormalizedWaveProfile input W Phi) (z : ℝ) :
    deriv Phi z = waveDensity input W Phi z := by
  exact (h.2.2.2.2.1 z).deriv

/-- The analytic hard-edge density has the source's positive right-endpoint value. -/
@[simp]
theorem IsNormalizedHardEdgeProfile.hardEdgeDensity_zero {input : MainInput}
    {W Psi : ℝ → ℝ} (h : IsNormalizedHardEdgeProfile input W Psi) :
    hardEdgeDensity input W Psi 0 = input.beta * W 0 := by
  simp only [hardEdgeDensity, h.2.2.2.1]

/-- Strict positivity of the analytic hard-edge density at its finite endpoint. -/
theorem IsNormalizedHardEdgeProfile.hardEdgeDensity_zero_pos {input : MainInput}
    {W Psi : ℝ → ℝ} (h : IsNormalizedHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    0 < hardEdgeDensity input W Psi 0 := by
  rw [h.hardEdgeDensity_zero]
  exact mul_pos input.beta_pos (hpos 0 ⟨le_rfl, zero_lt_one⟩)

/-- On the positive half-line, the analytic hard-edge density is the ordinary
derivative of the phase. -/
theorem IsNormalizedHardEdgeProfile.hardEdgeDensity_eq_deriv {input : MainInput}
    {W Psi : ℝ → ℝ} (h : IsNormalizedHardEdgeProfile input W Psi)
    {z : ℝ} (hz : z ∈ Ioi (0 : ℝ)) :
    hardEdgeDensity input W Psi z = deriv Psi z := by
  simpa only [hardEdgePhaseRhs, hardEdgeDensity] using
    (h.2.2.2.2.2.1 z hz).deriv.symm

theorem IsNormalizedHardEdgeProfile.derivWithin_eq_hardEdgeDensity
    {input : MainInput} {W Psi : ℝ → ℝ}
    (h : IsNormalizedHardEdgeProfile input W Psi) {z : ℝ} (hz : z ∈ Ici (0 : ℝ)) :
    derivWithin Psi (Ici 0) z = hardEdgeDensity input W Psi z := by
  have hzle : 0 ≤ z := hz
  rcases eq_or_lt_of_le hzle with rfl | hzpos
  · simpa only [hardEdgePhaseRhs, hardEdgeDensity] using
      h.2.2.2.2.1.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  · simpa only [hardEdgePhaseRhs, hardEdgeDensity] using
      (h.2.2.2.2.2.1 z hzpos).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Ici (0 : ℝ)) z hz)

/-- At the hard edge, the analytic density is the right derivative of the phase. -/
theorem IsNormalizedHardEdgeProfile.hardEdgeDensity_zero_eq_derivWithin
    {input : MainInput} {W Psi : ℝ → ℝ}
    (h : IsNormalizedHardEdgeProfile input W Psi) :
    hardEdgeDensity input W Psi 0 = derivWithin Psi (Ici 0) 0 := by
  exact (h.derivWithin_eq_hardEdgeDensity (show (0 : ℝ) ∈ Ici 0 by simp)).symm

/-- `eq:appendix-wave-equation`, derived pointwise from the phase equation,
`aβ³=2`, and the W--ODE. -/
theorem waveEquationAt_of_phase_of_wODE {input : MainInput} {lambda : ℝ}
    {W Phi : ℝ → ℝ} {z : ℝ}
    (hPhi : HasDerivAt Phi (waveDensity input W Phi z) z)
    (hWODE : SatisfiesWODEAt lambda W (1 - Phi z)) :
    input.a * waveDensity input W Phi z * deriv (waveDensity input W Phi) z -
        2 * Phi z * (1 - Phi z) =
      -input.kappa lambda * waveDensity input W Phi z := by
  rcases hWODE with ⟨hWdiff, hode⟩
  have hq := waveDensity_hasDerivAt hPhi hWdiff.hasDerivAt
  rw [hq.deriv]
  unfold waveDensity waveDensityD1
  calc
    input.a * (input.beta * W (1 - Phi z)) *
          (-input.beta ^ 2 * W (1 - Phi z) * deriv W (1 - Phi z)) -
          2 * Phi z * (1 - Phi z) =
        -(input.a * input.beta ^ 3) * W (1 - Phi z) ^ 2 *
          deriv W (1 - Phi z) - 2 * Phi z * (1 - Phi z) := by ring
    _ = -2 * W (1 - Phi z) ^ 2 * deriv W (1 - Phi z) -
          2 * Phi z * (1 - Phi z) := by rw [input.a_mul_beta_cube]
    _ = -2 * lambda * W (1 - Phi z) := by
      unfold wODEValue at hode
      nlinarith
    _ = -input.kappa lambda * (input.beta * W (1 - Phi z)) := by
      unfold MainInput.kappa
      field_simp [input.beta_ne_zero]

/-- `eq:subcritical-profile-equation` on the open half-line. -/
theorem hardEdgeProfileEquationAt_of_phase_of_wODE {input : MainInput} {lambda : ℝ}
    {W Psi : ℝ → ℝ} {z : ℝ}
    (hPsi : HasDerivAt Psi (hardEdgeDensity input W Psi z) z)
    (hWODE : SatisfiesWODEAt lambda W (Psi z)) :
    input.a * hardEdgeDensity input W Psi z * deriv (hardEdgeDensity input W Psi) z +
        2 * Psi z * (1 - Psi z) =
      input.kappa lambda * hardEdgeDensity input W Psi z := by
  rcases hWODE with ⟨hWdiff, hode⟩
  have hq := hardEdgeDensity_hasDerivAt hPsi hWdiff.hasDerivAt
  rw [hq.deriv]
  unfold hardEdgeDensity hardEdgeDensityD1
  calc
    input.a * (input.beta * W (Psi z)) *
          (input.beta ^ 2 * W (Psi z) * deriv W (Psi z)) +
          2 * Psi z * (1 - Psi z) =
        (input.a * input.beta ^ 3) * W (Psi z) ^ 2 * deriv W (Psi z) +
          2 * Psi z * (1 - Psi z) := by ring
    _ = 2 * W (Psi z) ^ 2 * deriv W (Psi z) +
          2 * Psi z * (1 - Psi z) := by rw [input.a_mul_beta_cube]
    _ = 2 * lambda * W (Psi z) := by
      unfold wODEValue at hode
      nlinarith
    _ = input.kappa lambda * (input.beta * W (Psi z)) := by
      unfold MainInput.kappa
      field_simp [input.beta_ne_zero]

/-- One-sided version of the hard-edge profile equation, including `z=0`. -/
theorem hardEdgeProfileEquationWithin_of_phase_of_wODE {input : MainInput}
    {lambda : ℝ} {W Psi : ℝ → ℝ} {z dW : ℝ}
    (hz : z ∈ Ici (0 : ℝ))
    (hPsi : HasDerivWithinAt Psi (hardEdgeDensity input W Psi z) (Ici 0) z)
    (hmaps : MapsTo Psi (Ici 0) (Ici 0))
    (hW : HasDerivWithinAt W dW (Ici 0) (Psi z))
    (hode : W (Psi z) ^ 2 * dW - lambda * W (Psi z) +
      Psi z * (1 - Psi z) = 0) :
    input.a * hardEdgeDensity input W Psi z *
          derivWithin (hardEdgeDensity input W Psi) (Ici 0) z +
        2 * Psi z * (1 - Psi z) =
      input.kappa lambda * hardEdgeDensity input W Psi z := by
  have hq := hardEdgeDensity_hasDerivWithinAt hPsi hmaps hW
  have hqderiv := hq.derivWithin ((uniqueDiffOn_Ici (0 : ℝ)) z hz)
  rw [hqderiv]
  unfold hardEdgeDensity
  calc
    input.a * (input.beta * W (Psi z)) *
          (input.beta ^ 2 * W (Psi z) * dW) + 2 * Psi z * (1 - Psi z) =
        (input.a * input.beta ^ 3) * W (Psi z) ^ 2 * dW +
          2 * Psi z * (1 - Psi z) := by ring
    _ = 2 * W (Psi z) ^ 2 * dW + 2 * Psi z * (1 - Psi z) := by
      rw [input.a_mul_beta_cube]
    _ = 2 * lambda * W (Psi z) := by nlinarith
    _ = input.kappa lambda * (input.beta * W (Psi z)) := by
      unfold MainInput.kappa
      field_simp [input.beta_ne_zero]

/-- The three relative derivative identities (B3.4), expressed without division. -/
structure WaveDensityDerivativeIdentities (input : MainInput) (W W1 W2 W3 Phi q :
    ℝ → ℝ) : Prop where
  qValue : ∀ z, q z = input.beta * W (1 - Phi z)
  first : ∀ z, deriv q z = -input.beta ^ 2 * W (1 - Phi z) * W1 (1 - Phi z)
  second : ∀ z, iteratedDeriv 2 q z = input.beta ^ 3 * W (1 - Phi z) *
    (W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z))
  third : ∀ z, iteratedDeriv 3 q z = -input.beta ^ 4 * W (1 - Phi z) *
    (W1 (1 - Phi z) ^ 3 +
      4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
      W (1 - Phi z) ^ 2 * W3 (1 - Phi z))

/-- The three relative derivative identities (B4.5), expressed without division. -/
structure HardEdgeDensityDerivativeIdentities (input : MainInput)
    (W W1 W2 W3 Psi q : ℝ → ℝ) : Prop where
  qValue : ∀ z ∈ Ici (0 : ℝ), q z = input.beta * W (Psi z)
  first : ∀ z ∈ Ici (0 : ℝ), iteratedDerivWithin 1 q (Ici 0) z =
    input.beta ^ 2 * W (Psi z) * W1 (Psi z)
  second : ∀ z ∈ Ici (0 : ℝ), iteratedDerivWithin 2 q (Ici 0) z =
    input.beta ^ 3 * W (Psi z) * (W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z))
  third : ∀ z ∈ Ici (0 : ℝ), iteratedDerivWithin 3 q (Ici 0) z =
    input.beta ^ 4 * W (Psi z) *
      (W1 (Psi z) ^ 3 + 4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
        W (Psi z) ^ 2 * W3 (Psi z))

/-! ## Source-facing profile conclusions -/

/-- Uniform relative derivative bounds through order three on the full line. -/
def FullLineRelativeDerivativeBounds (q : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z : ℝ,
    |iteratedDeriv j q z| ≤ M * q z

/-- Uniform one-sided relative derivative bounds through order three on `[0,∞)`. -/
def HalfLineRelativeDerivativeBounds (q : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z ∈ Ici (0 : ℝ),
    |iteratedDerivWithin j q (Ici 0) z| ≤ M * q z

/-- The two exponential tail bounds stated in B3. -/
def HasTwoSidedExponentialTails (Phi : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (∀ z ≤ 0, Phi z ≤ C * Real.exp (c * z)) ∧
    ∀ z ≥ 0, 1 - Phi z ≤ C * Real.exp (-c * z)

/-- The right exponential tail stated in B4. -/
def HasRightExponentialTail (Psi : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ z ∈ Ici (0 : ℝ), 1 - Psi z ≤ C * Real.exp (-c * z)

/-- The probability law determined by a CDF, together with the exact CDF equation. -/
def IsProbabilityLawOfCDF (cdf : ℝ → ℝ) (mu : Measure ℝ) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ x, mu (Iic x) = ENNReal.ofReal (cdf x)

/-- A positive global `C³` extension of the hard-edge density with the source's
relative derivative bounds. -/
def IsPositiveC3DensityExtension (q extension : ℝ → ℝ) : Prop :=
  ContDiff ℝ 3 extension ∧
    EqOn extension q (Ici 0) ∧
    (∀ z, 0 < extension z) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z : ℝ,
      |iteratedDeriv j extension z| ≤ M * extension z

/-! ## Extension formulas from the final paragraph of B4 -/

/-- `h=log q` on the nonnegative half-line. -/
noncomputable def logDensity (q : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.log (q z)

/-- The cubic polynomial formed from the one-sided jet of `h` at zero. -/
noncomputable def rightJetPolynomial3 (h : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j : Fin 4, iteratedDerivWithin j h (Ici 0) 0 / (j.1.factorial : ℝ) * z ^ j.1

/-- The source's cutoff extension of `h=log q`. -/
noncomputable def extendedLogDensity (q cutoff : ℝ → ℝ) (z : ℝ) : ℝ :=
  if 0 ≤ z then logDensity q z
  else cutoff z * rightJetPolynomial3 (logDensity q) z +
    (1 - cutoff z) * logDensity q 0

/-- The positive extension `qBar=exp(hBar)`. -/
noncomputable def extendedDensity (q cutoff : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (extendedLogDensity q cutoff z)

theorem extendedDensity_pos (q cutoff : ℝ → ℝ) (z : ℝ) :
    0 < extendedDensity q cutoff z := by
  exact Real.exp_pos _

end SeriesParallel.Appendix
