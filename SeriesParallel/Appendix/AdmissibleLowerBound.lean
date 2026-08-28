import SeriesParallel.Appendix.AdmissibleParameters
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The lower estimate for admissible parameters

This module formalizes the differential inequality in the lower-bound half of
`prop:Cstar-halfline`.  The source obtains the global estimate by applying the
ODE on `(0,1)` and then using continuity at the zero endpoint.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SeriesParallel.Appendix

/-- Equation `eq:ODE divide W`: the derivative of `W_lambda^2` on `(0,1)`. -/
theorem WSolution_sq_hasDerivAt (lambda : ℝ) (hlambda : 0 < lambda)
    {u : ℝ} (hu : u ∈ openUnitInterval) :
    HasDerivAt (fun v ↦ WSolution lambda hlambda v ^ 2)
      (2 * lambda - 2 * (u * (1 - u) / WSolution lambda hlambda u)) u := by
  have hW := WSolution_hasDerivAt lambda hlambda hu
  have hpow := hW.fun_pow 2
  have hWne : WSolution lambda hlambda u ≠ 0 :=
    (WSolution_pos lambda hlambda u hu).ne'
  apply hpow.congr_deriv
  norm_num
  field_simp [hWne]

/-- The derivative in `eq:ODE divide W` is bounded above by `2 lambda`. -/
theorem WSolution_sq_deriv_le (lambda : ℝ) (hlambda : 0 < lambda)
    {u : ℝ} (hu : u ∈ openUnitInterval) :
    2 * lambda - 2 * (u * (1 - u) / WSolution lambda hlambda u) ≤ 2 * lambda := by
  have hu0 : 0 ≤ u := hu.1.le
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2.le
  have hW : 0 < WSolution lambda hlambda u := WSolution_pos lambda hlambda u hu
  have hquot : 0 ≤ u * (1 - u) / WSolution lambda hlambda u := by positivity
  linarith

/-- The auxiliary function `W_lambda(u)^2 - 2 lambda u` is antitone on `[0,1]`. -/
theorem WSolution_sq_sub_antitoneOn (lambda : ℝ) (hlambda : 0 < lambda) :
    AntitoneOn (fun u ↦ WSolution lambda hlambda u ^ 2 - 2 * lambda * u)
      unitInterval := by
  apply ManualInterfaces.MI06_antitoneOn_of_deriv_nonpos (a := 0) (b := 1)
    (by norm_num)
  · exact ((WSolution_continuousOn lambda hlambda).pow 2).sub
      (continuousOn_const.mul continuousOn_id)
  · intro u hu
    let derivativeValue : ℝ :=
      2 * lambda - 2 * (u * (1 - u) / WSolution lambda hlambda u) - 2 * lambda
    refine ⟨derivativeValue, ?_, ?_⟩
    · have hsq := WSolution_sq_hasDerivAt lambda hlambda hu
      have hlinear : HasDerivAt (fun v : ℝ ↦ 2 * lambda * v) (2 * lambda) u := by
        simpa using (hasDerivAt_id u).const_mul (2 * lambda)
      exact hsq.sub hlinear
    · dsimp [derivativeValue]
      linarith [WSolution_sq_deriv_le lambda hlambda hu]

/-- The pointwise square estimate obtained by integrating from the zero endpoint. -/
theorem WSolution_sq_le (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) {u : ℝ} (hu : u ∈ unitInterval) :
    WSolution lambda hlambda u ^ 2 ≤ 2 * lambda * u := by
  have hanti := WSolution_sq_sub_antitoneOn lambda hlambda
    (show (0 : ℝ) ∈ unitInterval by constructor <;> norm_num) hu hu.1
  dsimp only at hanti
  rw [WSolution_zero_of_admissible hlambda hadmissible] at hanti
  norm_num at hanti ⊢
  linarith

/-- The source's estimate `W_lambda(u) ≤ sqrt (2 lambda u)` on `[0,1]`. -/
theorem WSolution_le_sqrt (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) {u : ℝ} (hu : u ∈ unitInterval) :
    WSolution lambda hlambda u ≤ Real.sqrt (2 * lambda * u) := by
  have hrad : 0 ≤ 2 * lambda * u :=
    mul_nonneg (mul_nonneg (by norm_num) hlambda.le) hu.1
  have hsquare := WSolution_sq_le lambda hlambda hadmissible hu
  have hWnonneg : 0 ≤ WSolution lambda hlambda u := by
    unfold WSolution wOfY
    exact Real.cbrt_nonneg.mpr
      (shooting_solution_nonneg hlambda (shootingY_isSolution lambda hlambda)
        (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (2 * lambda * u)]

/-- Canonical endpoint extension upgrades the closed-interval continuity to global continuity. -/
theorem WSolution_continuous (lambda : ℝ) (hlambda : 0 < lambda) :
    Continuous (WSolution lambda hlambda) := by
  have hclamp : Continuous unitClamp := by
    unfold unitClamp
    fun_prop
  have hcomp : ContinuousOn (WSolution lambda hlambda ∘ unitClamp) univ :=
    (WSolution_continuousOn lambda hlambda).comp hclamp.continuousOn
      (fun u _ ↦ unitClamp_mem_unitInterval u)
  apply continuousOn_univ.mp
  convert hcomp using 1
  funext u
  simpa only [Function.comp_apply] using WSolution_isCanonical lambda hlambda u

/-- The nonnegative quotient in the integral identity `eq:lambda-integral-W`. -/
noncomputable def WQuotient (lambda : ℝ) (hlambda : 0 < lambda) (u : ℝ) : ℝ :=
  u * (1 - u) / WSolution lambda hlambda u

/-- On every compact subinterval of `(0,1)`, the quotient in the source is continuous. -/
theorem WQuotient_continuousOn (lambda : ℝ) (hlambda : 0 < lambda)
    {rho : ℝ} (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2) :
    ContinuousOn (WQuotient lambda hlambda) (Icc rho (1 - rho)) := by
  have hsub : Icc rho (1 - rho) ⊆ openUnitInterval := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  unfold WQuotient
  apply ContinuousOn.div
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · exact (WSolution_continuousOn lambda hlambda).mono
      (hsub.trans Ioo_subset_Icc_self)
  · intro u hu
    exact (WSolution_pos lambda hlambda u (hsub hu)).ne'

/-- The exact compact-interval identity used before sending `rho` to zero. -/
theorem WSolution_compact_integral_identity (lambda : ℝ) (hlambda : 0 < lambda)
    {rho : ℝ} (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2) :
    WSolution lambda hlambda (1 - rho) ^ 2 - WSolution lambda hlambda rho ^ 2 =
      2 * lambda * (1 - 2 * rho) -
        2 * ∫ u in rho..(1 - rho), WQuotient lambda hlambda u := by
  let derivativeFormula : ℝ → ℝ := fun u ↦ 2 * lambda - 2 * WQuotient lambda hlambda u
  have hsub : Icc rho (1 - rho) ⊆ openUnitInterval := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hderiv : ∀ u ∈ uIcc rho (1 - rho),
      HasDerivAt (fun v ↦ WSolution lambda hlambda v ^ 2) (derivativeFormula u) u := by
    rw [uIcc_of_le (by linarith : rho ≤ 1 - rho)]
    intro u hu
    simpa only [derivativeFormula, WQuotient] using
      WSolution_sq_hasDerivAt lambda hlambda (hsub hu)
  have hquotientContinuous := WQuotient_continuousOn lambda hlambda hrho hrhoHalf
  have hformulaContinuous : ContinuousOn derivativeFormula (Icc rho (1 - rho)) :=
    continuousOn_const.sub (continuousOn_const.mul hquotientContinuous)
  have hformulaIntegrable : IntervalIntegrable derivativeFormula volume rho (1 - rho) :=
    by
      have hformulaContinuous' : ContinuousOn derivativeFormula (uIcc rho (1 - rho)) := by
        simpa [uIcc_of_le (by linarith : rho ≤ 1 - rho)] using hformulaContinuous
      exact hformulaContinuous'.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hformulaIntegrable
  rw [uIcc_of_le (by linarith : rho ≤ 1 - rho)] at hderiv
  rw [← hFTC]
  unfold derivativeFormula
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul]
  · simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    ring
  · exact intervalIntegrable_const
  · have hcontinuous' :
        ContinuousOn (fun u ↦ 2 * WQuotient lambda hlambda u) (uIcc rho (1 - rho)) := by
      simpa [uIcc_of_le (by linarith : rho ≤ 1 - rho)] using
        hquotientContinuous.const_mul 2
    exact hcontinuous'.intervalIntegrable

/-- Mathlib's almost-everywhere-cover form of monotone convergence gives the
exact compact exhaustion `[rho,1-rho] ↑ (0,1)`. -/
theorem lintegral_Icc_exhaustion_unitInterval (f : ℝ → ℝ≥0∞)
    (hmeasurable : Measurable f) :
    Tendsto (fun rho : ℝ ↦ ∫⁻ x in Icc rho (1 - rho), f x) (𝓝[>] 0)
      (𝓝 (∫⁻ x in Ioo (0 : ℝ) 1, f x)) := by
  have hleft : Tendsto (fun rho : ℝ ↦ rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hright : Tendsto (fun rho : ℝ ↦ 1 - rho) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert (tendsto_const_nhds.sub hleft) using 1 <;> norm_num
  have hcover : MeasureTheory.AECover
      (volume.restrict (Ioo (0 : ℝ) 1)) (𝓝[>] (0 : ℝ))
      (fun rho : ℝ ↦ Icc rho (1 - rho)) :=
    MeasureTheory.aecover_Ioo_of_Icc hleft hright
  have hlimit := hcover.lintegral_tendsto_of_countably_generated
    hmeasurable.aemeasurable
  apply hlimit.congr'
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with rho hrho
  have hsubset : Icc rho (1 - rho) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hrho.1, hrho.2]
  change (∫⁻ x, f x ∂((volume.restrict (Ioo (0 : ℝ) 1)).restrict
      (Icc rho (1 - rho)))) =
    ∫⁻ x, f x ∂(volume.restrict (Icc rho (1 - rho)))
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsubset]

/-- `eq:lambda-integral-W`: for an admissible parameter, `lambda` is the
nonnegative Lebesgue integral of the quotient on the open unit interval. -/
theorem lambda_eq_lintegral (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    ENNReal.ofReal lambda =
      ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (WQuotient lambda hlambda u) := by
  let q : ℝ → ℝ := WQuotient lambda hlambda
  let qENN : ℝ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal (q u)
  have hqMeasurable : Measurable q := by
    unfold q WQuotient
    exact ((measurable_id.mul (measurable_const.sub measurable_id)).div
      (WSolution_continuous lambda hlambda).measurable)
  have hqENNMeasurable : Measurable qENN :=
    ENNReal.measurable_ofReal.comp hqMeasurable
  have hcompactValue : ∀ {rho : ℝ}, 0 < rho → rho < 1 / 2 →
      (∫⁻ u in Icc rho (1 - rho), qENN u) =
        ENNReal.ofReal
          (lambda * (1 - 2 * rho) -
            (WSolution lambda hlambda (1 - rho) ^ 2 -
              WSolution lambda hlambda rho ^ 2) / 2) := by
    intro rho hrho hrhoHalf
    have hrhoOrder : rho ≤ 1 - rho := by linarith
    have hsub : Icc rho (1 - rho) ⊆ openUnitInterval := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2]
    have hqContinuous := WQuotient_continuousOn lambda hlambda hrho hrhoHalf
    have hqIntegrable : IntegrableOn q (Icc rho (1 - rho)) := by
      simpa only [q] using hqContinuous.integrableOn_Icc
    have hqNonneg : ∀ᵐ u ∂volume.restrict (Icc rho (1 - rho)), 0 ≤ q u := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      unfold q WQuotient
      have huOpen := hsub hu
      have hWpos := WSolution_pos lambda hlambda u huOpen
      exact div_nonneg
        (mul_nonneg huOpen.1.le (sub_nonneg.mpr huOpen.2.le)) hWpos.le
    have hsetToInterval : (∫ u in Icc rho (1 - rho), q u) =
        ∫ u in rho..(1 - rho), q u := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrhoOrder]
    have hlintegral : (∫⁻ u in Icc rho (1 - rho), qENN u) =
        ENNReal.ofReal (∫ u in rho..(1 - rho), q u) := by
      unfold qENN
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hqIntegrable hqNonneg,
        hsetToInterval]
    have hidentity := WSolution_compact_integral_identity lambda hlambda hrho hrhoHalf
    rw [hlintegral]
    congr 1
    change WSolution lambda hlambda (1 - rho) ^ 2 -
        WSolution lambda hlambda rho ^ 2 =
      2 * lambda * (1 - 2 * rho) -
        2 * ∫ u in rho..(1 - rho), q u at hidentity
    linarith
  have hWzero : WSolution lambda hlambda 0 = 0 :=
    WSolution_zero_of_admissible hlambda hadmissible
  have hWone : WSolution lambda hlambda 1 = 0 := WSolution_one lambda hlambda
  let endpointValue : ℝ → ℝ := fun rho ↦
    lambda * (1 - 2 * rho) -
      (WSolution lambda hlambda (1 - rho) ^ 2 -
        WSolution lambda hlambda rho ^ 2) / 2
  have hendpointContinuous : Continuous endpointValue := by
    unfold endpointValue
    have hWcontinuous := WSolution_continuous lambda hlambda
    exact (continuous_const.mul (continuous_const.sub
      (continuous_const.mul continuous_id))).sub
        ((((hWcontinuous.comp (continuous_const.sub continuous_id)).pow 2).sub
          (hWcontinuous.pow 2)).div_const 2)
  have hendpointZero : endpointValue 0 = lambda := by
    unfold endpointValue
    norm_num [hWzero, hWone]
  have hendpointLimit : Tendsto endpointValue (𝓝[>] (0 : ℝ)) (𝓝 lambda) := by
    rw [← hendpointZero]
    exact hendpointContinuous.continuousAt.tendsto.mono_left inf_le_left
  have hcompactLimit :
      Tendsto (fun rho : ℝ ↦ ∫⁻ u in Icc rho (1 - rho), qENN u)
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal lambda)) := by
    have hofRealLimit : Tendsto (fun rho ↦ ENNReal.ofReal (endpointValue rho))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal lambda)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hendpointLimit
    have hhalf : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), rho < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
    apply hofRealLimit.congr'
    filter_upwards [self_mem_nhdsWithin, hhalf] with rho hrho hrhoHalf
    simpa only [qENN, endpointValue] using (hcompactValue hrho hrhoHalf).symm
  have hexhaustion :=
    lintegral_Icc_exhaustion_unitInterval qENN hqENNMeasurable
  have hunique := tendsto_nhds_unique hexhaustion hcompactLimit
  simpa only [qENN, q] using hunique.symm

/-- The quotient in `eq:lambda-integral-W` is Bochner integrable on `(0,1)`. -/
theorem WQuotient_integrableOn (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    IntegrableOn (WQuotient lambda hlambda) (Ioo (0 : ℝ) 1) := by
  have hmeasurable : Measurable (WQuotient lambda hlambda) := by
    unfold WQuotient
    exact ((measurable_id.mul (measurable_const.sub measurable_id)).div
      (WSolution_continuous lambda hlambda).measurable)
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ WQuotient lambda hlambda u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    unfold WQuotient
    exact div_nonneg (mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le))
      (WSolution_pos lambda hlambda u hu).le
  apply (lintegral_ofReal_ne_top_iff_integrable
    hmeasurable.aestronglyMeasurable hnonneg).mp
  rw [← lambda_eq_lintegral lambda hlambda hadmissible]
  exact ENNReal.ofReal_ne_top

/-- `eq:lambda-integral-W` in the paper's real-valued integral notation. -/
theorem lambda_eq_integral (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    lambda = ∫ u in Ioo (0 : ℝ) 1, WQuotient lambda hlambda u := by
  have hintegrable := WQuotient_integrableOn lambda hlambda hadmissible
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ WQuotient lambda hlambda u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    unfold WQuotient
    exact div_nonneg (mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le))
      (WSolution_pos lambda hlambda u hu).le
  have hintegralNonneg :
      0 ≤ ∫ u in Ioo (0 : ℝ) 1, WQuotient lambda hlambda u :=
    integral_nonneg_of_ae hnonneg
  apply (ENNReal.ofReal_eq_ofReal_iff hlambda.le hintegralNonneg).mp
  calc
    ENNReal.ofReal lambda =
        ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (WQuotient lambda hlambda u) :=
      lambda_eq_lintegral lambda hlambda hadmissible
    _ = ENNReal.ofReal (∫ u in Ioo (0 : ℝ) 1, WQuotient lambda hlambda u) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg]

/-- The elementary beta integral occurring in the source's lower estimate. -/
theorem integral_sqrt_mul_one_sub :
    (∫ u in (0 : ℝ)..1, Real.sqrt u * (1 - u)) = 4 / 15 := by
  have hsqrtIntegrable :
      IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u) volume 0 1 :=
    Real.continuous_sqrt.intervalIntegrable 0 1
  have husqrtIntegrable :
      IntervalIntegrable (fun u : ℝ ↦ u * Real.sqrt u) volume 0 1 :=
    (continuous_id.mul Real.continuous_sqrt).intervalIntegrable 0 1
  calc
    (∫ u in (0 : ℝ)..1, Real.sqrt u * (1 - u)) =
        ∫ u in (0 : ℝ)..1, Real.sqrt u - u * Real.sqrt u := by
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = (∫ u in (0 : ℝ)..1, Real.sqrt u) -
        ∫ u in (0 : ℝ)..1, u * Real.sqrt u := by
      rw [intervalIntegral.integral_sub hsqrtIntegrable husqrtIntegrable]
    _ = (∫ u in (0 : ℝ)..1, u ^ (1 / 2 : ℝ)) -
        ∫ u in (0 : ℝ)..1, u ^ (3 / 2 : ℝ) := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro u _
        exact Real.sqrt_eq_rpow u
      · apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : 0 ≤ u := by
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu.1
        change u * Real.sqrt u = u ^ (3 / 2 : ℝ)
        rw [Real.sqrt_eq_rpow]
        have hadd := Real.rpow_add_one' hu0
          (show (1 / 2 : ℝ) + 1 ≠ 0 by norm_num)
        norm_num at hadd ⊢
        nlinarith
    _ = 4 / 15 := by
      rw [integral_rpow (r := (1 / 2 : ℝ)) (by norm_num),
        integral_rpow (r := (3 / 2 : ℝ)) (by norm_num)]
      norm_num

/-- Pointwise substitution of the square-root estimate into the quotient. -/
theorem sqrt_lower_le_WQuotient (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) {u : ℝ}
    (hu : u ∈ openUnitInterval) :
    Real.sqrt u * (1 - u) / Real.sqrt (2 * lambda) ≤
      WQuotient lambda hlambda u := by
  have hu0 : 0 < u := hu.1
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  have htwoLambda : 0 < 2 * lambda := mul_pos (by norm_num) hlambda
  have hrad : 0 < 2 * lambda * u := mul_pos htwoLambda hu0
  have hW : 0 < WSolution lambda hlambda u := WSolution_pos lambda hlambda u hu
  have hWle : WSolution lambda hlambda u ≤ Real.sqrt (2 * lambda * u) :=
    WSolution_le_sqrt lambda hlambda hadmissible ⟨hu0.le, hu.2.le⟩
  have hsqrtRad : 0 < Real.sqrt (2 * lambda * u) := Real.sqrt_pos.2 hrad
  have hnumerator : 0 ≤ u * (1 - u) := mul_nonneg hu0.le hu1.le
  have hdivision : u * (1 - u) / Real.sqrt (2 * lambda * u) ≤
      u * (1 - u) / WSolution lambda hlambda u := by
    rw [div_le_div_iff₀ hsqrtRad hW]
    exact mul_le_mul_of_nonneg_left hWle hnumerator
  have hsqrtMul : Real.sqrt (2 * lambda * u) =
      Real.sqrt (2 * lambda) * Real.sqrt u := by
    rw [Real.sqrt_mul htwoLambda.le]
  have hsqrtUSq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  unfold WQuotient
  calc
    Real.sqrt u * (1 - u) / Real.sqrt (2 * lambda) =
        u * (1 - u) / Real.sqrt (2 * lambda * u) := by
      rw [hsqrtMul]
      have hslambda : Real.sqrt (2 * lambda) ≠ 0 := (Real.sqrt_pos.2 htwoLambda).ne'
      have hsu : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu0).ne'
      field_simp [hslambda, hsu]
      nlinarith
    _ ≤ u * (1 - u) / WSolution lambda hlambda u := hdivision

/-- The source's lower-integrand estimate on a compact exhaustion interval. -/
theorem compact_sqrt_integral_le (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) {rho : ℝ}
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2) :
    (∫ u in rho..(1 - rho),
        Real.sqrt u * (1 - u) / Real.sqrt (2 * lambda)) ≤
      lambda * (1 - 2 * rho) -
        (WSolution lambda hlambda (1 - rho) ^ 2 -
          WSolution lambda hlambda rho ^ 2) / 2 := by
  let lower : ℝ → ℝ := fun u ↦ Real.sqrt u * (1 - u) / Real.sqrt (2 * lambda)
  have hlowerContinuous : Continuous lower := by
    unfold lower
    fun_prop
  have hlowerIntegrable : IntervalIntegrable lower volume rho (1 - rho) :=
    hlowerContinuous.intervalIntegrable rho (1 - rho)
  have hquotientContinuous := WQuotient_continuousOn lambda hlambda hrho hrhoHalf
  have hquotientIntegrable :
      IntervalIntegrable (WQuotient lambda hlambda) volume rho (1 - rho) := by
    have hcontinuous' : ContinuousOn (WQuotient lambda hlambda) (uIcc rho (1 - rho)) := by
      simpa [uIcc_of_le (by linarith : rho ≤ 1 - rho)] using hquotientContinuous
    exact hcontinuous'.intervalIntegrable
  have hmono : (∫ u in rho..(1 - rho), lower u) ≤
      ∫ u in rho..(1 - rho), WQuotient lambda hlambda u := by
    apply intervalIntegral.integral_mono_on (by linarith : rho ≤ 1 - rho)
      hlowerIntegrable hquotientIntegrable
    intro u hu
    apply sqrt_lower_le_WQuotient lambda hlambda hadmissible
    exact ⟨hrho.trans_le hu.1, by linarith [hu.2]⟩
  have hidentity := WSolution_compact_integral_identity lambda hlambda hrho hrhoHalf
  change (∫ u in rho..(1 - rho), lower u) ≤ _
  nlinarith

/-- Sending the compact exhaustion parameter to zero yields the numerical inequality
`4 / (15 sqrt (2 lambda)) ≤ lambda`. -/
theorem admissible_numerical_lower_inequality (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    4 / (15 * Real.sqrt (2 * lambda)) ≤ lambda := by
  let lower : ℝ → ℝ := fun u ↦ Real.sqrt u * (1 - u) / Real.sqrt (2 * lambda)
  let rho : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hlowerContinuous : Continuous lower := by
    unfold lower
    fun_prop
  have hprimitive : Continuous (fun b ↦ ∫ u in (0 : ℝ)..b, lower u) :=
    intervalIntegral.continuous_primitive
      (fun a b ↦ hlowerContinuous.intervalIntegrable a b) 0
  have hexhaustionContinuous : Continuous (fun r ↦ ∫ u in r..(1 - r), lower u) := by
    let primitive : ℝ → ℝ := fun b ↦ ∫ u in (0 : ℝ)..b, lower u
    have hcontinuous : Continuous (fun r ↦ primitive (1 - r) - primitive r) :=
      (hprimitive.comp (continuous_const.sub continuous_id)).sub hprimitive
    convert hcontinuous using 1
    funext r
    unfold primitive
    have hleft : IntervalIntegrable lower volume 0 r :=
      hlowerContinuous.intervalIntegrable 0 r
    have hright : IntervalIntegrable lower volume r (1 - r) :=
      hlowerContinuous.intervalIntegrable r (1 - r)
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    ring
  have hrho : Tendsto rho atTop (𝓝 0) := by
    unfold rho
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hintegralLimit :
      Tendsto (fun n ↦ ∫ u in rho n..(1 - rho n), lower u) atTop
        (𝓝 (4 / (15 * Real.sqrt (2 * lambda)))) := by
    have hlimit := hexhaustionContinuous.continuousAt.tendsto.comp hrho
    have hconst : Real.sqrt (2 * lambda) ≠ 0 := by positivity
    convert hlimit using 1
    · funext n
      rfl
    · unfold lower
      norm_num
      rw [integral_sqrt_mul_one_sub]
      field_simp [hconst]
  have hWzero : WSolution lambda hlambda 0 = 0 :=
    WSolution_zero_of_admissible hlambda hadmissible
  have hWone : WSolution lambda hlambda 1 = 0 := WSolution_one lambda hlambda
  have hWcontinuous := WSolution_continuous lambda hlambda
  have hWleft : Tendsto (fun n ↦ WSolution lambda hlambda (rho n)) atTop (𝓝 0) := by
    change Tendsto (WSolution lambda hlambda ∘ rho) atTop (𝓝 0)
    rw [← hWzero]
    exact hWcontinuous.continuousAt.tendsto.comp hrho
  have hWright : Tendsto (fun n ↦ WSolution lambda hlambda (1 - rho n)) atTop (𝓝 0) := by
    have honeMinus : Tendsto (fun n ↦ 1 - rho n) atTop (𝓝 (1 : ℝ)) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hrho using 1 <;> norm_num
    change Tendsto (WSolution lambda hlambda ∘ fun n ↦ 1 - rho n) atTop (𝓝 0)
    rw [← hWone]
    exact hWcontinuous.continuousAt.tendsto.comp honeMinus
  have hrightLimit : Tendsto
      (fun n ↦ lambda * (1 - 2 * rho n) -
        (WSolution lambda hlambda (1 - rho n) ^ 2 -
          WSolution lambda hlambda (rho n) ^ 2) / 2) atTop (𝓝 lambda) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hlambdaT : Tendsto (fun _ : ℕ ↦ lambda) atTop (𝓝 lambda) := tendsto_const_nhds
    have hfactor : Tendsto (fun n ↦ 1 - 2 * rho n) atTop (𝓝 (1 : ℝ)) := by
      convert hone.sub (htwo.mul hrho) using 1 <;> norm_num
    have hfirst : Tendsto (fun n ↦ lambda * (1 - 2 * rho n)) atTop (𝓝 lambda) := by
      convert hlambdaT.mul hfactor using 1 <;> ring
    have hboundary : Tendsto
        (fun n ↦ (WSolution lambda hlambda (1 - rho n) ^ 2 -
          WSolution lambda hlambda (rho n) ^ 2) / 2) atTop (𝓝 0) := by
      have hraw := ((hWright.mul hWright).sub (hWleft.mul hWleft)).div_const 2
      convert hraw using 1
      · funext n
        ring
      · norm_num
    simpa using hfirst.sub hboundary
  apply le_of_tendsto_of_tendsto hintegralLimit hrightLimit
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn ↦ hn⟩] with n hn
  have hrhoPos : 0 < rho n := by
    unfold rho
    positivity
  have hrhoHalf : rho n < 1 / 2 := by
    unfold rho
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1) (by norm_num)]
    norm_num
    exact_mod_cast Nat.succ_lt_succ hn
  exact compact_sqrt_integral_le lambda hlambda hadmissible hrhoPos hrhoHalf

/-- Every admissible parameter satisfies the source's explicit lower bound. -/
theorem lambdaLower_le_of_admissible (lambda : ℝ) (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    lambdaLower ≤ lambda := by
  have hnum := admissible_numerical_lower_inequality lambda hlambda hadmissible
  have hsqrtPos : 0 < Real.sqrt (2 * lambda) := by positivity
  have hmul : 4 / 15 ≤ lambda * Real.sqrt (2 * lambda) := by
    rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 15) hsqrtPos)] at hnum
    nlinarith
  have hrightNonneg : 0 ≤ lambda * Real.sqrt (2 * lambda) :=
    mul_nonneg hlambda.le hsqrtPos.le
  have hsquare : (4 / 15 : ℝ) ^ 2 ≤
      (lambda * Real.sqrt (2 * lambda)) ^ 2 := by
    nlinarith [sq_nonneg (lambda * Real.sqrt (2 * lambda) + 4 / 15)]
  have hsqrtSq : Real.sqrt (2 * lambda) ^ 2 = 2 * lambda := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num) hlambda.le)
  have hcube : 8 / 225 ≤ lambda ^ 3 := by
    nlinarith
  by_contra hnot
  have hlt : lambda < lambdaLower := lt_of_not_ge hnot
  have hcubelt : lambda ^ 3 < lambdaLower ^ 3 :=
    pow_lt_pow_left₀ hlt hlambda.le (by norm_num)
  rw [lambdaLower_cube] at hcubelt
  linarith

/-- Set-membership form of the lower estimate. -/
theorem lambdaLower_le_of_mem_admissibleSet {lambda : ℝ}
    (hadmissible : lambda ∈ admissibleSet) : lambdaLower ≤ lambda := by
  rcases hadmissible with ⟨hlambda, hzero⟩
  exact lambdaLower_le_of_admissible lambda hlambda hzero

/-- The critical parameter is defined only after the admissible set has been
shown nonempty and every admissible parameter has acquired the uniform strict
positive lower bound. -/
noncomputable def lambdaStar : ℝ := sInf admissibleSet

theorem lambdaLower_le_lambdaStar : lambdaLower ≤ lambdaStar := by
  exact le_csInf admissibleSet_nonempty (fun _ h ↦ lambdaLower_le_of_mem_admissibleSet h)

theorem lambdaStar_pos : 0 < lambdaStar :=
  lambdaLower_pos.trans_le lambdaLower_le_lambdaStar

theorem lambdaStar_le_upper : lambdaStar ≤ lambdaUpper := by
  exact csInf_le admissibleSet_bddBelow lambdaUpper_mem_admissibleSet

end SeriesParallel.Appendix
