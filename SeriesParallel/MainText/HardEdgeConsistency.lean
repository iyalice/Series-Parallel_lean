/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.DensityGateRegions
import SeriesParallel.MainText.GeneralizedInverseCoupling
import SeriesParallel.MainText.WeightedConsistency
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Hard-edge consistency for the subcritical profile

The physical density is extended by zero, while Taylor expansion is carried out only
with the positive `C³` extension supplied by the hard-edge profile façade.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff ENNReal Topology unitInterval

namespace SeriesParallel.MainText

open SeriesParallel.Appendix
open SeriesParallel.AppendixPublicAPI

/-- The zero-extended hard-edge profile at spatial scale `epsilon`. -/
noncomputable def hardEdgeScaledCDF
    (Psi : ℝ → ℝ) (epsilon x : ℝ) : ℝ :=
  hardEdgeCDF Psi (epsilon * x)

/-- The physical scaled density; its value at the hard edge is zero. -/
noncomputable def hardEdgeScaledDensity
    (input : MainInput) (W Psi : ℝ → ℝ) (epsilon y : ℝ) : ℝ :=
  scaledDensity (zeroExtendedHardEdgeDensity input W Psi) epsilon 0 y

theorem zeroExtendedHardEdgeDensity_eq_positiveZeroExtension
    (input : MainInput) (W Psi : ℝ → ℝ) :
    zeroExtendedHardEdgeDensity input W Psi =
      positiveZeroExtension (hardEdgeDensity input W Psi) := by
  rfl

theorem hardEdgeScaledDensity_nonneg
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (y : ℝ) :
    0 ≤ hardEdgeScaledDensity diffusionMainInput W Psi epsilon y := by
  have hdata := hard_edge_density_probability hprofile
  unfold hardEdgeScaledDensity scaledDensity
  apply mul_nonneg hepsilon
  by_cases hy : 0 < epsilon * y
  · simp only [zero_add, zeroExtendedHardEdgeDensity, if_pos hy]
    exact hdata.1 (epsilon * y) hy.le
  · simp only [zero_add, zeroExtendedHardEdgeDensity, if_neg hy]
    exact le_rfl

theorem zeroExtendedHardEdgeDensity_nonneg
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) (z : ℝ) :
    0 ≤ zeroExtendedHardEdgeDensity diffusionMainInput W Psi z := by
  by_cases hz : 0 < z
  · simp only [zeroExtendedHardEdgeDensity, if_pos hz]
    exact (hard_edge_density_probability hprofile).1 z hz.le
  · simp only [zeroExtendedHardEdgeDensity, if_neg hz]
    exact le_rfl

theorem zeroExtendedHardEdgeDensity_integrable
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) :
    Integrable (zeroExtendedHardEdgeDensity diffusionMainInput W Psi) := by
  exact (hard_edge_density_probability hprofile).2.2.2.1

theorem measurable_zeroExtendedHardEdgeDensity
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) :
    Measurable (zeroExtendedHardEdgeDensity diffusionMainInput W Psi) := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨qbar, hbar⟩ := hard_edge_density_extension_bounds hprofile
  have heq : EqOn qbar q (Ici 0) := hbar.2.1
  rw [zeroExtendedHardEdgeDensity_eq_positiveZeroExtension]
  rw [positiveZeroExtension_congr_of_eqOn heq]
  exact measurable_positiveZeroExtension hbar.1.continuous.measurable

theorem zeroExtendedHardEdgeDensity_integral
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) :
    (∫ z, zeroExtendedHardEdgeDensity diffusionMainInput W Psi z) = 1 := by
  let q0 := zeroExtendedHardEdgeDensity diffusionMainInput W Psi
  have hq0Int : Integrable q0 := by
    exact zeroExtendedHardEdgeDensity_integrable hprofile
  have hq0Nonneg : ∀ z, 0 ≤ q0 z := by
    exact zeroExtendedHardEdgeDensity_nonneg hprofile
  have htail : HasRightExponentialTail Psi :=
    hprofile.2.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure (densityLaw q0) := by
    change IsProbabilityMeasure
      (hardEdgeLaw diffusionMainInput W Psi)
    exact (hardEdgeLaw_probability_with_finiteMean
      hprofile.1 htail).1.1
  have hmeasure : (densityLaw q0) Set.univ = 1 := measure_univ
  have hofReal : ENNReal.ofReal (∫ z, q0 z) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hq0Int
      (Filter.Eventually.of_forall hq0Nonneg)]
    simpa only [densityLaw, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using hmeasure
  exact ENNReal.ofReal_eq_one.mp hofReal

theorem hardEdgeScaledDensity_integrable
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    Integrable (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) := by
  have hq0 := zeroExtendedHardEdgeDensity_integrable hprofile
  have hscaled := hq0.comp_mul_left' hepsilon
  unfold hardEdgeScaledDensity scaledDensity
  simpa only [zero_add] using hscaled.const_mul epsilon

theorem measurable_hardEdgeScaledDensity
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    (epsilon : ℝ) :
    Measurable (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) := by
  unfold hardEdgeScaledDensity scaledDensity
  exact measurable_const.mul
    ((measurable_zeroExtendedHardEdgeDensity hprofile).comp (by fun_prop))

theorem hardEdgeScaledDensity_integral
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (∫ y, hardEdgeScaledDensity diffusionMainInput W Psi epsilon y) = 1 := by
  let q0 := zeroExtendedHardEdgeDensity diffusionMainInput W Psi
  have hmass : (∫ z, q0 z) = 1 := by
    exact zeroExtendedHardEdgeDensity_integral hprofile
  unfold hardEdgeScaledDensity scaledDensity
  simp only [zero_add]
  rw [integral_const_mul]
  rw [Measure.integral_comp_mul_left q0 epsilon, hmass]
  rw [abs_of_pos (inv_pos.mpr hepsilon)]
  simp only [smul_eq_mul]
  field_simp

theorem integral_Iic_scaledDensity
    (q : ℝ → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) (x : ℝ) :
    (∫ y in Iic x, scaledDensity q epsilon 0 y) =
      ∫ z in Iic (epsilon * x), q z := by
  let g : ℝ → ℝ := (Iic (epsilon * x)).indicator q
  have hindicator :
      (Iic x).indicator (fun y ↦ q (epsilon * y)) =
        fun y ↦ g (epsilon * y) := by
    funext y
    by_cases hy : y ≤ x
    · have hscaled : epsilon * y ≤ epsilon * x :=
        (mul_le_mul_iff_of_pos_left hepsilon).2 hy
      simp [g, Set.indicator, hy, hscaled]
    · have hscaled : ¬epsilon * y ≤ epsilon * x := by
        intro hle
        exact hy ((mul_le_mul_iff_of_pos_left hepsilon).1 hle)
      simp [g, Set.indicator, hy, hscaled]
  have hinner :
      (∫ y in Iic x, q (epsilon * y)) =
        |epsilon⁻¹| * ∫ z in Iic (epsilon * x), q z := by
    calc
      (∫ y in Iic x, q (epsilon * y)) =
          ∫ y, (Iic x).indicator (fun u ↦ q (epsilon * u)) y := by
        rw [integral_indicator measurableSet_Iic]
      _ = ∫ y, g (epsilon * y) := by rw [hindicator]
      _ = |epsilon⁻¹| • ∫ z, g z :=
        Measure.integral_comp_mul_left g epsilon
      _ = |epsilon⁻¹| * ∫ z in Iic (epsilon * x), q z := by
        rw [integral_indicator measurableSet_Iic]
        rfl
  unfold scaledDensity
  simp only [zero_add]
  rw [integral_const_mul, hinner, abs_of_pos (inv_pos.mpr hepsilon)]
  field_simp

theorem integral_Iic_zeroExtendedHardEdgeDensity
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) (z : ℝ) :
    (∫ y in Iic z,
        zeroExtendedHardEdgeDensity diffusionMainInput W Psi y) =
      hardEdgeCDF Psi z := by
  let q0 := zeroExtendedHardEdgeDensity diffusionMainInput W Psi
  have hq0Int : Integrable q0 :=
    zeroExtendedHardEdgeDensity_integrable hprofile
  have hq0Nonneg : ∀ y, 0 ≤ q0 y :=
    zeroExtendedHardEdgeDensity_nonneg hprofile
  have htail : HasRightExponentialTail Psi :=
    hprofile.2.2.2.2.2.2.2.1
  have hbaseCDF : Appendix.IsProbabilityLawOfCDF (hardEdgeCDF Psi)
      (densityLaw q0) := by
    change Appendix.IsProbabilityLawOfCDF (hardEdgeCDF Psi)
      (hardEdgeLaw diffusionMainInput W Psi)
    exact (hardEdgeLaw_probability_with_finiteMean
      hprofile.1 htail).1
  have hmeasure := hbaseCDF.2 z
  have hnonnegIntegral : 0 ≤ ∫ y in Iic z, q0 y := by
    exact setIntegral_nonneg measurableSet_Iic fun y _hy ↦ hq0Nonneg y
  have hnonnegCDF : 0 ≤ hardEdgeCDF Psi z :=
    (hardEdgeCDF_range hprofile.1 z).1
  apply (ENNReal.ofReal_eq_ofReal_iff hnonnegIntegral hnonnegCDF).mp
  rw [ofReal_integral_eq_lintegral_ofReal hq0Int.integrableOn
    (Filter.Eventually.of_forall hq0Nonneg)]
  simpa only [densityLaw, withDensity_apply _ measurableSet_Iic]
    using hmeasure

/-- The density-defined physical hard-edge law at spatial scale `epsilon`. -/
noncomputable def hardEdgeScaledLaw
    (input : MainInput) (W Psi : ℝ → ℝ) (epsilon : ℝ) : Measure ℝ :=
  densityLaw (hardEdgeScaledDensity input W Psi epsilon)

theorem hardEdgeScaledLaw_isProbabilityMeasure
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) := by
  unfold hardEdgeScaledLaw
  exact densityLaw_isProbabilityMeasure _
    (hardEdgeScaledDensity_integrable hprofile hepsilon.ne')
    (hardEdgeScaledDensity_nonneg hprofile hepsilon.le)
    (hardEdgeScaledDensity_integral hprofile hepsilon)

theorem cdf_hardEdgeScaledLaw
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ProbabilityTheory.cdf
        (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) =
      hardEdgeScaledCDF Psi epsilon := by
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  have hrhoInt : Integrable rho :=
    hardEdgeScaledDensity_integrable hprofile hepsilon.ne'
  have hrhoNonneg : ∀ y, 0 ≤ rho y :=
    hardEdgeScaledDensity_nonneg hprofile hepsilon.le
  funext x
  rw [ProbabilityTheory.cdf_eq_real]
  unfold Measure.real hardEdgeScaledLaw densityLaw
  rw [withDensity_apply _ measurableSet_Iic]
  have hrhoOn : IntegrableOn rho (Iic x) := hrhoInt.integrableOn
  have hrhoNonnegAE : 0 ≤ᵐ[volume.restrict (Iic x)] rho :=
    Filter.Eventually.of_forall hrhoNonneg
  rw [← ofReal_integral_eq_lintegral_ofReal hrhoOn hrhoNonnegAE]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hrhoNonnegAE)]
  rw [show (∫ y in Iic x, rho y) =
      ∫ z in Iic (epsilon * x),
        zeroExtendedHardEdgeDensity diffusionMainInput W Psi z by
    exact integral_Iic_scaledDensity _ hepsilon x]
  simpa only [hardEdgeScaledCDF] using
    integral_Iic_zeroExtendedHardEdgeDensity hprofile (epsilon * x)

theorem integrable_id_hardEdgeScaledLaw
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Integrable id
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) := by
  let q0 := zeroExtendedHardEdgeDensity diffusionMainInput W Psi
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  have hq0Nonneg : ∀ z, 0 ≤ q0 z :=
    zeroExtendedHardEdgeDensity_nonneg hprofile
  have htail : HasRightExponentialTail Psi :=
    hprofile.2.2.2.2.2.2.2.1
  have hbaseMean : Integrable id (densityLaw q0) := by
    change Integrable id (hardEdgeLaw diffusionMainInput W Psi)
    exact (hardEdgeLaw_probability_with_finiteMean
      hprofile.1 htail).2.2
  have hq0Meas : Measurable q0 :=
    measurable_zeroExtendedHardEdgeDensity hprofile
  have hbaseProduct : Integrable (fun z ↦ z * q0 z) := by
    have hiff := (integrable_withDensity_iff hq0Meas.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp
      hbaseMean
    simpa only [id_eq, ENNReal.toReal_ofReal (hq0Nonneg _)] using hiff
  have hscaledProduct := hbaseProduct.comp_mul_left' hepsilon.ne'
  have hrhoProduct : Integrable (fun y ↦ y * rho y) := by
    apply hscaledProduct.congr
    filter_upwards with y
    dsimp only [rho, hardEdgeScaledDensity, scaledDensity, q0]
    simp only [zero_add]
    ring
  unfold hardEdgeScaledLaw densityLaw
  apply (integrable_withDensity_iff
    (measurable_hardEdgeScaledDensity hprofile epsilon).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  simpa only [id_eq, ENNReal.toReal_ofReal
    (hardEdgeScaledDensity_nonneg hprofile hepsilon.le _)] using
      hrhoProduct

theorem cdf_dirac_zero_hardEdge (x : ℝ) :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x =
      if 0 ≤ x then 1 else 0 := by
  rw [ProbabilityTheory.cdf_eq_real]
  unfold Measure.real
  rw [Measure.dirac_apply' 0 measurableSet_Iic]
  by_cases hx : 0 ≤ x <;> simp [hx]

theorem hardEdgeScaledLaw_initial_CDFOrdered
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    CDFOrdered (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)
      (Measure.dirac 0) := by
  letI : IsProbabilityMeasure
      (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) :=
    hardEdgeScaledLaw_isProbabilityMeasure hprofile hepsilon
  intro x
  rw [congrFun (cdf_hardEdgeScaledLaw hprofile hepsilon) x]
  rw [cdf_dirac_zero_hardEdge]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact (hardEdgeCDF_range hprofile.1 (epsilon * x)).2
  · rw [if_neg hx]
    unfold hardEdgeScaledCDF hardEdgeCDF
    rw [if_pos]
    exact mul_neg_of_pos_of_neg hepsilon (lt_of_not_ge hx)

theorem Iplus_nonneg_of_nonneg {rho : ℝ → ℝ}
    (hrho : ∀ y, 0 ≤ rho y) (x : ℝ) :
    0 ≤ Iplus rho x := by
  unfold Iplus
  apply setIntegral_nonneg measurableSet_Ici
  intro r hr
  apply intervalIntegral.integral_nonneg (h_nonneg r)
  intro s _hs
  exact mul_nonneg (hrho _) (hrho _)

theorem Iminus_nonneg_of_nonneg {rho : ℝ → ℝ}
    (hrho : ∀ y, 0 ≤ rho y) (x : ℝ) :
    0 ≤ Iminus rho x := by
  unfold Iminus
  apply setIntegral_nonneg measurableSet_Ici
  intro r hr
  apply intervalIntegral.integral_nonneg (h_nonneg r)
  intro s _hs
  exact mul_nonneg (hrho _) (hrho _)

private theorem extension_deriv_eq_derivWithin
    {q qbar : ℝ → ℝ} (hsmooth : ContDiff ℝ 3 qbar)
    (heq : EqOn qbar q (Ici 0)) {z : ℝ} (hz : z ∈ Ici (0 : ℝ)) :
    deriv qbar z = derivWithin q (Ici 0) z := by
  have hbarWithin : derivWithin qbar (Ici 0) z = deriv qbar z :=
    (hsmooth.differentiable (by norm_num)).differentiableAt.derivWithin
      ((uniqueDiffOn_Ici 0).uniqueDiffWithinAt hz)
  rw [← hbarWithin]
  exact derivWithin_congr heq (heq hz)

/-- `lem:hard-edge-consistency`: a uniform lower consistency estimate for the
physical zero extension. -/
theorem hard_edge_weighted_lower_consistency
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) :
    let q := hardEdgeDensity diffusionMainInput W Psi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon < epsilon0 →
        Iplus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x -
            Iminus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x ≥
          diffusionMainInput.a * epsilon ^ 3 * q (epsilon * x) *
              derivWithin q (Ici 0) (epsilon * x) -
            C * epsilon ^ 5 * q (epsilon * x) := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨qbar, hbar⟩ := hard_edge_density_extension_bounds hprofile
  obtain ⟨M, hM, hbound⟩ := hbar.2.2.2
  have hsmooth : ContDiff ℝ 3 qbar := hbar.1
  have heq : EqOn qbar q (Ici 0) := hbar.2.1
  have hpos : ∀ z, 0 < qbar z := hbar.2.2.1
  have hrelative : RelativeC3Bound qbar M := ⟨hM, hbound⟩
  have hprobability := hard_edge_density_probability hprofile
  have hqIntegrable : IntegrableOn q (Ici 0) := by
    simpa only [q] using hprobability.2.1
  have hqMass : (∫ z in Ici (0 : ℝ), q z) = 1 := by
    simpa only [q] using hprobability.2.2.1
  have hbarIntegrable : IntegrableOn qbar (Ici 0) :=
    hqIntegrable.congr_fun (fun z hz ↦ (heq hz).symm) measurableSet_Ici
  have hbarMass : (∫ z in Ici (0 : ℝ), qbar z) = 1 := by
    calc
      (∫ z in Ici (0 : ℝ), qbar z) = ∫ z in Ici (0 : ℝ), q z := by
        exact setIntegral_congr_fun measurableSet_Ici heq
      _ = 1 := hqMass
  let K := Real.exp M
  let C := weightedDifferenceConstant M K + 1
  let epsilon0 := relativeConsistencyEpsilon M
  have hK : 0 ≤ K := (Real.exp_pos M).le
  have hbaseC : 0 ≤ weightedDifferenceConstant M K := by
    unfold weightedDifferenceConstant
    exact mul_nonneg (by positivity) cubicExponentialMoment_nonneg
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hepsilon0 : 0 < epsilon0 := by
    exact relativeConsistencyEpsilon_pos hM
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro x epsilon hx hepsilon hsmall
  let xi := epsilon * x
  have hxi : xi ∈ Ici (0 : ℝ) := mul_nonneg hepsilon.le hx
  have hsq : qbar xi ^ 2 ≤ K * qbar xi := by
    exact half_line_density_sq_le_exp hsmooth hpos hrelative
      hbarIntegrable hbarMass hxi
  have hdiff := weightedIntegral_difference_bound hsmooth hpos hrelative
    hK hsq hepsilon hsmall
  have hbarLower :
      diffusionCoefficient * epsilon ^ 3 * qbar xi * deriv qbar xi -
          weightedDifferenceConstant M K * epsilon ^ 5 * qbar xi ≤
        weightedIplus qbar epsilon xi - weightedIminus qbar epsilon xi := by
    have hlower := (abs_le.mp hdiff).1
    linarith
  have hplus :
      Iplus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x =
        weightedIplus qbar epsilon xi := by
    exact Iplus_zeroExtension_scaled_eq_weightedIplus heq
      hepsilon hx
  have hminus :
      Iminus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x ≤
        weightedIminus qbar epsilon xi := by
    exact Iminus_zeroExtension_scaled_le_weightedIminus heq
      hsmooth hpos hrelative hepsilon hsmall
  have hphysical :
      weightedIplus qbar epsilon xi - weightedIminus qbar epsilon xi ≤
        Iplus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x -
          Iminus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x := by
    rw [hplus]
    linarith
  have hderiv : deriv qbar xi = derivWithin q (Ici 0) xi :=
    extension_deriv_eq_derivWithin hsmooth heq hxi
  have hqeq : qbar xi = q xi := heq hxi
  have hmain :
      diffusionMainInput.a * epsilon ^ 3 * q xi *
            derivWithin q (Ici 0) xi -
          weightedDifferenceConstant M K * epsilon ^ 5 * q xi ≤
        Iplus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x -
          Iminus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x := by
    rw [diffusionMainInput_a, ← hqeq, ← hderiv]
    exact hbarLower.trans hphysical
  have hremainder : 0 ≤ epsilon ^ 5 * q xi := by
    rw [← hqeq]
    exact mul_nonneg (pow_nonneg hepsilon.le 5) (hpos xi).le
  dsimp only [C]
  dsimp only [xi] at hmain ⊢
  nlinarith

/-- The exact lower-bias one-step expression has the profile drift, up to the
uniform fifth-order error. -/
theorem hard_edge_one_step_gain_lower
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi) :
    let q := hardEdgeDensity diffusionMainInput W Psi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon < epsilon0 →
        let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
        let F := hardEdgeScaledCDF Psi epsilon
        Iplus rho x - Iminus rho x +
              2 * epsilon ^ 3 * F x * (1 - F x) +
              2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) ≥
            diffusionMainInput.kappa lambda * epsilon ^ 3 *
                q (epsilon * x) -
              C * epsilon ^ 5 * q (epsilon * x) := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨C, epsilon0, hC, hepsilon0, hweighted⟩ :=
    hard_edge_weighted_lower_consistency hprofile
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro x epsilon hx hepsilon hsmall
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  let F := hardEdgeScaledCDF Psi epsilon
  have hxi : epsilon * x ∈ Ici (0 : ℝ) :=
    mul_nonneg hepsilon.le hx
  have hxi0 : 0 ≤ epsilon * x := hxi
  have hF : F x = Psi (epsilon * x) := by
    simp only [F, hardEdgeScaledCDF, hardEdgeCDF,
      if_neg (not_lt_of_ge hxi0)]
  have hprofileEquation := lower_profile_equation hprofile
    (epsilon * x) hxi
  have hscaledEquation :
      diffusionMainInput.a * epsilon ^ 3 * q (epsilon * x) *
            derivWithin q (Ici 0) (epsilon * x) +
          2 * epsilon ^ 3 * Psi (epsilon * x) *
            (1 - Psi (epsilon * x)) =
        diffusionMainInput.kappa lambda * epsilon ^ 3 *
          q (epsilon * x) := by
    calc
      _ = epsilon ^ 3 *
          (diffusionMainInput.a * q (epsilon * x) *
              derivWithin q (Ici 0) (epsilon * x) +
            2 * Psi (epsilon * x) * (1 - Psi (epsilon * x))) := by
        ring
      _ = epsilon ^ 3 *
          (diffusionMainInput.kappa lambda * q (epsilon * x)) := by
        rw [hprofileEquation]
      _ = _ := by ring
  have hweightedAt := hweighted x epsilon hx hepsilon hsmall
  have hrhoNonneg : ∀ y, 0 ≤ rho y := by
    exact hardEdgeScaledDensity_nonneg hprofile hepsilon.le
  have hplus0 : 0 ≤ Iplus rho x :=
    Iplus_nonneg_of_nonneg hrhoNonneg x
  have hminus0 : 0 ≤ Iminus rho x :=
    Iminus_nonneg_of_nonneg hrhoNonneg x
  have hlast :
      0 ≤ 2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) := by
    positivity
  dsimp only [F] at hF
  dsimp only [rho] at hlast
  dsimp only
  rw [hF]
  nlinarith

/-! ## Positive translation of the hard-edge profile -/

noncomputable def hardEdgeTranslationEpsilon (M kappa : ℝ) : ℝ :=
  min 1 (1 / (M * kappa + 1))

theorem hardEdgeTranslationEpsilon_pos {M kappa : ℝ}
    (hM : 0 ≤ M) (hkappa : 0 ≤ kappa) :
    0 < hardEdgeTranslationEpsilon M kappa := by
  unfold hardEdgeTranslationEpsilon
  exact lt_min zero_lt_one (one_div_pos.mpr (by positivity))

private theorem relative_translation_exponent_small
    {M kappa epsilon : ℝ} (hM : 0 ≤ M) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < hardEdgeTranslationEpsilon M kappa) :
    M * kappa * epsilon ^ 3 < 1 := by
  have hepsilonOne : epsilon < 1 :=
    hsmall.trans_le (min_le_left _ _)
  have hdenom : 0 < M * kappa + 1 := by positivity
  have hepsilonDiv : epsilon < 1 / (M * kappa + 1) :=
    hsmall.trans_le (min_le_right _ _)
  have hscaled : epsilon * (M * kappa + 1) < 1 := by
    exact (lt_div_iff₀ hdenom).mp hepsilonDiv
  have hepsilonSq : epsilon ^ 2 ≤ epsilon := by
    nlinarith [mul_nonneg hepsilon.le
      (sub_nonneg.mpr hepsilonOne.le)]
  have hepsilonCube : epsilon ^ 3 ≤ epsilon := by
    nlinarith [mul_nonneg (sq_nonneg epsilon)
      (sub_nonneg.mpr hepsilonOne.le)]
  have hMk : 0 ≤ M * kappa := mul_nonneg hM hkappa
  have hle : M * kappa * epsilon ^ 3 ≤ M * kappa * epsilon :=
    mul_le_mul_of_nonneg_left hepsilonCube hMk
  nlinarith

/-- Uniform first-order expansion for a positive translation of the scaled hard-edge
profile. -/
theorem hard_edge_positive_translation_expansion
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    let q := hardEdgeDensity diffusionMainInput W Psi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon < epsilon0 →
        |hardEdgeScaledCDF Psi epsilon (x + kappa * epsilon ^ 2) -
            hardEdgeScaledCDF Psi epsilon x -
            kappa * epsilon ^ 3 * q (epsilon * x)| ≤
          C * epsilon ^ 6 * q (epsilon * x) := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨qbar, hbar⟩ := hard_edge_density_extension_bounds hprofile
  obtain ⟨M, hM, hbound⟩ := hbar.2.2.2
  have hsmooth : ContDiff ℝ 3 qbar := hbar.1
  have heq : EqOn qbar q (Ici 0) := hbar.2.1
  have hpos : ∀ z, 0 < qbar z := hbar.2.2.1
  have hrelative : RelativeC3Bound qbar M := ⟨hM, hbound⟩
  let C := M * Real.exp 1 * kappa ^ 2 + 1
  let epsilon0 := hardEdgeTranslationEpsilon M kappa
  have hbaseC : 0 ≤ M * Real.exp 1 * kappa ^ 2 := by positivity
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hepsilon0 : 0 < epsilon0 :=
    hardEdgeTranslationEpsilon_pos hM hkappa
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro x epsilon hx hepsilon hsmall
  let xi := epsilon * x
  let d := kappa * epsilon ^ 3
  have hxi : xi ∈ Ici (0 : ℝ) := mul_nonneg hepsilon.le hx
  have hd : 0 ≤ d := mul_nonneg hkappa (pow_nonneg hepsilon.le 3)
  have hMd : M * d < 1 := by
    dsimp only [d]
    simpa only [mul_assoc] using
      relative_translation_exponent_small hM hkappa hepsilon hsmall
  have hqeq : qbar xi = q xi := heq hxi
  let B := M * Real.exp 1 * qbar xi
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg hM (Real.exp_pos 1).le) (hpos xi).le
  have hxiLe : xi ≤ xi + d := le_add_of_nonneg_right hd
  have hsegmentQ : ∀ u ∈ Icc xi (xi + d),
      qbar u ≤ Real.exp 1 * qbar xi := by
    intro u hu
    have huSub : 0 ≤ u - xi := sub_nonneg.mpr hu.1
    have huAbs : |u - xi| ≤ d := by
      rw [abs_of_nonneg huSub]
      linarith [hu.2]
    have hshift :=
      (density_shift_bounds hsmooth hpos hrelative xi (u - xi)).2
    calc
      qbar u = qbar (xi + (u - xi)) := by ring_nf
      _ ≤ Real.exp (M * |u - xi|) * qbar xi := hshift
      _ ≤ Real.exp 1 * qbar xi := by
        apply mul_le_mul_of_nonneg_right _ (hpos xi).le
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul_of_nonneg_left huAbs hM).trans hMd.le
  have hderivBound : ∀ u ∈ Icc xi (xi + d),
      ‖deriv qbar u‖ ≤ B := by
    intro u hu
    rw [Real.norm_eq_abs]
    calc
      |deriv qbar u| ≤ M * qbar u :=
        deriv_bound_of_relativeC3 hrelative u
      _ ≤ M * (Real.exp 1 * qbar xi) :=
        mul_le_mul_of_nonneg_left (hsegmentQ u hu) hM
      _ = B := by
        dsimp only [B]
        ring
  have hqDiff : ∀ u ∈ Icc xi (xi + d),
      ‖qbar u - qbar xi‖ ≤ B * d := by
    intro u hu
    have hmv : ‖qbar u - qbar xi‖ ≤ B * ‖u - xi‖ :=
      (convex_Icc xi (xi + d)).norm_image_sub_le_of_norm_deriv_le
        (fun z _hz ↦
          (hsmooth.differentiable (by norm_num)).differentiableAt)
        hderivBound (left_mem_Icc.mpr hxiLe) hu
    have huSub : 0 ≤ u - xi := sub_nonneg.mpr hu.1
    have huAbs : |u - xi| ≤ d := by
      rw [abs_of_nonneg huSub]
      linarith [hu.2]
    calc
      ‖qbar u - qbar xi‖ ≤ B * ‖u - xi‖ := hmv
      _ ≤ B * d := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left huAbs hB
  let R : ℝ → ℝ := fun z ↦ Psi z - q xi * z
  have hRContinuous : ContinuousOn R (Icc xi (xi + d)) := by
    apply ContinuousOn.sub
    · exact hprofile.1.1.continuousOn.mono fun z hz ↦
        hxi.trans hz.1
    · fun_prop
  have hRDeriv : ∀ u ∈ Ico xi (xi + d),
      HasDerivWithinAt R (q u - q xi) (Ici u) u := by
    intro u hu
    have hu0 : 0 ≤ u := hxi.trans hu.1
    have hPsiDeriv : HasDerivWithinAt Psi (q u) (Ici u) u := by
      by_cases huz : u = 0
      · subst u
        simpa only [q, hardEdgeDensity, hardEdgePhaseRhs] using
          hprofile.1.2.2.2.2.1
      · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huz)
        have hAt : HasDerivAt Psi (q u) u := by
          simpa only [q, hardEdgeDensity, hardEdgePhaseRhs] using
            (hprofile.1.2.2.2.2.2.1 u hupos)
        exact hAt.hasDerivWithinAt
    have hlinear : HasDerivAt (fun z ↦ q xi * z) (q xi) u := by
      simpa using (hasDerivAt_const_mul (x := u) (q xi))
    change HasDerivWithinAt
      (fun z ↦ Psi z - q xi * z) (q u - q xi) (Ici u) u
    exact hPsiDeriv.sub hlinear.hasDerivWithinAt
  have hRBound : ∀ u ∈ Ico xi (xi + d),
      ‖q u - q xi‖ ≤ B * d := by
    intro u hu
    have huIcc : u ∈ Icc xi (xi + d) := ⟨hu.1, hu.2.le⟩
    have hu0 : u ∈ Ici (0 : ℝ) := hxi.trans hu.1
    simpa only [heq hu0, heq hxi] using hqDiff u huIcc
  have hRemainder :
      ‖R (xi + d) - R xi‖ ≤ (B * d) * ((xi + d) - xi) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hRContinuous hRDeriv hRBound (xi + d) (right_mem_Icc.mpr hxiLe)
  have hRaw :
      |Psi (xi + d) - Psi xi - d * q xi| ≤ B * d ^ 2 := by
    calc
      |Psi (xi + d) - Psi xi - d * q xi| =
          ‖R (xi + d) - R xi‖ := by
        rw [Real.norm_eq_abs]
        dsimp only [R]
        congr 1
        ring
      _ ≤ (B * d) * ((xi + d) - xi) := hRemainder
      _ = B * d ^ 2 := by ring
  have hMain :
      |Psi (xi + d) - Psi xi - kappa * epsilon ^ 3 * q xi| ≤
        (M * Real.exp 1 * kappa ^ 2) * epsilon ^ 6 * q xi := by
    rw [show kappa * epsilon ^ 3 = d by rfl]
    calc
      |Psi (xi + d) - Psi xi - d * q xi| ≤ B * d ^ 2 := hRaw
      _ = (M * Real.exp 1 * kappa ^ 2) * epsilon ^ 6 * q xi := by
        dsimp only [B, d]
        rw [hqeq]
        ring
  have hshiftCoordinate :
      epsilon * (x + kappa * epsilon ^ 2) = xi + d := by
    dsimp only [xi, d]
    ring
  have hxiShift : 0 ≤ xi + d := add_nonneg hxi hd
  have hxi0 : 0 ≤ xi := hxi
  have hF0 : hardEdgeScaledCDF Psi epsilon x = Psi xi := by
    change hardEdgeCDF Psi xi = Psi xi
    simp only [hardEdgeCDF, if_neg (not_lt_of_ge hxi0)]
  have hFShift :
      hardEdgeScaledCDF Psi epsilon (x + kappa * epsilon ^ 2) =
        Psi (xi + d) := by
    rw [hardEdgeScaledCDF, hshiftCoordinate]
    simp only [hardEdgeCDF, if_neg (not_lt_of_ge hxiShift)]
  rw [hFShift, hF0]
  exact hMain.trans (by
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        linarith
      · exact pow_nonneg hepsilon.le 6
    · rw [← hqeq]
      exact (hpos xi).le)

/-- On the positive half-line, a translation slower than the profile speed is
strictly dominated by one lower-biased update, with a uniform margin. -/
theorem hard_edge_positive_strict_margin
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hmargin : kappa < diffusionMainInput.kappa lambda) :
    let q := hardEdgeDensity diffusionMainInput W Psi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon < epsilon0 →
        let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
        let F := hardEdgeScaledCDF Psi epsilon
        F (x + kappa * epsilon ^ 2) - F x +
              (diffusionMainInput.kappa lambda - kappa) / 2 *
                epsilon ^ 3 * q (epsilon * x) ≤
            Iplus rho x - Iminus rho x +
              2 * epsilon ^ 3 * F x * (1 - F x) +
              2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨C1, epsilon1, hC1, hepsilon1, honeStep⟩ :=
    hard_edge_one_step_gain_lower hprofile
  obtain ⟨C2, epsilon2, hC2, hepsilon2, htranslation⟩ :=
    hard_edge_positive_translation_expansion hprofile hkappa.le
  let gap := diffusionMainInput.kappa lambda - kappa
  have hgap : 0 < gap := sub_pos.mpr hmargin
  let C := C1 + C2 + 1
  let epsilon0 :=
    min epsilon1 (min epsilon2 (min 1 (gap / (2 * C))))
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hdenom : 0 < 2 * C := by positivity
  have hratio : 0 < gap / (2 * C) := div_pos hgap hdenom
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilon1
      (lt_min hepsilon2 (lt_min zero_lt_one hratio))
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro x epsilon hx hepsilon hsmall
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  let F := hardEdgeScaledCDF Psi epsilon
  have hsmall1 : epsilon < epsilon1 :=
    hsmall.trans_le (min_le_left _ _)
  have hsmallRest :
      epsilon < min epsilon2 (min 1 (gap / (2 * C))) :=
    hsmall.trans_le (min_le_right _ _)
  have hsmall2 : epsilon < epsilon2 :=
    hsmallRest.trans_le (min_le_left _ _)
  have hsmallFinal : epsilon < min 1 (gap / (2 * C)) :=
    hsmallRest.trans_le (min_le_right _ _)
  have hepsilonOne : epsilon < 1 :=
    hsmallFinal.trans_le (min_le_left _ _)
  have hepsilonRatio : epsilon < gap / (2 * C) :=
    hsmallFinal.trans_le (min_le_right _ _)
  have hone := honeStep x epsilon hx hepsilon hsmall1
  have htransAbs := htranslation x epsilon hx hepsilon hsmall2
  have htransUpper := (abs_le.mp htransAbs).2
  have hepsilonSq : epsilon ^ 2 ≤ epsilon := by
    nlinarith [mul_nonneg hepsilon.le
      (sub_nonneg.mpr hepsilonOne.le)]
  have hepsilonCube : epsilon ^ 3 ≤ epsilon := by
    nlinarith [mul_nonneg (sq_nonneg epsilon)
      (sub_nonneg.mpr hepsilonOne.le)]
  have hcoefficient :
      C1 * epsilon ^ 2 + C2 * epsilon ^ 3 ≤
        (C1 + C2) * epsilon := by
    calc
      C1 * epsilon ^ 2 + C2 * epsilon ^ 3 ≤
          C1 * epsilon + C2 * epsilon :=
        add_le_add
          (mul_le_mul_of_nonneg_left hepsilonSq hC1.le)
          (mul_le_mul_of_nonneg_left hepsilonCube hC2.le)
      _ = (C1 + C2) * epsilon := by ring
  have hsumC : C1 + C2 ≤ C := by
    dsimp only [C]
    linarith
  have hcoefficientC :
      C1 * epsilon ^ 2 + C2 * epsilon ^ 3 ≤ C * epsilon :=
    hcoefficient.trans
      (mul_le_mul_of_nonneg_right hsumC hepsilon.le)
  have hcross : epsilon * (2 * C) < gap :=
    (lt_div_iff₀ hdenom).mp hepsilonRatio
  have hscaledMargin : C * epsilon < gap / 2 := by
    nlinarith
  have hcoefficientMargin :
      C1 * epsilon ^ 2 + C2 * epsilon ^ 3 ≤ gap / 2 :=
    hcoefficientC.trans hscaledMargin.le
  have hxi : epsilon * x ∈ Ici (0 : ℝ) :=
    mul_nonneg hepsilon.le hx
  have hqNonneg : 0 ≤ q (epsilon * x) :=
    (hard_edge_density_probability hprofile).1 (epsilon * x) hxi
  have hfactor : 0 ≤ epsilon ^ 3 * q (epsilon * x) :=
    mul_nonneg (pow_nonneg hepsilon.le 3) hqNonneg
  have herrors :
      C1 * epsilon ^ 5 * q (epsilon * x) +
          C2 * epsilon ^ 6 * q (epsilon * x) ≤
        gap / 2 * epsilon ^ 3 * q (epsilon * x) := by
    calc
      C1 * epsilon ^ 5 * q (epsilon * x) +
            C2 * epsilon ^ 6 * q (epsilon * x) =
          (C1 * epsilon ^ 2 + C2 * epsilon ^ 3) *
            (epsilon ^ 3 * q (epsilon * x)) := by ring
      _ ≤ gap / 2 * (epsilon ^ 3 * q (epsilon * x)) :=
        mul_le_mul_of_nonneg_right hcoefficientMargin hfactor
      _ = gap / 2 * epsilon ^ 3 * q (epsilon * x) := by ring
  dsimp only [rho, F]
  dsimp only [gap] at herrors
  nlinarith

/-- The strict-margin estimate rewritten as the actual biased CDF update on the
positive half-line.  This is the local input used in the three-region barrier. -/
theorem hard_edge_positive_one_step_strict_margin
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hmargin : kappa < diffusionMainInput.kappa lambda) :
    let q := hardEdgeDensity diffusionMainInput W Psi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (x epsilon : ℝ),
        0 ≤ x → 0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 - epsilon ^ 3 →
            hardEdgeScaledCDF Psi epsilon
                  (x + kappa * epsilon ^ 2) +
                (diffusionMainInput.kappa lambda - kappa) / 2 *
                  epsilon ^ 3 * q (epsilon * x) ≤
              cdfOperator p
                (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨C, epsilon0, hC, hepsilon0, hstrict⟩ :=
    hard_edge_positive_strict_margin hprofile hkappa hmargin
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro p x epsilon hx hepsilon hsmall hp
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  let F := hardEdgeScaledCDF Psi epsilon
  have hrhoMeas : Measurable rho := by
    exact measurable_hardEdgeScaledDensity hprofile epsilon
  have hrhoInt : Integrable rho := by
    exact hardEdgeScaledDensity_integrable hprofile hepsilon.ne'
  have hrhoNonneg : ∀ y, 0 ≤ rho y := by
    exact hardEdgeScaledDensity_nonneg hprofile hepsilon.le
  have hrhoMass : (∫ y, rho y) = 1 := by
    exact hardEdgeScaledDensity_integral hprofile hepsilon
  have hpExact : (p : ℝ) = 1 / 2 + (-epsilon ^ 3) := by
    rw [hp]
    ring
  have hexact := exact_cdf_operator_density p rho (-epsilon ^ 3) x
    hrhoMeas hrhoInt hrhoNonneg hrhoMass hpExact
  have hcdf : ProbabilityTheory.cdf (densityLaw rho) = F := by
    simpa only [rho, F, hardEdgeScaledLaw] using
      cdf_hardEdgeScaledLaw hprofile hepsilon
  rw [congrFun hcdf x] at hexact
  have hupdate :
      cdfOperator p
            (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x - F x =
        Iplus rho x - Iminus rho x +
          2 * epsilon ^ 3 * F x * (1 - F x) +
          2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) := by
    change cdfOperator p (densityLaw rho) x - F x = _
    nlinarith [hexact]
  have hstrictAt := hstrict x epsilon hx hepsilon hsmall
  dsimp only [rho, F] at hupdate
  nlinarith

/-! ## The hard-edge transition strip -/

private theorem antitone_h : Antitone h := by
  intro a b hab
  unfold h
  apply Real.log_le_log (by positivity)
  have hexp : Real.exp (-b) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (by linarith)
  exact add_le_add le_rfl hexp

/-- The series crossing correction vanishes strictly to the left of the physical
hard edge. -/
theorem Iminus_hardEdgeScaledDensity_eq_zero_of_neg
    (input : MainInput) (W Psi : ℝ → ℝ) {epsilon x : ℝ}
    (hepsilon : 0 < epsilon) (hx : x < 0) :
    Iminus (hardEdgeScaledDensity input W Psi epsilon) x = 0 := by
  unfold Iminus
  apply integral_eq_zero_of_ae
  filter_upwards with r
  have hinner :
      (∫ s in (0 : ℝ)..h r,
        hardEdgeScaledDensity input W Psi epsilon (x - s) *
          hardEdgeScaledDensity input W Psi epsilon (x - s - r)) = 0 := by
    calc
      (∫ s in (0 : ℝ)..h r,
          hardEdgeScaledDensity input W Psi epsilon (x - s) *
            hardEdgeScaledDensity input W Psi epsilon (x - s - r)) =
          ∫ _s in (0 : ℝ)..h r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (h_nonneg r)] at hs
        have hxs : x - s < 0 := by linarith [hs.1]
        have hscaled : epsilon * (x - s) < 0 :=
          mul_neg_of_pos_of_neg hepsilon hxs
        unfold hardEdgeScaledDensity scaledDensity
        simp only [zero_add, zeroExtendedHardEdgeDensity,
          if_neg (not_lt_of_ge hscaled.le), mul_zero, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  simpa using hinner

/-- A fixed rectangle inside the parallel crossing region gives uniform positive
mass throughout the width-`epsilon^2` transition strip. -/
theorem hard_edge_transition_Iplus_lower
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ c epsilon0 : ℝ, 0 < c ∧ 0 < epsilon0 ∧
      ∀ x epsilon : ℝ,
        -kappa * epsilon ^ 2 ≤ x → x < 0 →
          0 < epsilon → epsilon < epsilon0 →
            c * epsilon ^ 2 ≤
              Iplus
                (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨qbar, hbar⟩ := hard_edge_density_extension_bounds hprofile
  obtain ⟨M, hM, hbound⟩ := hbar.2.2.2
  have hsmooth : ContDiff ℝ 3 qbar := hbar.1
  have heq : EqOn qbar q (Ici 0) := hbar.2.1
  have hpos : ∀ z, 0 < qbar z := hbar.2.2.1
  have hrelative : RelativeC3Bound qbar M := ⟨hM, hbound⟩
  let b := h 1 / 4
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (h_pos 1) (by norm_num)
  let eta := 1 / (M + 1)
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  let c0 := Real.exp (-1) * qbar 0
  have hc0 : 0 < c0 := by
    dsimp only [c0]
    exact mul_pos (Real.exp_pos (-1)) (hpos 0)
  let c := b * c0 ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  let epsilon0 :=
    min 1 (min (b / (kappa + 1)) (eta / (3 * b + 1)))
  have hkappaDenom : 0 < kappa + 1 := by positivity
  have hbRatio : 0 < b / (kappa + 1) := div_pos hb hkappaDenom
  have hcoordinateDenom : 0 < 3 * b + 1 := by positivity
  have hetaRatio : 0 < eta / (3 * b + 1) :=
    div_pos heta hcoordinateDenom
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min zero_lt_one (lt_min hbRatio hetaRatio)
  refine ⟨c, epsilon0, hc, hepsilon0, ?_⟩
  intro x epsilon hxLower hx hepsilon hsmall
  have hepsilonOne : epsilon < 1 :=
    hsmall.trans_le (min_le_left _ _)
  have hsmallRest :
      epsilon < min (b / (kappa + 1)) (eta / (3 * b + 1)) :=
    hsmall.trans_le (min_le_right _ _)
  have hepsilonB : epsilon < b / (kappa + 1) :=
    hsmallRest.trans_le (min_le_left _ _)
  have hepsilonEta : epsilon < eta / (3 * b + 1) :=
    hsmallRest.trans_le (min_le_right _ _)
  have hepsilonScaledB : epsilon * (kappa + 1) < b :=
    (lt_div_iff₀ hkappaDenom).mp hepsilonB
  have hepsilonSq : epsilon ^ 2 ≤ epsilon := by
    nlinarith [mul_nonneg hepsilon.le
      (sub_nonneg.mpr hepsilonOne.le)]
  have hshiftB : kappa * epsilon ^ 2 < b := by
    have hkappaNonneg : 0 ≤ kappa := hkappa.le
    have hle : kappa * epsilon ^ 2 ≤ kappa * epsilon :=
      mul_le_mul_of_nonneg_left hepsilonSq hkappaNonneg
    nlinarith
  have hepsilonScaledEta : epsilon * (3 * b + 1) < eta :=
    (lt_div_iff₀ hcoordinateDenom).mp hepsilonEta
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  let rectangle : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) 1 ×ˢ Icc (2 * b) (3 * b)
  let f : ℝ × ℝ → ℝ := fun z ↦
    rho (x + z.2) * rho (x + z.2 + z.1)
  have hrhoInt : Integrable rho := by
    exact hardEdgeScaledDensity_integrable hprofile hepsilon.ne'
  have hrhoNonneg : ∀ y, 0 ≤ rho y := by
    exact hardEdgeScaledDensity_nonneg hprofile hepsilon.le
  have hf : Integrable f (volume.prod volume) := by
    have hbase := hrhoInt.mul_prod hrhoInt
    have hcomp :=
      (parallelCrossingEquiv_measurePreserving x).integrable_comp_emb
        (parallelCrossingEquiv x).measurableEmbedding |>.2 hbase
    convert hcomp using 1
    ext z
    rfl
  have hrectangleMeas : MeasurableSet rectangle := by
    exact measurableSet_Icc.prod measurableSet_Icc
  have hrectangleSubset : rectangle ⊆ parallelParameterRegion := by
    intro z hz
    rcases hz with ⟨hr, hs⟩
    refine ⟨hr.1, ?_, ?_⟩
    · nlinarith [hs.1, hb]
    · have hh : h 1 ≤ h z.1 := antitone_h hr.2
      dsimp only [b] at hs
      nlinarith [hs.2, h_pos 1]
  have hqLower : ∀ u : ℝ, 0 ≤ u → u < eta → c0 ≤ q u := by
    intro u hu0 huEta
    have hdenom : 0 < M + 1 := by positivity
    have hscaled : u * (M + 1) < 1 := by
      dsimp only [eta] at huEta
      exact (lt_div_iff₀ hdenom).mp huEta
    have hMu : M * |u| ≤ 1 := by
      rw [abs_of_nonneg hu0]
      nlinarith
    have hexp : Real.exp (-1) ≤ Real.exp (-M * |u|) :=
      Real.exp_le_exp.mpr (by linarith)
    have hshift :=
      (density_shift_bounds hsmooth hpos hrelative 0 u).1
    have hbarLower : c0 ≤ qbar u := by
      calc
        c0 = Real.exp (-1) * qbar 0 := rfl
        _ ≤ Real.exp (-M * |u|) * qbar 0 :=
          mul_le_mul_of_nonneg_right hexp (hpos 0).le
        _ ≤ qbar (0 + u) := hshift
        _ = qbar u := by ring_nf
    rw [← heq (mem_Ici.mpr hu0)]
    exact hbarLower
  have hrhoLower : ∀ y : ℝ, 0 < y → epsilon * y < eta →
      epsilon * c0 ≤ rho y := by
    intro y hy hyEta
    have hscaled0 : 0 ≤ epsilon * y := (mul_pos hepsilon hy).le
    have hq := hqLower (epsilon * y) hscaled0 hyEta
    calc
      epsilon * c0 ≤ epsilon * q (epsilon * y) :=
        mul_le_mul_of_nonneg_left hq hepsilon.le
      _ = rho y := by
        dsimp only [rho, q, hardEdgeScaledDensity, scaledDensity]
        simp only [zero_add, zeroExtendedHardEdgeDensity,
          if_pos (mul_pos hepsilon hy)]
  have hpointwise : ∀ z ∈ rectangle,
      epsilon ^ 2 * c0 ^ 2 ≤ f z := by
    intro z hz
    rcases hz with ⟨hr, hs⟩
    have hy1 : 0 < x + z.2 := by
      nlinarith [hxLower, hs.1, hshiftB]
    have hy2 : 0 < x + z.2 + z.1 := by
      linarith [hy1, hr.1]
    have hy1Upper : x + z.2 ≤ 3 * b + 1 := by
      nlinarith [hx, hs.2]
    have hy2Upper : x + z.2 + z.1 ≤ 3 * b + 1 := by
      nlinarith [hx, hs.2, hr.2]
    have hscaled1 : epsilon * (x + z.2) < eta :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hy1Upper hepsilon.le)
        hepsilonScaledEta
    have hscaled2 : epsilon * (x + z.2 + z.1) < eta :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hy2Upper hepsilon.le)
        hepsilonScaledEta
    have hlower1 := hrhoLower (x + z.2) hy1 hscaled1
    have hlower2 := hrhoLower (x + z.2 + z.1) hy2 hscaled2
    have hproduct := mul_le_mul hlower1 hlower2
      (mul_nonneg hepsilon.le hc0.le)
      (hrhoNonneg (x + z.2))
    dsimp only [f]
    nlinarith
  have hconstInt : IntegrableOn
      (fun _z : ℝ × ℝ ↦ epsilon ^ 2 * c0 ^ 2) rectangle
      (volume.prod volume) := by
    exact integrableOn_const
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne (by finiteness)
  have hrectangleLower :
      (∫ _z : ℝ × ℝ in rectangle, epsilon ^ 2 * c0 ^ 2
          ∂(volume.prod volume)) ≤
        ∫ z in rectangle, f z ∂(volume.prod volume) :=
    setIntegral_mono_on hconstInt hf.integrableOn hrectangleMeas hpointwise
  have hparameterNonneg :
      0 ≤ᵐ[(volume.prod volume).restrict parallelParameterRegion] f :=
    Filter.Eventually.of_forall fun z ↦
      mul_nonneg (hrhoNonneg (x + z.2))
        (hrhoNonneg (x + z.2 + z.1))
  have hrectangleAE :
      rectangle ≤ᵐ[volume.prod volume] parallelParameterRegion :=
    Filter.Eventually.of_forall fun _z hz ↦ hrectangleSubset hz
  have hsetMono :
      (∫ z in rectangle, f z ∂(volume.prod volume)) ≤
        ∫ z in parallelParameterRegion, f z ∂(volume.prod volume) :=
    setIntegral_mono_set hf.integrableOn hparameterNonneg hrectangleAE
  have hrectangleVolume :
      (volume.prod volume).real rectangle = b := by
    dsimp only [rectangle]
    rw [MeasureTheory.measureReal_prod_prod]
    norm_num [Real.volume_Icc]
    rw [max_eq_left] <;> linarith
  have hconstValue :
      (∫ _z : ℝ × ℝ in rectangle, epsilon ^ 2 * c0 ^ 2
          ∂(volume.prod volume)) = c * epsilon ^ 2 := by
    rw [setIntegral_const, hrectangleVolume]
    dsimp only [c]
    simp only [smul_eq_mul]
    ring
  rw [Iplus_eq_integral_parallelParameterRegion rho hrhoInt x]
  change c * epsilon ^ 2 ≤
    ∫ z in parallelParameterRegion, f z ∂(volume.prod volume)
  rw [← hconstValue]
  exact hrectangleLower.trans hsetMono

/-- In the narrow strip immediately to the left of the hard edge, the fixed
parallel-crossing rectangle dominates the translated profile. -/
theorem hard_edge_transition_one_step_barrier
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (x epsilon : ℝ),
        -kappa * epsilon ^ 2 ≤ x → x < 0 →
          0 < epsilon → epsilon < epsilon0 →
            (p : ℝ) = 1 / 2 - epsilon ^ 3 →
              hardEdgeScaledCDF Psi epsilon
                  (x + kappa * epsilon ^ 2) ≤
                cdfOperator p
                  (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨c, epsilon1, hc, hepsilon1, hIplus⟩ :=
    hard_edge_transition_Iplus_lower hprofile hkappa
  obtain ⟨Ct, epsilon2, hCt, hepsilon2, htranslation⟩ :=
    hard_edge_positive_translation_expansion hprofile hkappa.le
  have hq0 : 0 < q 0 := hprofile.2.2.1
  let D := (kappa + Ct) * q 0
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (add_nonneg hkappa.le hCt.le) hq0.le
  let epsilon0 :=
    min epsilon1 (min epsilon2 (min 1 (c / (D + 1))))
  have hdenom : 0 < D + 1 := by positivity
  have hratio : 0 < c / (D + 1) := div_pos hc hdenom
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilon1
      (lt_min hepsilon2 (lt_min zero_lt_one hratio))
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro p x epsilon hxLower hx hepsilon hsmall hp
  have hsmall1 : epsilon < epsilon1 :=
    hsmall.trans_le (min_le_left _ _)
  have hsmallRest :
      epsilon < min epsilon2 (min 1 (c / (D + 1))) :=
    hsmall.trans_le (min_le_right _ _)
  have hsmall2 : epsilon < epsilon2 :=
    hsmallRest.trans_le (min_le_left _ _)
  have hsmallFinal : epsilon < min 1 (c / (D + 1)) :=
    hsmallRest.trans_le (min_le_right _ _)
  have hepsilonOne : epsilon < 1 :=
    hsmallFinal.trans_le (min_le_left _ _)
  have hepsilonRatio : epsilon < c / (D + 1) :=
    hsmallFinal.trans_le (min_le_right _ _)
  have hIplusAt := hIplus x epsilon hxLower hx hepsilon hsmall1
  have htranslationAt :=
    htranslation 0 epsilon (le_refl 0) hepsilon hsmall2
  have hFzero : hardEdgeScaledCDF Psi epsilon 0 = 0 := by
    simp only [hardEdgeScaledCDF, mul_zero, hardEdgeCDF,
      if_neg (not_lt_of_ge le_rfl), hprofile.1.2.2.2.1]
  have htranslationUpper := (abs_le.mp htranslationAt).2
  have hFAtShift :
      hardEdgeScaledCDF Psi epsilon (kappa * epsilon ^ 2) ≤
        kappa * epsilon ^ 3 * q 0 +
          Ct * epsilon ^ 6 * q 0 := by
    rw [hFzero] at htranslationUpper
    have hupper' :
        hardEdgeScaledCDF Psi epsilon (kappa * epsilon ^ 2) -
              kappa * epsilon ^ 3 * q 0 ≤
            Ct * epsilon ^ 6 * q 0 := by
      simpa only [zero_add, sub_zero, mul_zero, q] using
        htranslationUpper
    linarith
  have hargumentOrder :
      epsilon * (x + kappa * epsilon ^ 2) ≤
        epsilon * (kappa * epsilon ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hepsilon.le
    linarith
  have hFmonotone :
      hardEdgeScaledCDF Psi epsilon (x + kappa * epsilon ^ 2) ≤
        hardEdgeScaledCDF Psi epsilon (kappa * epsilon ^ 2) := by
    exact hardEdgeCDF_monotone hprofile.1 hargumentOrder
  have hepsilonCubeOne : epsilon ^ 3 ≤ 1 :=
    pow_le_one₀ hepsilon.le hepsilonOne.le
  have hepsilonSix : epsilon ^ 6 ≤ epsilon ^ 3 := by
    calc
      epsilon ^ 6 = epsilon ^ 3 * epsilon ^ 3 := by ring
      _ ≤ epsilon ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hepsilonCubeOne
          (pow_nonneg hepsilon.le 3)
      _ = epsilon ^ 3 := by ring
  have herrorOrder :
      Ct * epsilon ^ 6 * q 0 ≤ Ct * epsilon ^ 3 * q 0 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hepsilonSix hCt.le) hq0.le
  have hFAtShiftD :
      hardEdgeScaledCDF Psi epsilon (kappa * epsilon ^ 2) ≤
        D * epsilon ^ 3 := by
    calc
      hardEdgeScaledCDF Psi epsilon (kappa * epsilon ^ 2) ≤
          kappa * epsilon ^ 3 * q 0 +
            Ct * epsilon ^ 6 * q 0 := hFAtShift
      _ ≤ kappa * epsilon ^ 3 * q 0 +
          Ct * epsilon ^ 3 * q 0 := add_le_add le_rfl herrorOrder
      _ = D * epsilon ^ 3 := by
        dsimp only [D]
        ring
  have hscaled : epsilon * (D + 1) < c :=
    (lt_div_iff₀ hdenom).mp hepsilonRatio
  have hDepsilon : D * epsilon < c := by
    nlinarith
  have hDdominated : D * epsilon ^ 3 ≤ c * epsilon ^ 2 := by
    calc
      D * epsilon ^ 3 = (D * epsilon) * epsilon ^ 2 := by ring
      _ ≤ c * epsilon ^ 2 :=
        mul_le_mul_of_nonneg_right hDepsilon.le (sq_nonneg epsilon)
  have hFleIplus :
      hardEdgeScaledCDF Psi epsilon (x + kappa * epsilon ^ 2) ≤
        Iplus (hardEdgeScaledDensity diffusionMainInput W Psi epsilon) x :=
    hFmonotone.trans (hFAtShiftD.trans
      (hDdominated.trans hIplusAt))
  let rho := hardEdgeScaledDensity diffusionMainInput W Psi epsilon
  let F := hardEdgeScaledCDF Psi epsilon
  have hrhoMeas : Measurable rho :=
    measurable_hardEdgeScaledDensity hprofile epsilon
  have hrhoInt : Integrable rho :=
    hardEdgeScaledDensity_integrable hprofile hepsilon.ne'
  have hrhoNonneg : ∀ y, 0 ≤ rho y :=
    hardEdgeScaledDensity_nonneg hprofile hepsilon.le
  have hrhoMass : (∫ y, rho y) = 1 :=
    hardEdgeScaledDensity_integral hprofile hepsilon
  have hpExact : (p : ℝ) = 1 / 2 + (-epsilon ^ 3) := by
    rw [hp]
    ring
  have hexact := exact_cdf_operator_density p rho (-epsilon ^ 3) x
    hrhoMeas hrhoInt hrhoNonneg hrhoMass hpExact
  have hcdf : ProbabilityTheory.cdf (densityLaw rho) = F := by
    simpa only [rho, F, hardEdgeScaledLaw] using
      cdf_hardEdgeScaledLaw hprofile hepsilon
  have hscaledNeg : epsilon * x < 0 :=
    mul_neg_of_pos_of_neg hepsilon hx
  have hFx : F x = 0 := by
    simp only [F, hardEdgeScaledCDF, hardEdgeCDF,
      if_pos hscaledNeg]
  have hminus : Iminus rho x = 0 := by
    exact Iminus_hardEdgeScaledDensity_eq_zero_of_neg
      diffusionMainInput W Psi hepsilon hx
  rw [congrFun hcdf x, hFx, hminus] at hexact
  have hplusNonneg : 0 ≤ Iplus rho x :=
    Iplus_nonneg_of_nonneg hrhoNonneg x
  have hoperatorLower :
      Iplus rho x ≤ cdfOperator p (densityLaw rho) x := by
    nlinarith [hexact, pow_nonneg hepsilon.le 3]
  change hardEdgeScaledCDF Psi epsilon
      (x + kappa * epsilon ^ 2) ≤ cdfOperator p (densityLaw rho) x
  exact hFleIplus.trans hoperatorLower

/-! ## The global three-region lower barrier -/

/-- The physical hard-edge CDF is a global lower barrier for every sufficiently
small scale.  The proof joins the positive consistency region, the transition
rectangle, and the region where the translated CDF vanishes. -/
theorem hard_edge_global_lower_barrier
    {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hprofile :
      IsHardEdgeProfileConclusion diffusionMainInput lambda W Psi)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hmargin : kappa < diffusionMainInput.kappa lambda) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (epsilon : ℝ),
        0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 - epsilon ^ 3 →
            ∀ x : ℝ,
              hardEdgeScaledCDF Psi epsilon
                  (x + kappa * epsilon ^ 2) ≤
                cdfOperator p
                  (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x := by
  let q := hardEdgeDensity diffusionMainInput W Psi
  obtain ⟨C, epsilon1, hC, hepsilon1, hpositive⟩ :=
    hard_edge_positive_one_step_strict_margin
      hprofile hkappa hmargin
  obtain ⟨epsilon2, hepsilon2, htransition⟩ :=
    hard_edge_transition_one_step_barrier hprofile hkappa
  let epsilon0 := min epsilon1 epsilon2
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilon1 hepsilon2
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro p epsilon hepsilon hsmall hp x
  have hsmall1 : epsilon < epsilon1 :=
    hsmall.trans_le (min_le_left _ _)
  have hsmall2 : epsilon < epsilon2 :=
    hsmall.trans_le (min_le_right _ _)
  by_cases hx : 0 ≤ x
  · have hpositiveAt :=
      hpositive p x epsilon hx hepsilon hsmall1 hp
    have hxi : epsilon * x ∈ Ici (0 : ℝ) :=
      mul_nonneg hepsilon.le hx
    have hqNonneg : 0 ≤ q (epsilon * x) :=
      (hard_edge_density_probability hprofile).1 (epsilon * x) hxi
    have hmarginNonneg :
        0 ≤ (diffusionMainInput.kappa lambda - kappa) / 2 *
          epsilon ^ 3 * q (epsilon * x) := by
      exact mul_nonneg
        (mul_nonneg (div_nonneg (sub_nonneg.mpr hmargin.le) (by norm_num))
          (pow_nonneg hepsilon.le 3)) hqNonneg
    nlinarith
  · have hxNeg : x < 0 := lt_of_not_ge hx
    by_cases hfar : x < -kappa * epsilon ^ 2
    · have hshiftNeg : x + kappa * epsilon ^ 2 < 0 := by
        linarith
      have hscaledNeg :
          epsilon * (x + kappa * epsilon ^ 2) < 0 :=
        mul_neg_of_pos_of_neg hepsilon hshiftNeg
      have hFzero :
          hardEdgeScaledCDF Psi epsilon
              (x + kappa * epsilon ^ 2) = 0 := by
        simp only [hardEdgeScaledCDF, hardEdgeCDF,
          if_pos hscaledNeg]
      have hoperatorNonneg :
          0 ≤ cdfOperator p
            (hardEdgeScaledLaw diffusionMainInput W Psi epsilon) x := by
        unfold cdfOperator
        exact add_nonneg
          (mul_nonneg p.2.1
            (ProbabilityTheory.cdf_nonneg
              (seriesLaw
                (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)) x))
          (mul_nonneg (sub_nonneg.mpr p.2.2)
            (ProbabilityTheory.cdf_nonneg
              (parallelLaw
                (hardEdgeScaledLaw diffusionMainInput W Psi epsilon)) x))
      rw [hFzero]
      exact hoperatorNonneg
    · exact htransition p x epsilon (le_of_not_gt hfar) hxNeg
        hepsilon hsmall2 hp

end SeriesParallel.MainText
