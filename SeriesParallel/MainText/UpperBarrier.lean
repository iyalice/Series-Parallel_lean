/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.DensityGateRegions
import SeriesParallel.MainText.GeneralizedInverseCoupling
import SeriesParallel.MainText.JensenAndCenter
import SeriesParallel.MainText.MainTextStatementContract
import SeriesParallel.MainText.ProfileInstantiation
import SeriesParallel.MainText.WeightedConsistency

/-!
# The supercritical upper barrier

This file constructs the truncated full-line profile barrier.  The atom created at zero is
kept at the level of probability laws, so the absolutely continuous CDF formula is never
applied to the truncated law.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff ENNReal Topology unitInterval

namespace SeriesParallel.MainText

open SeriesParallel.Appendix

/-! ## The affine profile and its cutoff -/

/-- The affine copy of a full-line profile used by the upper barrier. -/
def affineProfileCDF (Phi : ℝ → ℝ) (epsilon z0 x : ℝ) : ℝ :=
  Phi (z0 + epsilon * x)

/-- The unique profile coordinate at CDF level `epsilon ^ 4`, when that level is attained. -/
noncomputable def upperCutoff (Phi : ℝ → ℝ) (epsilon : ℝ) : ℝ :=
  Function.invFun Phi (epsilon ^ 4)

/-- The upper profile after pushing its negative part to zero. -/
noncomputable def cutoffProfileCDF (Phi : ℝ → ℝ) (epsilon : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else affineProfileCDF Phi epsilon (upperCutoff Phi epsilon) x

private theorem epsilon_fourth_mem_Ioo {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    epsilon ^ 4 ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨pow_pos hepsilon 4, pow_lt_one₀ hepsilon.le hepsilon_one (by omega)⟩

/-- A normalized full-line profile assumes the cutoff level exactly once. -/
theorem existsUnique_upperCutoff {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    ∃! z : ℝ, Phi z = epsilon ^ 4 := by
  have halpha := epsilon_fourth_mem_Ioo hepsilon hepsilon_one
  have hleftEventually : ∀ᶠ z in atBot, Phi z < epsilon ^ 4 :=
    hprofile.1.2.2.2.2.2.1.eventually (Iio_mem_nhds halpha.1)
  have hrightEventually : ∀ᶠ z in atTop, epsilon ^ 4 < Phi z :=
    hprofile.1.2.2.2.2.2.2.eventually (Ioi_mem_nhds halpha.2)
  obtain ⟨left, hleft⟩ := hleftEventually.exists
  obtain ⟨right, hright⟩ := hrightEventually.exists
  have hle : left ≤ right := by
    by_contra hnot
    have hstrict := hprofile.1.2.1 (lt_of_not_ge hnot)
    linarith
  obtain ⟨z, _hz, hzeq⟩ :=
    (intermediate_value_Icc hle hprofile.1.1.continuous.continuousOn)
      ⟨hleft.le, hright.le⟩
  refine ⟨z, hzeq, ?_⟩
  intro y hy
  exact hprofile.1.2.1.injective (hy.trans hzeq.symm)

/-- The chosen cutoff has precisely the source level `epsilon ^ 4`. -/
theorem upperCutoff_spec {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    Phi (upperCutoff Phi epsilon) = epsilon ^ 4 := by
  apply Function.invFun_eq
  exact (existsUnique_upperCutoff hprofile hepsilon hepsilon_one).exists

/-- Characterization of the chosen cutoff, useful when strict monotonicity is the last step. -/
theorem eq_upperCutoff_of_profile_eq {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon z : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (hz : Phi z = epsilon ^ 4) :
    z = upperCutoff Phi epsilon := by
  exact hprofile.1.2.1.injective (hz.trans (upperCutoff_spec hprofile
    hepsilon hepsilon_one).symm)

@[simp]
theorem cutoffProfileCDF_zero {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    cutoffProfileCDF Phi epsilon 0 = epsilon ^ 4 := by
  rw [cutoffProfileCDF, if_neg (by norm_num), affineProfileCDF]
  simpa using upperCutoff_spec hprofile hepsilon hepsilon_one

/-- The cutoff, even after an `epsilon * log 2` displacement, moves through every left-tail
threshold.  This is the quantified form of `z_epsilon + epsilon log 2 → -∞`. -/
theorem upperCutoff_tail_position {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) (A : ℝ) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        upperCutoff Phi epsilon + epsilon * Real.log 2 < A := by
  have hPhiPos : 0 < Phi (A - 1) := (hprofile.1.2.2.1 (A - 1)).1
  let epsilon0 : ℝ := min (Phi (A - 1)) (min 1 (1 / (Real.log 2 + 1)))
  have hdenom : 0 < Real.log 2 + 1 := by positivity
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hPhiPos (lt_min zero_lt_one (one_div_pos.mpr hdenom))
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon_lt
  have hepsilon_Phi : epsilon < Phi (A - 1) :=
    hepsilon_lt.trans_le (min_le_left _ _)
  have hepsilon_one : epsilon < 1 :=
    hepsilon_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilon_denom : epsilon < 1 / (Real.log 2 + 1) :=
    hepsilon_lt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hepsilon_fourth_lt : epsilon ^ 4 < Phi (A - 1) := by
    exact (pow_lt_self_of_lt_one₀ hepsilon hepsilon_one (by omega)).trans
      hepsilon_Phi
  have hcutoff_lt : upperCutoff Phi epsilon < A - 1 := by
    apply (hprofile.1.2.1.lt_iff_lt).mp
    rw [upperCutoff_spec hprofile hepsilon hepsilon_one]
    exact hepsilon_fourth_lt
  have hshift_lt : epsilon * Real.log 2 < 1 := by
    have hmul : epsilon * (Real.log 2 + 1) < 1 := by
      rw [lt_div_iff₀ hdenom] at hepsilon_denom
      simpa only [one_mul] using hepsilon_denom
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  linarith

/-! ## The untruncated and truncated profile laws -/

/-- The probability law supplied by the full-line profile conclusion. -/
noncomputable def waveProfileLaw {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) : Measure ℝ :=
  Classical.choose hprofile.2.2.2.2.2.2.2.2

theorem waveProfileLaw_spec {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) :
    SeriesParallel.Appendix.IsProbabilityLawOfCDF Phi (waveProfileLaw hprofile) ∧
      Integrable (fun x : ℝ ↦ |x|) (waveProfileLaw hprofile) := by
  exact Classical.choose_spec hprofile.2.2.2.2.2.2.2.2

theorem waveProfileLaw_isProbabilityMeasure {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) :
    IsProbabilityMeasure (waveProfileLaw hprofile) :=
  (waveProfileLaw_spec hprofile).1.1

/-- Push the profile law through `z ↦ (z-z0)/epsilon`. -/
noncomputable def affineWaveProfileLaw {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (epsilon z0 : ℝ) : Measure ℝ :=
  (waveProfileLaw hprofile).map fun z ↦ (z - z0) / epsilon

theorem affineWaveProfileLaw_isProbabilityMeasure
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (epsilon z0 : ℝ) :
    IsProbabilityMeasure (affineWaveProfileLaw hprofile epsilon z0) := by
  letI : IsProbabilityMeasure (waveProfileLaw hprofile) :=
    waveProfileLaw_isProbabilityMeasure hprofile
  unfold affineWaveProfileLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The affine law has CDF `Phi (z0 + epsilon * x)`. -/
theorem cdf_affineWaveProfileLaw
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z0 : ℝ) :
    ProbabilityTheory.cdf (affineWaveProfileLaw hprofile epsilon z0) =
      affineProfileCDF Phi epsilon z0 := by
  letI : IsProbabilityMeasure (waveProfileLaw hprofile) :=
    waveProfileLaw_isProbabilityMeasure hprofile
  letI : IsProbabilityMeasure (affineWaveProfileLaw hprofile epsilon z0) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon z0
  funext x
  rw [ProbabilityTheory.cdf_eq_real]
  unfold affineWaveProfileLaw
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hpreimage : (fun z : ℝ ↦ (z - z0) / epsilon) ⁻¹' Iic x =
      Iic (z0 + epsilon * x) := by
    ext z
    simp only [mem_preimage, mem_Iic]
    rw [div_le_iff₀ hepsilon]
    constructor <;> intro hz <;> linarith
  rw [hpreimage]
  unfold Measure.real
  rw [(waveProfileLaw_spec hprofile).1.2]
  rw [ENNReal.toReal_ofReal
    (hprofile.1.2.2.1 (z0 + epsilon * x)).1.le]
  rfl

/-! ## The affine density bridge -/

/-- The analytic density of an affine profile is integrable. -/
theorem integrable_scaledDensity_waveDensity
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) (z0 : ℝ) :
    Integrable
      (scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0) := by
  let q := waveDensity diffusionMainInput W Phi
  have hq : Integrable q := (full_line_density_probability hprofile).2.1
  have hshift : Integrable (fun y : ℝ ↦ q (z0 + y)) :=
    hq.comp_add_left z0
  have hscale : Integrable (fun y : ℝ ↦ q (z0 + epsilon * y)) := by
    simpa only using hshift.comp_mul_left' hepsilon
  change Integrable (fun y : ℝ ↦
    epsilon * waveDensity diffusionMainInput W Phi (z0 + epsilon * y))
  simpa only [q] using hscale.const_mul epsilon

/-- The analytic affine density has total mass one. -/
theorem integral_scaledDensity_waveDensity
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z0 : ℝ) :
    (∫ y, scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0 y) = 1 := by
  let q := waveDensity diffusionMainInput W Phi
  have hqMass : (∫ z, q z) = 1 :=
    (full_line_density_probability hprofile).2.2.1
  unfold scaledDensity
  rw [integral_const_mul]
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ q (z0 + y)) epsilon
  rw [hscale, integral_add_left_eq_self, hqMass]
  rw [abs_of_pos (inv_pos.mpr hepsilon)]
  simp only [smul_eq_mul]
  field_simp

/-- The affine density is nonnegative. -/
theorem scaledDensity_waveDensity_nonneg
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (z0 y : ℝ) :
    0 ≤ scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0 y := by
  unfold scaledDensity
  exact mul_nonneg hepsilon (hprofile.2.2.1 _).le

/-- The affine density is measurable. -/
theorem measurable_scaledDensity_waveDensity
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (epsilon z0 : ℝ) :
    Measurable
      (scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0) := by
  have hq : Continuous (waveDensity diffusionMainInput W Phi) := by
    have hqEq : waveDensity diffusionMainInput W Phi = deriv Phi := by
      funext z
      exact (hprofile.2.1 z).symm
    rw [hqEq]
    have hPhi4 : ContDiff ℝ 4 Phi :=
      hprofile.1.1.of_le ENat.LEInfty.out
    exact (hPhi4.deriv' : ContDiff ℝ 3 (deriv Phi)).continuous
  unfold scaledDensity
  fun_prop

/-- The density-defined affine law has the expected affine profile CDF. -/
theorem cdf_densityLaw_scaled_waveDensity
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z0 : ℝ) :
    ProbabilityTheory.cdf
        (densityLaw
          (scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0)) =
      affineProfileCDF Phi epsilon z0 := by
  let q := waveDensity diffusionMainInput W Phi
  let rho := scaledDensity q epsilon z0
  have hrhoInt : Integrable rho :=
    integrable_scaledDensity_waveDensity hprofile hepsilon.ne' z0
  have hrhoNonneg : ∀ y, 0 ≤ rho y :=
    scaledDensity_waveDensity_nonneg hprofile hepsilon.le z0
  have hrhoMass : (∫ y, rho y) = 1 :=
    integral_scaledDensity_waveDensity hprofile hepsilon z0
  letI : IsProbabilityMeasure (densityLaw rho) :=
    densityLaw_isProbabilityMeasure rho hrhoInt hrhoNonneg hrhoMass
  have hPhiDeriv (z : ℝ) : HasDerivAt Phi (q z) z := by
    change HasDerivAt Phi (waveDensity diffusionMainInput W Phi z) z
    rw [← hprofile.2.1 z]
    exact (hprofile.1.1.differentiable (by norm_num) z).hasDerivAt
  have haffineDeriv (y : ℝ) :
      HasDerivAt (affineProfileCDF Phi epsilon z0) (rho y) y := by
    have hinner : HasDerivAt (fun t : ℝ ↦ z0 + epsilon * t) epsilon y := by
      exact (hasDerivAt_const_mul epsilon).const_add z0
    have hcomp := (hPhiDeriv (z0 + epsilon * y)).comp y hinner
    change HasDerivAt (fun t : ℝ ↦ Phi (z0 + epsilon * t))
      (epsilon * q (z0 + epsilon * y)) y
    have hcomp' : HasDerivAt (Phi ∘ fun t : ℝ ↦ z0 + epsilon * t)
        (epsilon * q (z0 + epsilon * y)) y := by
      simpa only [mul_comm] using hcomp
    apply hcomp'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hinnerBot : Tendsto (fun y : ℝ ↦ z0 + epsilon * y) atBot atBot := by
    apply tendsto_atBot_add_const_left
    exact (tendsto_const_mul_atBot_of_pos hepsilon).2 tendsto_id
  have haffineBot : Tendsto (affineProfileCDF Phi epsilon z0) atBot (nhds 0) := by
    exact hprofile.1.2.2.2.2.2.1.comp hinnerBot
  funext x
  rw [ProbabilityTheory.cdf_eq_real]
  unfold Measure.real densityLaw
  rw [withDensity_apply _ measurableSet_Iic]
  have hrhoOn : IntegrableOn rho (Iic x) := hrhoInt.integrableOn
  have hrhoNonnegAE : 0 ≤ᵐ[volume.restrict (Iic x)] rho :=
    Filter.Eventually.of_forall hrhoNonneg
  rw [← ofReal_integral_eq_lintegral_ofReal hrhoOn hrhoNonnegAE]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hrhoNonnegAE)]
  rw [integral_Iic_of_hasDerivAt_of_tendsto'
    (fun y _hy ↦ haffineDeriv y) hrhoOn haffineBot]
  simp only [sub_zero]

/-- The pushforward and density constructions of the affine profile law coincide. -/
theorem densityLaw_scaled_waveDensity_eq_affineWaveProfileLaw
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z0 : ℝ) :
    densityLaw
        (scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0) =
      affineWaveProfileLaw hprofile epsilon z0 := by
  let rho := scaledDensity (waveDensity diffusionMainInput W Phi) epsilon z0
  letI : IsProbabilityMeasure (densityLaw rho) :=
    densityLaw_isProbabilityMeasure rho
      (integrable_scaledDensity_waveDensity hprofile hepsilon.ne' z0)
      (scaledDensity_waveDensity_nonneg hprofile hepsilon.le z0)
      (integral_scaledDensity_waveDensity hprofile hepsilon z0)
  letI : IsProbabilityMeasure (affineWaveProfileLaw hprofile epsilon z0) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon z0
  apply Measure.eq_of_cdf
  ext x
  rw [congrFun (cdf_densityLaw_scaled_waveDensity hprofile hepsilon z0) x]
  rw [congrFun (cdf_affineWaveProfileLaw hprofile hepsilon z0) x]

/-! ## Weighted one-step consistency for the untruncated profile -/

/-- The exact CDF recursion and the profile ODE give a uniform weighted one-step
expansion for every affine copy of the full-line profile. -/
theorem affineWaveProfile_oneStep_consistency
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (x z0 epsilon : ℝ),
        0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 + epsilon ^ 3 →
            let xi := z0 + epsilon * x
            |cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x -
                affineProfileCDF Phi epsilon z0 x +
                diffusionMainInput.kappa lambda * epsilon ^ 3 * q xi| ≤
              C * epsilon ^ 5 * q xi := by
  let q := waveDensity diffusionMainInput W Phi
  obtain ⟨C0, epsilon0, hC0, hepsilon0, hweighted⟩ :=
    full_line_weighted_consistency hprofile
  refine ⟨3 * C0, epsilon0, by positivity, hepsilon0, ?_⟩
  intro p x z0 epsilon hepsilon hepsilonSmall hp
  let xi := z0 + epsilon * x
  let rho := scaledDensity q epsilon z0
  have hrhoMeas : Measurable rho :=
    measurable_scaledDensity_waveDensity hprofile epsilon z0
  have hrhoInt : Integrable rho :=
    integrable_scaledDensity_waveDensity hprofile hepsilon.ne' z0
  have hrhoNonneg : ∀ y, 0 ≤ rho y :=
    scaledDensity_waveDensity_nonneg hprofile hepsilon.le z0
  have hrhoMass : (∫ y, rho y) = 1 :=
    integral_scaledDensity_waveDensity hprofile hepsilon z0
  letI : IsProbabilityMeasure (densityLaw rho) :=
    densityLaw_isProbabilityMeasure rho hrhoInt hrhoNonneg hrhoMass
  letI : IsProbabilityMeasure (affineWaveProfileLaw hprofile epsilon z0) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon z0
  have hlaw : densityLaw rho = affineWaveProfileLaw hprofile epsilon z0 :=
    densityLaw_scaled_waveDensity_eq_affineWaveProfileLaw
      hprofile hepsilon z0
  have hcdf : ProbabilityTheory.cdf (densityLaw rho) =
      affineProfileCDF Phi epsilon z0 := by
    simpa only [rho, q] using
      cdf_densityLaw_scaled_waveDensity hprofile hepsilon z0
  have hexact := exact_cdf_operator_density p rho (epsilon ^ 3) x
    hrhoMeas hrhoInt hrhoNonneg hrhoMass hp
  rw [congrFun hcdf x, hlaw] at hexact
  have hbounds := hweighted x z0 epsilon hepsilon hepsilonSmall
  change
    |Iplus rho x - Iminus rho x -
        diffusionMainInput.a * epsilon ^ 3 * q xi * deriv q xi| ≤
          C0 * epsilon ^ 5 * q xi ∧
      Iplus rho x + Iminus rho x ≤ C0 * epsilon ^ 2 * q xi at hbounds
  have hplus : 0 ≤ Iplus rho x := by
    rw [Iplus_eq_parallelCrossing_measureReal rho hrhoMeas hrhoInt
      hrhoNonneg x]
    exact measureReal_nonneg
  have hminus : 0 ≤ Iminus rho x := by
    rw [Iminus_eq_seriesCrossing_measureReal rho hrhoMeas hrhoInt
      hrhoNonneg x]
    exact measureReal_nonneg
  have hsumNonneg : 0 ≤ Iplus rho x + Iminus rho x :=
    add_nonneg hplus hminus
  have hode := upper_profile_equation hprofile xi
  change diffusionMainInput.a * q xi * deriv q xi -
      2 * Phi xi * (1 - Phi xi) =
        -diffusionMainInput.kappa lambda * q xi at hode
  have halgebra :
      cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x -
          affineProfileCDF Phi epsilon z0 x +
          diffusionMainInput.kappa lambda * epsilon ^ 3 * q xi =
        (Iplus rho x - Iminus rho x -
            diffusionMainInput.a * epsilon ^ 3 * q xi * deriv q xi) -
          2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) := by
    rw [hexact]
    have hF : affineProfileCDF Phi epsilon z0 x = Phi xi := rfl
    rw [hF]
    linear_combination epsilon ^ 3 * hode
  change
    |cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x -
        affineProfileCDF Phi epsilon z0 x +
        diffusionMainInput.kappa lambda * epsilon ^ 3 * q xi| ≤
      3 * C0 * epsilon ^ 5 * q xi
  rw [halgebra]
  have hsecond :
      |2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x)| ≤
        2 * C0 * epsilon ^ 5 * q xi := by
    rw [abs_of_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg hepsilon.le 3)) hsumNonneg)]
    calc
      2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x) ≤
          2 * epsilon ^ 3 * (C0 * epsilon ^ 2 * q xi) := by
        exact mul_le_mul_of_nonneg_left hbounds.2
          (mul_nonneg (by positivity) (pow_nonneg hepsilon.le 3))
      _ = 2 * C0 * epsilon ^ 5 * q xi := by ring
  calc
    |(Iplus rho x - Iminus rho x -
          diffusionMainInput.a * epsilon ^ 3 * q xi * deriv q xi) -
        2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x)| ≤
      |Iplus rho x - Iminus rho x -
          diffusionMainInput.a * epsilon ^ 3 * q xi * deriv q xi| +
        |2 * epsilon ^ 3 * (Iplus rho x + Iminus rho x)| := abs_sub _ _
    _ ≤ C0 * epsilon ^ 5 * q xi +
        2 * C0 * epsilon ^ 5 * q xi := add_le_add hbounds.1 hsecond
    _ = 3 * C0 * epsilon ^ 5 * q xi := by ring

/-- Translating an affine profile by `kappa * epsilon ^ 2` has the expected first-order
term, with a uniform relative error of order `epsilon ^ 6`. -/
theorem affineProfile_translation_consistency
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x z0 epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        let xi := z0 + epsilon * x
        |affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) -
            affineProfileCDF Phi epsilon z0 x +
            kappa * epsilon ^ 3 * q xi| ≤
          C * epsilon ^ 6 * q xi := by
  let q := waveDensity diffusionMainInput W Phi
  have hqEq : q = deriv Phi := by
    funext z
    exact (hprofile.2.1 z).symm
  have hsmooth : ContDiff ℝ 3 q := by
    rw [hqEq]
    have hPhi4 : ContDiff ℝ 4 Phi :=
      hprofile.1.1.of_le ENat.LEInfty.out
    exact hPhi4.deriv'
  have hpos : ∀ z, 0 < q z := hprofile.2.2.1
  obtain ⟨M, hM, hrel⟩ := full_line_relative_bounds hprofile
  have hrelative : RelativeC3Bound q M := ⟨hM, hrel⟩
  let C := M * Real.exp (M * kappa) * kappa ^ 2 + 1
  refine ⟨C, 1, by dsimp only [C]; positivity, zero_lt_one, ?_⟩
  intro x z0 epsilon hepsilon hepsilonOne
  let xi := z0 + epsilon * x
  let d := kappa * epsilon ^ 3
  have hd : 0 ≤ d := mul_nonneg hkappa (pow_nonneg hepsilon.le 3)
  have hdLe : d ≤ kappa := by
    dsimp only [d]
    have hepsilonCube : epsilon ^ 3 ≤ 1 := by
      exact pow_le_one₀ hepsilon.le hepsilonOne.le
    nlinarith
  have hMExp : 0 ≤ M * Real.exp (M * kappa) :=
    mul_nonneg hM (Real.exp_pos _).le
  have hPhiDeriv (z : ℝ) : HasDerivAt Phi (q z) z := by
    change HasDerivAt Phi (waveDensity diffusionMainInput W Phi z) z
    rw [← hprofile.2.1 z]
    exact (hprofile.1.1.differentiable (by norm_num) z).hasDerivAt
  have hqDifference (t : ℝ) (ht0 : 0 ≤ t) (htd : t ≤ d) :
      |q xi - q (xi - t)| ≤
        M * Real.exp (M * kappa) * q xi * t := by
    have hsegment : xi - t ≤ xi := by linarith
    have hderivOn : ∀ y ∈ Icc (xi - t) xi,
        HasDerivWithinAt q (deriv q y) (Icc (xi - t) xi) y := by
      intro y _hy
      exact (hsmooth.differentiable (by norm_num) y).hasDerivAt.hasDerivWithinAt
    have hderivBound : ∀ y ∈ Ico (xi - t) xi,
        ‖deriv q y‖ ≤ M * Real.exp (M * kappa) * q xi := by
      intro y hy
      have hyDist : |y - xi| ≤ d := by
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      have hshift :=
        (density_shift_bounds hsmooth hpos hrelative xi (y - xi)).2
      have hqy : q y ≤ Real.exp (M * kappa) * q xi := by
        rw [show xi + (y - xi) = y by ring] at hshift
        calc
          q y ≤ Real.exp (M * |y - xi|) * q xi := hshift
          _ ≤ Real.exp (M * kappa) * q xi := by
            apply mul_le_mul_of_nonneg_right _ (hpos xi).le
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (hyDist.trans hdLe) hM
      rw [Real.norm_eq_abs]
      calc
        |deriv q y| ≤ M * q y := deriv_bound_of_relativeC3 hrelative y
        _ ≤ M * (Real.exp (M * kappa) * q xi) :=
          mul_le_mul_of_nonneg_left hqy hM
        _ = M * Real.exp (M * kappa) * q xi := by ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      hderivOn hderivBound xi (right_mem_Icc.mpr hsegment)
    rw [Real.norm_eq_abs] at hmv
    convert hmv using 1 <;> ring
  let R : ℝ → ℝ := fun t ↦ Phi (xi - t) - Phi xi + t * q xi
  have hRDeriv : ∀ t ∈ Icc (0 : ℝ) d,
      HasDerivWithinAt R (-q (xi - t) + q xi) (Icc 0 d) t := by
    intro t _ht
    have hinner : HasDerivAt (fun u : ℝ ↦ xi - u) (-1) t := by
      have hinnerRaw := (hasDerivAt_id t).const_sub xi
      apply hinnerRaw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ ↦ rfl
    have hcomp := (hPhiDeriv (xi - t)).comp t hinner
    have hraw := (hcomp.sub_const (Phi xi)).add
      ((hasDerivAt_id t).mul_const (q xi))
    have hraw' := hraw.congr_deriv (by ring :
      q (xi - t) * -1 + 1 * q xi = -q (xi - t) + q xi)
    have hfinal : HasDerivAt R (-q (xi - t) + q xi) t := by
      apply hraw'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun u ↦ by
        simp only [R, Function.comp_apply, Pi.add_apply, Pi.sub_apply,
          Pi.mul_apply, id_eq]
    exact hfinal.hasDerivWithinAt
  have hRBound : ∀ t ∈ Ico (0 : ℝ) d,
      ‖-q (xi - t) + q xi‖ ≤
        M * Real.exp (M * kappa) * q xi * d := by
    intro t ht
    rw [Real.norm_eq_abs]
    have htBound := hqDifference t ht.1 ht.2.le
    rw [show -q (xi - t) + q xi = q xi - q (xi - t) by ring]
    exact htBound.trans (mul_le_mul_of_nonneg_left ht.2.le
      (mul_nonneg hMExp (hpos xi).le))
  have hR := norm_image_sub_le_of_norm_deriv_le_segment'
    hRDeriv hRBound d (right_mem_Icc.mpr hd)
  have hRzero : R 0 = 0 := by simp [R]
  rw [hRzero, sub_zero, Real.norm_eq_abs] at hR
  change
    |affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) -
        affineProfileCDF Phi epsilon z0 x +
        kappa * epsilon ^ 3 * q xi| ≤ C * epsilon ^ 6 * q xi
  have hcoordinates :
      affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) =
        Phi (xi - d) := by
    unfold affineProfileCDF xi d
    congr 1
    ring
  have hcenter : affineProfileCDF Phi epsilon z0 x = Phi xi := rfl
  rw [hcoordinates, hcenter]
  change |R d| ≤ C * epsilon ^ 6 * q xi
  calc
    |R d| ≤ M * Real.exp (M * kappa) * q xi * d * d := by
      simpa only [sub_zero] using hR
    _ = M * Real.exp (M * kappa) * kappa ^ 2 *
        epsilon ^ 6 * q xi := by
      unfold d
      ring
    _ ≤ C * epsilon ^ 6 * q xi := by
      have hcoef : M * Real.exp (M * kappa) * kappa ^ 2 ≤ C := by
        dsimp only [C]
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hepsilon.le 6))
        (hpos xi).le

/-- A translation coefficient strictly larger than the profile speed gives a uniform
one-step upper barrier for the untruncated affine profile. -/
theorem affineWaveProfile_strict_upper_margin
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (x z0 epsilon : ℝ),
        0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 + epsilon ^ 3 →
            affineProfileCDF Phi epsilon z0
                (x - kappa * epsilon ^ 2) ≤
              cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x := by
  let q := waveDensity diffusionMainInput W Phi
  obtain ⟨Cstep, epsilonStep, hCstep, hepsilonStep, hstep⟩ :=
    affineWaveProfile_oneStep_consistency hprofile
  obtain ⟨Ctrans, epsilonTrans, hCtrans, hepsilonTrans, htrans⟩ :=
    affineProfile_translation_consistency hprofile hkappa
  let gap := kappa - diffusionMainInput.kappa lambda
  have hgap : 0 < gap := sub_pos.mpr hstrict
  have hdenom : 0 < Cstep + Ctrans + 1 := by positivity
  let epsilon0 := min epsilonStep
    (min epsilonTrans (min 1 (gap / (Cstep + Ctrans + 1))))
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilonStep
      (lt_min hepsilonTrans (lt_min zero_lt_one (div_pos hgap hdenom)))
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro p x z0 epsilon hepsilon hepsilonSmall hp
  have hepsilonStepSmall : epsilon < epsilonStep :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonTransSmall : epsilon < epsilonTrans :=
    hepsilonSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilonOne : epsilon < 1 :=
    hepsilonSmall.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsilonGap : epsilon < gap / (Cstep + Ctrans + 1) :=
    hepsilonSmall.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let xi := z0 + epsilon * x
  have hstepAt := hstep p x z0 epsilon hepsilon hepsilonStepSmall hp
  change
    |cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x -
        affineProfileCDF Phi epsilon z0 x +
        diffusionMainInput.kappa lambda * epsilon ^ 3 * q xi| ≤
      Cstep * epsilon ^ 5 * q xi at hstepAt
  have htransAt := htrans x z0 epsilon hepsilon hepsilonTransSmall
  change
    |affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) -
        affineProfileCDF Phi epsilon z0 x +
        kappa * epsilon ^ 3 * q xi| ≤
      Ctrans * epsilon ^ 6 * q xi at htransAt
  have hepsilonSq : epsilon ^ 2 ≤ epsilon :=
    (pow_lt_self_of_lt_one₀ hepsilon hepsilonOne (by omega)).le
  have hepsilonCube : epsilon ^ 3 ≤ epsilon :=
    (pow_lt_self_of_lt_one₀ hepsilon hepsilonOne (by omega)).le
  have hproduct : epsilon * (Cstep + Ctrans + 1) < gap := by
    exact (lt_div_iff₀ hdenom).mp hepsilonGap
  have hcoefficient :
      Cstep * epsilon ^ 2 + Ctrans * epsilon ^ 3 ≤ gap := by
    calc
      Cstep * epsilon ^ 2 + Ctrans * epsilon ^ 3 ≤
          Cstep * epsilon + Ctrans * epsilon := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hepsilonSq hCstep.le)
          (mul_le_mul_of_nonneg_left hepsilonCube hCtrans.le)
      _ ≤ gap := by
        nlinarith
  have hqNonneg : 0 ≤ q xi := hprofile.2.2.1 xi |>.le
  have herror :
      Cstep * epsilon ^ 5 * q xi + Ctrans * epsilon ^ 6 * q xi ≤
        gap * epsilon ^ 3 * q xi := by
    have hmul := mul_le_mul_of_nonneg_right hcoefficient
      (mul_nonneg (pow_nonneg hepsilon.le 3) hqNonneg)
    nlinarith
  have hstepLower := neg_le_of_abs_le hstepAt
  have htransUpper := le_of_abs_le htransAt
  dsimp only [gap] at herror
  linarith

/-- A strict speed gap leaves a quantitative half-gap margin of order
`epsilon ^ 3 * q`.  This is the margin which absorbs the cutoff atom. -/
theorem affineWaveProfile_strict_upper_margin_quantitative
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (x z0 epsilon : ℝ),
        0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 + epsilon ^ 3 →
            let xi := z0 + epsilon * x
            affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) +
                (kappa - diffusionMainInput.kappa lambda) / 2 *
                  epsilon ^ 3 * q xi ≤
              cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x := by
  let q := waveDensity diffusionMainInput W Phi
  obtain ⟨Cstep, epsilonStep, hCstep, hepsilonStep, hstep⟩ :=
    affineWaveProfile_oneStep_consistency hprofile
  obtain ⟨Ctrans, epsilonTrans, hCtrans, hepsilonTrans, htrans⟩ :=
    affineProfile_translation_consistency hprofile hkappa
  let gap := kappa - diffusionMainInput.kappa lambda
  have hgap : 0 < gap := sub_pos.mpr hstrict
  have hdenom : 0 < 2 * (Cstep + Ctrans + 1) := by positivity
  let epsilon0 := min epsilonStep
    (min epsilonTrans (min 1 (gap / (2 * (Cstep + Ctrans + 1)))))
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilonStep
      (lt_min hepsilonTrans (lt_min zero_lt_one (div_pos hgap hdenom)))
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro p x z0 epsilon hepsilon hepsilonSmall hp
  have hepsilonStepSmall : epsilon < epsilonStep :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonTransSmall : epsilon < epsilonTrans :=
    hepsilonSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilonOne : epsilon < 1 :=
    hepsilonSmall.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsilonGap : epsilon < gap / (2 * (Cstep + Ctrans + 1)) :=
    hepsilonSmall.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let xi := z0 + epsilon * x
  have hstepAt := hstep p x z0 epsilon hepsilon hepsilonStepSmall hp
  change
    |cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x -
        affineProfileCDF Phi epsilon z0 x +
        diffusionMainInput.kappa lambda * epsilon ^ 3 * q xi| ≤
      Cstep * epsilon ^ 5 * q xi at hstepAt
  have htransAt := htrans x z0 epsilon hepsilon hepsilonTransSmall
  change
    |affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) -
        affineProfileCDF Phi epsilon z0 x +
        kappa * epsilon ^ 3 * q xi| ≤
      Ctrans * epsilon ^ 6 * q xi at htransAt
  have hepsilonSq : epsilon ^ 2 ≤ epsilon :=
    (pow_lt_self_of_lt_one₀ hepsilon hepsilonOne (by omega)).le
  have hepsilonCube : epsilon ^ 3 ≤ epsilon :=
    (pow_lt_self_of_lt_one₀ hepsilon hepsilonOne (by omega)).le
  have hproduct : epsilon * (2 * (Cstep + Ctrans + 1)) < gap :=
    (lt_div_iff₀ hdenom).mp hepsilonGap
  have hcoefficient :
      Cstep * epsilon ^ 2 + Ctrans * epsilon ^ 3 ≤ gap / 2 := by
    calc
      Cstep * epsilon ^ 2 + Ctrans * epsilon ^ 3 ≤
          Cstep * epsilon + Ctrans * epsilon := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hepsilonSq hCstep.le)
          (mul_le_mul_of_nonneg_left hepsilonCube hCtrans.le)
      _ ≤ gap / 2 := by nlinarith
  have hqNonneg : 0 ≤ q xi := hprofile.2.2.1 xi |>.le
  have herror :
      Cstep * epsilon ^ 5 * q xi + Ctrans * epsilon ^ 6 * q xi ≤
        gap / 2 * epsilon ^ 3 * q xi := by
    have hmul := mul_le_mul_of_nonneg_right hcoefficient
      (mul_nonneg (pow_nonneg hepsilon.le 3) hqNonneg)
    nlinarith
  have hstepLower := neg_le_of_abs_le hstepAt
  have htransUpper := le_of_abs_le htransAt
  dsimp only [gap] at herror
  linarith

/-! ## Atom-aware cutoff coupling -/

private theorem seriesCDF_eq_gateEvent (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    seriesCDF mu x =
      (mu.prod mu).real {z : ℝ × ℝ | logSeriesGate z.1 z.2 ≤ x} := by
  letI : IsProbabilityMeasure (seriesLaw mu) :=
    seriesLaw_isProbabilityMeasure mu
  unfold seriesCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold seriesLaw
  rw [map_measureReal_apply measurable_logSeriesGate_pair measurableSet_Iic]
  rfl

private theorem parallelCDF_eq_gateEvent (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    parallelCDF mu x =
      (mu.prod mu).real
        {z : ℝ × ℝ | logParallelGate .resistance z.1 z.2 ≤ x} := by
  letI : IsProbabilityMeasure (parallelLaw mu) :=
    parallelLaw_isProbabilityMeasure mu
  unfold parallelCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold parallelLaw
  rw [map_measureReal_apply measurable_logResistanceParallelGate_pair
    measurableSet_Iic]
  rfl

private theorem seriesCDF_nonnegativePartLaw_eq_gateEvent
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    seriesCDF (nonnegativePartLaw mu) x =
      (mu.prod mu).real
        {z : ℝ × ℝ |
          logSeriesGate (max z.1 0) (max z.2 0) ≤ x} := by
  letI : IsProbabilityMeasure (nonnegativePartLaw mu) :=
    nonnegativePartLaw_isProbabilityMeasure mu
  rw [seriesCDF_eq_gateEvent]
  unfold nonnegativePartLaw
  rw [Measure.map_prod_map mu mu (by fun_prop) (by fun_prop)]
  rw [map_measureReal_apply (by fun_prop)
    (measurableSet_le measurable_logSeriesGate_pair measurable_const)]
  rfl

private theorem parallelCDF_nonnegativePartLaw_eq_gateEvent
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    parallelCDF (nonnegativePartLaw mu) x =
      (mu.prod mu).real
        {z : ℝ × ℝ |
          logParallelGate .resistance (max z.1 0) (max z.2 0) ≤ x} := by
  letI : IsProbabilityMeasure (nonnegativePartLaw mu) :=
    nonnegativePartLaw_isProbabilityMeasure mu
  rw [parallelCDF_eq_gateEvent]
  unfold nonnegativePartLaw
  rw [Measure.map_prod_map mu mu (by fun_prop) (by fun_prop)]
  rw [map_measureReal_apply (by fun_prop)
    (measurableSet_le measurable_logResistanceParallelGate_pair measurable_const)]
  rfl

private theorem logSeriesGate_right_le_gate (u v : ℝ) :
    v ≤ logSeriesGate u v := by
  rw [logSeriesGate_eq_max_add_h]
  exact (le_max_right u v).trans (le_add_of_nonneg_right (h_nonneg _))

private theorem logResistanceParallelGate_le_left' (u v : ℝ) :
    logParallelGate .resistance u v ≤ u := by
  rw [logParallelGate_eq_min_sub_h, Mode.eta_resistance]
  have hh : 0 ≤ h |u - v| := h_nonneg _
  linarith [min_le_left u v]

private theorem logResistanceParallelGate_le_right' (u v : ℝ) :
    logParallelGate .resistance u v ≤ v := by
  rw [logParallelGate_eq_min_sub_h, Mode.eta_resistance]
  have hh : 0 ≤ h |u - v| := h_nonneg _
  linarith [min_le_right u v]

/-- Pushing negative inputs to zero does not alter the resistance-parallel CDF at a
nonnegative threshold. -/
theorem parallelCDF_nonnegativePartLaw_eq (mu : Measure ℝ)
    [IsProbabilityMeasure mu] {x : ℝ} (hx : 0 ≤ x) :
    parallelCDF (nonnegativePartLaw mu) x = parallelCDF mu x := by
  rw [parallelCDF_nonnegativePartLaw_eq_gateEvent,
    parallelCDF_eq_gateEvent]
  congr 1
  ext z
  simp only [mem_setOf_eq]
  by_cases hu : 0 ≤ z.1
  · by_cases hv : 0 ≤ z.2
    · rw [max_eq_left hu, max_eq_left hv]
    · have hv' : z.2 ≤ 0 := le_of_not_ge hv
      have horiginal : logParallelGate .resistance z.1 z.2 ≤ x :=
        (logResistanceParallelGate_le_right' z.1 z.2).trans (hv'.trans hx)
      have hcutoff :
          logParallelGate .resistance (max z.1 0) (max z.2 0) ≤ x := by
        rw [max_eq_left hu, max_eq_right hv']
        exact (logResistanceParallelGate_le_right' z.1 0).trans hx
      exact iff_of_true hcutoff horiginal
  · have hu' : z.1 ≤ 0 := le_of_not_ge hu
    have horiginal : logParallelGate .resistance z.1 z.2 ≤ x :=
      (logResistanceParallelGate_le_left' z.1 z.2).trans (hu'.trans hx)
    have hcutoff :
        logParallelGate .resistance (max z.1 0) (max z.2 0) ≤ x := by
      rw [max_eq_right hu']
      exact (logResistanceParallelGate_le_left' 0 (max z.2 0)).trans hx
    exact iff_of_true hcutoff horiginal

/-- A first atom-aware coupling bound: the series CDF can lose mass only when at least
one original input lies below the cutoff. -/
theorem seriesCDF_le_nonnegativePartLaw_add_cutoffMass
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 := by
  let nu := mu.prod mu
  letI : IsProbabilityMeasure nu := inferInstance
  let original : Set (ℝ × ℝ) :=
    {z | logSeriesGate z.1 z.2 ≤ x}
  let cutoff : Set (ℝ × ℝ) :=
    {z | logSeriesGate (max z.1 0) (max z.2 0) ≤ x}
  let bad : Set (ℝ × ℝ) :=
    (Iic (0 : ℝ) ×ˢ univ) ∪ (univ ×ˢ Iic (0 : ℝ))
  have horiginalMeas : MeasurableSet original :=
    measurableSet_le measurable_logSeriesGate_pair measurable_const
  have hcutoffMeas : MeasurableSet cutoff := by
    have hmap : Measurable
        (fun z : ℝ × ℝ ↦ (max z.1 0, max z.2 0)) :=
      (measurable_fst.max measurable_const).prodMk
        (measurable_snd.max measurable_const)
    exact measurableSet_le (measurable_logSeriesGate_pair.comp hmap) measurable_const
  have hbadMeas : MeasurableSet bad :=
    (measurableSet_Iic.prod MeasurableSet.univ).union
      (MeasurableSet.univ.prod measurableSet_Iic)
  have hsubset : original ⊆ cutoff ∪ bad := by
    intro z hz
    by_cases hu : z.1 ≤ 0
    · exact Or.inr (Or.inl ⟨hu, mem_univ z.2⟩)
    · by_cases hv : z.2 ≤ 0
      · exact Or.inr (Or.inr ⟨mem_univ z.1, hv⟩)
      · apply Or.inl
        have hu0 : 0 ≤ z.1 := (lt_of_not_ge hu).le
        have hv0 : 0 ≤ z.2 := (lt_of_not_ge hv).le
        change logSeriesGate z.1 z.2 ≤ x at hz
        simpa only [cutoff, mem_setOf_eq, max_eq_left hu0,
          max_eq_left hv0] using hz
  have hmeasure := measureReal_mono (μ := nu) hsubset (by finiteness)
  have hunion := measureReal_union_le cutoff bad (μ := nu)
  have hleft : nu.real (Iic (0 : ℝ) ×ˢ univ) =
      ProbabilityTheory.cdf mu 0 := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    change mu.real (Iic 0) * mu.real univ = _
    rw [probReal_univ, mul_one, ← ProbabilityTheory.cdf_eq_real]
  have hright : nu.real (univ ×ˢ Iic (0 : ℝ)) =
      ProbabilityTheory.cdf mu 0 := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    change mu.real univ * mu.real (Iic 0) = _
    rw [probReal_univ, one_mul, ← ProbabilityTheory.cdf_eq_real]
  have hbad : nu.real bad ≤ 2 * ProbabilityTheory.cdf mu 0 := by
    calc
      nu.real bad ≤ nu.real (Iic (0 : ℝ) ×ˢ univ) +
          nu.real (univ ×ˢ Iic (0 : ℝ)) := measureReal_union_le _ _
      _ = 2 * ProbabilityTheory.cdf mu 0 := by rw [hleft, hright]; ring
  rw [seriesCDF_eq_gateEvent,
    seriesCDF_nonnegativePartLaw_eq_gateEvent]
  change nu.real original ≤ nu.real cutoff + 2 * ProbabilityTheory.cdf mu 0
  exact hmeasure.trans (hunion.trans (by linarith))

/-- The lower endpoint of the second coordinate interval in the cutoff coupling. -/
noncomputable def seriesCutoffLower (x : ℝ) : ℝ :=
  if x < Real.log 2 then 0 else Real.log (Real.exp x - 1)

private theorem two_le_exp_of_log_two_le {x : ℝ}
    (hx : Real.log 2 ≤ x) : (2 : ℝ) ≤ Real.exp x := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr hx

/-- The cutoff interval stays in `[0,x]` for every nonnegative threshold. -/
theorem seriesCutoffLower_mem {x : ℝ} (hx : 0 ≤ x) :
    seriesCutoffLower x ∈ Icc 0 x := by
  by_cases hsmall : x < Real.log 2
  · simp only [seriesCutoffLower, if_pos hsmall, mem_Icc]
    exact ⟨le_rfl, hx⟩
  · have hxLog : Real.log 2 ≤ x := le_of_not_gt hsmall
    have hExp : (2 : ℝ) ≤ Real.exp x := two_le_exp_of_log_two_le hxLog
    have hpos : 0 < Real.exp x - 1 := by linarith
    rw [seriesCutoffLower, if_neg hsmall, mem_Icc]
    constructor
    · exact Real.log_nonneg (by linarith)
    · exact (Real.log_le_iff_le_exp hpos).2 (by linarith)

/-- The interval exposed by moving one input to zero has length at most `log 2`. -/
theorem seriesCutoffLower_gap_le_log_two {x : ℝ} (hx : 0 ≤ x) :
    x - seriesCutoffLower x ≤ Real.log 2 := by
  by_cases hsmall : x < Real.log 2
  · rw [seriesCutoffLower, if_pos hsmall, sub_zero]
    exact hsmall.le
  · have hxLog : Real.log 2 ≤ x := le_of_not_gt hsmall
    have hExp : (2 : ℝ) ≤ Real.exp x := two_le_exp_of_log_two_le hxLog
    have hpos : 0 < Real.exp x - 1 := by linarith
    have hhalf : Real.exp (x - Real.log 2) ≤ Real.exp x - 1 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.exp_pos x]
    have hlog : x - Real.log 2 ≤ Real.log (Real.exp x - 1) :=
      (Real.le_log_iff_exp_le hpos).2 hhalf
    rw [seriesCutoffLower, if_neg hsmall]
    linarith

private theorem logSeriesGate_zero_seriesCutoffLower {x : ℝ}
    (hx : Real.log 2 ≤ x) :
    logSeriesGate 0 (seriesCutoffLower x) = x := by
  have hsmall : ¬x < Real.log 2 := not_lt.mpr hx
  have hExp : (2 : ℝ) ≤ Real.exp x := two_le_exp_of_log_two_le hx
  have hpos : 0 < Real.exp x - 1 := by linarith
  rw [seriesCutoffLower, if_neg hsmall]
  unfold logSeriesGate
  rw [Real.exp_zero, Real.exp_log hpos]
  convert Real.log_exp x using 1 <;> ring

private theorem seriesCutoffLower_lt_of_cutoff_crossing
    {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v)
    (hcross : x < logSeriesGate 0 v) :
    seriesCutoffLower x < v := by
  by_cases hsmall : x < Real.log 2
  · rw [seriesCutoffLower, if_pos hsmall]
    exact hv
  · have hxLog : Real.log 2 ≤ x := le_of_not_gt hsmall
    have hExp : (2 : ℝ) ≤ Real.exp x := two_le_exp_of_log_two_le hxLog
    have hpos : 0 < Real.exp x - 1 := by linarith
    apply Real.exp_lt_exp.mp
    rw [seriesCutoffLower, if_neg hsmall, Real.exp_log hpos]
    have hexpCross := Real.exp_lt_exp.mpr hcross
    unfold logSeriesGate at hexpCross
    rw [Real.exp_log (add_pos (Real.exp_pos 0) (Real.exp_pos v))] at hexpCross
    rw [Real.exp_zero] at hexpCross
    linarith

private theorem logSeriesGate_left_le_gate (u v : ℝ) :
    u ≤ logSeriesGate u v := by
  rw [logSeriesGate_eq_max_add_h]
  exact (le_max_left u v).trans (le_add_of_nonneg_right (h_nonneg _))

private theorem logSeriesGate_comm' (u v : ℝ) :
    logSeriesGate u v = logSeriesGate v u := by
  unfold logSeriesGate
  rw [add_comm]

/-- Atom-aware series coupling error.  Besides the two-atom event, the second input is
confined to the interval exposed by replacing the first input by zero. -/
theorem seriesCDF_le_nonnegativePartLaw_add_localized
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {x : ℝ} (hx : 0 ≤ x) :
    seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 *
        (ProbabilityTheory.cdf mu 0 +
          (ProbabilityTheory.cdf mu x -
            ProbabilityTheory.cdf mu (seriesCutoffLower x))) := by
  let nu := mu.prod mu
  letI : IsProbabilityMeasure nu := inferInstance
  let lower := seriesCutoffLower x
  let near : Set ℝ := Iic (0 : ℝ) ∪ Ioc lower x
  let original : Set (ℝ × ℝ) :=
    {z | logSeriesGate z.1 z.2 ≤ x}
  let cutoff : Set (ℝ × ℝ) :=
    {z | logSeriesGate (max z.1 0) (max z.2 0) ≤ x}
  let bad : Set (ℝ × ℝ) :=
    (Iic (0 : ℝ) ×ˢ near) ∪ (near ×ˢ Iic (0 : ℝ))
  have hlower : lower ∈ Icc (0 : ℝ) x := seriesCutoffLower_mem hx
  have hnearMeas : MeasurableSet near :=
    measurableSet_Iic.union measurableSet_Ioc
  have hsubset : original ⊆ cutoff ∪ bad := by
    intro z hz
    change logSeriesGate z.1 z.2 ≤ x at hz
    by_cases hcut : logSeriesGate (max z.1 0) (max z.2 0) ≤ x
    · exact Or.inl hcut
    · apply Or.inr
      have hcross := lt_of_not_ge hcut
      by_cases hu : z.1 ≤ 0
      · apply Or.inl
        refine ⟨hu, ?_⟩
        by_cases hv : z.2 ≤ 0
        · exact Or.inl hv
        · have hvPos : 0 < z.2 := lt_of_not_ge hv
          have hvx : z.2 ≤ x := (logSeriesGate_right_le_gate _ _).trans hz
          have hcross' : x < logSeriesGate 0 z.2 := by
            simpa only [max_eq_right hu, max_eq_left hvPos.le] using hcross
          exact Or.inr
            ⟨seriesCutoffLower_lt_of_cutoff_crossing hx hvPos hcross', hvx⟩
      · have huPos : 0 < z.1 := lt_of_not_ge hu
        have hv : z.2 ≤ 0 := by
          by_contra hvNot
          have hvPos : 0 < z.2 := lt_of_not_ge hvNot
          have hsame :
              logSeriesGate (max z.1 0) (max z.2 0) ≤ x := by
            simpa only [max_eq_left huPos.le, max_eq_left hvPos.le] using hz
          exact hcut hsame
        apply Or.inr
        refine ⟨?_, hv⟩
        have hux : z.1 ≤ x := (logSeriesGate_left_le_gate _ _).trans hz
        have hcross' : x < logSeriesGate 0 z.1 := by
          rw [max_eq_left huPos.le, max_eq_right hv,
            logSeriesGate_comm'] at hcross
          exact hcross
        exact Or.inr
          ⟨seriesCutoffLower_lt_of_cutoff_crossing hx huPos hcross', hux⟩
  have hset : Iic x \ Iic lower = Ioc lower x := by
    ext y
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hyx, hynot⟩
      exact ⟨lt_of_not_ge hynot, hyx⟩
    · rintro ⟨hlowy, hyx⟩
      exact ⟨hyx, not_le_of_gt hlowy⟩
  have hinterval : mu.real (Ioc lower x) =
      ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower := by
    rw [← hset, measureReal_sdiff (Iic_subset_Iic.mpr hlower.2)
      measurableSet_Iic]
    rw [← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real]
  have hnear : mu.real near ≤ ProbabilityTheory.cdf mu 0 +
      (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower) := by
    calc
      mu.real near ≤ mu.real (Iic (0 : ℝ)) + mu.real (Ioc lower x) :=
        measureReal_union_le _ _
      _ = ProbabilityTheory.cdf mu 0 +
          (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower) := by
        rw [← ProbabilityTheory.cdf_eq_real, hinterval]
  have halpha : 0 ≤ ProbabilityTheory.cdf mu 0 :=
    ProbabilityTheory.cdf_nonneg mu 0
  have hcdfZero : (mu (Iic (0 : ℝ))).toReal =
      ProbabilityTheory.cdf mu 0 := by
    change mu.real (Iic (0 : ℝ)) = ProbabilityTheory.cdf mu 0
    rw [← ProbabilityTheory.cdf_eq_real]
  have hleft : nu.real (Iic (0 : ℝ) ×ˢ near) =
      ProbabilityTheory.cdf mu 0 * mu.real near := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    rw [hcdfZero]
  have hright : nu.real (near ×ˢ Iic (0 : ℝ)) =
      mu.real near * ProbabilityTheory.cdf mu 0 := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    rw [hcdfZero]
  have hbad : nu.real bad ≤
      2 * ProbabilityTheory.cdf mu 0 *
        (ProbabilityTheory.cdf mu 0 +
          (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower)) := by
    calc
      nu.real bad ≤ nu.real (Iic (0 : ℝ) ×ˢ near) +
          nu.real (near ×ˢ Iic (0 : ℝ)) := measureReal_union_le _ _
      _ = ProbabilityTheory.cdf mu 0 * mu.real near +
          mu.real near * ProbabilityTheory.cdf mu 0 := by rw [hleft, hright]
      _ ≤ 2 * ProbabilityTheory.cdf mu 0 *
          (ProbabilityTheory.cdf mu 0 +
            (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower)) := by
        nlinarith
  have hmeasure := measureReal_mono (μ := nu) hsubset (by finiteness)
  have hunion := measureReal_union_le cutoff bad (μ := nu)
  rw [seriesCDF_eq_gateEvent,
    seriesCDF_nonnegativePartLaw_eq_gateEvent]
  change nu.real original ≤ nu.real cutoff +
    2 * ProbabilityTheory.cdf mu 0 *
      (ProbabilityTheory.cdf mu 0 +
        (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower))
  exact hmeasure.trans (hunion.trans (by linarith))

private theorem seriesCDF_le_nonnegativePartLaw_add_large
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {x : ℝ}
    (hx : Real.log 2 ≤ x) :
    seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 *
        (ProbabilityTheory.cdf mu x -
          ProbabilityTheory.cdf mu (seriesCutoffLower x)) := by
  let nu := mu.prod mu
  letI : IsProbabilityMeasure nu := inferInstance
  let lower := seriesCutoffLower x
  let near : Set ℝ := Ioc lower x
  let original : Set (ℝ × ℝ) :=
    {z | logSeriesGate z.1 z.2 ≤ x}
  let cutoff : Set (ℝ × ℝ) :=
    {z | logSeriesGate (max z.1 0) (max z.2 0) ≤ x}
  let bad : Set (ℝ × ℝ) :=
    (Iic (0 : ℝ) ×ˢ near) ∪ (near ×ˢ Iic (0 : ℝ))
  have hx0 : 0 ≤ x := by
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hx
  have hlower : lower ∈ Icc (0 : ℝ) x := seriesCutoffLower_mem hx0
  have hgateZero : logSeriesGate 0 0 ≤ x := by
    have hgate : logSeriesGate 0 0 = Real.log 2 := by
      unfold logSeriesGate
      norm_num
    rw [hgate]
    exact hx
  have hsubset : original ⊆ cutoff ∪ bad := by
    intro z hz
    change logSeriesGate z.1 z.2 ≤ x at hz
    by_cases hcut : logSeriesGate (max z.1 0) (max z.2 0) ≤ x
    · exact Or.inl hcut
    · apply Or.inr
      have hcross := lt_of_not_ge hcut
      by_cases hu : z.1 ≤ 0
      · have hvPos : 0 < z.2 := by
          by_contra hvNot
          have hv : z.2 ≤ 0 := le_of_not_gt hvNot
          apply hcut
          simpa only [max_eq_right hu, max_eq_right hv] using hgateZero
        apply Or.inl
        refine ⟨hu, ?_⟩
        have hvx : z.2 ≤ x := (logSeriesGate_right_le_gate _ _).trans hz
        have hcross' : x < logSeriesGate 0 z.2 := by
          simpa only [max_eq_right hu, max_eq_left hvPos.le] using hcross
        exact ⟨seriesCutoffLower_lt_of_cutoff_crossing hx0 hvPos hcross', hvx⟩
      · have huPos : 0 < z.1 := lt_of_not_ge hu
        have hv : z.2 ≤ 0 := by
          by_contra hvNot
          have hvPos : 0 < z.2 := lt_of_not_ge hvNot
          apply hcut
          simpa only [max_eq_left huPos.le, max_eq_left hvPos.le] using hz
        apply Or.inr
        refine ⟨?_, hv⟩
        have hux : z.1 ≤ x := (logSeriesGate_left_le_gate _ _).trans hz
        have hcross' : x < logSeriesGate 0 z.1 := by
          rw [max_eq_left huPos.le, max_eq_right hv,
            logSeriesGate_comm'] at hcross
          exact hcross
        exact ⟨seriesCutoffLower_lt_of_cutoff_crossing hx0 huPos hcross', hux⟩
  have hset : Iic x \ Iic lower = Ioc lower x := by
    ext y
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hyx, hynot⟩
      exact ⟨lt_of_not_ge hynot, hyx⟩
    · rintro ⟨hlowy, hyx⟩
      exact ⟨hyx, not_le_of_gt hlowy⟩
  have hinterval : mu.real near = ProbabilityTheory.cdf mu x -
      ProbabilityTheory.cdf mu lower := by
    change mu.real (Ioc lower x) = _
    rw [← hset, measureReal_sdiff (Iic_subset_Iic.mpr hlower.2)
      measurableSet_Iic]
    rw [← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real]
  have hcdfZero : (mu (Iic (0 : ℝ))).toReal =
      ProbabilityTheory.cdf mu 0 := by
    change mu.real (Iic (0 : ℝ)) = ProbabilityTheory.cdf mu 0
    rw [← ProbabilityTheory.cdf_eq_real]
  have hleft : nu.real (Iic (0 : ℝ) ×ˢ near) =
      ProbabilityTheory.cdf mu 0 * mu.real near := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul, hcdfZero]
  have hright : nu.real (near ×ˢ Iic (0 : ℝ)) =
      mu.real near * ProbabilityTheory.cdf mu 0 := by
    unfold nu Measure.real
    rw [Measure.prod_prod, ENNReal.toReal_mul, hcdfZero]
  have hbad : nu.real bad ≤ 2 * ProbabilityTheory.cdf mu 0 *
      (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower) := by
    calc
      nu.real bad ≤ nu.real (Iic (0 : ℝ) ×ˢ near) +
          nu.real (near ×ˢ Iic (0 : ℝ)) := measureReal_union_le _ _
      _ = 2 * ProbabilityTheory.cdf mu 0 *
          (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower) := by
        rw [hleft, hright, hinterval]
        ring
  have hmeasure := measureReal_mono (μ := nu) hsubset (by finiteness)
  have hunion := measureReal_union_le cutoff bad (μ := nu)
  rw [seriesCDF_eq_gateEvent,
    seriesCDF_nonnegativePartLaw_eq_gateEvent]
  change nu.real original ≤ nu.real cutoff +
    2 * ProbabilityTheory.cdf mu 0 *
      (ProbabilityTheory.cdf mu x - ProbabilityTheory.cdf mu lower)
  exact hmeasure.trans (hunion.trans (by linarith))

/-- Sharp atom-aware series error with the two-atom term present only below `log 2`. -/
theorem seriesCDF_le_nonnegativePartLaw_add_atomAware
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {x : ℝ} (hx : 0 ≤ x) :
    seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 *
        ((if x < Real.log 2 then ProbabilityTheory.cdf mu 0 else 0) +
          (ProbabilityTheory.cdf mu x -
            ProbabilityTheory.cdf mu (seriesCutoffLower x))) := by
  by_cases hsmall : x < Real.log 2
  · simpa only [if_pos hsmall] using
      seriesCDF_le_nonnegativePartLaw_add_localized mu hx
  · have hxLog : Real.log 2 ≤ x := le_of_not_gt hsmall
    simpa only [if_neg hsmall, zero_add] using
      seriesCDF_le_nonnegativePartLaw_add_large mu hxLog

/-- The atom-aware coupling error for the full CDF operator.  The parallel branch has
zero error at nonnegative thresholds, while the Bernoulli weight of the series branch
is at most one. -/
theorem cdfOperator_le_nonnegativePartLaw_add_localized
    (p : Set.Icc (0 : ℝ) 1) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] {x : ℝ} (hx : 0 ≤ x) :
    cdfOperator p mu x ≤ cdfOperator p (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 *
        (ProbabilityTheory.cdf mu 0 +
          (ProbabilityTheory.cdf mu x -
            ProbabilityTheory.cdf mu (seriesCutoffLower x))) := by
  let error := 2 * ProbabilityTheory.cdf mu 0 *
    (ProbabilityTheory.cdf mu 0 +
      (ProbabilityTheory.cdf mu x -
        ProbabilityTheory.cdf mu (seriesCutoffLower x)))
  have hlower := seriesCutoffLower_mem hx
  have hcdfInc : 0 ≤ ProbabilityTheory.cdf mu x -
      ProbabilityTheory.cdf mu (seriesCutoffLower x) :=
    sub_nonneg.mpr (ProbabilityTheory.monotone_cdf mu hlower.2)
  have halpha : 0 ≤ ProbabilityTheory.cdf mu 0 :=
    ProbabilityTheory.cdf_nonneg mu 0
  have herror : 0 ≤ error := by
    dsimp only [error]
    exact mul_nonneg (mul_nonneg (by positivity) halpha)
      (add_nonneg halpha hcdfInc)
  have hseries := seriesCDF_le_nonnegativePartLaw_add_localized mu hx
  change seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x + error at hseries
  have hweighted := mul_le_mul_of_nonneg_left hseries p.2.1
  have hweightError : (p : ℝ) * error ≤ error := by
    nlinarith [p.2.2]
  have hparallel := parallelCDF_nonnegativePartLaw_eq mu hx
  unfold cdfOperator
  rw [hparallel]
  nlinarith

/-- Sharp operator cutoff error, with the two-atom contribution restricted to
`0 ≤ x < log 2`. -/
theorem cdfOperator_le_nonnegativePartLaw_add_atomAware
    (p : Set.Icc (0 : ℝ) 1) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] {x : ℝ} (hx : 0 ≤ x) :
    cdfOperator p mu x ≤ cdfOperator p (nonnegativePartLaw mu) x +
      2 * ProbabilityTheory.cdf mu 0 *
        ((if x < Real.log 2 then ProbabilityTheory.cdf mu 0 else 0) +
          (ProbabilityTheory.cdf mu x -
            ProbabilityTheory.cdf mu (seriesCutoffLower x))) := by
  let error := 2 * ProbabilityTheory.cdf mu 0 *
    ((if x < Real.log 2 then ProbabilityTheory.cdf mu 0 else 0) +
      (ProbabilityTheory.cdf mu x -
        ProbabilityTheory.cdf mu (seriesCutoffLower x)))
  have hlower := seriesCutoffLower_mem hx
  have hcdfInc : 0 ≤ ProbabilityTheory.cdf mu x -
      ProbabilityTheory.cdf mu (seriesCutoffLower x) :=
    sub_nonneg.mpr (ProbabilityTheory.monotone_cdf mu hlower.2)
  have halpha : 0 ≤ ProbabilityTheory.cdf mu 0 :=
    ProbabilityTheory.cdf_nonneg mu 0
  have hfirst : 0 ≤
      if x < Real.log 2 then ProbabilityTheory.cdf mu 0 else 0 := by
    split_ifs <;> positivity
  have herror : 0 ≤ error := by
    dsimp only [error]
    exact mul_nonneg (mul_nonneg (by positivity) halpha)
      (add_nonneg hfirst hcdfInc)
  have hseries := seriesCDF_le_nonnegativePartLaw_add_atomAware mu hx
  change seriesCDF mu x ≤ seriesCDF (nonnegativePartLaw mu) x + error at hseries
  have hweighted := mul_le_mul_of_nonneg_left hseries p.2.1
  have hweightError : (p : ℝ) * error ≤ error := by
    nlinarith [p.2.2]
  have hparallel := parallelCDF_nonnegativePartLaw_eq mu hx
  unfold cdfOperator
  rw [hparallel]
  nlinarith

/-! ## Quantitative cutoff error for the affine profile -/

/-- The sharp atom-aware coupling error is `O(epsilon ^ 4 q(xi))`, uniformly over
all nonnegative thresholds. -/
theorem affineWaveProfile_atomAware_error_bound
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (hlambda : 0 < lambda) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ epsilon x : ℝ, 0 < epsilon → epsilon < epsilon0 → 0 ≤ x →
        let z0 := upperCutoff Phi epsilon
        let xi := z0 + epsilon * x
        2 * epsilon ^ 4 *
            ((if x < Real.log 2 then epsilon ^ 4 else 0) +
              (affineProfileCDF Phi epsilon z0 x -
                affineProfileCDF Phi epsilon z0 (seriesCutoffLower x))) ≤
          C * epsilon ^ 4 * q xi := by
  let q := waveDensity diffusionMainInput W Phi
  have hqEq : q = deriv Phi := by
    funext z
    exact (hprofile.2.1 z).symm
  have hsmooth : ContDiff ℝ 3 q := by
    rw [hqEq]
    have hPhi4 : ContDiff ℝ 4 Phi :=
      hprofile.1.1.of_le ENat.LEInfty.out
    exact hPhi4.deriv'
  have hpos : ∀ z, 0 < q z := hprofile.2.2.1
  obtain ⟨M, hM, hrel⟩ := full_line_relative_bounds hprofile
  have hrelative : RelativeC3Bound q M := ⟨hM, hrel⟩
  let c := diffusionMainInput.beta / (2 * lambda)
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos diffusionMainInput.beta_pos (mul_pos (by positivity) hlambda)
  have hcLimit : c < diffusionMainInput.beta / lambda := by
    dsimp only [c]
    have hbeta := diffusionMainInput.beta_pos
    have hleft := div_pos hbeta hlambda
    field_simp
    nlinarith
  have hratioEventually : ∀ᶠ z in atBot,
      c < q z / Phi z := by
    exact (full_line_tail_ratios hprofile).1.eventually
      (Ioi_mem_nhds hcLimit)
  obtain ⟨A, hA⟩ := eventually_atBot.1 hratioEventually
  obtain ⟨epsilonTail, hepsilonTail, htail⟩ :=
    upperCutoff_tail_position hprofile A
  let C := 2 * (c⁻¹ + Real.exp (M * Real.log 2) * Real.log 2)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let epsilon0 := min epsilonTail 1
  have hepsilon0 : 0 < epsilon0 := lt_min hepsilonTail zero_lt_one
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro epsilon x hepsilon hepsilonSmall hx
  have hepsilonTailSmall : epsilon < epsilonTail :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonOne : epsilon < 1 :=
    hepsilonSmall.trans_le (min_le_right _ _)
  let z0 := upperCutoff Phi epsilon
  let xi := z0 + epsilon * x
  let lower := seriesCutoffLower x
  have hlower : lower ∈ Icc (0 : ℝ) x := seriesCutoffLower_mem hx
  have hgap : x - lower ≤ Real.log 2 :=
    seriesCutoffLower_gap_le_log_two hx
  have hcutoffA : z0 + epsilon * Real.log 2 < A :=
    htail epsilon hepsilon hepsilonTailSmall
  have hPhiDeriv (z : ℝ) : HasDerivAt Phi (q z) z := by
    change HasDerivAt Phi (waveDensity diffusionMainInput W Phi z) z
    rw [← hprofile.2.1 z]
    exact (hprofile.1.1.differentiable (by norm_num) z).hasDerivAt
  have haffineDeriv (y : ℝ) :
      HasDerivAt (affineProfileCDF Phi epsilon z0)
        (epsilon * q (z0 + epsilon * y)) y := by
    have hinner : HasDerivAt (fun t : ℝ ↦ z0 + epsilon * t) epsilon y :=
      (hasDerivAt_const_mul epsilon).const_add z0
    have hcomp := (hPhiDeriv (z0 + epsilon * y)).comp y hinner
    have hcomp' : HasDerivAt (Phi ∘ fun t : ℝ ↦ z0 + epsilon * t)
        (epsilon * q (z0 + epsilon * y)) y := by
      simpa only [mul_comm] using hcomp
    change HasDerivAt (fun t : ℝ ↦ Phi (z0 + epsilon * t))
      (epsilon * q (z0 + epsilon * y)) y
    apply hcomp'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hderivBound : ∀ y ∈ Ico lower x,
      ‖epsilon * q (z0 + epsilon * y)‖ ≤
        epsilon * Real.exp (M * Real.log 2) * q xi := by
    intro y hy
    have hyGap : |y - x| ≤ Real.log 2 := by
      rw [abs_le]
      constructor
      · linarith [hy.1, hgap]
      · linarith [hy.2]
    have hshift :=
      (density_shift_bounds hsmooth hpos hrelative xi (epsilon * (y - x))).2
    have hcoordinate : xi + epsilon * (y - x) = z0 + epsilon * y := by
      unfold xi
      ring
    rw [hcoordinate] at hshift
    have hexp : Real.exp (M * |epsilon * (y - x)|) ≤
        Real.exp (M * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_pos hepsilon]
      apply mul_le_mul_of_nonneg_left _ hM
      exact (mul_le_mul_of_nonneg_left hyGap hepsilon.le).trans
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hepsilonOne.le hlogTwo.le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hepsilon,
      abs_of_pos (hpos (z0 + epsilon * y))]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (hshift.trans (mul_le_mul_of_nonneg_right hexp (hpos xi).le))
      hepsilon.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y _hy ↦ (haffineDeriv y).hasDerivWithinAt)
    hderivBound x (right_mem_Icc.mpr hlower.2)
  have hincrement :
      affineProfileCDF Phi epsilon z0 x -
          affineProfileCDF Phi epsilon z0 lower ≤
        epsilon * Real.exp (M * Real.log 2) * q xi * Real.log 2 := by
    have hmono : affineProfileCDF Phi epsilon z0 lower ≤
        affineProfileCDF Phi epsilon z0 x := by
      unfold affineProfileCDF
      apply hprofile.1.2.1.monotone
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hlower.2 hepsilon.le) z0
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hmono)] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_left hgap
      (mul_nonneg (mul_nonneg hepsilon.le (Real.exp_pos _).le)
        (hpos xi).le))
  have hatom :
      (if x < Real.log 2 then epsilon ^ 4 else 0) ≤ c⁻¹ * q xi := by
    by_cases hsmall : x < Real.log 2
    · rw [if_pos hsmall]
      have hxiA : xi ≤ A := by
        have hxLog : x ≤ Real.log 2 := hsmall.le
        have : xi ≤ z0 + epsilon * Real.log 2 := by
          unfold xi
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left hxLog hepsilon.le) z0
        exact this.trans hcutoffA.le
      have hratio := hA xi hxiA
      have hPhiPos := (hprofile.1.2.2.1 xi).1
      have hcPhi : c * Phi xi ≤ q xi := by
        exact ((lt_div_iff₀ hPhiPos).mp hratio).le
      have hcutoffSpec := upperCutoff_spec hprofile hepsilon hepsilonOne
      have hz0xi : z0 ≤ xi := by
        unfold xi
        exact le_add_of_nonneg_right (mul_nonneg hepsilon.le hx)
      have halphaPhi : epsilon ^ 4 ≤ Phi xi := by
        rw [← hcutoffSpec]
        exact hprofile.1.2.1.monotone hz0xi
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hc).2
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left halphaPhi hc.le).trans hcPhi
    · rw [if_neg hsmall]
      exact mul_nonneg (inv_nonneg.mpr hc.le) (hpos xi).le
  change
    2 * epsilon ^ 4 *
        ((if x < Real.log 2 then epsilon ^ 4 else 0) +
          (affineProfileCDF Phi epsilon z0 x -
            affineProfileCDF Phi epsilon z0 lower)) ≤
      C * epsilon ^ 4 * q xi
  have hinside :
      (if x < Real.log 2 then epsilon ^ 4 else 0) +
          (affineProfileCDF Phi epsilon z0 x -
            affineProfileCDF Phi epsilon z0 lower) ≤
        (c⁻¹ + Real.exp (M * Real.log 2) * Real.log 2) * q xi := by
    calc
      _ ≤ c⁻¹ * q xi +
          epsilon * Real.exp (M * Real.log 2) * q xi * Real.log 2 :=
        add_le_add hatom hincrement
      _ ≤ c⁻¹ * q xi +
          Real.exp (M * Real.log 2) * q xi * Real.log 2 := by
        have hfactor : epsilon *
            (Real.exp (M * Real.log 2) * q xi * Real.log 2) ≤
            1 * (Real.exp (M * Real.log 2) * q xi * Real.log 2) :=
          mul_le_mul_of_nonneg_right hepsilonOne.le
            (mul_nonneg (mul_nonneg
              (Real.exp_pos (M * Real.log 2)).le (hpos xi).le) hlogTwo.le)
        nlinarith [hfactor]
      _ = (c⁻¹ + Real.exp (M * Real.log 2) * Real.log 2) * q xi := by ring
  calc
    _ ≤ (2 * epsilon ^ 4) *
        ((c⁻¹ + Real.exp (M * Real.log 2) * Real.log 2) * q xi) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ = C * epsilon ^ 4 * q xi := by
      dsimp only [C]
      ring

/-- The law of the upper barrier after pushing its negative part to zero. -/
noncomputable def upperBarrierLaw {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (epsilon : ℝ) : Measure ℝ :=
  nonnegativePartLaw
    (affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon))

theorem upperBarrierLaw_isProbabilityMeasure
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (epsilon : ℝ) : IsProbabilityMeasure (upperBarrierLaw hprofile epsilon) := by
  letI : IsProbabilityMeasure
      (affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon)) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon (upperCutoff Phi epsilon)
  unfold upperBarrierLaw
  exact nonnegativePartLaw_isProbabilityMeasure _

/-- Exact CDF of the atom-aware truncated law. -/
theorem cdf_upperBarrierLaw {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ProbabilityTheory.cdf (upperBarrierLaw hprofile epsilon) =
      cutoffProfileCDF Phi epsilon := by
  letI : IsProbabilityMeasure
      (affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon)) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon (upperCutoff Phi epsilon)
  letI : IsProbabilityMeasure (upperBarrierLaw hprofile epsilon) :=
    upperBarrierLaw_isProbabilityMeasure hprofile epsilon
  funext x
  unfold upperBarrierLaw
  rw [cdf_nonnegativePartLaw]
  rw [congrFun (cdf_affineWaveProfileLaw hprofile hepsilon
    (upperCutoff Phi epsilon)) x]
  rfl

/-- Replacing the affine profile by its cutoff law changes one CDF step by at most
`C * epsilon ^ 4 * q` at every nonnegative threshold. -/
theorem affineWaveProfile_cdfOperator_le_upperBarrier_add_error
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (hlambda : 0 < lambda) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (epsilon x : ℝ),
        0 < epsilon → epsilon < epsilon0 → 0 ≤ x →
          let z0 := upperCutoff Phi epsilon
          let xi := z0 + epsilon * x
          cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x ≤
            cdfOperator p (upperBarrierLaw hprofile epsilon) x +
              C * epsilon ^ 4 * q xi := by
  let q := waveDensity diffusionMainInput W Phi
  obtain ⟨C, epsilonError, hC, hepsilonError, herror⟩ :=
    affineWaveProfile_atomAware_error_bound hprofile hlambda
  let epsilon0 := min epsilonError 1
  have hepsilon0 : 0 < epsilon0 := by
    exact lt_min hepsilonError zero_lt_one
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro p epsilon x hepsilon hepsilonSmall hx
  have hepsilonErrorSmall : epsilon < epsilonError :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonOne : epsilon < 1 :=
    hepsilonSmall.trans_le (min_le_right _ _)
  let z0 := upperCutoff Phi epsilon
  let xi := z0 + epsilon * x
  let mu := affineWaveProfileLaw hprofile epsilon z0
  letI : IsProbabilityMeasure mu :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon z0
  have hgeneric := cdfOperator_le_nonnegativePartLaw_add_atomAware p mu hx
  have hcdf (y : ℝ) : ProbabilityTheory.cdf mu y =
      affineProfileCDF Phi epsilon z0 y := by
    exact congrFun (cdf_affineWaveProfileLaw hprofile hepsilon z0) y
  have hcdfZero : ProbabilityTheory.cdf mu 0 = epsilon ^ 4 := by
    rw [hcdf]
    unfold affineProfileCDF z0
    rw [mul_zero, add_zero, upperCutoff_spec hprofile hepsilon hepsilonOne]
  rw [hcdfZero, hcdf x, hcdf (seriesCutoffLower x)] at hgeneric
  change
    cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x ≤
      cdfOperator p (upperBarrierLaw hprofile epsilon) x +
        2 * epsilon ^ 4 *
          ((if x < Real.log 2 then epsilon ^ 4 else 0) +
            (affineProfileCDF Phi epsilon z0 x -
              affineProfileCDF Phi epsilon z0 (seriesCutoffLower x))) at hgeneric
  have herrorAt := herror epsilon x hepsilon hepsilonErrorSmall hx
  change
    2 * epsilon ^ 4 *
        ((if x < Real.log 2 then epsilon ^ 4 else 0) +
          (affineProfileCDF Phi epsilon z0 x -
            affineProfileCDF Phi epsilon z0 (seriesCutoffLower x))) ≤
      C * epsilon ^ 4 * q xi at herrorAt
  have hadd := add_le_add_left herrorAt
    (cdfOperator p (upperBarrierLaw hprofile epsilon) x)
  exact hgeneric.trans (by
    simpa only [add_comm, q, xi, z0] using hadd)

/-- Truncation creates the exact source atom `epsilon ^ 4` at zero. -/
theorem upperBarrierLaw_atom_zero {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    (upperBarrierLaw hprofile epsilon).real {0} = epsilon ^ 4 := by
  let mu := affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon)
  letI : IsProbabilityMeasure mu :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon (upperCutoff Phi epsilon)
  unfold upperBarrierLaw
  change (nonnegativePartLaw mu {0}).toReal = epsilon ^ 4
  rw [nonnegativePartLaw_atom_zero]
  rw [show mu (Iic 0) = ENNReal.ofReal (epsilon ^ 4) by
    have hcdf := ProbabilityTheory.ofReal_cdf mu 0
    rw [congrFun (cdf_affineWaveProfileLaw hprofile hepsilon
      (upperCutoff Phi epsilon)) 0] at hcdf
    rw [affineProfileCDF, mul_zero, add_zero,
      upperCutoff_spec hprofile hepsilon hepsilon_one] at hcdf
    exact hcdf.symm]
  rw [ENNReal.toReal_ofReal (pow_nonneg hepsilon.le 4)]

/-- The original profile law has an integrable identity random variable. -/
theorem integrable_id_waveProfileLaw
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) :
    Integrable id (waveProfileLaw hprofile) := by
  apply Integrable.mono' (waveProfileLaw_spec hprofile).2 aestronglyMeasurable_id
  filter_upwards with x
  simp

/-- Every nondegenerate affine profile law has finite first absolute moment. -/
theorem integrable_id_affineWaveProfileLaw
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) (z0 : ℝ) :
    Integrable id (affineWaveProfileLaw hprofile epsilon z0) := by
  letI : IsProbabilityMeasure (waveProfileLaw hprofile) :=
    waveProfileLaw_isProbabilityMeasure hprofile
  let transform : ℝ → ℝ := fun z ↦ (z - z0) / epsilon
  have htransform : Integrable transform (waveProfileLaw hprofile) := by
    exact ((integrable_id_waveProfileLaw hprofile).sub (integrable_const z0)).div_const epsilon
  unfold affineWaveProfileLaw
  apply (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2
  simpa only [Function.comp_def, id_eq, transform] using htransform

/-- The atom-aware upper barrier remains integrable. -/
theorem integrable_id_upperBarrierLaw
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    Integrable id (upperBarrierLaw hprofile epsilon) := by
  let mu := affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon)
  have hid : Integrable id mu :=
    integrable_id_affineWaveProfileLaw hprofile hepsilon (upperCutoff Phi epsilon)
  unfold upperBarrierLaw nonnegativePartLaw
  apply (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2
  apply Integrable.mono' hid.norm (by fun_prop)
  filter_upwards with x
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs]
  exact abs_max_le_max_abs_abs.trans (by simp)

theorem cdf_dirac_zero (x : ℝ) :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x =
      if 0 ≤ x then 1 else 0 := by
  rw [ProbabilityTheory.cdf_eq_real]
  unfold Measure.real
  rw [Measure.dirac_apply' 0 measurableSet_Iic]
  by_cases hx : 0 ≤ x <;> simp [hx]

/-- Every nonnegative-part law is stochastically above the point mass at zero. -/
theorem cdfOrdered_nonnegativePart_dirac (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    CDFOrdered (nonnegativePartLaw mu) (Measure.dirac 0) := by
  letI : IsProbabilityMeasure (nonnegativePartLaw mu) :=
    nonnegativePartLaw_isProbabilityMeasure mu
  intro x
  rw [cdf_nonnegativePartLaw]
  rw [cdf_dirac_zero]
  by_cases hx : x < 0
  · simp [hx, not_le_of_gt hx]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [if_neg hx, if_pos hx0]
    exact ProbabilityTheory.cdf_le_one mu x

/-! ## Stochastic order under the concrete one-step law -/

/-- The mathlib CDF of `oneStepLaw` is the real-valued operator `cdfOperator`. -/
theorem cdf_oneStepLaw (p : Set.Icc (0 : ℝ) 1) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    ProbabilityTheory.cdf (oneStepLaw p mu) = cdfOperator p mu := by
  letI : IsProbabilityMeasure (oneStepLaw p mu) :=
    oneStepLaw_isProbabilityMeasure p mu
  funext x
  have hnonneg : 0 ≤ cdfOperator p mu x := by
    unfold cdfOperator
    exact add_nonneg
      (mul_nonneg p.2.1 (ProbabilityTheory.cdf_nonneg (seriesLaw mu) x))
      (mul_nonneg (sub_nonneg.mpr p.2.2)
        (ProbabilityTheory.cdf_nonneg (parallelLaw mu) x))
  have hmeasure := congrArg ENNReal.toReal ((oneStepLaw_hasCDF p mu).2 x)
  rw [ENNReal.toReal_ofReal hnonneg] at hmeasure
  rw [ProbabilityTheory.cdf_eq_real]
  exact hmeasure

/-! ## The global upper barrier -/

/-- The strict profile margin absorbs the localized cutoff error.  Negative translated
thresholds are handled by the support of the cutoff law, so the conclusion is global in `x`. -/
theorem upperBarrier_global_translation
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (hlambda : 0 < lambda) {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ (p : Set.Icc (0 : ℝ) 1) (epsilon : ℝ),
        0 < epsilon → epsilon < epsilon0 →
          (p : ℝ) = 1 / 2 + epsilon ^ 3 →
            ∀ x : ℝ,
              cutoffProfileCDF Phi epsilon (x - kappa * epsilon ^ 2) ≤
                cdfOperator p (upperBarrierLaw hprofile epsilon) x := by
  let q := waveDensity diffusionMainInput W Phi
  let gap := kappa - diffusionMainInput.kappa lambda
  have hgap : 0 < gap := sub_pos.mpr hstrict
  obtain ⟨epsilonMargin, hepsilonMargin, hmargin⟩ :=
    affineWaveProfile_strict_upper_margin_quantitative hprofile hkappa hstrict
  obtain ⟨Ccut, epsilonCut, hCcut, hepsilonCut, hcut⟩ :=
    affineWaveProfile_cdfOperator_le_upperBarrier_add_error hprofile hlambda
  have habsorbDenom : 0 < 2 * Ccut := by positivity
  let epsilon0 := min epsilonMargin
    (min epsilonCut (gap / (2 * Ccut)))
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hepsilonMargin
      (lt_min hepsilonCut (div_pos hgap habsorbDenom))
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro p epsilon hepsilon hepsilonSmall hp x
  have hepsilonMarginSmall : epsilon < epsilonMargin :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonCutSmall : epsilon < epsilonCut :=
    hepsilonSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilonAbsorb : epsilon < gap / (2 * Ccut) :=
    hepsilonSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let z0 := upperCutoff Phi epsilon
  let xi := z0 + epsilon * x
  by_cases hleft : x < kappa * epsilon ^ 2
  · have htranslated : x - kappa * epsilon ^ 2 < 0 := sub_neg.mpr hleft
    rw [cutoffProfileCDF, if_pos htranslated]
    letI : IsProbabilityMeasure (upperBarrierLaw hprofile epsilon) :=
      upperBarrierLaw_isProbabilityMeasure hprofile epsilon
    letI : IsProbabilityMeasure
        (oneStepLaw p (upperBarrierLaw hprofile epsilon)) :=
      oneStepLaw_isProbabilityMeasure p (upperBarrierLaw hprofile epsilon)
    have hnonneg := ProbabilityTheory.cdf_nonneg
      (oneStepLaw p (upperBarrierLaw hprofile epsilon)) x
    rwa [congrFun (cdf_oneStepLaw p (upperBarrierLaw hprofile epsilon)) x]
      at hnonneg
  · have htranslated : 0 ≤ x - kappa * epsilon ^ 2 :=
      sub_nonneg.mpr (le_of_not_gt hleft)
    have hx : 0 ≤ x := by
      have hshiftNonneg : 0 ≤ kappa * epsilon ^ 2 :=
        mul_nonneg hkappa (pow_nonneg hepsilon.le 2)
      linarith
    rw [cutoffProfileCDF, if_neg (not_lt.mpr htranslated)]
    have hmarginAt := hmargin p x z0 epsilon hepsilon
      hepsilonMarginSmall hp
    change
      affineProfileCDF Phi epsilon z0 (x - kappa * epsilon ^ 2) +
          gap / 2 * epsilon ^ 3 * q xi ≤
        cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x at hmarginAt
    have hcutAt := hcut p epsilon x hepsilon hepsilonCutSmall hx
    change
      cdfOperator p (affineWaveProfileLaw hprofile epsilon z0) x ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x +
          Ccut * epsilon ^ 4 * q xi at hcutAt
    have hcoefficient : Ccut * epsilon ≤ gap / 2 := by
      have hproduct : epsilon * (2 * Ccut) < gap :=
        (lt_div_iff₀ habsorbDenom).mp hepsilonAbsorb
      nlinarith
    have hqNonneg : 0 ≤ q xi := hprofile.2.2.1 xi |>.le
    have habsorb : Ccut * epsilon ^ 4 * q xi ≤
        gap / 2 * epsilon ^ 3 * q xi := by
      have hmul := mul_le_mul_of_nonneg_right hcoefficient
        (mul_nonneg (pow_nonneg hepsilon.le 3) hqNonneg)
      nlinarith
    linarith

/-- Integrating the root Bernoulli variable gives exactly the mixture in `oneStepLaw`. -/
theorem bernoulliResistanceGate_map_eq_oneStepLaw
    (p : Set.Icc (0 : ℝ) 1) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ((bernoulliBool p).prod (mu.prod mu)).map
        (fun values : Bool × (ℝ × ℝ) ↦
          if values.1 then logSeriesGate values.2.1 values.2.2
          else logParallelGate .resistance values.2.1 values.2.2) =
      oneStepLaw p mu := by
  let gate : Bool × (ℝ × ℝ) → ℝ := fun values ↦
    if values.1 then logSeriesGate values.2.1 values.2.2
    else logParallelGate .resistance values.2.1 values.2.2
  have hgate : Measurable gate := by
    have htrue : MeasurableSet {values : Bool × (ℝ × ℝ) | values.1 = true} :=
      measurable_fst (measurableSet_singleton true)
    exact Measurable.ite htrue
      (measurable_logSeriesGate_pair.comp measurable_snd)
      (measurable_logResistanceParallelGate_pair.comp measurable_snd)
  change ((bernoulliBool p).prod (mu.prod mu)).map gate = oneStepLaw p mu
  unfold bernoulliBool
  rw [ProbabilityTheory.bernoulliMeasure_def]
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
  rw [Measure.map_add _ _ hgate, Measure.map_smul, Measure.map_smul]
  rw [Measure.dirac_prod, Measure.dirac_prod]
  rw [Measure.map_map hgate (by fun_prop), Measure.map_map hgate (by fun_prop)]
  have htrue : gate ∘ Prod.mk true =
      (fun z : ℝ × ℝ ↦ logSeriesGate z.1 z.2) := by
    funext z
    simp [gate]
  have hfalse : gate ∘ Prod.mk false =
      (fun z : ℝ × ℝ ↦ logParallelGate .resistance z.1 z.2) := by
    funext z
    simp [gate]
  rw [htrue, hfalse]
  have hp : ((unitInterval.toNNReal p : NNReal) : ENNReal) =
      ENNReal.ofReal (p : ℝ) := by
    simpa using ENNReal.coe_nnreal_eq (unitInterval.toNNReal p)
  have hsymm : ((unitInterval.toNNReal (σ p) : NNReal) : ENNReal) =
      ENNReal.ofReal (1 - (p : ℝ)) := by
    simpa [unitInterval.coe_symm_eq] using
      ENNReal.coe_nnreal_eq (unitInterval.toNNReal (σ p))
  unfold oneStepLaw seriesLaw parallelLaw
  rw [ENNReal.smul_def, ENNReal.smul_def, hp, hsymm]

/-- The one-step law preserves the closed-left-ray stochastic order. -/
theorem CDFOrdered.oneStep (p : Set.Icc (0 : ℝ) 1) {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) :
    CDFOrdered (oneStepLaw p mu) (oneStepLaw p nu) := by
  letI : IsProbabilityMeasure (oneStepLaw p mu) :=
    oneStepLaw_isProbabilityMeasure p mu
  letI : IsProbabilityMeasure (oneStepLaw p nu) :=
    oneStepLaw_isProbabilityMeasure p nu
  intro x
  rw [congrFun (cdf_oneStepLaw p mu) x, congrFun (cdf_oneStepLaw p nu) x]
  exact cdfOperator_mono_of_CDFOrdered p h x

/-- A pointwise one-step barrier is precisely a stochastic-order comparison with its
right translation. -/
theorem cdfOrdered_translate_oneStep_of_barrier (p : Set.Icc (0 : ℝ) 1)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {shift : ℝ}
    (hbarrier : ∀ x, ProbabilityTheory.cdf mu (x - shift) ≤ cdfOperator p mu x) :
    CDFOrdered (translateLaw shift mu) (oneStepLaw p mu) := by
  letI : IsProbabilityMeasure (translateLaw shift mu) :=
    translateLaw_isProbabilityMeasure shift mu
  letI : IsProbabilityMeasure (oneStepLaw p mu) :=
    oneStepLaw_isProbabilityMeasure p mu
  intro x
  rw [congrFun (cdf_translateLaw shift mu) x]
  rw [congrFun (cdf_oneStepLaw p mu) x]
  unfold translateCDF
  exact hbarrier x

/-! ## Translation induction -/

/-- Iterate the concrete resistance one-step law. -/
noncomputable def iteratedOneStepLaw
    (p : Set.Icc (0 : ℝ) 1) (mu : Measure ℝ) : ℕ → Measure ℝ
  | 0 => mu
  | n + 1 => oneStepLaw p (iteratedOneStepLaw p mu n)

theorem iteratedOneStepLaw_isProbabilityMeasure (p : Set.Icc (0 : ℝ) 1)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    IsProbabilityMeasure (iteratedOneStepLaw p mu n) := by
  induction n with
  | zero => simpa [iteratedOneStepLaw] using (inferInstance : IsProbabilityMeasure mu)
  | succ n ih =>
      letI : IsProbabilityMeasure (iteratedOneStepLaw p mu n) := ih
      simpa [iteratedOneStepLaw] using
        oneStepLaw_isProbabilityMeasure p (iteratedOneStepLaw p mu n)

/-! ## The recursion law of the resistance process -/

/-- The canonical law of the generation-`n` resistance logarithm. -/
noncomputable def resistanceGenerationLaw
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) : Measure ℝ :=
  (environmentMeasure p).map (X .resistance n)

theorem resistanceGenerationLaw_isProbabilityMeasure
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    IsProbabilityMeasure (resistanceGenerationLaw p n) := by
  unfold resistanceGenerationLaw
  exact Measure.isProbabilityMeasure_map (measurable_X .resistance n).aemeasurable

@[simp]
theorem resistanceGenerationLaw_zero (p : Set.Icc (0 : ℝ) 1) :
    resistanceGenerationLaw p 0 = Measure.dirac 0 := by
  unfold resistanceGenerationLaw
  have hfun : X .resistance 0 = fun _environment ↦ (0 : ℝ) := by
    funext environment
    simp [X]
  rw [hfun, Measure.map_const]
  simp

/-- The exact one-step recursion of the resistance logarithm at the level of laws. -/
theorem resistanceGenerationLaw_succ
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    resistanceGenerationLaw p (n + 1) =
      oneStepLaw p (resistanceGenerationLaw p n) := by
  letI : IsProbabilityMeasure (resistanceGenerationLaw p n) :=
    resistanceGenerationLaw_isProbabilityMeasure p n
  change (environmentMeasure p).map (X .resistance (n + 1)) =
    oneStepLaw p (resistanceGenerationLaw p n)
  rw [(X_succ_hasLaw p .resistance n).map_eq]
  simpa only [resistanceGenerationLaw] using
    bernoulliResistanceGate_map_eq_oneStepLaw p (resistanceGenerationLaw p n)

/-- The environment-defined resistance law agrees with the canonical iterated one-step law. -/
theorem resistanceGenerationLaw_eq_iterated
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    resistanceGenerationLaw p n =
      iteratedOneStepLaw p (Measure.dirac 0) n := by
  induction n with
  | zero => simp [iteratedOneStepLaw]
  | succ n ih =>
      rw [resistanceGenerationLaw_succ, ih]
      simp only [iteratedOneStepLaw]

/-- Translating by zero leaves a law unchanged. -/
theorem translateLaw_zero (mu : Measure ℝ) : translateLaw 0 mu = mu := by
  unfold translateLaw
  simpa using Measure.map_id (m := mu)

/-- Successive translations add their displacements. -/
theorem translateLaw_add (a b : ℝ) (mu : Measure ℝ) :
    translateLaw a (translateLaw b mu) = translateLaw (a + b) mu := by
  unfold translateLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards with x
  simp only [Function.comp_apply]
  ring

/-- Translation by `n * shift` of a one-step barrier stays stochastically above the
`n`-fold recursion. -/
theorem cdfOrdered_iteratedOneStepLaw (p : Set.Icc (0 : ℝ) 1)
    (barrier initial : Measure ℝ) [IsProbabilityMeasure barrier]
    [IsProbabilityMeasure initial] {shift : ℝ}
    (hinitial : CDFOrdered barrier initial)
    (hbarrier : CDFOrdered (translateLaw shift barrier) (oneStepLaw p barrier)) :
    ∀ n : ℕ,
      CDFOrdered (translateLaw (n * shift) barrier)
        (iteratedOneStepLaw p initial n) := by
  intro n
  induction n with
  | zero =>
      simpa [iteratedOneStepLaw, translateLaw_zero] using hinitial
  | succ n ih =>
      letI : IsProbabilityMeasure (iteratedOneStepLaw p initial n) :=
        iteratedOneStepLaw_isProbabilityMeasure p initial n
      letI : IsProbabilityMeasure (translateLaw (n * shift) barrier) :=
        translateLaw_isProbabilityMeasure (n * shift) barrier
      letI : IsProbabilityMeasure (translateLaw shift barrier) :=
        translateLaw_isProbabilityMeasure shift barrier
      letI : IsProbabilityMeasure (oneStepLaw p barrier) :=
        oneStepLaw_isProbabilityMeasure p barrier
      have honeStep := ih.oneStep p
      have htranslated := hbarrier.translate (n * shift)
      have hcovariance :
          oneStepLaw p (translateLaw (n * shift) barrier) =
            translateLaw (n * shift) (oneStepLaw p barrier) :=
        oneStepLaw_translate p (n * shift) barrier
      rw [hcovariance] at honeStep
      have hcombined := htranslated.trans honeStep
      rw [translateLaw_add] at hcombined
      convert hcombined using 1
      · push_cast
        congr 2
        ring
      · simp only [iteratedOneStepLaw]

/-! ## CDF iteration and the speed consequence -/

theorem integrable_id_translateLaw {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hmu : Integrable id mu) (shift : ℝ) :
    Integrable id (translateLaw shift mu) := by
  unfold translateLaw
  apply (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2
  change Integrable (id + fun _ : ℝ ↦ shift) mu
  exact hmu.add (integrable_const shift)

theorem integral_id_translateLaw {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hmu : Integrable id mu) (shift : ℝ) :
    (∫ x, x ∂translateLaw shift mu) = (∫ x, x ∂mu) + shift := by
  unfold translateLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ x, id x + (fun _ : ℝ ↦ shift) x ∂mu) = _
  rw [integral_add hmu (integrable_const shift)]
  simp

theorem integrable_id_resistanceGenerationLaw
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable id (resistanceGenerationLaw p n) := by
  unfold resistanceGenerationLaw
  apply (integrable_map_measure aestronglyMeasurable_id
    (measurable_X .resistance n).aemeasurable).2
  change Integrable (X .resistance n) (environmentMeasure p)
  exact integrable_X p .resistance n

theorem integral_id_resistanceGenerationLaw
    (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (∫ x, x ∂resistanceGenerationLaw p n) = meanLog p .resistance n := by
  simpa only [meanLog, resistanceGenerationLaw] using
    (X_hasLaw p .resistance n).integral_eq.symm

/-- The source CDF translation induction for the truncated upper profile. -/
theorem upperBarrier_CDF_translation_induction
    (p : Set.Icc (0 : ℝ) 1) {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {shift : ℝ}
    (hglobal : ∀ x : ℝ,
      cutoffProfileCDF Phi epsilon (x - shift) ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x) :
    ∀ n : ℕ,
      CDFOrdered (translateLaw (n * shift) (upperBarrierLaw hprofile epsilon))
        (resistanceGenerationLaw p n) := by
  letI : IsProbabilityMeasure (upperBarrierLaw hprofile epsilon) :=
    upperBarrierLaw_isProbabilityMeasure hprofile epsilon
  letI : IsProbabilityMeasure
      (affineWaveProfileLaw hprofile epsilon (upperCutoff Phi epsilon)) :=
    affineWaveProfileLaw_isProbabilityMeasure hprofile epsilon (upperCutoff Phi epsilon)
  have hinitial : CDFOrdered (upperBarrierLaw hprofile epsilon) (Measure.dirac 0) := by
    unfold upperBarrierLaw
    exact cdfOrdered_nonnegativePart_dirac _
  have honeStep : CDFOrdered
      (translateLaw shift (upperBarrierLaw hprofile epsilon))
      (oneStepLaw p (upperBarrierLaw hprofile epsilon)) := by
    apply cdfOrdered_translate_oneStep_of_barrier
    intro x
    rw [congrFun (cdf_upperBarrierLaw hprofile hepsilon) (x - shift)]
    exact hglobal x
  intro n
  rw [resistanceGenerationLaw_eq_iterated]
  exact cdfOrdered_iteratedOneStepLaw p (upperBarrierLaw hprofile epsilon)
    (Measure.dirac 0) hinitial honeStep n

/-- The iterated CDF barrier gives the finite-generation expectation inequality. -/
theorem meanLog_resistance_le_upperBarrier
    (p : Set.Icc (0 : ℝ) 1) {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {shift : ℝ}
    (hglobal : ∀ x : ℝ,
      cutoffProfileCDF Phi epsilon (x - shift) ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x) (n : ℕ) :
    meanLog p .resistance n ≤ n * shift +
      ∫ x, x ∂upperBarrierLaw hprofile epsilon := by
  letI : IsProbabilityMeasure (upperBarrierLaw hprofile epsilon) :=
    upperBarrierLaw_isProbabilityMeasure hprofile epsilon
  letI : IsProbabilityMeasure (resistanceGenerationLaw p n) :=
    resistanceGenerationLaw_isProbabilityMeasure p n
  letI : IsProbabilityMeasure
      (translateLaw (n * shift) (upperBarrierLaw hprofile epsilon)) :=
    translateLaw_isProbabilityMeasure _ _
  have hbarrierIntegrable :=
    integrable_id_upperBarrierLaw hprofile hepsilon.ne'
  have htranslatedIntegrable :=
    integrable_id_translateLaw hbarrierIntegrable (n * shift)
  have hprocessIntegrable := integrable_id_resistanceGenerationLaw p n
  have horder := upperBarrier_CDF_translation_induction p hprofile hepsilon hglobal n
  have hexpectation := integral_id_mono_of_CDFOrdered horder
    htranslatedIntegrable hprocessIntegrable
  rw [integral_id_resistanceGenerationLaw,
    integral_id_translateLaw hbarrierIntegrable] at hexpectation
  linarith

/-- Normalized finite-generation form of the upper-barrier expectation inequality. -/
theorem normalizedMeanLog_resistance_le_upperBarrier
    (p : Set.Icc (0 : ℝ) 1) {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {shift : ℝ}
    (hglobal : ∀ x : ℝ,
      cutoffProfileCDF Phi epsilon (x - shift) ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x) (n : ℕ) :
    normalizedMeanLog p .resistance n ≤ shift +
      (∫ x, x ∂upperBarrierLaw hprofile epsilon) / ((n : ℝ) + 1) := by
  rw [normalizedMeanLog]
  have hmean := meanLog_resistance_le_upperBarrier p hprofile hepsilon hglobal (n + 1)
  have hdenom : 0 < (n : ℝ) + 1 := by positivity
  calc
    meanLog p .resistance (n + 1) / ((n : ℝ) + 1) ≤
        (((n : ℝ) + 1) * shift +
          ∫ x, x ∂upperBarrierLaw hprofile epsilon) /
            ((n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      simpa only [Nat.cast_add, Nat.cast_one] using hmean
    _ = shift + (∫ x, x ∂upperBarrierLaw hprofile epsilon) /
        ((n : ℝ) + 1) := by
      field_simp

/-- Any global translated upper barrier bounds the canonical supercritical mean-log speed. -/
theorem chosenResistanceSpeed_le_of_upperBarrier
    (p : Set.Icc (0 : ℝ) 1) (hp : (1 / 2 : ℝ) < (p : ℝ))
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {shift : ℝ}
    (hglobal : ∀ x : ℝ,
      cutoffProfileCDF Phi epsilon (x - shift) ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x) :
    chosenSequentialLimit (normalizedMeanLog p .resistance) ≤ shift := by
  let barrierMean := ∫ x, x ∂upperBarrierLaw hprofile epsilon
  have hlimit : Tendsto (normalizedMeanLog p .resistance) atTop
      (nhds (chosenSequentialLimit (normalizedMeanLog p .resistance))) :=
    chosenSequentialLimit_spec
      (normalizedMeanLog_converges_supercritical p .resistance hp)
  have hvanish : Tendsto (fun n : ℕ ↦ barrierMean / ((n : ℝ) + 1)) atTop
      (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul barrierMean
  have hupper : Tendsto (fun n : ℕ ↦
      shift + barrierMean / ((n : ℝ) + 1)) atTop (nhds shift) := by
    simpa using tendsto_const_nhds.add hvanish
  apply le_of_tendsto_of_tendsto' hlimit hupper
  intro n
  exact normalizedMeanLog_resistance_le_upperBarrier p hprofile hepsilon hglobal n

/-- Source-facing canonical speed version of the upper-barrier implication. -/
theorem vR_coe_le_of_upperBarrier
    (p : Set.Icc (0 : ℝ) 1) (hp : (1 / 2 : ℝ) < (p : ℝ))
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {shift : ℝ}
    (hglobal : ∀ x : ℝ,
      cutoffProfileCDF Phi epsilon (x - shift) ≤
        cdfOperator p (upperBarrierLaw hprofile epsilon) x) :
    vR (p : ℝ) ≤ shift := by
  have hpMem : (p : ℝ) ∈ Icc (0 : ℝ) 1 := p.2
  unfold vR
  rw [modelParameter_eq_of_mem hpMem]
  exact chosenResistanceSpeed_le_of_upperBarrier p hp hprofile hepsilon hglobal

/-- A positive cubic perturbation below `1 / 2` defines a valid Bernoulli parameter. -/
theorem half_add_cube_mem_unitInterval {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hcube : epsilon ^ 3 ≤ 1 / 2) :
    1 / 2 + epsilon ^ 3 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · have hcubePos : 0 < epsilon ^ 3 := pow_pos hepsilon 3
    linarith
  · linarith

/-- The global profile barrier gives the fixed-profile cubic-parameter speed bound. -/
theorem vR_half_add_cube_le_kappa_sq_of_profile
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (hlambda : 0 < lambda) {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        vR (1 / 2 + epsilon ^ 3) ≤ kappa * epsilon ^ 2 := by
  obtain ⟨epsilonBarrier, hepsilonBarrier, hbarrier⟩ :=
    upperBarrier_global_translation hprofile hlambda hkappa hstrict
  let epsilon0 := min epsilonBarrier (1 / 2)
  have hepsilon0 : 0 < epsilon0 :=
    lt_min hepsilonBarrier (by norm_num)
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilonSmall
  have hepsilonBarrierSmall : epsilon < epsilonBarrier :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonHalf : epsilon < 1 / 2 :=
    hepsilonSmall.trans_le (min_le_right _ _)
  have hcubeLt : epsilon ^ 3 < (1 / 2 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hepsilonHalf hepsilon.le (by norm_num)
  have hcube : epsilon ^ 3 ≤ 1 / 2 := by
    calc
      epsilon ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := hcubeLt.le
      _ ≤ 1 / 2 := by norm_num
  let p : Set.Icc (0 : ℝ) 1 :=
    ⟨1 / 2 + epsilon ^ 3, half_add_cube_mem_unitInterval hepsilon hcube⟩
  have hp : (p : ℝ) = 1 / 2 + epsilon ^ 3 := rfl
  have hpSuper : (1 / 2 : ℝ) < (p : ℝ) := by
    rw [hp]
    exact lt_add_of_pos_right _ (pow_pos hepsilon 3)
  have hglobal := hbarrier p epsilon hepsilon hepsilonBarrierSmall hp
  simpa only [hp] using vR_coe_le_of_upperBarrier p hpSuper hprofile
    hepsilon hglobal

/-- Fixed-profile upper speed bound on the right punctured neighborhood of zero. -/
theorem vR_half_add_cube_le_kappa_sq_eventually_of_profile
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi)
    (hlambda : 0 < lambda) {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Ioi 0),
      vR (1 / 2 + epsilon ^ 3) ≤ kappa * epsilon ^ 2 := by
  obtain ⟨epsilon0, hepsilon0, hpointwise⟩ :=
    vR_half_add_cube_le_kappa_sq_of_profile hprofile hlambda hkappa hstrict
  have heventuallySmall : ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Ioi 0),
      epsilon < epsilon0 :=
    (eventually_lt_nhds hepsilon0).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, heventuallySmall] with epsilon
    hepsilon hepsilonSmall
  exact hpointwise epsilon hepsilon hepsilonSmall

/-- Source-facing supercritical upper barrier in the cubic parameterization. -/
theorem vR_half_add_cube_le_kappa_sq_eventually
    (lambda kappa : ℝ)
    (horder : SeriesParallel.Appendix.lambdaStar < lambda)
    (hstrict : diffusionMainInput.kappa lambda < kappa) :
    ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Ioi 0),
      vR (1 / 2 + epsilon ^ 3) ≤ kappa * epsilon ^ 2 := by
  have hlambda : 0 < lambda :=
    SeriesParallel.Appendix.lambdaStar_pos.trans horder
  let W := WSolution lambda hlambda
  obtain ⟨Phi, hprofile, _hunique⟩ := diffusion_full_line_distribution horder
  have hkappaProfile : 0 < diffusionMainInput.kappa lambda := by
    rw [diffusionMainInput_kappa_eq]
    exact mul_pos
      (mul_pos (by norm_num) (Real.cbrt_pos.2 zetaThree_pos)) hlambda
  have hkappa : 0 ≤ kappa := (hkappaProfile.trans hstrict).le
  exact vR_half_add_cube_le_kappa_sq_eventually_of_profile
    hprofile hlambda hkappa hstrict

end SeriesParallel.MainText
