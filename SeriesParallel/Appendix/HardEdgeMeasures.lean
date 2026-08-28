import SeriesParallel.Appendix.HardEdgeConsequences
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The hard-edge CDF, probability law, and finite mean
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

theorem hardEdgeCDF_continuous {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    Continuous (hardEdgeCDF Psi) := by
  unfold hardEdgeCDF
  apply continuous_if
  · intro a ha
    have ha0 : a = 0 := by
      change a ∈ frontier (Iio (0 : ℝ)) at ha
      simpa only [frontier_Iio, mem_singleton_iff] using ha
    subst a
    simpa using hPsi.2.2.2.1.symm
  · exact (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℝ)).continuousOn
  · simp only [not_lt]
    have hclosure : closure {x : ℝ | 0 ≤ x} = Ici (0 : ℝ) := by
      change closure (Ici (0 : ℝ)) = Ici (0 : ℝ)
      exact isClosed_Ici.closure_eq
    rw [hclosure]
    exact hPsi.1.continuousOn

theorem hardEdgeCDF_monotone {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    Monotone (hardEdgeCDF Psi) := by
  intro x y hxy
  by_cases hy : y < 0
  · have hx : x < 0 := hxy.trans_lt hy
    simp [hardEdgeCDF, hx, hy]
  · have hy0 : 0 ≤ y := le_of_not_gt hy
    by_cases hx : x < 0
    · have hnonneg : 0 ≤ Psi y := (hPsi.2.2.1 hy0).1
      simpa [hardEdgeCDF, hx, hy] using hnonneg
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hmono := hPsi.2.1.monotoneOn hx0 hy0 hxy
      simpa [hardEdgeCDF, hx, hy] using hmono

/-- The zero-extended hard-edge CDF is strictly increasing on its natural half-line. -/
theorem hardEdgeCDF_strictMonoOn {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    StrictMonoOn (hardEdgeCDF Psi) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hstrict := hPsi.2.1 hx hy hxy
  have hxnot : ¬x < 0 := not_lt.mpr (mem_Ici.mp hx)
  have hynot : ¬y < 0 := not_lt.mpr (mem_Ici.mp hy)
  simpa only [hardEdgeCDF, if_neg hxnot, if_neg hynot] using hstrict

/-- The zero extension has left derivative zero and positive right derivative at the
hard edge, so it is not ordinarily differentiable there. -/
theorem hardEdgeCDF_not_differentiableAt_zero {input : MainInput}
    {W Psi : ℝ → ℝ} (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hqzero : 0 < hardEdgeDensity input W Psi 0) :
    ¬DifferentiableAt ℝ (hardEdgeCDF Psi) 0 := by
  intro hdifferentiable
  have hleft : HasDerivWithinAt (hardEdgeCDF Psi) 0 (Iic 0) 0 := by
    apply (hasDerivWithinAt_const (x := (0 : ℝ)) (s := Iic 0) (c := (0 : ℝ))).congr
    · intro x hx
      by_cases hxneg : x < 0
      · simp [hardEdgeCDF, hxneg]
      · have hxzero : x = 0 := le_antisymm hx (not_lt.mp hxneg)
        subst x
        simp [hardEdgeCDF, hPsi.2.2.2.1]
    · simp [hardEdgeCDF, hPsi.2.2.2.1]
  have hrightPsi : HasDerivWithinAt Psi (hardEdgeDensity input W Psi 0) (Ici 0) 0 := by
    simpa only [hardEdgePhaseRhs, hardEdgeDensity] using hPsi.2.2.2.2.1
  have hright : HasDerivWithinAt (hardEdgeCDF Psi)
      (hardEdgeDensity input W Psi 0) (Ici 0) 0 := by
    apply hrightPsi.congr
    · intro x hx
      simp only [hardEdgeCDF, if_neg (not_lt.mpr (mem_Ici.mp hx))]
    · simp [hardEdgeCDF, hPsi.2.2.2.1]
  have hglobal := hdifferentiable.hasDerivAt
  have hleftValue : derivWithin (hardEdgeCDF Psi) (Iic 0) 0 = 0 :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have hglobalLeft : derivWithin (hardEdgeCDF Psi) (Iic 0) 0 =
      deriv (hardEdgeCDF Psi) 0 :=
    hglobal.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have hderivZero : deriv (hardEdgeCDF Psi) 0 = 0 := hglobalLeft.symm.trans hleftValue
  have hrightValue : derivWithin (hardEdgeCDF Psi) (Ici 0) 0 =
      hardEdgeDensity input W Psi 0 :=
    hright.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  have hglobalRight : derivWithin (hardEdgeCDF Psi) (Ici 0) 0 =
      deriv (hardEdgeCDF Psi) 0 :=
    hglobal.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  have hqzeroEq : hardEdgeDensity input W Psi 0 = 0 := by
    calc
      hardEdgeDensity input W Psi 0 = derivWithin (hardEdgeCDF Psi) (Ici 0) 0 :=
        hrightValue.symm
      _ = deriv (hardEdgeCDF Psi) 0 := hglobalRight
      _ = 0 := hderivZero
  exact hqzero.ne' hqzeroEq

theorem hardEdgeCDF_range {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) (x : ℝ) :
    hardEdgeCDF Psi x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x < 0
  · simp [hardEdgeCDF, hx]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    exact ⟨by simpa [hardEdgeCDF, hx] using (hPsi.2.2.1 hx0).1,
      by simpa [hardEdgeCDF, hx] using (hPsi.2.2.1 hx0).2.le⟩

theorem hardEdgeCDF_tendsto_atBot {input : MainInput} {W Psi : ℝ → ℝ}
    (_hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    Tendsto (hardEdgeCDF Psi) atBot (𝓝 0) := by
  apply (tendsto_congr' ?_).2 (tendsto_const_nhds :
    Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atBot (𝓝 0))
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp [hardEdgeCDF, hx]

theorem hardEdgeCDF_tendsto_atTop {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    Tendsto (hardEdgeCDF Psi) atTop (𝓝 1) := by
  apply (tendsto_congr' ?_).2 hPsi.2.2.2.2.2.2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp [hardEdgeCDF, not_lt.mpr hx]

/-- A probability law with the normalized hard-edge CDF has no atom at the hard edge. -/
theorem hardEdge_probabilityLaw_singleton_zero {input : MainInput}
    {W Psi : ℝ → ℝ} {mu : Measure ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hmu : IsProbabilityLawOfCDF (hardEdgeCDF Psi) mu) :
    mu ({0} : Set ℝ) = 0 := by
  have hIicZero : mu (Iic (0 : ℝ)) = 0 := by
    rw [hmu.2 0]
    simp [hardEdgeCDF, hPsi.2.2.2.1]
  apply measure_mono_null (s := ({0} : Set ℝ)) (t := Iic (0 : ℝ)) _ hIicZero
  intro x hx
  exact mem_Iic.mpr (mem_singleton_iff.mp hx).le

theorem one_sub_hardEdgeProfile_integrableOn_Ici_of_exponentialTail
    {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (htail : HasRightExponentialTail Psi) :
    IntegrableOn (fun z : ℝ ↦ 1 - hardEdgeCDF Psi z) (Ici (0 : ℝ)) := by
  rcases htail with ⟨c, C, hc, hC, hbound⟩
  have hexpIoi : IntegrableOn (fun z : ℝ ↦ Real.exp ((-c) * z))
      (Ioi (0 : ℝ)) := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have hexp : IntegrableOn (fun z : ℝ ↦ Real.exp (-c * z))
      (Ici (0 : ℝ)) := by
    have h := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hexpIoi
    simpa only [neg_mul] using h
  have hmajor : IntegrableOn (fun z : ℝ ↦ C * Real.exp (-c * z))
      (Ici (0 : ℝ)) := hexp.const_mul C
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ 1 - hardEdgeCDF Psi z)
      (volume.restrict (Ici (0 : ℝ))) :=
    (continuous_const.sub (hardEdgeCDF_continuous hPsi)).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  have hnotlt : ¬z < 0 := not_lt.mpr hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    simp only [hardEdgeCDF, if_neg hnotlt]
    exact sub_nonneg.mpr (hPsi.2.2.1 hz).2.le)]
  simpa only [hardEdgeCDF, if_neg hnotlt] using hbound z hz

/-- The physical hard-edge probability density: it excludes the hard-edge point itself,
whereas the analytic half-line density has a positive right-hand value. -/
noncomputable def hardEdgeProbabilityDensity (input : MainInput)
    (W Psi : ℝ → ℝ) (z : ℝ) : ℝ :=
  if 0 < z then hardEdgeDensity input W Psi z else 0

/-- The hard-edge law is constructed directly from the zero-extended physical density. -/
noncomputable def hardEdgeLaw (input : MainInput) (W Psi : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal (hardEdgeProbabilityDensity input W Psi z))

/-- The explicitly density-defined hard-edge law has the exact `Iic` CDF, no mass below
zero or at zero, and a finite first moment. -/
theorem hardEdgeLaw_probability_with_finiteMean {input : MainInput}
    {W Psi : ℝ → ℝ} (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (htail : HasRightExponentialTail Psi) :
    IsProbabilityLawOfCDF (hardEdgeCDF Psi) (hardEdgeLaw input W Psi) ∧
      hardEdgeLaw input W Psi (Iio (0 : ℝ)) = 0 ∧
      Integrable id (hardEdgeLaw input W Psi) := by
  let q : ℝ → ℝ := hardEdgeDensity input W Psi
  let q0 : ℝ → ℝ := fun z ↦ if 0 < z then q z else 0
  have hqnonneg : ∀ z ∈ Ici (0 : ℝ), 0 ≤ q z := by
    intro z hz
    change 0 ≤ hardEdgeDensity input W Psi z
    rw [← hPsi.derivWithin_eq_hardEdgeDensity hz]
    exact hPsi.2.1.monotoneOn.derivWithin_nonneg
  have hderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt Psi (q z) z := by
    intro z hz
    simpa only [q, hardEdgeDensity, hardEdgePhaseRhs] using
      hPsi.2.2.2.2.2.1 z hz
  have hcont0 : ContinuousWithinAt Psi (Ici (0 : ℝ)) 0 :=
    hPsi.1.continuousOn 0 (by simp)
  have hqnonnegIoi : ∀ z ∈ Ioi (0 : ℝ), 0 ≤ q z := by
    intro z hz
    exact hqnonneg z (mem_Ici.mpr (mem_Ioi.mp hz).le)
  have hright : IntegrableOn q (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg hcont0 hderiv hqnonnegIoi
      hPsi.2.2.2.2.2.2
  have hrightClosed : IntegrableOn q (Ici (0 : ℝ)) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright
  have hmass : (∫ z in Ici (0 : ℝ), q z) = 1 := by
    rw [integral_Ici_eq_integral_Ioi]
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont0 hderiv hqnonnegIoi
      hPsi.2.2.2.2.2.2]
    rw [hPsi.2.2.2.1]
    norm_num
  have hq0nonneg : ∀ z, 0 ≤ q0 z := by
    intro z
    by_cases hz : 0 < z
    · simpa only [q0, if_pos hz] using hqnonneg z hz.le
    · simp only [q0, if_neg hz, le_refl]
  have hleft0 : IntegrableOn q0 (Iio (0 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Iio
    intro z hz
    simp only [q0, if_neg (not_lt_of_ge (mem_Iio.mp hz).le)]
  have hright0 : IntegrableOn q0 (Ici (0 : ℝ)) := by
    have hne : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      simp [ae_iff]
    apply hrightClosed.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici, ae_restrict_of_ae hne] with z hz hzne
    have hzpos : 0 < z := lt_of_le_of_ne (mem_Ici.mp hz) hzne.symm
    simp only [q0, if_pos hzpos]
  have hq0Integrable : Integrable q0 := by
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hleft0, hright0⟩
  have hq0IntegralCDF (x : ℝ) :
      (∫ z in Iic x, q0 z) = hardEdgeCDF Psi x := by
    by_cases hx : x < 0
    · have hzero : (∫ z in Iic x, q0 z) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
        have hz0 : z < 0 := (mem_Iic.mp hz).trans_lt hx
        change q0 z = (0 : ℝ)
        simp only [q0, if_neg (not_lt_of_ge hz0.le)]
      rw [hzero]
      simp [hardEdgeCDF, hx]
    · have hx0 : 0 ≤ x := not_lt.mp hx
      have hIicZero : (∫ z in Iic (0 : ℝ), q0 z) = 0 := by
        rw [integral_Iic_eq_integral_Iio]
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
        change q0 z = (0 : ℝ)
        simp only [q0, if_neg (not_lt_of_ge (mem_Iio.mp hz).le)]
      have hsplit : (∫ z in Iic x, q0 z) =
          (∫ z in Iic (0 : ℝ), q0 z) + ∫ z in Ioc (0 : ℝ) x, q0 z := by
        rw [← setIntegral_union]
        · rw [Iic_union_Ioc_eq_Iic hx0]
        · exact Set.disjoint_left.2 fun _ hz0 hzpos ↦ (not_lt_of_ge hz0) hzpos.1
        · exact measurableSet_Ioc
        · exact hq0Integrable.integrableOn
        · exact hq0Integrable.integrableOn
      have hIoc : (∫ z in Ioc (0 : ℝ) x, q0 z) = Psi x - Psi 0 := by
        calc
          (∫ z in Ioc (0 : ℝ) x, q0 z) = ∫ z in Ioc (0 : ℝ) x, q z := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
            simp only [q0, if_pos (mem_Ioc.mp hz).1]
          _ = ∫ z in (0 : ℝ)..x, q z := by
            rw [intervalIntegral.integral_of_le hx0]
          _ = Psi x - Psi 0 := by
            apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0
            · exact hPsi.1.continuousOn.mono fun z hz ↦ hz.1
            · intro z hz
              exact hderiv z hz.1
            · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0).2
                (hrightClosed.mono_set fun _ hz ↦
                  mem_Ici.mpr (mem_Ioc.mp hz).1.le)
      rw [hsplit, hIicZero, hIoc, hPsi.2.2.2.1]
      simp [hardEdgeCDF, hx]
  let cdf : ℝ → ℝ := hardEdgeCDF Psi
  have hrange : ∀ x, cdf x ∈ Icc (0 : ℝ) 1 := hardEdgeCDF_range hPsi
  let mu : Measure ℝ := hardEdgeLaw input W Psi
  have hmuCDF (x : ℝ) : mu (Iic x) = ENNReal.ofReal (cdf x) := by
    rw [show mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q0 z)) from rfl,
      withDensity_apply _ measurableSet_Iic]
    have hqx : IntegrableOn q0 (Iic x) := hq0Integrable.integrableOn
    have hqxNonneg : 0 ≤ᵐ[volume.restrict (Iic x)] q0 :=
      Filter.Eventually.of_forall hq0nonneg
    rw [← ofReal_integral_eq_lintegral_ofReal hqx hqxNonneg, hq0IntegralCDF x]
  have hmuProbability : IsProbabilityMeasure mu := by
    refine ⟨?_⟩
    rw [show mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q0 z)) from rfl,
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hq0Integrable
      (Filter.Eventually.of_forall hq0nonneg)]
    have hq0mass : (∫ z, q0 z) = 1 := by
      calc
        (∫ z, q0 z) = ∫ z, (Ici (0 : ℝ)).indicator q0 z := by
          apply integral_congr_ae
          filter_upwards with z
          by_cases hz : 0 ≤ z
          · simp only [Set.indicator_of_mem (mem_Ici.mpr hz)]
          · have hzlt : z < 0 := lt_of_not_ge hz
            simp [Set.indicator, hz, q0, not_lt_of_ge hzlt.le]
        _ = ∫ z in Ici (0 : ℝ), q0 z := by
          rw [integral_indicator measurableSet_Ici]
        _ = ∫ z in Ici (0 : ℝ), q z := by
          apply integral_congr_ae
          have hne : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by simp [ae_iff]
          filter_upwards [ae_restrict_mem measurableSet_Ici, ae_restrict_of_ae hne]
            with z hz hzne
          have hzpos : 0 < z := lt_of_le_of_ne (mem_Ici.mp hz) hzne.symm
          simp only [q0, if_pos hzpos]
        _ = 1 := hmass
    rw [hq0mass]
    norm_num
  have hIicZero : mu (Iic (0 : ℝ)) = 0 := by
    rw [hmuCDF 0]
    simp [cdf, hardEdgeCDF, hPsi.2.2.2.1]
  have hsupport : mu (Iio (0 : ℝ)) = 0 :=
    measure_mono_null Iio_subset_Iic_self hIicZero
  have htailInt := one_sub_hardEdgeProfile_integrableOn_Ici_of_exponentialTail hPsi htail
  have htailFinite :
      (∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (1 - cdf x)) < (∞ : ℝ≥0∞) := by
    have hfinite : HasFiniteIntegral (fun x : ℝ ↦ 1 - cdf x)
        (volume.restrict (Ici (0 : ℝ))) := htailInt.hasFiniteIntegral
    apply (hasFiniteIntegral_iff_ofReal ?_).mp hfinite
    exact Filter.Eventually.of_forall fun x ↦ sub_nonneg.mpr (hrange x).2
  letI : IsProbabilityMeasure mu := hmuProbability
  have htailMeasure (t : ℝ) : mu (Ioi t) = ENNReal.ofReal (1 - cdf t) := by
    rw [← compl_Iic, measure_compl measurableSet_Iic, hmuCDF]
    · rw [measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (hrange t).1]
    · exact measure_ne_top mu (Iic t)
  have hidNonneg : ∀ᵐ x ∂mu, 0 ≤ id x := by
    have hmem : Ici (0 : ℝ) ∈ ae mu := by
      rw [mem_ae_iff]
      simpa only [compl_Ici] using hsupport
    filter_upwards [hmem] with x hx
    exact hx
  have hidLintegral :
      (∫⁻ x, ENNReal.ofReal (id x) ∂mu) =
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (1 - cdf x) := by
    rw [lintegral_eq_lintegral_meas_lt mu hidNonneg measurable_id.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    change mu {x : ℝ | t < id x} = ENNReal.ofReal (1 - cdf t)
    rw [show {x : ℝ | t < id x} = Ioi t by ext x; simp]
    exact htailMeasure t
  have htailIoiFinite :
      (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (1 - cdf x)) < (∞ : ℝ≥0∞) :=
    (lintegral_mono_set Ioi_subset_Ici_self).trans_lt htailFinite
  have hidFinite : HasFiniteIntegral id mu := by
    apply (hasFiniteIntegral_iff_ofReal hidNonneg).2
    rw [hidLintegral]
    exact htailIoiFinite
  have hidMeas : AEStronglyMeasurable id mu := by fun_prop
  exact ⟨⟨hmuProbability, hmuCDF⟩, hsupport, ⟨hidMeas, hidFinite⟩⟩

/-- Existential packaging used by the B4 assembly, with witness fixed to `hardEdgeLaw`. -/
theorem exists_hardEdge_probabilityLaw_with_finiteMean {input : MainInput}
    {W Psi : ℝ → ℝ} (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (htail : HasRightExponentialTail Psi) :
    ∃ mu : Measure ℝ, IsProbabilityLawOfCDF (hardEdgeCDF Psi) mu ∧
      mu (Iio (0 : ℝ)) = 0 ∧ Integrable id mu := by
  exact ⟨hardEdgeLaw input W Psi,
    hardEdgeLaw_probability_with_finiteMean hPsi htail⟩

/-- The physical hard-edge law assigns zero mass to the hard-edge singleton. -/
@[simp]
theorem hardEdgeLaw_singleton_zero {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (htail : HasRightExponentialTail Psi) :
    hardEdgeLaw input W Psi ({0} : Set ℝ) = 0 := by
  exact hardEdge_probabilityLaw_singleton_zero hPsi
    (hardEdgeLaw_probability_with_finiteMean hPsi htail).1

end SeriesParallel.Appendix
