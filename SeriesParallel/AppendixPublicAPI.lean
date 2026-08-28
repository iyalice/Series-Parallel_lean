import SeriesParallel.Appendix.WaveProfileAssembly
import SeriesParallel.Appendix.HardEdgeAssembly
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Narrow appendix API for the main text

This module is intentionally separate from source-fidelity declarations.  The two density-law
glue theorems are added here only after the corresponding B3/B4 profile packages are closed.
-/

namespace SeriesParallel.AppendixPublicAPI

open Filter MeasureTheory Set
open scoped ENNReal Topology

open SeriesParallel.Appendix

/-- The density conclusion extracted from B3: the phase derivative is a
nonnegative integrable function of total mass one, and every probability law
having `Phi` as its CDF is its Lebesgue-density measure. -/
theorem wave_density_probability {input : MainInput} {lambda : ℝ}
    {W Phi : ℝ → ℝ} (h : IsWaveProfileConclusion input lambda W Phi) :
    let q : ℝ → ℝ := waveDensity input W Phi
    (∀ z, 0 ≤ q z) ∧ Integrable q ∧ (∫ z, q z) = 1 ∧
      ∀ mu : Measure ℝ, IsProbabilityLawOfCDF Phi mu →
        mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)) := by
  let q : ℝ → ℝ := waveDensity input W Phi
  have hderiv : ∀ z, HasDerivAt Phi (q z) z := by
    intro z
    exact h.1.2.2.2.2.1 z
  have hqpos : ∀ z, 0 < q z := h.2.2.1
  have hqnonneg : ∀ z, 0 ≤ q z := fun z ↦ (hqpos z).le
  have hright : IntegrableOn q (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg h.1.1.continuous.continuousWithinAt
      (fun z _ ↦ hderiv z) (fun z _ ↦ hqnonneg z) h.1.2.2.2.2.2.2
  let reflected : ℝ → ℝ := fun z ↦ -Phi (-z)
  let reflectedDensity : ℝ → ℝ := fun z ↦ q (-z)
  have hreflectedDeriv : ∀ z,
      HasDerivAt reflected (reflectedDensity z) z := by
    intro z
    have hcomp := (hderiv (-z)).comp z (hasDerivAt_neg z)
    have hscaled := hcomp.const_mul (-1)
    have hsame : HasDerivAt reflected (-1 * (q (-z) * -1)) z := by
      apply hscaled.congr_of_eventuallyEq
      filter_upwards with x
      simp [reflected]
    exact hsame.congr_deriv (by dsimp only [reflectedDensity]; ring)
  have hreflectedLimit : Tendsto reflected atTop (𝓝 0) := by
    simpa only [reflected, Function.comp_apply, Pi.neg_apply, neg_zero] using
      (h.1.2.2.2.2.2.1.comp tendsto_neg_atTop_atBot).neg
  have hreflectedIntegrable : IntegrableOn reflectedDensity (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg
      (hreflectedDeriv 0).continuousAt.continuousWithinAt
      (fun z _ ↦ hreflectedDeriv z) (fun z _ ↦ hqnonneg (-z)) hreflectedLimit
  have hleft : IntegrableOn q (Iio (0 : ℝ)) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero,
      reflectedDensity] using hreflectedIntegrable
  have hrightClosed : IntegrableOn q (Ici (0 : ℝ)) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright
  have hqIntegrable : Integrable q := by
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hleft, hrightClosed⟩
  have hqIntegral : (∫ z, q z) = 1 := by
    simpa using integral_of_hasDerivAt_of_tendsto hderiv hqIntegrable
      h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2
  have hnuCDF (x : ℝ) :
      (volume.withDensity (fun z ↦ ENNReal.ofReal (q z))) (Iic x) =
        ENNReal.ofReal (Phi x) := by
    rw [withDensity_apply _ measurableSet_Iic]
    have hqx : IntegrableOn q (Iic x) := hqIntegrable.integrableOn
    have hqxNonneg : 0 ≤ᵐ[volume.restrict (Iic x)] q :=
      Filter.Eventually.of_forall hqnonneg
    rw [← ofReal_integral_eq_lintegral_ofReal hqx hqxNonneg]
    rw [integral_Iic_of_hasDerivAt_of_tendsto'
      (fun z _ ↦ hderiv z) hqx h.1.2.2.2.2.2.1]
    simp
  refine ⟨hqnonneg, hqIntegrable, hqIntegral, ?_⟩
  intro mu hmu
  letI : IsProbabilityMeasure mu := hmu.1
  apply Measure.ext_of_Iic
  intro x
  rw [hmu.2 x, hnuCDF x]

/-- The hard-edge density, extended by zero to the negative half-line. -/
noncomputable def zeroExtendedHardEdgeDensity (input : MainInput)
    (W Psi : ℝ → ℝ) (z : ℝ) : ℝ :=
  if 0 < z then hardEdgeDensity input W Psi z else 0

@[simp]
theorem zeroExtendedHardEdgeDensity_zero (input : MainInput) (W Psi : ℝ → ℝ) :
    zeroExtendedHardEdgeDensity input W Psi 0 = 0 := by
  simp [zeroExtendedHardEdgeDensity]

/-- The public zero extension is exactly the physical density used to construct
`hardEdgeLaw`; in particular it is not the positive analytic extension `qbar`. -/
theorem zeroExtendedHardEdgeDensity_eq_probabilityDensity (input : MainInput)
    (W Psi : ℝ → ℝ) :
    zeroExtendedHardEdgeDensity input W Psi =
      hardEdgeProbabilityDensity input W Psi := by
  rfl

/-- Regression theorem: the hard-edge probability measure is built from `q0`, not
from the positive full-line analytic extension. -/
theorem hardEdgeLaw_eq_withDensity_zeroExtended (input : MainInput)
    (W Psi : ℝ → ℝ) :
    hardEdgeLaw input W Psi =
      volume.withDensity (fun z ↦
        ENNReal.ofReal (zeroExtendedHardEdgeDensity input W Psi z)) := by
  rfl

/-- The density conclusion extracted from B4: the hard-edge phase derivative is
nonnegative and has total mass one on `[0,∞)`, while its zero extension to the
negative half-line induces every probability law having the zero-extended phase
as its CDF. -/
theorem hardEdge_density_probability {input : MainInput} {lambda : ℝ}
    {W Psi : ℝ → ℝ} (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    let q : ℝ → ℝ := hardEdgeDensity input W Psi
    let q0 : ℝ → ℝ := zeroExtendedHardEdgeDensity input W Psi
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ q z) ∧ IntegrableOn q (Ici 0) ∧
      (∫ z in Ici (0 : ℝ), q z) = 1 ∧ Integrable q0 ∧
      ∀ mu : Measure ℝ, IsProbabilityLawOfCDF (hardEdgeCDF Psi) mu →
        mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q0 z)) := by
  let q : ℝ → ℝ := hardEdgeDensity input W Psi
  let q0 : ℝ → ℝ := zeroExtendedHardEdgeDensity input W Psi
  have hPsi : IsNormalizedHardEdgeProfile input W Psi := h.1
  have hqpos : ∀ z ∈ Ici (0 : ℝ), 0 < q z := h.2.2.2.1
  have hqnonneg : ∀ z ∈ Ici (0 : ℝ), 0 ≤ q z :=
    fun z hz ↦ (hqpos z hz).le
  have hderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt Psi (q z) z := by
    intro z hz
    simpa only [q, hardEdgePhaseRhs, hardEdgeDensity] using
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
    · simpa [q0, zeroExtendedHardEdgeDensity, hz] using hqnonneg z hz.le
    · simp [q0, zeroExtendedHardEdgeDensity, hz]
  have hleft0 : IntegrableOn q0 (Iio (0 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Iio
    intro z hz
    simp only [q0, zeroExtendedHardEdgeDensity,
      if_neg (not_lt_of_ge (mem_Iio.mp hz).le)]
  have hright0 : IntegrableOn q0 (Ici (0 : ℝ)) := by
    have hne : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      simp [ae_iff]
    apply hrightClosed.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici, ae_restrict_of_ae hne] with z hz hzne
    have hzpos : 0 < z := lt_of_le_of_ne (mem_Ici.mp hz) hzne.symm
    simp only [q0, zeroExtendedHardEdgeDensity, if_pos hzpos, q]
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
        simp only [q0, zeroExtendedHardEdgeDensity, if_neg (not_lt_of_ge hz0.le)]
      rw [hzero]
      simp [hardEdgeCDF, hx]
    · have hx0 : 0 ≤ x := not_lt.mp hx
      have hIicZero : (∫ z in Iic (0 : ℝ), q0 z) = 0 := by
        rw [integral_Iic_eq_integral_Iio]
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
        change q0 z = (0 : ℝ)
        simp only [q0, zeroExtendedHardEdgeDensity,
          if_neg (not_lt_of_ge (mem_Iio.mp hz).le)]
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
            simp only [q0, zeroExtendedHardEdgeDensity,
              if_pos (mem_Ioc.mp hz).1, q]
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
  have hnuCDF (x : ℝ) :
      (volume.withDensity (fun z ↦ ENNReal.ofReal (q0 z))) (Iic x) =
        ENNReal.ofReal (hardEdgeCDF Psi x) := by
    rw [withDensity_apply _ measurableSet_Iic]
    have hqx : IntegrableOn q0 (Iic x) := hq0Integrable.integrableOn
    have hqxNonneg : 0 ≤ᵐ[volume.restrict (Iic x)] q0 :=
      Filter.Eventually.of_forall hq0nonneg
    rw [← ofReal_integral_eq_lintegral_ofReal hqx hqxNonneg, hq0IntegralCDF x]
  refine ⟨hqnonneg, hrightClosed, hmass, hq0Integrable, ?_⟩
  intro mu hmu
  letI : IsProbabilityMeasure mu := hmu.1
  apply Measure.ext_of_Iic
  intro x
  rw [hmu.2 x, hnuCDF x]

end SeriesParallel.AppendixPublicAPI
