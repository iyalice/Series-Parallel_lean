import SeriesParallel.Appendix.WaveProfile
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Probability measures and moments for appendix profiles

The measure construction is kept separate from the ODE calculations.  The probability
laws are explicit density measures, and their moment bounds are proved by layer cake.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-- The left exponential estimate makes the CDF integrable on the negative half-line. -/
theorem waveProfile_integrableOn_Iio_of_exponentialTails {input : MainInput}
    {W Phi : ℝ → ℝ} (hPhi : IsNormalizedWaveProfile input W Phi)
    (htails : HasTwoSidedExponentialTails Phi) :
    IntegrableOn Phi (Iio (0 : ℝ)) := by
  rcases htails with ⟨c, C, hc, hC, hleft, _⟩
  have hexp : IntegrableOn (fun z : ℝ ↦ Real.exp (c * z)) (Iio (0 : ℝ)) := by
    exact ((integrableOn_Iic_iff_integrableOn_Iio).mp
      (integrableOn_exp_mul_Iic hc 0))
  have hmajor : IntegrableOn (fun z : ℝ ↦ C * Real.exp (c * z)) (Iio (0 : ℝ)) :=
    hexp.const_mul C
  have hmeas : AEStronglyMeasurable Phi (volume.restrict (Iio (0 : ℝ))) :=
    hPhi.1.continuous.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (hPhi.2.2.1 z).1.le]
  exact hleft z hz.le

/-- The right exponential estimate makes the survival function integrable on the
nonnegative half-line. -/
theorem one_sub_waveProfile_integrableOn_Ici_of_exponentialTails {input : MainInput}
    {W Phi : ℝ → ℝ} (hPhi : IsNormalizedWaveProfile input W Phi)
    (htails : HasTwoSidedExponentialTails Phi) :
    IntegrableOn (fun z : ℝ ↦ 1 - Phi z) (Ici (0 : ℝ)) := by
  rcases htails with ⟨c, C, hc, hC, _, hright⟩
  have hexpIoi : IntegrableOn (fun z : ℝ ↦ Real.exp ((-c) * z))
      (Ioi (0 : ℝ)) := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have hexp : IntegrableOn (fun z : ℝ ↦ Real.exp (-c * z))
      (Ici (0 : ℝ)) := by
    have h := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hexpIoi
    simpa only [neg_mul] using h
  have hmajor : IntegrableOn (fun z : ℝ ↦ C * Real.exp (-c * z))
      (Ici (0 : ℝ)) := hexp.const_mul C
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ 1 - Phi z)
      (volume.restrict (Ici (0 : ℝ))) := by
    exact (continuous_const.sub hPhi.1.continuous).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hPhi.2.2.1 z).2.le)]
  exact hright z hz

/-- The two CDF tails control the absolute first moment.  This is the
layer-cake/Tonelli argument specialized to an atomless probability law. -/
private theorem lintegral_abs_lt_top_of_cdf_tails (cdf : ℝ → ℝ) (mu : Measure ℝ)
    (hprob : IsProbabilityMeasure mu)
    (hrange : ∀ x, cdf x ∈ Icc (0 : ℝ) 1)
    (hcdf : ∀ x, mu (Iic x) = ENNReal.ofReal (cdf x))
    (hzero : ∀ x : ℝ, mu ({x} : Set ℝ) = 0)
    (hleftInt : IntegrableOn cdf (Iio (0 : ℝ)))
    (hrightFinite :
      (∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (1 - cdf x)) < (∞ : ℝ≥0∞)) :
    (∫⁻ x, ENNReal.ofReal |x| ∂mu) < (∞ : ℝ≥0∞) := by
  letI : IsProbabilityMeasure mu := hprob
  have htailMeasure (t : ℝ) : mu (Ioi t) = ENNReal.ofReal (1 - cdf t) := by
    rw [← compl_Iic, measure_compl measurableSet_Iic, hcdf]
    · rw [measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (hrange t).1]
    · exact measure_ne_top mu (Iic t)
  have hleftMeasure (t : ℝ) : mu (Iio t) = ENNReal.ofReal (cdf t) := by
    calc
      mu (Iio t) = mu (Iic t) := by
        have hset : Iic t = Iio t ∪ {t} := by
          ext x
          simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
          constructor
          · intro h
            exact (lt_or_eq_of_le h).elim Or.inl Or.inr
          · rintro (h | rfl)
            · exact h.le
            · exact le_rfl
        rw [hset, measure_union]
        · rw [hzero, add_zero]
        · exact Set.disjoint_left.2 fun x hx hxeq ↦ by
            subst x
            exact lt_irrefl t hx
        · exact measurableSet_singleton t
      _ = ENNReal.ofReal (cdf t) := hcdf t
  let pos : ℝ → ℝ := fun x ↦ max x 0
  let neg : ℝ → ℝ := fun x ↦ max (-x) 0
  have hposNN : 0 ≤ᵐ[mu] pos :=
    Filter.Eventually.of_forall fun x ↦ le_max_right x 0
  have hnegNN : 0 ≤ᵐ[mu] neg :=
    Filter.Eventually.of_forall fun x ↦ le_max_right (-x) 0
  have hposMeas : AEMeasurable pos mu := by
    exact (by fun_prop : Measurable pos).aemeasurable
  have hnegMeas : AEMeasurable neg mu := by
    exact (by fun_prop : Measurable neg).aemeasurable
  have hposLayer := lintegral_eq_lintegral_meas_lt mu hposNN hposMeas
  have hposEq : (∫⁻ x, ENNReal.ofReal (pos x) ∂mu) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 - cdf t) := by
    rw [hposLayer]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    change mu {a : ℝ | t < pos a} = ENNReal.ofReal (1 - cdf t)
    rw [show {a : ℝ | t < pos a} = Ioi t by
      ext a
      simp only [mem_setOf_eq, mem_Ioi, pos]
      by_cases ha : 0 ≤ a
      · simp [max_eq_left ha]
      · have ha' : a ≤ 0 := le_of_not_ge ha
        rw [max_eq_right ha']
        constructor <;> intro h <;> linarith]
    exact htailMeasure t
  have hrightIoiFinite :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 - cdf t)) < (∞ : ℝ≥0∞) :=
    (lintegral_mono_set Ioi_subset_Ici_self).trans_lt hrightFinite
  have hposFinite : (∫⁻ x, ENNReal.ofReal (pos x) ∂mu) < (∞ : ℝ≥0∞) := by
    rw [hposEq]
    exact hrightIoiFinite
  have hnegLayer := lintegral_eq_lintegral_meas_lt mu hnegNN hnegMeas
  have hnegEq : (∫⁻ x, ENNReal.ofReal (neg x) ∂mu) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cdf (-t)) := by
    rw [hnegLayer]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    change mu {a : ℝ | t < neg a} = ENNReal.ofReal (cdf (-t))
    rw [show {a : ℝ | t < neg a} = Iio (-t) by
      ext a
      simp only [mem_setOf_eq, mem_Iio, neg]
      by_cases ha : 0 ≤ -a
      · rw [max_eq_left ha]
        constructor <;> intro h <;> linarith
      · have ha' : -a ≤ 0 := le_of_not_ge ha
        rw [max_eq_right ha']
        constructor <;> intro h <;> linarith]
    exact hleftMeasure (-t)
  have hreflectedInt : IntegrableOn (fun t : ℝ ↦ cdf (-t)) (Ioi (0 : ℝ)) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Ioi, neg_zero, neg_neg] using hleftInt
  have hreflectedFinite :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cdf (-t))) < (∞ : ℝ≥0∞) := by
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun t ↦ (hrange (-t)).1)).mp
        hreflectedInt.hasFiniteIntegral
  have hnegFinite : (∫⁻ x, ENNReal.ofReal (neg x) ∂mu) < (∞ : ℝ≥0∞) := by
    rw [hnegEq]
    exact hreflectedFinite
  calc
    (∫⁻ x, ENNReal.ofReal |x| ∂mu) =
        ∫⁻ x, ENNReal.ofReal (pos x) + ENNReal.ofReal (neg x) ∂mu := by
      apply lintegral_congr
      intro x
      calc
        ENNReal.ofReal |x| = ENNReal.ofReal (pos x + neg x) := by
          congr 1
          simp only [pos, neg, max_zero_add_max_neg_zero_eq_abs_self]
        _ = ENNReal.ofReal (pos x) + ENNReal.ofReal (neg x) :=
          ENNReal.ofReal_add (le_max_right x 0) (le_max_right (-x) 0)
    _ = (∫⁻ x, ENNReal.ofReal (pos x) ∂mu) +
        ∫⁻ x, ENNReal.ofReal (neg x) ∂mu := by
      rw [lintegral_add_left]
      exact (by fun_prop : Measurable fun x ↦ ENNReal.ofReal (pos x))
    _ < (∞ : ℝ≥0∞) := ENNReal.add_lt_top.2 ⟨hposFinite, hnegFinite⟩

/-- The full-line probability law is the Lebesgue measure with the analytic density
`q = Phi'`; no abstract Stieltjes-measure admission is used. -/
noncomputable def waveProfileLaw (input : MainInput) (W Phi : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal (waveDensity input W Phi z))

/-- The explicitly density-defined full-line law has the exact `Iic` CDF convention
and a finite absolute first moment. -/
theorem waveProfileLaw_probability_with_finiteAbsoluteFirstMoment
    {input : MainInput} {W Phi : ℝ → ℝ}
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (htails : HasTwoSidedExponentialTails Phi) :
    IsProbabilityLawOfCDF Phi (waveProfileLaw input W Phi) ∧
      Integrable (fun x : ℝ ↦ |x|) (waveProfileLaw input W Phi) := by
  let q : ℝ → ℝ := waveDensity input W Phi
  have hderiv : ∀ z, HasDerivAt Phi (q z) z := by
    intro z
    simpa only [q, waveDensity, wavePhaseRhs] using hPhi.2.2.2.2.1 z
  have hqnonneg : ∀ z, 0 ≤ q z := by
    intro z
    rw [← (hderiv z).deriv]
    exact hPhi.2.1.monotone.deriv_nonneg
  have hright : IntegrableOn q (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg hPhi.1.continuous.continuousWithinAt
      (fun z _ ↦ hderiv z) (fun z _ ↦ hqnonneg z) hPhi.2.2.2.2.2.2
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
      (hPhi.2.2.2.2.2.1.comp tendsto_neg_atTop_atBot).neg
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
      hPhi.2.2.2.2.2.1 hPhi.2.2.2.2.2.2
  let mu : Measure ℝ := waveProfileLaw input W Phi
  have hmuCDF (x : ℝ) : mu (Iic x) = ENNReal.ofReal (Phi x) := by
    rw [show mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)) from rfl,
      withDensity_apply _ measurableSet_Iic]
    have hqx : IntegrableOn q (Iic x) := hqIntegrable.integrableOn
    have hqxNonneg : 0 ≤ᵐ[volume.restrict (Iic x)] q :=
      Filter.Eventually.of_forall hqnonneg
    rw [← ofReal_integral_eq_lintegral_ofReal hqx hqxNonneg]
    rw [integral_Iic_of_hasDerivAt_of_tendsto'
      (fun z _ ↦ hderiv z) hqx hPhi.2.2.2.2.2.1]
    simp
  have hmuProbability : IsProbabilityMeasure mu := by
    refine ⟨?_⟩
    rw [show mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)) from rfl,
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hqIntegrable
      (Filter.Eventually.of_forall hqnonneg), hqIntegral]
    norm_num
  have hrange : ∀ x, Phi x ∈ Icc (0 : ℝ) 1 := fun x ↦
    ⟨(hPhi.2.2.1 x).1.le, (hPhi.2.2.1 x).2.le⟩
  have hleftInt := waveProfile_integrableOn_Iio_of_exponentialTails hPhi htails
  have hrightInt := one_sub_waveProfile_integrableOn_Ici_of_exponentialTails hPhi htails
  have hrightFinite :
      (∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (1 - Phi x)) < (∞ : ℝ≥0∞) := by
    have hfinite : HasFiniteIntegral (fun x : ℝ ↦ 1 - Phi x)
        (volume.restrict (Ici (0 : ℝ))) := hrightInt.hasFiniteIntegral
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x ↦ sub_nonneg.mpr (hPhi.2.2.1 x).2.le)).mp hfinite
  have hmuSingleton (x : ℝ) : mu ({x} : Set ℝ) = 0 := by
    rw [show mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)) from rfl]
    exact withDensity_absolutelyContinuous volume
      (fun z ↦ ENNReal.ofReal (q z)) (measure_singleton x)
  have habsFinite :
      (∫⁻ x, ENNReal.ofReal |x| ∂mu) ≠ (∞ : ℝ≥0∞) :=
    (lintegral_abs_lt_top_of_cdf_tails Phi mu hmuProbability hrange hmuCDF
      hmuSingleton hleftInt hrightFinite).ne
  have hmomentMeas : AEStronglyMeasurable (fun x : ℝ ↦ |x|) mu := by
    fun_prop
  have hmomentFinite : HasFiniteIntegral (fun x : ℝ ↦ |x|) mu := by
    apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x : ℝ ↦ abs_nonneg x)).2
    exact lt_top_iff_ne_top.mpr habsFinite
  exact ⟨⟨hmuProbability, hmuCDF⟩, ⟨hmomentMeas, hmomentFinite⟩⟩

/-- Existential packaging used by the B3 assembly, with the witness fixed to
`waveProfileLaw`. -/
theorem exists_waveProfile_probabilityLaw_with_finiteAbsoluteFirstMoment
    {input : MainInput} {W Phi : ℝ → ℝ}
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (htails : HasTwoSidedExponentialTails Phi) :
    ∃ mu : Measure ℝ, IsProbabilityLawOfCDF Phi mu ∧
      Integrable (fun x : ℝ ↦ |x|) mu := by
  exact ⟨waveProfileLaw input W Phi,
    waveProfileLaw_probability_with_finiteAbsoluteFirstMoment hPhi htails⟩

end SeriesParallel.Appendix
