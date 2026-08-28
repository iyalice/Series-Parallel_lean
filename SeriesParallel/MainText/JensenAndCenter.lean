/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.FirstMomentSubmultiplicative
import SeriesParallel.MainText.JensenBasic
import SeriesParallel.MainText.LogarithmicDrift
import SeriesParallel.MainText.NormalizedSecondMoment
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Jensen gaps and centered logarithmic fluctuations

The logarithmic drift controls the expected width of two independent descendants in the
supercritical regime. Symmetrization transfers this bound to the distance from the mean, and
division by the generation gives the `L¹` part of center tracking. The bounded Jensen gap and
almost-sure interpolation are added below after their quantitative inputs are established.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology unitInterval

namespace SeriesParallel.MainText

/-- The source constant `C = log 2 / (p - 1/2)` for supercritical center tracking. -/
noncomputable def centerWidthBound (p : unitInterval) : ℝ :=
  Real.log 2 / ((p : ℝ) - 1 / 2)

/-- The expected absolute difference of the two depth-one descendant copies. -/
noncomputable def descendantPairWidth
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment,
    |X mode n (Environment.subtree [false] environment) -
      X mode n (Environment.subtree [true] environment)| ∂environmentMeasure p

/-- Absolute centered fluctuation at one generation. -/
noncomputable def centeredAbs
    (p : unitInterval) (mode : Mode) (n : ℕ) (environment : Environment) : ℝ :=
  |X mode n environment - meanLog p mode n|

theorem integrable_centeredAbs (p : unitInterval) (mode : Mode) (n : ℕ) :
    Integrable (centeredAbs p mode n) (environmentMeasure p) := by
  change Integrable
    (fun environment ↦ |X mode n environment - meanLog p mode n|)
    (environmentMeasure p)
  exact ((integrable_X p mode n).sub (integrable_const (meanLog p mode n))).abs

theorem centerWidthBound_nonneg (p : unitInterval)
    (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    0 ≤ centerWidthBound p := by
  exact div_nonneg (Real.log_nonneg (by norm_num)) (sub_pos.mpr hp).le

/-- The logarithmic drift and the adjacent-generation bound give the uniform iid-pair width. -/
theorem descendant_pair_width_le (p : unitInterval) (mode : Mode) (n : ℕ)
    (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    descendantPairWidth p mode n ≤ centerWidthBound p := by
  have hcoefficient :
      0 ≤ (p : ℝ) - mode.eta * (1 - (p : ℝ)) := by
    cases mode <;> simp [Mode.eta] <;> linarith
  have hcorrection :
      0 ≤ ∫ environment,
        h |X mode n (Environment.subtree [false] environment) -
          X mode n (Environment.subtree [true] environment)|
        ∂environmentMeasure p :=
    integral_nonneg fun environment ↦ h_nonneg _
  have hdriftLower :
      ((p : ℝ) - 1 / 2) * descendantPairWidth p mode n ≤
        meanLog p mode (n + 1) - meanLog p mode n := by
    rw [meanLog, meanLog, logarithmic_drift]
    exact le_add_of_nonneg_right (mul_nonneg hcoefficient hcorrection)
  have hdriftUpper :
      meanLog p mode (n + 1) - meanLog p mode n ≤ Real.log 2 :=
    (le_abs_self _).trans (meanLog_increment_bound p mode n)
  rw [centerWidthBound, le_div_iff₀ (sub_pos.mpr hp)]
  simpa [mul_comm] using hdriftLower.trans hdriftUpper

/-- Symmetrization: distance from the mean is bounded by the iid-pair width. -/
theorem integral_abs_sub_integral_le_pair {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → ℝ)
    (hf : Integrable f mu) :
    (∫ x, |f x - ∫ y, f y ∂mu| ∂mu) ≤
      ∫ z : α × α, |f z.1 - f z.2| ∂mu.prod mu := by
  have hfst : Integrable (fun z : α × α ↦ f z.1) (mu.prod mu) :=
    hf.comp_fst mu
  have hsnd : Integrable (fun z : α × α ↦ f z.2) (mu.prod mu) :=
    hf.comp_snd mu
  have hpair : Integrable (fun z : α × α ↦ f z.1 - f z.2) (mu.prod mu) :=
    hfst.sub hsnd
  have habsPair : Integrable
      (fun z : α × α ↦ |f z.1 - f z.2|) (mu.prod mu) := by
    simpa only [Real.norm_eq_abs] using hpair.abs
  rw [integral_prod _ habsPair]
  apply integral_mono
  · exact (hf.sub (integrable_const _)).abs
  · exact habsPair.integral_prod_left
  · intro x
    change |f x - ∫ y, f y ∂mu| ≤ ∫ y, |f x - f y| ∂mu
    have hcenter :
        f x - ∫ y, f y ∂mu = ∫ y, (f x - f y) ∂mu := by
      rw [integral_sub (integrable_const _) hf]
      simp
    rw [hcenter, ← Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun y ↦ f x - f y))

/-- The centered logarithmic variable is bounded by its canonical descendant-pair width. -/
theorem centered_X_le_descendant_pair (p : unitInterval) (mode : Mode) (n : ℕ) :
    (∫ environment, |X mode n environment - meanLog p mode n|
        ∂environmentMeasure p) ≤ descendantPairWidth p mode n := by
  let law : Measure ℝ := (environmentMeasure p).map (X mode n)
  letI : IsProbabilityMeasure law := by
    dsimp only [law]
    exact Measure.isProbabilityMeasure_map (measurable_X mode n).aemeasurable
  have hid : Integrable id law := by
    rw [integrable_map_measure aestronglyMeasurable_id
      (measurable_X mode n).aemeasurable]
    simpa only [Function.comp_def, id_eq] using integrable_X p mode n
  have hmean : (∫ x, x ∂law) = meanLog p mode n := by
    have h := (X_hasLaw p mode n).integral_comp aestronglyMeasurable_id
    simpa only [law, Function.comp_def, id_eq, meanLog] using h.symm
  have hcenterLaw :
      (∫ environment, |X mode n environment - meanLog p mode n|
          ∂environmentMeasure p) =
        ∫ x, |x - ∫ y, y ∂law| ∂law := by
    have h := (X_hasLaw p mode n).integral_comp
      (f := fun x : ℝ ↦ |x - ∫ y : ℝ, y ∂law|)
      ((measurable_id.sub measurable_const).abs.aestronglyMeasurable)
    simpa only [law, Function.comp_apply, hmean] using h
  have hpairLaw :
      descendantPairWidth p mode n =
        ∫ z : ℝ × ℝ, |z.1 - z.2| ∂law.prod law := by
    have h := (left_right_X_hasLaw p mode n).integral_comp
      ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)
    simpa only [law, Function.comp_apply, Pi.sub_apply, descendantPairWidth] using h
  calc
    (∫ environment, |X mode n environment - meanLog p mode n|
        ∂environmentMeasure p) =
        ∫ x, |x - ∫ y, y ∂law| ∂law := hcenterLaw
    _ ≤ ∫ z : ℝ × ℝ, |z.1 - z.2| ∂law.prod law :=
      integral_abs_sub_integral_le_pair law id hid
    _ = descendantPairWidth p mode n := hpairLaw.symm

/-- The centered logarithmic width is uniformly bounded in the supercritical regime. -/
theorem centered_X_uniform_bound (p : unitInterval) (mode : Mode) (n : ℕ)
    (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    (∫ environment, |X mode n environment - meanLog p mode n|
        ∂environmentMeasure p) ≤ centerWidthBound p :=
  (centered_X_le_descendant_pair p mode n).trans
    (descendant_pair_width_le p mode n hp)

/-- Paley--Zygmund and the uniform centered width bound the Jensen gap. -/
theorem jensenGap_le_uniform_bound
    (p : unitInterval) (mode : Mode) (n : ℕ) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    jensenGap p mode n ≤
      Real.log 2 +
        4 * secondMomentBoundConstant p mode * centerWidthBound p := by
  let event := halfMeanEvent p mode n
  let probability := (environmentMeasure p).real event
  let gap := jensenGap p mode n - Real.log 2
  have hevent : MeasurableSet event := measurableSet_halfMeanEvent p mode n
  have hK : 0 < secondMomentBoundConstant p mode :=
    secondMomentBoundConstant_pos p mode hp
  have hprobability :
      1 / (4 * secondMomentBoundConstant p mode) ≤ probability := by
    simpa only [probability, event, halfMeanEvent] using
      paleyZygmund_half_probability_lower_bound p mode hp n
  have hpointwise (environment : Environment) (henvironment : environment ∈ event) :
      gap ≤ centeredAbs p mode n environment := by
    have hmem :
        firstMoment p mode n / 2 ≤ Z mode n environment := by
      simpa only [event, halfMeanEvent, Set.mem_setOf_eq] using henvironment
    have hmeanPositive : 0 < firstMoment p mode n / 2 := by
      exact div_pos (firstMoment_pos p mode n) (by norm_num)
    have hlog :
        Real.log (firstMoment p mode n / 2) ≤ X mode n environment := by
      rw [X]
      exact Real.log_le_log hmeanPositive hmem
    have hlogDiv :
        Real.log (firstMoment p mode n / 2) =
          Real.log (firstMoment p mode n) - Real.log 2 :=
      Real.log_div (firstMoment_ne_zero p mode n) (by norm_num)
    dsimp only [gap]
    rw [jensenGap, centeredAbs]
    calc
      Real.log (firstMoment p mode n) - meanLog p mode n - Real.log 2 =
          (Real.log (firstMoment p mode n) - Real.log 2) -
            meanLog p mode n := by ring
      _ = Real.log (firstMoment p mode n / 2) - meanLog p mode n := by
        rw [hlogDiv]
      _ ≤ X mode n environment - meanLog p mode n := sub_le_sub_right hlog _
      _ ≤ |X mode n environment - meanLog p mode n| := le_abs_self _
  have hprobabilityGap :
      probability * gap ≤ centerWidthBound p := by
    calc
      probability * gap =
          ∫ environment in event, gap ∂environmentMeasure p := by
            simp only [setIntegral_const, probability, smul_eq_mul]
      _ ≤ ∫ environment in event, centeredAbs p mode n environment
          ∂environmentMeasure p := by
            exact setIntegral_mono_on
              (integrable_const gap).integrableOn
              (integrable_centeredAbs p mode n).integrableOn hevent hpointwise
      _ ≤ ∫ environment, centeredAbs p mode n environment
          ∂environmentMeasure p := by
            exact setIntegral_le_integral (integrable_centeredAbs p mode n)
              (Eventually.of_forall fun environment ↦ abs_nonneg _)
      _ ≤ centerWidthBound p := by
        simpa only [centeredAbs] using centered_X_uniform_bound p mode n hp
  by_cases hsmall : jensenGap p mode n ≤ Real.log 2
  · exact hsmall.trans (le_add_of_nonneg_right
      (mul_nonneg
        (mul_nonneg (by norm_num) hK.le)
        (centerWidthBound_nonneg p hp)))
  · have hgap : 0 ≤ gap := by
      dsimp only [gap]
      exact sub_nonneg.mpr (le_of_not_ge hsmall)
    have hscaled :
        (1 / (4 * secondMomentBoundConstant p mode)) * gap ≤
          centerWidthBound p :=
      (mul_le_mul_of_nonneg_right hprobability hgap).trans hprobabilityGap
    have hdenom : 0 < 4 * secondMomentBoundConstant p mode := mul_pos (by norm_num) hK
    have hgapBound :
        gap ≤ 4 * secondMomentBoundConstant p mode * centerWidthBound p := by
      rw [mul_comm]
      apply (div_le_iff₀ hdenom).1
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hscaled
    dsimp only [gap] at hgapBound
    linarith

/-- The normalized Jensen gap vanishes in the supercritical regime. -/
theorem normalizedJensenGap_tendsto_zero
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    Tendsto
      (fun n : ℕ ↦ jensenGap p mode (n + 1) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let bound := Real.log 2 +
    4 * secondMomentBoundConstant p mode * centerWidthBound p
  have hboundTendsto :
      Tendsto (fun n : ℕ ↦ bound / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul bound
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (jensenGap_nonneg p mode (n + 1)) (by positivity)
  · exact Eventually.of_forall fun n ↦
      div_le_div_of_nonneg_right
        (by simpa only [bound] using jensenGap_le_uniform_bound p mode (n + 1) hp)
        (by positivity)
  · exact hboundTendsto

/-- Supercritical normalized means share the Fekete first-moment limit. -/
theorem normalizedMeanLog_tendsto_firstMomentLimit
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    Tendsto (normalizedMeanLog p mode) atTop
      (𝓝 (chosenSequentialLimit (normalizedLogFirstMoment p mode))) := by
  have hfirst := normalizedLogFirstMoment_tendsto_chosenSequentialLimit p mode
  have hgap := normalizedJensenGap_tendsto_zero p mode hp
  have hdifference := hfirst.sub hgap
  convert hdifference using 1
  · funext n
    simp only [normalizedLogFirstMoment, normalizedMeanLog, jensenGap]
    ring
  · simp

/-- The canonical mean-log limit exists for every supercritical unit-interval parameter. -/
theorem normalizedMeanLog_converges_supercritical
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∃ value : ℝ, Tendsto (normalizedMeanLog p mode) atTop (𝓝 value) :=
  ⟨chosenSequentialLimit (normalizedLogFirstMoment p mode),
    normalizedMeanLog_tendsto_firstMomentLimit p mode hp⟩

/-- Telescoping the samplewise adjacent bound across an arbitrary finite interval. -/
theorem abs_X_add_sub_X_le_log_two (mode : Mode) (m k : ℕ)
    (environment : Environment) :
    |X mode (m + k) environment - X mode m environment| ≤
      (k : ℝ) * Real.log 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := abs_X_increment_le_log_two mode (m + k) environment
      calc
        |X mode (m + (k + 1)) environment - X mode m environment| =
            |(X mode (m + k + 1) environment - X mode (m + k) environment) +
              (X mode (m + k) environment - X mode m environment)| := by
                congr 1
                rw [Nat.add_assoc]
                ring
        _ ≤ |X mode (m + k + 1) environment - X mode (m + k) environment| +
              |X mode (m + k) environment - X mode m environment| := abs_add_le _ _
        _ ≤ Real.log 2 + (k : ℝ) * Real.log 2 := add_le_add hstep ih
        _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
          push_cast
          ring

/-- Telescoping the mean adjacent bound across an arbitrary finite interval. -/
theorem abs_meanLog_add_sub_meanLog_le_log_two
    (p : unitInterval) (mode : Mode) (m k : ℕ) :
    |meanLog p mode (m + k) - meanLog p mode m| ≤
      (k : ℝ) * Real.log 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := meanLog_increment_bound p mode (m + k)
      calc
        |meanLog p mode (m + (k + 1)) - meanLog p mode m| =
            |(meanLog p mode (m + k + 1) - meanLog p mode (m + k)) +
              (meanLog p mode (m + k) - meanLog p mode m)| := by
                congr 1
                rw [Nat.add_assoc]
                ring
        _ ≤ |meanLog p mode (m + k + 1) - meanLog p mode (m + k)| +
              |meanLog p mode (m + k) - meanLog p mode m| := abs_add_le _ _
        _ ≤ Real.log 2 + (k : ℝ) * Real.log 2 := add_le_add hstep ih
        _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
          push_cast
          ring

/-- A centered logarithm moves by at most twice the telescoped adjacent bound. -/
theorem centeredAbs_le_centeredAbs_add_gap
    (p : unitInterval) (mode : Mode) (m k : ℕ) (environment : Environment) :
    centeredAbs p mode (m + k) environment ≤
      centeredAbs p mode m environment + 2 * (k : ℝ) * Real.log 2 := by
  have hX := abs_X_add_sub_X_le_log_two mode m k environment
  have hmean := abs_meanLog_add_sub_meanLog_le_log_two p mode m k
  rw [centeredAbs, centeredAbs]
  calc
    |X mode (m + k) environment - meanLog p mode (m + k)| =
        |(X mode m environment - meanLog p mode m) +
          ((X mode (m + k) environment - X mode m environment) -
            (meanLog p mode (m + k) - meanLog p mode m))| := by
              congr 1
              ring
    _ ≤ |X mode m environment - meanLog p mode m| +
          |(X mode (m + k) environment - X mode m environment) -
            (meanLog p mode (m + k) - meanLog p mode m)| := abs_add_le _ _
    _ ≤ |X mode m environment - meanLog p mode m| +
          (|X mode (m + k) environment - X mode m environment| +
            |meanLog p mode (m + k) - meanLog p mode m|) := by
              gcongr
              exact abs_sub _ _
    _ ≤ |X mode m environment - meanLog p mode m| +
          ((k : ℝ) * Real.log 2 + (k : ℝ) * Real.log 2) := by
            gcongr
    _ = |X mode m environment - meanLog p mode m| +
          2 * (k : ℝ) * Real.log 2 := by ring

/-- Markov's inequality with the uniform supercritical center-width constant. -/
theorem centeredAbs_measureReal_ge_le (p : unitInterval) (mode : Mode) (n : ℕ)
    (hp : (1 / 2 : ℝ) < (p : ℝ)) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (environmentMeasure p).real
        {environment | threshold ≤ centeredAbs p mode n environment} ≤
      centerWidthBound p / threshold := by
  change (environmentMeasure p).real
      {environment | threshold ≤
        |X mode n environment - meanLog p mode n|} ≤
    centerWidthBound p / threshold
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := environmentMeasure p)
    (Eventually.of_forall fun environment ↦ abs_nonneg
      (X mode n environment - meanLog p mode n))
    (integrable_centeredAbs p mode n) threshold
  have hintegral :
      (∫ environment, centeredAbs p mode n environment ∂environmentMeasure p) ≤
        centerWidthBound p := by
    simpa only [centeredAbs] using centered_X_uniform_bound p mode n hp
  rw [le_div_iff₀ hthreshold]
  simpa only [mul_comm] using hmarkov.trans hintegral

/-- The square subsequence starts at generation one, avoiding every zero denominator. -/
def squareGeneration (k : ℕ) : ℕ :=
  (k + 1) ^ 2

/-- Bad event at square generation and reciprocal-integer accuracy. -/
noncomputable def centerSquareEvent
    (p : unitInterval) (mode : Mode) (j k : ℕ) : Set Environment :=
  {environment |
    ((squareGeneration k : ℕ) : ℝ) / ((j : ℝ) + 1) ≤
      centeredAbs p mode (squareGeneration k) environment}

private theorem centerSquareEvent_measureReal_le
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) (j k : ℕ) :
    (environmentMeasure p).real (centerSquareEvent p mode j k) ≤
      centerWidthBound p * ((j : ℝ) + 1) / ((squareGeneration k : ℕ) : ℝ) := by
  have hgeneration : 0 < ((squareGeneration k : ℕ) : ℝ) := by
    simp only [squareGeneration]
    positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hthreshold :
      0 < ((squareGeneration k : ℕ) : ℝ) / ((j : ℝ) + 1) :=
    div_pos hgeneration hj
  have hmarkov := centeredAbs_measureReal_ge_le p mode (squareGeneration k) hp hthreshold
  change (environmentMeasure p).real (centerSquareEvent p mode j k) ≤ _
  calc
    (environmentMeasure p).real (centerSquareEvent p mode j k) ≤
        centerWidthBound p /
          (((squareGeneration k : ℕ) : ℝ) / ((j : ℝ) + 1)) := by
      simpa only [centerSquareEvent] using hmarkov
    _ = centerWidthBound p * ((j : ℝ) + 1) /
          ((squareGeneration k : ℕ) : ℝ) := by
      field_simp

private theorem centerSquareEvent_tsum_ne_top
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) (j : ℕ) :
    (∑' k, environmentMeasure p (centerSquareEvent p mode j k)) ≠ ∞ := by
  have hbase : Summable
      (fun k : ℕ ↦ (((squareGeneration k : ℕ) : ℝ))⁻¹) := by
    have hshift := (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    simpa only [squareGeneration, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hshift
  have hreal : Summable
      (fun k : ℕ ↦
        centerWidthBound p * ((j : ℝ) + 1) /
          ((squareGeneration k : ℕ) : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      hbase.mul_left (centerWidthBound p * ((j : ℝ) + 1))
  have hmeasure (k : ℕ) :
      environmentMeasure p (centerSquareEvent p mode j k) ≤
        ENNReal.ofReal
          (centerWidthBound p * ((j : ℝ) + 1) /
            ((squareGeneration k : ℕ) : ℝ)) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal
      (centerSquareEvent_measureReal_le p mode hp j k)
  exact ne_top_of_le_ne_top hreal.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hmeasure)

/-- Borel--Cantelli makes the centered square subsequence negligible almost surely. -/
theorem centered_square_subsequence_ae_tendsto_zero
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∀ᵐ environment ∂environmentMeasure p,
      Tendsto
        (fun k : ℕ ↦
          centeredAbs p mode (squareGeneration k) environment /
            ((squareGeneration k : ℕ) : ℝ))
        atTop (𝓝 0) := by
  have hbad : ∀ᵐ environment ∂environmentMeasure p, ∀ j : ℕ,
      ∀ᶠ k in atTop, environment ∉ centerSquareEvent p mode j k := by
    apply ae_all_iff.2
    intro j
    exact ae_eventually_notMem (centerSquareEvent_tsum_ne_top p mode hp j)
  filter_upwards [hbad] with environment henvironment
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 (henvironment j)
  refine ⟨N, ?_⟩
  intro k hkN
  have hk := hN k hkN
  have hgeneration : 0 < ((squareGeneration k : ℕ) : ℝ) := by
    simp only [squareGeneration]
    positivity
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hk' :
      centeredAbs p mode (squareGeneration k) environment <
        ((squareGeneration k : ℕ) : ℝ) / ((j : ℝ) + 1) := by
    simpa only [centerSquareEvent, Set.mem_setOf_eq, not_le] using hk
  have hratio :
      centeredAbs p mode (squareGeneration k) environment /
          ((squareGeneration k : ℕ) : ℝ) <
        1 / ((j : ℝ) + 1) := by
    rw [div_lt_iff₀ hgeneration]
    calc
      centeredAbs p mode (squareGeneration k) environment <
          ((squareGeneration k : ℕ) : ℝ) / ((j : ℝ) + 1) := hk'
      _ = 1 / ((j : ℝ) + 1) * ((squareGeneration k : ℕ) : ℝ) := by
        ring
  have hcentered :
      0 ≤ centeredAbs p mode (squareGeneration k) environment := abs_nonneg _
  have hnonneg :
      0 ≤ centeredAbs p mode (squareGeneration k) environment /
        ((squareGeneration k : ℕ) : ℝ) :=
    div_nonneg hcentered hgeneration.le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hratio.trans hj

/-- Removing the harmless initial shift gives convergence along all perfect squares. -/
theorem centered_squares_ae_tendsto_zero
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∀ᵐ environment ∂environmentMeasure p,
      Tendsto
        (fun k : ℕ ↦
          centeredAbs p mode (k ^ 2) environment / (((k ^ 2 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
  filter_upwards [centered_square_subsequence_ae_tendsto_zero p mode hp]
    with environment henvironment
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa only [squareGeneration] using henvironment

/-- The integer square root tends to infinity. -/
theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with n hn
  exact Nat.le_sqrt'.2 hn

/-- Deterministic interpolation from the preceding perfect square. -/
theorem centeredAbs_div_le_squareRoot_bound
    (p : unitInterval) (mode : Mode) (n : ℕ) (hn : 0 < n)
    (environment : Environment) :
    centeredAbs p mode n environment / (n : ℝ) ≤
      centeredAbs p mode ((Nat.sqrt n) ^ 2) environment /
          ((((Nat.sqrt n) ^ 2 : ℕ) : ℝ)) +
        4 * Real.log 2 / (Nat.sqrt n : ℝ) := by
  let k := Nat.sqrt n
  have hk : 0 < k := Nat.sqrt_pos.2 hn
  have hsq : k ^ 2 ≤ n := Nat.sqrt_le' n
  have hnext : n < (k + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hgap : n - k ^ 2 ≤ 2 * k := by
    have hexpand : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [hexpand] at hnext
    omega
  have hdecomp : k ^ 2 + (n - k ^ 2) = n := Nat.add_sub_of_le hsq
  have hcenter := centeredAbs_le_centeredAbs_add_gap
    p mode (k ^ 2) (n - k ^ 2) environment
  rw [hdecomp] at hcenter
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsqReal : 0 < ((k ^ 2 : ℕ) : ℝ) := by positivity
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqLeReal : ((k ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsq
  have hgapReal : ((n - k ^ 2 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    exact_mod_cast hgap
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcenterNonneg : 0 ≤ centeredAbs p mode (k ^ 2) environment := abs_nonneg _
  have hgapTermNonneg :
      0 ≤ 2 * ((n - k ^ 2 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hgapNumerator :
      2 * ((n - k ^ 2 : ℕ) : ℝ) * Real.log 2 ≤
        2 * (2 * (k : ℝ)) * Real.log 2 := by
    gcongr
  calc
    centeredAbs p mode n environment / (n : ℝ) ≤
        (centeredAbs p mode (k ^ 2) environment +
          2 * ((n - k ^ 2 : ℕ) : ℝ) * Real.log 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right hcenter hnReal.le
    _ = centeredAbs p mode (k ^ 2) environment / (n : ℝ) +
          (2 * ((n - k ^ 2 : ℕ) : ℝ) * Real.log 2) / (n : ℝ) :=
      add_div _ _ _
    _ ≤ centeredAbs p mode (k ^ 2) environment / (((k ^ 2 : ℕ) : ℝ)) +
          (2 * ((n - k ^ 2 : ℕ) : ℝ) * Real.log 2) /
            (((k ^ 2 : ℕ) : ℝ)) :=
      add_le_add
        (div_le_div_of_nonneg_left hcenterNonneg hsqReal hsqLeReal)
        (div_le_div_of_nonneg_left hgapTermNonneg hsqReal hsqLeReal)
    _ ≤ centeredAbs p mode (k ^ 2) environment / (((k ^ 2 : ℕ) : ℝ)) +
          (2 * (2 * (k : ℝ)) * Real.log 2) / (((k ^ 2 : ℕ) : ℝ)) := by
      gcongr
    _ = centeredAbs p mode (k ^ 2) environment / (((k ^ 2 : ℕ) : ℝ)) +
          4 * Real.log 2 / (k : ℝ) := by
      norm_num [Nat.cast_pow]
      field_simp
      ring

/-- Centered logarithmic fluctuations are sublinear almost surely. -/
theorem centered_X_ae_tendsto_zero
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∀ᵐ environment ∂environmentMeasure p,
      Tendsto
        (fun n : ℕ ↦ centeredAbs p mode n environment / (n : ℝ))
        atTop (𝓝 0) := by
  filter_upwards [centered_squares_ae_tendsto_zero p mode hp]
    with environment hsquares
  have hsqrtSquares := hsquares.comp natSqrt_tendsto_atTop
  have hsqrtReal :
      Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp natSqrt_tendsto_atTop
  have hinverse :
      Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtReal
  have herror :
      Tendsto (fun n : ℕ ↦ 4 * Real.log 2 / (Nat.sqrt n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinverse.const_mul (4 * Real.log 2)
  have hupper :
      Tendsto
        (fun n : ℕ ↦
          centeredAbs p mode ((Nat.sqrt n) ^ 2) environment /
              ((((Nat.sqrt n) ^ 2 : ℕ) : ℝ)) +
            4 * Real.log 2 / (Nat.sqrt n : ℝ))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_add] using hsqrtSquares.add herror
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact centeredAbs_div_le_squareRoot_bound p mode n hn environment
  · exact hupper

/-- Signed centered logarithmic fluctuations are also sublinear almost surely. -/
theorem centered_X_ae_tendsto_zero_signed
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∀ᵐ environment ∂environmentMeasure p,
      Tendsto
        (fun n : ℕ ↦
          (X mode n environment - meanLog p mode n) / (n : ℝ))
        atTop (𝓝 0) := by
  filter_upwards [centered_X_ae_tendsto_zero p mode hp]
    with environment hcentered
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hnorm :
      (fun n : ℕ ↦
        ‖(X mode n environment - meanLog p mode n) / (n : ℝ)‖) =
        (fun n : ℕ ↦ centeredAbs p mode n environment / (n : ℝ)) := by
    funext n
    have hcastAbs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_div, hcastAbs]
    rfl
  rw [hnorm]
  exact hcentered

/-- The centered normalized logarithm converges to zero in `L¹`. -/
theorem centered_X_div_L1_tendsto_zero (p : unitInterval) (mode : Mode)
    (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    Tendsto
      (fun n : ℕ ↦
        ∫ environment,
          |X mode (n + 1) environment / ((n : ℝ) + 1) -
            meanLog p mode (n + 1) / ((n : ℝ) + 1)|
          ∂environmentMeasure p)
      atTop (𝓝 0) := by
  have hboundTendsto :
      Tendsto (fun n : ℕ ↦ centerWidthBound p / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (centerWidthBound p))
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _
  · apply Eventually.of_forall
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    calc
      (∫ environment,
          |X mode (n + 1) environment / ((n : ℝ) + 1) -
            meanLog p mode (n + 1) / ((n : ℝ) + 1)|
          ∂environmentMeasure p) =
          (∫ environment,
            |X mode (n + 1) environment - meanLog p mode (n + 1)|
            ∂environmentMeasure p) / ((n : ℝ) + 1) := by
        rw [← integral_div]
        apply integral_congr_ae
        filter_upwards with environment
        rw [← sub_div, abs_div, abs_of_pos hden]
      _ ≤ centerWidthBound p / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right
          (centered_X_uniform_bound p mode (n + 1) hp) hden.le
  · exact hboundTendsto

/-- The contract's chosen mean-log limit is realized in the supercritical regime. -/
theorem normalizedMeanLog_tendsto_chosenMeanLimit_supercritical
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    Tendsto (normalizedMeanLog p mode) atTop
      (𝓝 (chosenSequentialLimit (normalizedMeanLog p mode))) :=
  chosenSequentialLimit_spec (normalizedMeanLog_converges_supercritical p mode hp)

/-- The chosen first-moment and mean-log limits agree above criticality. -/
theorem chosenFirstMomentLimit_eq_chosenMeanLimit_supercritical
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    chosenSequentialLimit (normalizedLogFirstMoment p mode) =
      chosenSequentialLimit (normalizedMeanLog p mode) :=
  tendsto_nhds_unique
    (normalizedMeanLog_tendsto_firstMomentLimit p mode hp)
    (normalizedMeanLog_tendsto_chosenMeanLimit_supercritical p mode hp)

/-- Adding the deterministic mean gives samplewise normalized-log convergence. -/
theorem normalized_X_ae_tendsto_chosenMeanLimit_supercritical
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    ∀ᵐ environment ∂environmentMeasure p,
      Tendsto
        (fun n : ℕ ↦ X mode (n + 1) environment / (((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (chosenSequentialLimit (normalizedMeanLog p mode))) := by
  filter_upwards [centered_X_ae_tendsto_zero_signed p mode hp]
    with environment hcentered
  have hcenteredShift := (tendsto_add_atTop_iff_nat 1).2 hcentered
  have hmean := normalizedMeanLog_tendsto_chosenMeanLimit_supercritical p mode hp
  have hsum := hcenteredShift.add hmean
  convert hsum using 1
  · funext n
    simp only [normalizedMeanLog, Nat.cast_add, Nat.cast_one]
    ring
  · simp

/-- Adding the deterministic mean gives normalized-log convergence in `L¹`. -/
theorem normalized_X_L1_tendsto_chosenMeanLimit_supercritical
    (p : unitInterval) (mode : Mode) (hp : (1 / 2 : ℝ) < (p : ℝ)) :
    Tendsto
      (fun n : ℕ ↦
        ∫ environment,
          |X mode (n + 1) environment / (((n + 1 : ℕ) : ℝ)) -
            chosenSequentialLimit (normalizedMeanLog p mode)|
          ∂environmentMeasure p)
      atTop (𝓝 0) := by
  let value := chosenSequentialLimit (normalizedMeanLog p mode)
  simp only [Nat.cast_add, Nat.cast_one]
  have hmean := normalizedMeanLog_tendsto_chosenMeanLimit_supercritical p mode hp
  have hmeanAbs :
      Tendsto (fun n : ℕ ↦ |normalizedMeanLog p mode n - value|)
        atTop (𝓝 0) := by
    have hdifference := hmean.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ value)
      atTop (𝓝 value))
    simpa only [value, sub_self, abs_zero] using hdifference.abs
  have hcentered := centered_X_div_L1_tendsto_zero p mode hp
  have hupper :
      Tendsto
        (fun n : ℕ ↦
          (∫ environment,
            |X mode (n + 1) environment / ((n : ℝ) + 1) -
              meanLog p mode (n + 1) / ((n : ℝ) + 1)|
            ∂environmentMeasure p) +
            |normalizedMeanLog p mode n - value|)
        atTop (𝓝 0) := by
    simpa only [zero_add] using hcentered.add hmeanAbs
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _
  · apply Eventually.of_forall
    intro n
    have hden : 0 < ((n : ℝ) + 1) := by positivity
    have hX : Integrable
        (fun environment ↦ X mode (n + 1) environment / ((n : ℝ) + 1))
        (environmentMeasure p) :=
      (integrable_X p mode (n + 1)).div_const ((n : ℝ) + 1)
    have htarget : Integrable
        (fun environment ↦
          |X mode (n + 1) environment / ((n : ℝ) + 1) - value|)
        (environmentMeasure p) :=
      (hX.sub (integrable_const value)).abs
    have hcenter : Integrable
        (fun environment ↦
          |X mode (n + 1) environment / ((n : ℝ) + 1) -
            meanLog p mode (n + 1) / ((n : ℝ) + 1)|)
        (environmentMeasure p) :=
      (hX.sub (integrable_const _)).abs
    change (∫ environment,
        |X mode (n + 1) environment / ((n : ℝ) + 1) - value|
        ∂environmentMeasure p) ≤ _
    calc
      (∫ environment,
          |X mode (n + 1) environment / ((n : ℝ) + 1) - value|
          ∂environmentMeasure p) ≤
          ∫ environment,
            |X mode (n + 1) environment / ((n : ℝ) + 1) -
                meanLog p mode (n + 1) / ((n : ℝ) + 1)| +
              |normalizedMeanLog p mode n - value|
            ∂environmentMeasure p := by
        apply integral_mono htarget (hcenter.add (integrable_const _))
        intro environment
        rw [normalizedMeanLog]
        calc
          |X mode (n + 1) environment / ((n : ℝ) + 1) - value| =
              |(X mode (n + 1) environment / ((n : ℝ) + 1) -
                  meanLog p mode (n + 1) / ((n : ℝ) + 1)) +
                (meanLog p mode (n + 1) / ((n : ℝ) + 1) - value)| := by
                    congr 1
                    ring
          _ ≤ |X mode (n + 1) environment / ((n : ℝ) + 1) -
                  meanLog p mode (n + 1) / ((n : ℝ) + 1)| +
                |meanLog p mode (n + 1) / ((n : ℝ) + 1) - value| :=
            abs_add_le _ _
      _ = (∫ environment,
            |X mode (n + 1) environment / ((n : ℝ) + 1) -
              meanLog p mode (n + 1) / ((n : ℝ) + 1)|
            ∂environmentMeasure p) +
            |normalizedMeanLog p mode n - value| := by
        rw [integral_add hcenter (integrable_const _), integral_const]
        simp only [smul_eq_mul, probReal_univ, one_mul]
  · simpa only [value, Nat.cast_add, Nat.cast_one] using hupper

/-- Supercritical source parameters satisfy the contract's combined convergence predicate. -/
theorem convergesASAndL1AtLinearRate_supercritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 < p) (mode : Mode) :
    ConvergesASAndL1AtLinearRate p mode
      (chosenSequentialLimit (normalizedMeanLog (modelParameter p) mode)) := by
  have hpUnit : (1 / 2 : ℝ) < (modelParameter p : ℝ) := by
    simpa only [modelParameter_coe_of_mem hpMem] using hp
  exact ⟨normalized_X_ae_tendsto_chosenMeanLimit_supercritical
      (modelParameter p) mode hpUnit,
    normalized_X_L1_tendsto_chosenMeanLimit_supercritical
      (modelParameter p) mode hpUnit⟩

theorem gammaD_eq_vD_supercritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 < p) :
    gammaD p = vD p := by
  have hpUnit : (1 / 2 : ℝ) < (modelParameter p : ℝ) := by
    simpa only [modelParameter_coe_of_mem hpMem] using hp
  simpa only [gammaD, vD] using
    chosenFirstMomentLimit_eq_chosenMeanLimit_supercritical
      (modelParameter p) .distance hpUnit

theorem gammaR_eq_vR_supercritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 < p) :
    gammaR p = vR p := by
  have hpUnit : (1 / 2 : ℝ) < (modelParameter p : ℝ) := by
    simpa only [modelParameter_coe_of_mem hpMem] using hp
  simpa only [gammaR, vR] using
    chosenFirstMomentLimit_eq_chosenMeanLimit_supercritical
      (modelParameter p) .resistance hpUnit

theorem distance_convergesASAndL1_supercritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 < p) :
    ConvergesASAndL1AtLinearRate p .distance (vD p) := by
  simpa only [vD] using
    convergesASAndL1AtLinearRate_supercritical hpMem hp .distance

theorem resistance_convergesASAndL1_supercritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 < p) :
    ConvergesASAndL1AtLinearRate p .resistance (vR p) := by
  simpa only [vR] using
    convergesASAndL1AtLinearRate_supercritical hpMem hp .resistance

end SeriesParallel.MainText
