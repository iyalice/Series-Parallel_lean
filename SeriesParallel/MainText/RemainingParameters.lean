/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.FiniteFlows
import SeriesParallel.MainText.JensenAndCenter
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Moments.Basic

/-!
# Remaining parameter ranges

This file contains the internal part of the remaining-parameter argument.  The common-uniform
coupling transfers the single critical distance input to every parameter below one half.
Resistance complementarity, the critical deterministic squeeze, and the elementary normalized
first-moment dichotomy are kept separate from the literature and Jensen/centering inputs.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology unitInterval

namespace SeriesParallel.MainText

/-! ## Common-uniform parameter coupling -/

/-- A coordinatewise uniform source from which every Bernoulli environment is obtained. -/
abbrev UniformEnvironment := Word → unitInterval

/-- The product Lebesgue probability measure on common-uniform coordinates. -/
noncomputable def uniformEnvironmentMeasure : Measure UniformEnvironment :=
  Measure.infinitePi fun _ : Word ↦ (volume : Measure unitInterval)

instance : IsProbabilityMeasure uniformEnvironmentMeasure := by
  unfold uniformEnvironmentMeasure
  infer_instance

/-- A single uniform coordinate thresholded at parameter `p`. -/
noncomputable def thresholdCoordinate (p : unitInterval) (u : unitInterval) : Bool :=
  if u ≤ p then true else false

theorem measurable_thresholdCoordinate (p : unitInterval) :
    Measurable (thresholdCoordinate p) := by
  unfold thresholdCoordinate
  exact measurable_const.piecewise measurableSet_Iic measurable_const

private theorem ofReal_coe_unitInterval (q : unitInterval) :
    ENNReal.ofReal (q : ℝ) = (unitInterval.toNNReal q : ENNReal) := by
  rw [ENNReal.ofReal_eq_coe_nnreal q.2.1]
  congr

private theorem thresholdCoordinate_map (p : unitInterval) :
    (volume : Measure unitInterval).map (thresholdCoordinate p) = bernoulliBool p := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (measurable_thresholdCoordinate p) (MeasurableSet.singleton b)]
  cases b with
  | false =>
      rw [show thresholdCoordinate p ⁻¹' {false} = Ioi p by
        ext u
        simp [thresholdCoordinate]]
      rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq, ofReal_coe_unitInterval]
      simp [bernoulliBool]
  | true =>
      rw [show thresholdCoordinate p ⁻¹' {true} = Iic p by
        ext u
        simp [thresholdCoordinate]]
      rw [unitInterval.volume_Iic, ofReal_coe_unitInterval]
      simp [bernoulliBool]

/-- Threshold every common-uniform coordinate at `p`. -/
noncomputable def thresholdEnvironment (p : unitInterval)
    (uniforms : UniformEnvironment) : Environment :=
  fun word ↦ thresholdCoordinate p (uniforms word)

theorem measurable_thresholdEnvironment (p : unitInterval) :
    Measurable (thresholdEnvironment p) := by
  exact measurable_pi_iff.mpr fun word ↦
    (measurable_thresholdCoordinate p).comp (measurable_pi_apply word)

/-- Thresholding the common-uniform field gives exactly the canonical Bernoulli environment. -/
theorem thresholdEnvironment_map (p : unitInterval) :
    uniformEnvironmentMeasure.map (thresholdEnvironment p) = environmentMeasure p := by
  unfold uniformEnvironmentMeasure environmentMeasure thresholdEnvironment
  rw [Measure.infinitePi_map_pi (fun _ : Word ↦ (volume : Measure unitInterval))
    (fun _ ↦ measurable_thresholdCoordinate p)]
  simp_rw [thresholdCoordinate_map]

theorem thresholdEnvironment_measurePreserving (p : unitInterval) :
    MeasurePreserving (thresholdEnvironment p) uniformEnvironmentMeasure
      (environmentMeasure p) :=
  ⟨measurable_thresholdEnvironment p, thresholdEnvironment_map p⟩

/-- The common-uniform realization is pointwise monotone in the Bernoulli parameter. -/
theorem thresholdEnvironment_mono {p q : unitInterval} (hpq : p ≤ q)
    (uniforms : UniformEnvironment) :
    thresholdEnvironment p uniforms ≤ thresholdEnvironment q uniforms := by
  intro word
  by_cases hp : uniforms word ≤ p
  · have hq : uniforms word ≤ q := hp.trans hpq
    simp [thresholdEnvironment, thresholdCoordinate, hp, hq]
  · simp [thresholdEnvironment, thresholdCoordinate, hp, Bool.false_le]

/-- Turning additional parallel gates into series gates can only increase graph distance. -/
theorem distanceValue_mono_environment (n : ℕ) {environment environment' : Environment}
    (h : environment ≤ environment') :
    distanceValue n environment ≤ distanceValue n environment' := by
  induction n generalizing environment environment' with
  | zero => simp
  | succ n ih =>
      rw [distanceValue_succ, distanceValue_succ]
      have hleft : Environment.subtree [false] environment ≤
          Environment.subtree [false] environment' :=
        fun word ↦ h ([false] ++ word)
      have hright : Environment.subtree [true] environment ≤
          Environment.subtree [true] environment' :=
        fun word ↦ h ([true] ++ word)
      have ihleft := ih hleft
      have ihright := ih hright
      have hroot := h root
      cases he : environment root <;> cases he' : environment' root <;>
        simp only [he, he', Bool.false_eq_true, ↓reduceIte] at hroot ⊢
      · exact min_le_min ihleft ihright
      · exact (min_le_left _ _).trans (ihleft.trans (Nat.le_add_right _ _))
      · exfalso
        have hbad := Bool.eq_true_of_true_le hroot
        simp at hbad
      · exact Nat.add_le_add ihleft ihright

/-- The distance first moment is monotone in the common Bernoulli parameter. -/
theorem firstMoment_distance_mono {p q : unitInterval} (hpq : p ≤ q) (n : ℕ) :
    firstMoment p .distance n ≤ firstMoment q .distance n := by
  have hp := thresholdEnvironment_measurePreserving p
  have hq := thresholdEnvironment_measurePreserving q
  have hip : Integrable (fun uniforms ↦
      Z .distance n (thresholdEnvironment p uniforms)) uniformEnvironmentMeasure :=
    hp.integrable_comp_of_integrable (integrable_Z p .distance n)
  have hiq : Integrable (fun uniforms ↦
      Z .distance n (thresholdEnvironment q uniforms)) uniformEnvironmentMeasure :=
    hq.integrable_comp_of_integrable (integrable_Z q .distance n)
  calc
    firstMoment p .distance n =
        ∫ uniforms, Z .distance n (thresholdEnvironment p uniforms)
          ∂uniformEnvironmentMeasure := by
      symm
      simpa [firstMoment, Function.comp_def] using
        hp.hasLaw.integral_comp (measurable_Z .distance n).aestronglyMeasurable
    _ ≤ ∫ uniforms, Z .distance n (thresholdEnvironment q uniforms)
          ∂uniformEnvironmentMeasure := by
      apply integral_mono hip hiq
      intro uniforms
      change (distanceValue n (thresholdEnvironment p uniforms) : ℝ) ≤
        (distanceValue n (thresholdEnvironment q uniforms) : ℝ)
      exact_mod_cast distanceValue_mono_environment n
        (thresholdEnvironment_mono hpq uniforms)
    _ = firstMoment q .distance n := by
      simpa [firstMoment, Function.comp_def] using
        hq.hasLaw.integral_comp (measurable_Z .distance n).aestronglyMeasurable

theorem normalizedLogFirstMoment_distance_mono {p q : unitInterval} (hpq : p ≤ q)
    (n : ℕ) :
    normalizedLogFirstMoment p .distance n ≤
      normalizedLogFirstMoment q .distance n := by
  rw [normalizedLogFirstMoment]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.log_le_log (firstMoment_pos p .distance (n + 1))
    (firstMoment_distance_mono hpq (n + 1))

/-- The canonical distance first-moment exponent is monotone on the source parameter range. -/
theorem gammaD_mono {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hpq : p ≤ q) : gammaD p ≤ gammaD q := by
  have hmodel : modelParameter p ≤ modelParameter q := by
    rw [modelParameter_eq_of_mem hp, modelParameter_eq_of_mem hq]
    exact hpq
  exact le_of_tendsto_of_tendsto'
    (normalizedLogFirstMoment_tendsto_gammaD p)
    (normalizedLogFirstMoment_tendsto_gammaD q)
    (fun n ↦ normalizedLogFirstMoment_distance_mono hmodel n)

theorem one_le_firstMoment_distance (p : unitInterval) (n : ℕ) :
    1 ≤ firstMoment p .distance n := by
  rw [firstMoment]
  calc
    1 = ∫ _ : Environment, (1 : ℝ) ∂environmentMeasure p := by simp
    _ ≤ ∫ environment, Z .distance n environment ∂environmentMeasure p := by
      apply integral_mono (integrable_const _) (integrable_Z p .distance n)
      intro environment
      change (1 : ℝ) ≤ distanceValue n environment
      exact_mod_cast (randomNetwork n environment).distance_bounds.1

theorem gammaD_nonneg (p : ℝ) : 0 ≤ gammaD p := by
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds
    (normalizedLogFirstMoment_tendsto_gammaD p)
  intro n
  rw [normalizedLogFirstMoment]
  exact div_nonneg
    (Real.log_nonneg (one_le_firstMoment_distance (modelParameter p) (n + 1)))
    (by positivity)

/-- The only literature input needed for the subcritical annealed distance range is the critical
value.  Parameter monotonicity and positivity propagate it to every `p ≤ 1/2`. -/
theorem gammaD_eq_zero_of_le_half (hcrit : gammaD (1 / 2) = 0) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) : gammaD p = 0 := by
  have hp_mem : p ∈ Icc (0 : ℝ) 1 := ⟨hp0, hp.trans (by norm_num)⟩
  have hhalf_mem : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  apply le_antisymm
  · exact (gammaD_mono hp_mem hhalf_mem hp).trans_eq hcrit
  · exact gammaD_nonneg p

/-! ## Zero annealed distance rate: `L¹` and almost-sure reduction -/

theorem normalizedMeanLog_distance_nonneg (p : unitInterval) (n : ℕ) :
    0 ≤ normalizedMeanLog p .distance n := by
  rw [normalizedMeanLog]
  apply div_nonneg _ (by positivity)
  rw [meanLog]
  apply integral_nonneg
  intro environment
  rw [X]
  exact Real.log_nonneg (by
    change (1 : ℝ) ≤ distanceValue (n + 1) environment
    exact_mod_cast (randomNetwork (n + 1) environment).distance_bounds.1)

theorem normalizedMeanLog_distance_le_logFirstMoment (p : unitInterval) (n : ℕ) :
    normalizedMeanLog p .distance n ≤ normalizedLogFirstMoment p .distance n := by
  rw [normalizedMeanLog, normalizedLogFirstMoment]
  exact div_le_div_of_nonneg_right (meanLog_le_log_firstMoment p .distance (n + 1))
    (by positivity)

/-- A zero annealed distance exponent forces the normalized mean logarithm to vanish. -/
theorem normalizedMeanLog_distance_tendsto_zero {p : ℝ}
    (hgamma : gammaD p = 0) :
    Tendsto (normalizedMeanLog (modelParameter p) .distance) atTop (nhds 0) := by
  have hupper := normalizedLogFirstMoment_tendsto_gammaD p
  rw [hgamma] at hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ normalizedMeanLog_distance_nonneg (modelParameter p) n)
    (fun n ↦ normalizedMeanLog_distance_le_logFirstMoment (modelParameter p) n)

/-- The preceding squeeze is exactly the required `L¹` convergence statement for distance. -/
theorem distance_L1_zero_of_gammaD_eq_zero {p : ℝ} (hgamma : gammaD p = 0) :
    Tendsto
      (fun n : ℕ ↦
        ∫ environment,
          |X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|
            ∂environmentMeasure (modelParameter p))
      atTop (nhds 0) := by
  have heq : (fun n : ℕ ↦
      ∫ environment,
        |X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|
          ∂environmentMeasure (modelParameter p)) =
      normalizedMeanLog (modelParameter p) .distance := by
    funext n
    rw [normalizedMeanLog, meanLog, ← integral_div]
    apply integral_congr_ae
    filter_upwards with environment
    have hX : 0 ≤ X .distance (n + 1) environment := by
      change 0 ≤ Real.log (distanceValue (n + 1) environment)
      exact Real.log_nonneg (by
        exact_mod_cast (randomNetwork (n + 1) environment).distance_bounds.1)
    have hnormalized : 0 ≤
        X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg hX (Nat.cast_nonneg _)
    rw [abs_of_nonneg hnormalized, Nat.cast_add, Nat.cast_one]
  rw [heq]
  exact normalizedMeanLog_distance_tendsto_zero hgamma

/-- First Borel--Cantelli in a form tailored to nonnegative normalized logarithms. -/
theorem ae_tendsto_zero_of_summable_upper_tails {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f : ℕ → Omega → ℝ) (hnonneg : ∀ n omega, 0 ≤ f n omega)
    (htails : ∀ k : ℕ,
      (∑' n, mu {omega | 1 / ((k : ℝ) + 1) ≤ f n omega}) ≠ ∞) :
    ∀ᵐ omega ∂mu, Tendsto (fun n ↦ f n omega) atTop (nhds 0) := by
  have hall : ∀ᵐ omega ∂mu, ∀ k : ℕ,
      ∀ᶠ n in atTop, omega ∉ {omega | 1 / ((k : ℝ) + 1) ≤ f n omega} :=
    ae_all_iff.mpr fun k ↦ ae_eventually_notMem (htails k)
  filter_upwards [hall] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
  rcases (eventually_atTop.1 (homega k)) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg n omega)]
  exact (lt_of_not_ge (hN n hn)).trans hk

private theorem tsum_measure_ne_top_of_eventually_measureReal_le_exp
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (sets : ℕ → Set Omega) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ n in atTop,
      mu.real (sets n) ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ))) :
    (∑' n, mu (sets n)) ≠ ∞ := by
  have hrpos : 0 < Real.exp (-c) := Real.exp_pos _
  have hrlt : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos, Real.exp_lt_one_iff]
    linarith
  have hgeom := summable_geometric_of_norm_lt_one hrlt
  have hsum : Summable (fun n : ℕ ↦
      Real.exp (-c * ((n + 1 : ℕ) : ℝ))) := by
    apply (hgeom.mul_left (Real.exp (-c))).congr
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  let terms : ℕ → NNReal := fun n ↦ (mu (sets n)).toNNReal
  have hterms : Summable terms := by
    rw [← NNReal.summable_coe]
    apply Summable.of_norm_bounded_eventually hsum
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [h] with n hn
    calc
      ‖(terms n : ℝ)‖ = (terms n : ℝ) := Real.norm_of_nonneg (terms n).2
      _ = mu.real (sets n) := by
        simp only [terms, measureReal_def, ENNReal.coe_toNNReal_eq_toReal]
      _ ≤ _ := hn
  have hcoe : (fun n ↦ mu (sets n)) = fun n ↦ (terms n : ENNReal) := by
    funext n
    exact (ENNReal.coe_toNNReal (measure_ne_top mu (sets n))).symm
  rw [hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hterms

private theorem distance_upper_tail_measureReal_eventually {p : ℝ}
    (hgamma : gammaD p = 0) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      (environmentMeasure (modelParameter p)).real
          {environment | epsilon ≤
            X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)} ≤
        Real.exp (-(epsilon / 2) * ((n + 1 : ℕ) : ℝ)) := by
  have hlimit := normalizedLogFirstMoment_tendsto_gammaD p
  rw [hgamma] at hlimit
  have hevent : ∀ᶠ n in atTop,
      normalizedLogFirstMoment (modelParameter p) .distance n < epsilon / 2 :=
    (tendsto_order.1 hlimit).2 _ (half_pos hepsilon)
  filter_upwards [hevent] with n hn
  simp only [Nat.cast_add, Nat.cast_one] at hn ⊢
  have hmarkov :
      (environmentMeasure (modelParameter p)).real
          {environment | epsilon ≤
            X .distance (n + 1) environment / ((n : ℝ) + 1)} ≤
        firstMoment (modelParameter p) .distance (n + 1) /
          Real.exp (epsilon * ((n : ℝ) + 1)) := by
    have hset :
        {environment | epsilon ≤
          X .distance (n + 1) environment / ((n : ℝ) + 1)} =
        {environment | Real.exp (epsilon * ((n : ℝ) + 1)) ≤
          Z .distance (n + 1) environment} := by
      ext environment
      simp only [mem_setOf_eq]
      rw [le_div_iff₀ (by positivity)]
      change epsilon * ((n : ℝ) + 1) ≤
        Real.log (Z .distance (n + 1) environment) ↔ _
      exact Real.le_log_iff_exp_le (Z_pos .distance (n + 1) environment)
    rw [hset, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun environment ↦ (Z_pos .distance (n + 1) environment).le)
      (integrable_Z (modelParameter p) .distance (n + 1)) _
  apply hmarkov.trans
  have hlog :
      Real.log (firstMoment (modelParameter p) .distance (n + 1)) <
        epsilon / 2 * ((n : ℝ) + 1) := by
    rw [normalizedLogFirstMoment] at hn
    exact (div_lt_iff₀ (by positivity)).mp hn
  have hmoment :
      firstMoment (modelParameter p) .distance (n + 1) ≤
        Real.exp (epsilon / 2 * ((n : ℝ) + 1)) := by
    rw [← Real.exp_log (firstMoment_pos (modelParameter p) .distance (n + 1))]
    exact (Real.exp_lt_exp.mpr hlog).le
  calc
    firstMoment (modelParameter p) .distance (n + 1) /
          Real.exp (epsilon * ((n : ℝ) + 1)) ≤
        Real.exp (epsilon / 2 * ((n : ℝ) + 1)) /
          Real.exp (epsilon * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hmoment (Real.exp_pos _).le
    _ = Real.exp (-(epsilon / 2) * ((n : ℝ) + 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- A zero distance annealed exponent supplies every summable upper-tail family needed by
first Borel--Cantelli. -/
theorem distance_upper_tails_summable_of_gammaD_eq_zero {p : ℝ}
    (hgamma : gammaD p = 0) (k : ℕ) :
    (∑' n, environmentMeasure (modelParameter p)
      {environment | 1 / ((k : ℝ) + 1) ≤
        X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)}) ≠ ∞ := by
  have hepsilon : 0 < 1 / ((k : ℝ) + 1) := by positivity
  exact tsum_measure_ne_top_of_eventually_measureReal_le_exp
    (environmentMeasure (modelParameter p)) _ (half_pos hepsilon)
    (distance_upper_tail_measureReal_eventually hgamma hepsilon)

/-- The zero annealed distance exponent also gives the full almost-sure normalized-log limit. -/
theorem distance_ae_zero_of_gammaD_eq_zero {p : ℝ} (hgamma : gammaD p = 0) :
    ∀ᵐ environment ∂environmentMeasure (modelParameter p),
      Tendsto
        (fun n : ℕ ↦
          X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
  apply ae_tendsto_zero_of_summable_upper_tails
  · intro n environment
    apply div_nonneg _ (Nat.cast_nonneg _)
    change 0 ≤ Real.log (distanceValue (n + 1) environment)
    exact Real.log_nonneg (by
      exact_mod_cast (randomNetwork (n + 1) environment).distance_bounds.1)
  · exact distance_upper_tails_summable_of_gammaD_eq_zero hgamma

/-- Critical distance annealed input, propagated to the complete subcritical a.s./`L¹` result. -/
theorem distance_subcritical_convergesASAndL1 (hcrit : gammaD (1 / 2) = 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    ConvergesASAndL1AtLinearRate p .distance 0 := by
  have hgamma := gammaD_eq_zero_of_le_half hcrit hp0 hp
  refine ⟨distance_ae_zero_of_gammaD_eq_zero hgamma, ?_⟩
  simpa only [sub_zero] using distance_L1_zero_of_gammaD_eq_zero hgamma

/-! ## Resistance complementarity -/

/-- Complementing every gate negates the logarithmic resistance. -/
theorem X_resistance_complement (n : ℕ) (environment : Environment) :
    X .resistance n (complementEnvironment environment) =
      -X .resistance n environment := by
  change Real.log (resistanceValue n (complementEnvironment environment)) =
    -Real.log (resistanceValue n environment)
  exact log_resistanceValue_complement n environment

/-- Complementary Bernoulli parameters have opposite resistance mean logarithms. -/
theorem meanLog_resistance_symm (p : unitInterval) (n : ℕ) :
    meanLog (unitInterval.symm p) .resistance n =
      -meanLog p .resistance n := by
  have hcomp :=
    (complementEnvironment_measurePreserving p).hasLaw.integral_comp
      (measurable_X .resistance n).aestronglyMeasurable
  rw [meanLog, meanLog, ← hcomp]
  calc
    (∫ environment,
        X .resistance n (complementEnvironment environment)
          ∂environmentMeasure p) =
        ∫ environment, -X .resistance n environment
          ∂environmentMeasure p := by
      apply integral_congr_ae
      filter_upwards with environment
      exact X_resistance_complement n environment
    _ = -(∫ environment, X .resistance n environment
          ∂environmentMeasure p) := by
      rw [integral_neg]

/-- Complementarity persists after normalization by the generation. -/
theorem normalizedMeanLog_resistance_symm (p : unitInterval) (n : ℕ) :
    normalizedMeanLog (unitInterval.symm p) .resistance n =
      -normalizedMeanLog p .resistance n := by
  rw [normalizedMeanLog, normalizedMeanLog, meanLog_resistance_symm]
  ring

private theorem chosenSequentialLimit_neg (sequence : ℕ → ℝ) :
    chosenSequentialLimit (fun n ↦ -sequence n) =
      -chosenSequentialLimit sequence := by
  by_cases h : ∃ value, Tendsto sequence atTop (𝓝 value)
  · have hsequence := chosenSequentialLimit_spec h
    exact chosenSequentialLimit_eq hsequence.neg
  · have hneg : ¬ ∃ value, Tendsto (fun n ↦ -sequence n) atTop (𝓝 value) := by
      rintro ⟨value, hvalue⟩
      apply h
      refine ⟨-value, ?_⟩
      simpa only [neg_neg] using hvalue.neg
    simp [chosenSequentialLimit, h, hneg]

theorem modelParameter_one_sub {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    modelParameter (1 - p) = unitInterval.symm (modelParameter p) := by
  have hcomplement : 1 - p ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hp.1, hp.2]
  apply Subtype.ext
  rw [modelParameter_coe_of_mem hcomplement, unitInterval.coe_symm_eq,
    modelParameter_coe_of_mem hp]

/-- The resistance mean-log speed is odd under the parameter complement. -/
theorem vR_one_sub (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    vR (1 - p) = -vR p := by
  rw [vR, vR, modelParameter_one_sub hp]
  have hsequence :
      normalizedMeanLog (unitInterval.symm (modelParameter p)) .resistance =
        fun n ↦ -normalizedMeanLog (modelParameter p) .resistance n := by
    funext n
    exact normalizedMeanLog_resistance_symm (modelParameter p) n
  rw [hsequence, chosenSequentialLimit_neg]

/-- Complementarity transfers the supercritical resistance law to every strict subcritical
parameter. -/
theorem resistance_subcritical_convergesASAndL1
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2) :
    ConvergesASAndL1AtLinearRate p .resistance (vR p) := by
  have hcomplementMem : 1 - p ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hpMem.1, hpMem.2]
  have hcomplementSuper : 1 / 2 < 1 - p := by linarith
  have hsuper := resistance_convergesASAndL1_supercritical
    hcomplementMem hcomplementSuper
  have hmodel := modelParameter_one_sub hpMem
  have hspeed := vR_one_sub p hpMem
  unfold ConvergesASAndL1AtLinearRate at hsuper ⊢
  rw [hmodel] at hsuper
  constructor
  · have hpull :=
      (complementEnvironment_measurePreserving (modelParameter p)).quasiMeasurePreserving.ae
        hsuper.1
    filter_upwards [hpull] with environment henvironment
    have hneg := henvironment.neg
    convert hneg using 1
    · funext n
      rw [X_resistance_complement]
      ring
    · rw [hspeed]
      ring_nf
  · have hintegral : (fun n : ℕ ↦
        ∫ environment,
          |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) - vR p|
            ∂environmentMeasure (modelParameter p)) =
        fun n : ℕ ↦
          ∫ environment,
            |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
              vR (1 - p)|
              ∂environmentMeasure (unitInterval.symm (modelParameter p)) := by
      funext n
      have hmeas : AEStronglyMeasurable
          (fun environment : Environment ↦
            |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
              vR (1 - p)|)
          (environmentMeasure (unitInterval.symm (modelParameter p))) :=
        (((measurable_X .resistance (n + 1)).div_const
          (((n + 1 : ℕ) : ℝ))).sub measurable_const).abs.aestronglyMeasurable
      have hcomp :=
        (complementEnvironment_measurePreserving (modelParameter p)).hasLaw.integral_comp
          hmeas
      rw [← hcomp]
      apply integral_congr_ae
      filter_upwards with environment
      simp only [Function.comp_apply]
      rw [X_resistance_complement, hspeed]
      have hinside :
          -X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) - -vR p =
            -(X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
              vR p) := by
        ring
      rw [hinside, abs_neg]
    rw [hintegral]
    exact hsuper.2

/-! ## Deterministic resistance--distance squeeze -/

/-- Effective resistance is bounded above by graph distance in every realization. -/
theorem resistanceValue_le_distanceValue (n : ℕ) (environment : Environment) :
    resistanceValue n environment ≤ (distanceValue n environment : ℝ) :=
  (randomNetwork n environment).resistance_le_distance

theorem X_resistance_le_X_distance (n : ℕ) (environment : Environment) :
    X .resistance n environment ≤ X .distance n environment := by
  exact Real.log_le_log (resistanceValue_pos n environment)
    (resistanceValue_le_distanceValue n environment)

/-- Applying the upper comparison to the complemented environment gives the matching lower
comparison. -/
theorem X_resistance_sandwich (n : ℕ) (environment : Environment) :
    -X .distance n (complementEnvironment environment) ≤
        X .resistance n environment ∧
      X .resistance n environment ≤ X .distance n environment := by
  constructor
  · have h := X_resistance_le_X_distance n
      (complementEnvironment environment)
    rw [X_resistance_complement] at h
    linarith
  · exact X_resistance_le_X_distance n environment

/-- The critical distance input and the deterministic two-sided squeeze force the critical
resistance normalized logarithm to converge to zero both almost surely and in `L¹`. -/
theorem resistance_critical_convergesASAndL1
    (hcrit : gammaD (1 / 2) = 0) :
    ConvergesASAndL1AtLinearRate (1 / 2) .resistance 0 := by
  have hhalfMem : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hdistance := distance_subcritical_convergesASAndL1 hcrit
    (p := (1 / 2 : ℝ)) (by norm_num) le_rfl
  have hsymm : unitInterval.symm (modelParameter (1 / 2)) =
      modelParameter (1 / 2) := by
    apply Subtype.ext
    rw [unitInterval.coe_symm_eq, modelParameter_coe_of_mem hhalfMem]
    norm_num
  unfold ConvergesASAndL1AtLinearRate at hdistance ⊢
  constructor
  · have hdistanceTarget :
        ∀ᵐ environment
          ∂environmentMeasure (unitInterval.symm (modelParameter (1 / 2))),
          Tendsto
            (fun n : ℕ ↦
              X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ))
            atTop (𝓝 0) := by
      simpa only [hsymm] using hdistance.1
    have hdistanceComp :=
      (complementEnvironment_measurePreserving
        (modelParameter (1 / 2))).quasiMeasurePreserving.ae hdistanceTarget
    filter_upwards [hdistance.1, hdistanceComp] with environment hupper hlower
    have hlowerNeg :
        Tendsto
          (fun n : ℕ ↦
            -X .distance (n + 1) (complementEnvironment environment) /
              ((n + 1 : ℕ) : ℝ))
          atTop (𝓝 0) := by
      convert hlower.neg using 1
      · funext n
        ring
      · simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerNeg hupper
      (fun n ↦ by
        apply (div_le_div_iff_of_pos_right (by positivity)).2
        exact (X_resistance_sandwich (n + 1) environment).1)
      (fun n ↦ by
        apply (div_le_div_iff_of_pos_right (by positivity)).2
        exact (X_resistance_sandwich (n + 1) environment).2)
  · let distanceNorm : ℕ → Environment → ℝ := fun n environment ↦
      |X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|
    simp only [sub_zero]
    have hdistanceL1 : Tendsto
        (fun n : ℕ ↦
          ∫ environment, distanceNorm n environment
            ∂environmentMeasure (modelParameter (1 / 2)))
        atTop (𝓝 0) := by
      simpa only [distanceNorm, sub_zero] using hdistance.2
    have hcompIntegral : ∀ n : ℕ,
        (∫ environment,
          distanceNorm n (complementEnvironment environment)
            ∂environmentMeasure (modelParameter (1 / 2))) =
          ∫ environment, distanceNorm n environment
            ∂environmentMeasure (modelParameter (1 / 2)) := by
      intro n
      have hmeas : AEStronglyMeasurable (distanceNorm n)
          (environmentMeasure
            (unitInterval.symm (modelParameter (1 / 2)))) := by
        exact (((measurable_X .distance (n + 1)).div_const
          (((n + 1 : ℕ) : ℝ))).abs).aestronglyMeasurable
      have hcomp :=
        (complementEnvironment_measurePreserving
          (modelParameter (1 / 2))).hasLaw.integral_comp hmeas
      simpa only [Function.comp_apply, hsymm] using hcomp
    have hupper : Tendsto
        (fun n : ℕ ↦
          2 * ∫ environment, distanceNorm n environment
            ∂environmentMeasure (modelParameter (1 / 2)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hdistanceL1.const_mul 2
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _
    · apply Eventually.of_forall
      intro n
      have hR : Integrable
          (fun environment ↦
            |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|)
          (environmentMeasure (modelParameter (1 / 2))) :=
        ((integrable_X (modelParameter (1 / 2)) .resistance (n + 1)).div_const
          (((n + 1 : ℕ) : ℝ))).abs
      have hD : Integrable (distanceNorm n)
          (environmentMeasure (modelParameter (1 / 2))) :=
        ((integrable_X (modelParameter (1 / 2)) .distance (n + 1)).div_const
          (((n + 1 : ℕ) : ℝ))).abs
      have hDTarget : Integrable (distanceNorm n)
          (environmentMeasure
            (unitInterval.symm (modelParameter (1 / 2)))) := by
        simpa only [hsymm] using hD
      have hDComp : Integrable
          (fun environment ↦ distanceNorm n (complementEnvironment environment))
          (environmentMeasure (modelParameter (1 / 2))) :=
        (complementEnvironment_measurePreserving
          (modelParameter (1 / 2))).integrable_comp_of_integrable hDTarget
      calc
        (∫ environment,
            |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|
              ∂environmentMeasure (modelParameter (1 / 2))) ≤
            ∫ environment,
              (distanceNorm n (complementEnvironment environment) +
                distanceNorm n environment)
              ∂environmentMeasure (modelParameter (1 / 2)) := by
          apply integral_mono hR (hDComp.add hD)
          intro environment
          have hsandwich := X_resistance_sandwich (n + 1) environment
          have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
          have hcompNonneg :
              0 ≤ X .distance (n + 1) (complementEnvironment environment) := by
            change 0 ≤ Real.log (distanceValue (n + 1)
              (complementEnvironment environment))
            exact Real.log_nonneg (by
              exact_mod_cast (randomNetwork (n + 1)
                (complementEnvironment environment)).distance_bounds.1)
          have hdistNonneg : 0 ≤ X .distance (n + 1) environment := by
            change 0 ≤ Real.log (distanceValue (n + 1) environment)
            exact Real.log_nonneg (by
              exact_mod_cast (randomNetwork (n + 1) environment).distance_bounds.1)
          change |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ)| ≤
            |X .distance (n + 1) (complementEnvironment environment) /
                ((n + 1 : ℕ) : ℝ)| +
              |X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ)|
          rw [abs_of_nonneg (div_nonneg hcompNonneg hden.le),
            abs_of_nonneg (div_nonneg hdistNonneg hden.le), abs_le]
          have hsandwichLeft :
              -X .distance (n + 1) (complementEnvironment environment) /
                  ((n + 1 : ℕ) : ℝ) ≤
                X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) :=
            (div_le_div_iff_of_pos_right hden).2 hsandwich.1
          have hsandwichLeft' :
              -(X .distance (n + 1) (complementEnvironment environment) /
                  ((n + 1 : ℕ) : ℝ)) ≤
                X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) := by
            convert hsandwichLeft using 1
            ring
          have hsandwichRight :
              X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) ≤
                X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ) :=
            (div_le_div_iff_of_pos_right hden).2 hsandwich.2
          have hcompDivNonneg :
              0 ≤ X .distance (n + 1) (complementEnvironment environment) /
                ((n + 1 : ℕ) : ℝ) :=
            div_nonneg hcompNonneg hden.le
          have hdistDivNonneg :
              0 ≤ X .distance (n + 1) environment / ((n + 1 : ℕ) : ℝ) :=
            div_nonneg hdistNonneg hden.le
          constructor <;> linarith
        _ = 2 * ∫ environment, distanceNorm n environment
              ∂environmentMeasure (modelParameter (1 / 2)) := by
          rw [integral_add hDComp hD, hcompIntegral]
          ring
    · exact hupper

/-! ## The deterministic endpoint `p = 0` -/

/-- The environment in which every gate is parallel. -/
def allParallelEnvironment : Environment := fun _ ↦ false

@[simp]
theorem allParallelEnvironment_apply (word : Word) :
    allParallelEnvironment word = false := rfl

theorem bernoulliBool_zero :
    bernoulliBool (0 : unitInterval) = Measure.dirac false := by
  simp [bernoulliBool]

theorem environmentMeasure_zero :
    environmentMeasure (0 : unitInterval) = Measure.dirac allParallelEnvironment := by
  rw [environmentMeasure]
  simp only [bernoulliBool_zero, Measure.infinitePi_dirac]
  congr

/-- At the all-parallel endpoint, the depth-`n` effective resistance is exactly `2⁻ⁿ`. -/
theorem resistanceValue_allParallel (n : ℕ) :
    resistanceValue n allParallelEnvironment = ((2 : ℝ) ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [resistanceValue_succ]
      simp only [allParallelEnvironment_apply, Bool.false_eq_true, ↓reduceIte]
      have hleft : Environment.subtree [false] allParallelEnvironment =
          allParallelEnvironment := by
        ext word
        rfl
      have hright : Environment.subtree [true] allParallelEnvironment =
          allParallelEnvironment := by
        ext word
        rfl
      rw [hleft, hright, ih, pow_succ]
      have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring

theorem firstMoment_resistance_zero (n : ℕ) :
    firstMoment (0 : unitInterval) .resistance n = ((2 : ℝ) ^ n)⁻¹ := by
  rw [firstMoment, environmentMeasure_zero]
  simp [Z, resistanceValue_allParallel]

theorem meanLog_resistance_zero (n : ℕ) :
    meanLog (0 : unitInterval) .resistance n =
      -(n : ℝ) * Real.log 2 := by
  rw [meanLog, environmentMeasure_zero]
  simp only [integral_dirac, X, Z, resistanceValue_allParallel]
  rw [Real.log_inv, Real.log_pow]
  ring

theorem normalizedMeanLog_resistance_zero (n : ℕ) :
    normalizedMeanLog (0 : unitInterval) .resistance n = -Real.log 2 := by
  rw [normalizedMeanLog, meanLog_resistance_zero]
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

theorem normalizedLogFirstMoment_resistance_zero (n : ℕ) :
    normalizedLogFirstMoment (0 : unitInterval) .resistance n = -Real.log 2 := by
  rw [normalizedLogFirstMoment, firstMoment_resistance_zero, Real.log_inv,
    Real.log_pow]
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- Both resistance exponents take their exact deterministic endpoint value. -/
theorem vR_zero : vR 0 = -Real.log 2 := by
  rw [vR]
  have hmodel : modelParameter 0 = (0 : unitInterval) := by
    exact modelParameter_eq_of_mem (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  rw [hmodel]
  exact chosenSequentialLimit_eq
    (by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ -Real.log 2)
        atTop (𝓝 (-Real.log 2))) using 1
      funext n
      exact normalizedMeanLog_resistance_zero n)

theorem gammaR_zero : gammaR 0 = -Real.log 2 := by
  rw [gammaR]
  have hmodel : modelParameter 0 = (0 : unitInterval) := by
    exact modelParameter_eq_of_mem (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  rw [hmodel]
  exact chosenSequentialLimit_eq
    (by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ -Real.log 2)
        atTop (𝓝 (-Real.log 2))) using 1
      funext n
      exact normalizedLogFirstMoment_resistance_zero n)

theorem resistance_zero_convergesASAndL1 :
    ConvergesASAndL1AtLinearRate 0 .resistance (-Real.log 2) := by
  have hmodel : modelParameter 0 = (0 : unitInterval) := by
    exact modelParameter_eq_of_mem (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  unfold ConvergesASAndL1AtLinearRate
  rw [hmodel, environmentMeasure_zero]
  constructor
  · rw [ae_dirac_eq, eventually_pure]
    simp only [X, Z, resistanceValue_allParallel]
    have heq : (fun n : ℕ ↦
        Real.log (((2 : ℝ) ^ (n + 1))⁻¹) / ((n + 1 : ℕ) : ℝ)) =
        fun _ : ℕ ↦ -Real.log 2 := by
      funext n
      rw [Real.log_inv, Real.log_pow]
      have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact tendsto_const_nhds
  · rw [show (fun n : ℕ ↦
        ∫ environment,
          |X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
            -Real.log 2| ∂Measure.dirac allParallelEnvironment) =
        fun n : ℕ ↦
          |X .resistance (n + 1) allParallelEnvironment /
              ((n + 1 : ℕ) : ℝ) - -Real.log 2| by
      funext n
      rw [integral_dirac]]
    simp only [X, Z, resistanceValue_allParallel]
    have heq : (fun n : ℕ ↦
        |Real.log (((2 : ℝ) ^ (n + 1))⁻¹) / ((n + 1 : ℕ) : ℝ) -
          -Real.log 2|) = fun _ : ℕ ↦ 0 := by
      funext n
      rw [Real.log_inv, Real.log_pow]
      have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [show -(↑(n + 1) * Real.log 2) / ↑(n + 1) = -Real.log 2 by
        field_simp]
      simp
    rw [heq]
    exact tendsto_const_nhds

/-! ## Normalized first-moment recursion -/

/-- Resistance divided by its strictly positive first moment. -/
noncomputable def normalizedResistance (p : unitInterval) (n : ℕ)
    (environment : Environment) : ℝ :=
  Z .resistance n environment / firstMoment p .resistance n

theorem normalizedResistance_pos (p : unitInterval) (n : ℕ)
    (environment : Environment) : 0 < normalizedResistance p n environment := by
  exact div_pos (Z_pos .resistance n environment)
    (firstMoment_pos p .resistance n)

private noncomputable def resistanceSeriesDescendant (n : ℕ)
    (environment : Environment) : ℝ :=
  Z .resistance n (Environment.subtree [false] environment) +
    Z .resistance n (Environment.subtree [true] environment)

private noncomputable def resistanceParallelDescendant (n : ℕ)
    (environment : Environment) : ℝ :=
  Z .resistance n (Environment.subtree [false] environment) *
      Z .resistance n (Environment.subtree [true] environment) /
    (Z .resistance n (Environment.subtree [false] environment) +
      Z .resistance n (Environment.subtree [true] environment))

private noncomputable def normalizedResistanceParallelDescendant
    (p : unitInterval) (n : ℕ) (environment : Environment) : ℝ :=
  normalizedResistance p n (Environment.subtree [false] environment) *
      normalizedResistance p n (Environment.subtree [true] environment) /
    (normalizedResistance p n (Environment.subtree [false] environment) +
      normalizedResistance p n (Environment.subtree [true] environment))

/-- The normalized harmonic correction made from the two independent descendant copies. -/
noncomputable def resistanceParallelCorrection (p : unitInterval) (n : ℕ) : ℝ :=
  ∫ environment, normalizedResistanceParallelDescendant p n environment
    ∂environmentMeasure p

private def seriesRootWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 1 else 0

private def parallelRootWeight (environment : Environment) : ℝ :=
  if coordinate root environment then 0 else 1

private theorem measurable_seriesRootWeight : Measurable seriesRootWeight :=
  (measurable_of_finite (fun bit : Bool ↦ if bit then (1 : ℝ) else 0)).comp
    (measurable_coordinate root)

private theorem measurable_parallelRootWeight : Measurable parallelRootWeight :=
  (measurable_of_finite (fun bit : Bool ↦ if bit then (0 : ℝ) else 1)).comp
    (measurable_coordinate root)

private theorem measurable_resistanceSeriesDescendant (n : ℕ) :
    Measurable (resistanceSeriesDescendant n) := by
  exact ((measurable_Z .resistance n).comp (measurable_subtreeShift [false])).add
    ((measurable_Z .resistance n).comp (measurable_subtreeShift [true]))

private theorem measurable_resistanceParallelDescendant (n : ℕ) :
    Measurable (resistanceParallelDescendant n) := by
  exact (((measurable_Z .resistance n).comp
      (measurable_subtreeShift [false])).mul
        ((measurable_Z .resistance n).comp (measurable_subtreeShift [true]))).div
    (((measurable_Z .resistance n).comp
      (measurable_subtreeShift [false])).add
        ((measurable_Z .resistance n).comp (measurable_subtreeShift [true])))

private theorem integrable_resistance_subtree
    (p : unitInterval) (n : ℕ) (word : Word) :
    Integrable
      (fun environment ↦ Z .resistance n (Environment.subtree word environment))
      (environmentMeasure p) := by
  simpa only [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p word).integrable_comp_of_integrable
      (integrable_Z p .resistance n)

private theorem integral_resistance_subtree
    (p : unitInterval) (n : ℕ) (word : Word) :
    (∫ environment, Z .resistance n (Environment.subtree word environment)
      ∂environmentMeasure p) = firstMoment p .resistance n := by
  simpa only [firstMoment, Environment.subtree, Function.comp_def] using
    (subtreeShift_hasLaw p word).integral_comp
      (measurable_Z .resistance n).aestronglyMeasurable

private theorem integrable_resistanceSeriesDescendant
    (p : unitInterval) (n : ℕ) :
    Integrable (resistanceSeriesDescendant n) (environmentMeasure p) := by
  exact (integrable_resistance_subtree p n [false]).add
    (integrable_resistance_subtree p n [true])

private theorem integrable_resistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    Integrable (resistanceParallelDescendant n) (environmentMeasure p) := by
  apply Integrable.mono' (integrable_resistance_subtree p n [false])
    (measurable_resistanceParallelDescendant n).aestronglyMeasurable
  filter_upwards with environment
  let left := Z .resistance n (Environment.subtree [false] environment)
  let right := Z .resistance n (Environment.subtree [true] environment)
  have hleft : 0 < left := Z_pos .resistance n _
  have hright : 0 < right := Z_pos .resistance n _
  have hparallel : 0 ≤ left * right / (left + right) :=
    (div_pos (mul_pos hleft hright) (add_pos hleft hright)).le
  change |left * right / (left + right)| ≤ left
  rw [abs_of_nonneg hparallel]
  apply (div_le_iff₀ (add_pos hleft hright)).2
  nlinarith

private theorem integral_seriesRootWeight (p : unitInterval) :
    (∫ environment, seriesRootWeight environment ∂environmentMeasure p) = (p : ℝ) := by
  calc
    (∫ environment, seriesRootWeight environment ∂environmentMeasure p) =
        ∫ bit, (if bit then (1 : ℝ) else 0) ∂bernoulliBool p := by
      simpa only [seriesRootWeight, Function.comp_def] using
        (coordinate_hasLaw p root).integral_comp
          (measurable_of_finite
            (fun bit : Bool ↦ if bit then (1 : ℝ) else 0)).aestronglyMeasurable
    _ = (p : ℝ) := by
      rw [bernoulliBool, integral_bernoulliMeasure]
      simp

private theorem integral_parallelRootWeight (p : unitInterval) :
    (∫ environment, parallelRootWeight environment ∂environmentMeasure p) =
      1 - (p : ℝ) := by
  calc
    (∫ environment, parallelRootWeight environment ∂environmentMeasure p) =
        ∫ bit, (if bit then (0 : ℝ) else 1) ∂bernoulliBool p := by
      simpa only [parallelRootWeight, Function.comp_def] using
        (coordinate_hasLaw p root).integral_comp
          (measurable_of_finite
            (fun bit : Bool ↦ if bit then (0 : ℝ) else 1)).aestronglyMeasurable
    _ = 1 - (p : ℝ) := by
      rw [bernoulliBool, integral_bernoulliMeasure]
      simp

private theorem integrable_seriesRootWeight (p : unitInterval) :
    Integrable seriesRootWeight (environmentMeasure p) := by
  apply Integrable.of_bound measurable_seriesRootWeight.aestronglyMeasurable 1
  filter_upwards with environment
  simp only [seriesRootWeight]
  split <;> norm_num

private theorem integrable_parallelRootWeight (p : unitInterval) :
    Integrable parallelRootWeight (environmentMeasure p) := by
  apply Integrable.of_bound measurable_parallelRootWeight.aestronglyMeasurable 1
  filter_upwards with environment
  simp only [parallelRootWeight]
  split <;> norm_num

private theorem seriesRootWeight_indep_resistanceSeriesDescendant
    (p : unitInterval) (n : ℕ) :
    seriesRootWeight ⟂ᵢ[environmentMeasure p] resistanceSeriesDescendant n := by
  have hgate : Measurable (fun environments : Environment × Environment ↦
      Z .resistance n environments.1 + Z .resistance n environments.2) :=
    ((measurable_Z .resistance n).comp measurable_fst).add
      ((measurable_Z .resistance n).comp measurable_snd)
  change (fun environment ↦ if environment root then (1 : ℝ) else 0)
    ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        Z .resistance n (Environment.subtree [false] environment) +
          Z .resistance n (Environment.subtree [true] environment))
  have hindep := (root_subtrees_indep p).comp
    (measurable_of_finite (fun bit : Bool ↦ if bit then (1 : ℝ) else 0)) hgate
  convert hindep using 1 <;> rfl

private theorem parallelRootWeight_indep_resistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    parallelRootWeight ⟂ᵢ[environmentMeasure p]
      resistanceParallelDescendant n := by
  have hleft : Measurable (fun environments : Environment × Environment ↦
      Z .resistance n environments.1) :=
    (measurable_Z .resistance n).comp measurable_fst
  have hright : Measurable (fun environments : Environment × Environment ↦
      Z .resistance n environments.2) :=
    (measurable_Z .resistance n).comp measurable_snd
  have hgate : Measurable (fun environments : Environment × Environment ↦
      Z .resistance n environments.1 * Z .resistance n environments.2 /
        (Z .resistance n environments.1 + Z .resistance n environments.2)) :=
    (hleft.mul hright).div (hleft.add hright)
  change (fun environment ↦ if environment root then (0 : ℝ) else 1)
    ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        Z .resistance n (Environment.subtree [false] environment) *
            Z .resistance n (Environment.subtree [true] environment) /
          (Z .resistance n (Environment.subtree [false] environment) +
            Z .resistance n (Environment.subtree [true] environment)))
  have hindep := (root_subtrees_indep p).comp
    (measurable_of_finite (fun bit : Bool ↦ if bit then (0 : ℝ) else 1)) hgate
  convert hindep using 1 <;> rfl

private theorem integrable_seriesRoot_mul_resistanceSeriesDescendant
    (p : unitInterval) (n : ℕ) :
    Integrable (fun environment ↦
      seriesRootWeight environment * resistanceSeriesDescendant n environment)
      (environmentMeasure p) := by
  change Integrable (seriesRootWeight * resistanceSeriesDescendant n)
    (environmentMeasure p)
  exact (seriesRootWeight_indep_resistanceSeriesDescendant p n).integrable_mul
    (integrable_seriesRootWeight p)
    (integrable_resistanceSeriesDescendant p n)

private theorem integrable_parallelRoot_mul_resistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    Integrable (fun environment ↦
      parallelRootWeight environment * resistanceParallelDescendant n environment)
      (environmentMeasure p) := by
  change Integrable (parallelRootWeight * resistanceParallelDescendant n)
    (environmentMeasure p)
  exact (parallelRootWeight_indep_resistanceParallelDescendant p n).integrable_mul
    (integrable_parallelRootWeight p)
    (integrable_resistanceParallelDescendant p n)

private theorem integral_resistanceSeriesDescendant
    (p : unitInterval) (n : ℕ) :
    (∫ environment, resistanceSeriesDescendant n environment
      ∂environmentMeasure p) = 2 * firstMoment p .resistance n := by
  rw [show (∫ environment, resistanceSeriesDescendant n environment
      ∂environmentMeasure p) =
      ∫ environment,
        Z .resistance n (Environment.subtree [false] environment) +
          Z .resistance n (Environment.subtree [true] environment)
        ∂environmentMeasure p by rfl]
  rw [integral_add (integrable_resistance_subtree p n [false])
    (integrable_resistance_subtree p n [true]),
    integral_resistance_subtree p n [false],
    integral_resistance_subtree p n [true]]
  ring

private theorem resistanceParallelDescendant_eq_scaled
    (p : unitInterval) (n : ℕ) (environment : Environment) :
    resistanceParallelDescendant n environment =
      firstMoment p .resistance n *
        normalizedResistanceParallelDescendant p n environment := by
  let moment := firstMoment p .resistance n
  let left := Z .resistance n (Environment.subtree [false] environment)
  let right := Z .resistance n (Environment.subtree [true] environment)
  have hmoment : 0 < moment := firstMoment_pos p .resistance n
  have hleft : 0 < left := Z_pos .resistance n _
  have hright : 0 < right := Z_pos .resistance n _
  change left * right / (left + right) =
    moment * ((left / moment) * (right / moment) /
      (left / moment + right / moment))
  field_simp [hmoment.ne', (add_pos hleft hright).ne']

private theorem integral_resistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    (∫ environment, resistanceParallelDescendant n environment
      ∂environmentMeasure p) =
      firstMoment p .resistance n * resistanceParallelCorrection p n := by
  calc
    (∫ environment, resistanceParallelDescendant n environment
      ∂environmentMeasure p) =
        ∫ environment,
          firstMoment p .resistance n *
            normalizedResistanceParallelDescendant p n environment
          ∂environmentMeasure p := by
      apply integral_congr_ae
      filter_upwards with environment
      exact resistanceParallelDescendant_eq_scaled p n environment
    _ = firstMoment p .resistance n * resistanceParallelCorrection p n := by
      rw [integral_const_mul, resistanceParallelCorrection]

private theorem integral_seriesRoot_mul_resistanceSeriesDescendant
    (p : unitInterval) (n : ℕ) :
    (∫ environment,
      seriesRootWeight environment * resistanceSeriesDescendant n environment
      ∂environmentMeasure p) =
      (p : ℝ) * (2 * firstMoment p .resistance n) := by
  have hfactor :=
    IndepFun.integral_fun_mul_eq_mul_integral
      (seriesRootWeight_indep_resistanceSeriesDescendant p n)
    measurable_seriesRootWeight.aestronglyMeasurable
      (measurable_resistanceSeriesDescendant n).aestronglyMeasurable
  rw [hfactor, integral_seriesRootWeight, integral_resistanceSeriesDescendant]

private theorem integral_parallelRoot_mul_resistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    (∫ environment,
      parallelRootWeight environment * resistanceParallelDescendant n environment
      ∂environmentMeasure p) =
      (1 - (p : ℝ)) *
        (firstMoment p .resistance n * resistanceParallelCorrection p n) := by
  have hfactor :=
    IndepFun.integral_fun_mul_eq_mul_integral
      (parallelRootWeight_indep_resistanceParallelDescendant p n)
    measurable_parallelRootWeight.aestronglyMeasurable
      (measurable_resistanceParallelDescendant n).aestronglyMeasurable
  rw [hfactor, integral_parallelRootWeight, integral_resistanceParallelDescendant]

private theorem resistance_succ_eq_weighted_descendants
    (n : ℕ) (environment : Environment) :
    Z .resistance (n + 1) environment =
      seriesRootWeight environment * resistanceSeriesDescendant n environment +
        parallelRootWeight environment * resistanceParallelDescendant n environment := by
  rw [Z_succ]
  by_cases hroot : environment root
  · simp [hroot, seriesRootWeight, parallelRootWeight, coordinate,
      resistanceSeriesDescendant, seriesGate]
  · rw [if_neg hroot]
    simp only [seriesRootWeight, parallelRootWeight, coordinate, hroot,
      Bool.false_eq_true, ↓reduceIte, zero_mul, one_mul, zero_add]
    exact parallelGate_resistance_eq_harmonic
      (Z_pos .resistance n _) (Z_pos .resistance n _)

/-- Exact normalized one-step first-moment identity for resistance. -/
theorem firstMoment_resistance_succ_exact (p : unitInterval) (n : ℕ) :
    firstMoment p .resistance (n + 1) =
      firstMoment p .resistance n *
        (2 * (p : ℝ) + (1 - (p : ℝ)) * resistanceParallelCorrection p n) := by
  rw [firstMoment]
  calc
    (∫ environment, Z .resistance (n + 1) environment
      ∂environmentMeasure p) =
        ∫ environment,
          (seriesRootWeight environment * resistanceSeriesDescendant n environment +
            parallelRootWeight environment *
              resistanceParallelDescendant n environment)
          ∂environmentMeasure p := by
      apply integral_congr_ae
      filter_upwards with environment
      exact resistance_succ_eq_weighted_descendants n environment
    _ = (∫ environment,
          seriesRootWeight environment * resistanceSeriesDescendant n environment
          ∂environmentMeasure p) +
        ∫ environment,
          parallelRootWeight environment * resistanceParallelDescendant n environment
          ∂environmentMeasure p := by
      rw [integral_add
        (integrable_seriesRoot_mul_resistanceSeriesDescendant p n)
        (integrable_parallelRoot_mul_resistanceParallelDescendant p n)]
    _ = firstMoment p .resistance n *
        (2 * (p : ℝ) + (1 - (p : ℝ)) * resistanceParallelCorrection p n) := by
      rw [integral_seriesRoot_mul_resistanceSeriesDescendant,
        integral_parallelRoot_mul_resistanceParallelDescendant]
      ring

theorem measurable_normalizedResistance (p : unitInterval) (n : ℕ) :
    Measurable (normalizedResistance p n) :=
  (measurable_Z .resistance n).div_const (firstMoment p .resistance n)

theorem integrable_normalizedResistance (p : unitInterval) (n : ℕ) :
    Integrable (normalizedResistance p n) (environmentMeasure p) :=
  (integrable_Z p .resistance n).div_const (firstMoment p .resistance n)

/-- The normalized resistance has mean one. -/
theorem integral_normalizedResistance (p : unitInterval) (n : ℕ) :
    (∫ environment, normalizedResistance p n environment ∂environmentMeasure p) = 1 := by
  unfold normalizedResistance
  rw [integral_div]
  change firstMoment p .resistance n / firstMoment p .resistance n = 1
  exact div_self (firstMoment_pos p .resistance n).ne'

private theorem normalizedResistance_eq_exp_logDifference
    (p : unitInterval) (n : ℕ) (environment : Environment) :
    normalizedResistance p (n + 1) environment =
      Real.exp (((n + 1 : ℕ) : ℝ) *
        (X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
          normalizedLogFirstMoment p .resistance n)) := by
  have hz := Z_pos .resistance (n + 1) environment
  have hm := firstMoment_pos p .resistance (n + 1)
  rw [normalizedResistance]
  rw [show Z .resistance (n + 1) environment /
      firstMoment p .resistance (n + 1) =
        Real.exp (Real.log (Z .resistance (n + 1) environment) -
          Real.log (firstMoment p .resistance (n + 1))) by
    rw [Real.exp_sub, Real.exp_log hz, Real.exp_log hm]]
  congr 1
  rw [X, normalizedLogFirstMoment]
  have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- If the annealed resistance exponent is strictly larger than the sample speed, the
first-moment normalized resistance vanishes almost surely. -/
theorem normalizedResistance_ae_tendsto_zero_of_gammaR_gt_vR
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    ∀ᵐ environment ∂environmentMeasure (modelParameter p),
      Tendsto
        (fun n : ℕ ↦ normalizedResistance (modelParameter p) (n + 1) environment)
        atTop (𝓝 0) := by
  have hsample := (resistance_subcritical_convergesASAndL1 hpMem hp).1
  have hmoment := normalizedLogFirstMoment_tendsto_gammaR p
  filter_upwards [hsample] with environment henvironment
  have hdifference := henvironment.sub hmoment
  have hgeneration : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexponent : Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) *
        (X .resistance (n + 1) environment / ((n + 1 : ℕ) : ℝ) -
          normalizedLogFirstMoment (modelParameter p) .resistance n))
      atTop atBot :=
    hgeneration.atTop_mul_neg (sub_neg.mpr hgap) hdifference
  have hexp := Real.tendsto_exp_atBot.comp hexponent
  convert hexp using 1
  funext n
  exact normalizedResistance_eq_exp_logDifference
    (modelParameter p) n environment

theorem normalizedResistance_ae_tendsto_zero_of_gammaR_gt_vR'
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    ∀ᵐ environment ∂environmentMeasure (modelParameter p),
      Tendsto
        (fun n : ℕ ↦ normalizedResistance (modelParameter p) n environment)
        atTop (𝓝 0) := by
  filter_upwards [normalizedResistance_ae_tendsto_zero_of_gammaR_gt_vR
    hpMem hp hgap] with environment henvironment
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa only [Nat.add_comm] using henvironment

private noncomputable def leftNormalizedResistance
    (p : unitInterval) (n : ℕ) (environment : Environment) : ℝ :=
  normalizedResistance p n (Environment.subtree [false] environment)

private noncomputable def rightNormalizedResistance
    (p : unitInterval) (n : ℕ) (environment : Environment) : ℝ :=
  normalizedResistance p n (Environment.subtree [true] environment)

private theorem measurable_leftNormalizedResistance (p : unitInterval) (n : ℕ) :
    Measurable (leftNormalizedResistance p n) :=
  (measurable_normalizedResistance p n).comp (measurable_subtreeShift [false])

private theorem measurable_rightNormalizedResistance (p : unitInterval) (n : ℕ) :
    Measurable (rightNormalizedResistance p n) :=
  (measurable_normalizedResistance p n).comp (measurable_subtreeShift [true])

private theorem integrable_leftNormalizedResistance (p : unitInterval) (n : ℕ) :
    Integrable (leftNormalizedResistance p n) (environmentMeasure p) := by
  unfold leftNormalizedResistance Environment.subtree
  exact (subtreeShift_measurePreserving p [false]).integrable_comp_of_integrable
    (integrable_normalizedResistance p n)

private theorem integrable_rightNormalizedResistance (p : unitInterval) (n : ℕ) :
    Integrable (rightNormalizedResistance p n) (environmentMeasure p) := by
  unfold rightNormalizedResistance Environment.subtree
  exact (subtreeShift_measurePreserving p [true]).integrable_comp_of_integrable
    (integrable_normalizedResistance p n)

private theorem integral_leftNormalizedResistance (p : unitInterval) (n : ℕ) :
    (∫ environment, leftNormalizedResistance p n environment
      ∂environmentMeasure p) = 1 := by
  simpa only [leftNormalizedResistance, Environment.subtree, Function.comp_def,
    integral_normalizedResistance] using
    (subtreeShift_hasLaw p [false]).integral_comp
      (measurable_normalizedResistance p n).aestronglyMeasurable

private theorem integral_rightNormalizedResistance (p : unitInterval) (n : ℕ) :
    (∫ environment, rightNormalizedResistance p n environment
      ∂environmentMeasure p) = 1 := by
  simpa only [rightNormalizedResistance, Environment.subtree, Function.comp_def,
    integral_normalizedResistance] using
    (subtreeShift_hasLaw p [true]).integral_comp
      (measurable_normalizedResistance p n).aestronglyMeasurable

private theorem left_right_normalizedResistance_indep
    (p : unitInterval) (n : ℕ) :
    leftNormalizedResistance p n ⟂ᵢ[environmentMeasure p]
      rightNormalizedResistance p n := by
  have hindep := (left_right_Z_indep p .resistance n).comp
    (measurable_id.div_const (firstMoment p .resistance n))
    (measurable_id.div_const (firstMoment p .resistance n))
  change (fun environment ↦
      Z .resistance n (Environment.subtree [false] environment) /
        firstMoment p .resistance n)
    ⟂ᵢ[environmentMeasure p]
      (fun environment ↦
        Z .resistance n (Environment.subtree [true] environment) /
          firstMoment p .resistance n)
  convert hindep using 1 <;> rfl

private noncomputable def normalizedTailWeight
    (p : unitInterval) (n : ℕ) (threshold : ℝ) (environment : Environment) : ℝ :=
  if threshold ≤ leftNormalizedResistance p n environment then 1 else 0

private theorem measurable_normalizedTailWeight
    (p : unitInterval) (n : ℕ) (threshold : ℝ) :
    Measurable (normalizedTailWeight p n threshold) := by
  unfold normalizedTailWeight
  exact measurable_const.piecewise
    (measurableSet_Ici.preimage (measurable_leftNormalizedResistance p n))
    measurable_const

private theorem integrable_normalizedTailWeight
    (p : unitInterval) (n : ℕ) (threshold : ℝ) :
    Integrable (normalizedTailWeight p n threshold) (environmentMeasure p) := by
  apply Integrable.of_bound
    (measurable_normalizedTailWeight p n threshold).aestronglyMeasurable 1
  filter_upwards with environment
  unfold normalizedTailWeight
  split <;> norm_num

private theorem normalizedTailWeight_indep_right
    (p : unitInterval) (n : ℕ) (threshold : ℝ) :
    normalizedTailWeight p n threshold ⟂ᵢ[environmentMeasure p]
      rightNormalizedResistance p n := by
  change (fun environment ↦
      if threshold ≤ leftNormalizedResistance p n environment then (1 : ℝ) else 0)
    ⟂ᵢ[environmentMeasure p] rightNormalizedResistance p n
  exact (left_right_normalizedResistance_indep p n).comp
    (measurable_const.piecewise measurableSet_Ici measurable_const) measurable_id

private theorem integral_normalizedTailWeight
    (p : unitInterval) (n : ℕ) (threshold : ℝ) :
    (∫ environment, normalizedTailWeight p n threshold environment
      ∂environmentMeasure p) =
      (environmentMeasure p).real
        {environment | threshold ≤ leftNormalizedResistance p n environment} := by
  let tail : Set Environment :=
    {environment | threshold ≤ leftNormalizedResistance p n environment}
  have htail : MeasurableSet tail :=
    measurableSet_Ici.preimage (measurable_leftNormalizedResistance p n)
  have hfun : normalizedTailWeight p n threshold = tail.indicator 1 := by
    funext environment
    by_cases h : threshold ≤ leftNormalizedResistance p n environment
    · simp [normalizedTailWeight, tail, h]
    · simp [normalizedTailWeight, tail, h]
  rw [hfun, integral_indicator_one htail]

private theorem integral_normalizedTailWeight_mul_right
    (p : unitInterval) (n : ℕ) (threshold : ℝ) :
    (∫ environment,
      normalizedTailWeight p n threshold environment *
        rightNormalizedResistance p n environment
      ∂environmentMeasure p) =
      (environmentMeasure p).real
        {environment | threshold ≤ leftNormalizedResistance p n environment} := by
  have hfactor := IndepFun.integral_fun_mul_eq_mul_integral
    (normalizedTailWeight_indep_right p n threshold)
    (measurable_normalizedTailWeight p n threshold).aestronglyMeasurable
    (measurable_rightNormalizedResistance p n).aestronglyMeasurable
  rw [hfactor, integral_normalizedTailWeight,
    integral_rightNormalizedResistance, mul_one]

private theorem measurable_normalizedResistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    Measurable (normalizedResistanceParallelDescendant p n) := by
  change Measurable (fun environment ↦
    leftNormalizedResistance p n environment *
        rightNormalizedResistance p n environment /
      (leftNormalizedResistance p n environment +
        rightNormalizedResistance p n environment))
  exact ((measurable_leftNormalizedResistance p n).mul
    (measurable_rightNormalizedResistance p n)).div
      ((measurable_leftNormalizedResistance p n).add
        (measurable_rightNormalizedResistance p n))

private theorem integrable_normalizedResistanceParallelDescendant
    (p : unitInterval) (n : ℕ) :
    Integrable (normalizedResistanceParallelDescendant p n)
      (environmentMeasure p) := by
  apply Integrable.mono' (integrable_leftNormalizedResistance p n)
    (measurable_normalizedResistanceParallelDescendant p n).aestronglyMeasurable
  filter_upwards with environment
  let left := leftNormalizedResistance p n environment
  let right := rightNormalizedResistance p n environment
  have hleft : 0 < left := normalizedResistance_pos p n _
  have hright : 0 < right := normalizedResistance_pos p n _
  have hparallel : 0 ≤ left * right / (left + right) :=
    (div_pos (mul_pos hleft hright) (add_pos hleft hright)).le
  change |left * right / (left + right)| ≤ left
  rw [abs_of_nonneg hparallel]
  apply (div_le_iff₀ (add_pos hleft hright)).2
  nlinarith

theorem resistanceParallelCorrection_nonneg (p : unitInterval) (n : ℕ) :
    0 ≤ resistanceParallelCorrection p n := by
  rw [resistanceParallelCorrection]
  apply integral_nonneg
  intro environment
  exact (div_pos
    (mul_pos (normalizedResistance_pos p n _)
      (normalizedResistance_pos p n _))
    (add_pos (normalizedResistance_pos p n _)
      (normalizedResistance_pos p n _))).le

private theorem resistanceParallelCorrection_le_threshold_add_tail
    (p : unitInterval) (n : ℕ) {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    resistanceParallelCorrection p n ≤ threshold +
      (environmentMeasure p).real
        {environment | threshold ≤ leftNormalizedResistance p n environment} := by
  have hproduct : Integrable (fun environment ↦
      normalizedTailWeight p n threshold environment *
        rightNormalizedResistance p n environment) (environmentMeasure p) := by
    change Integrable
      (normalizedTailWeight p n threshold * rightNormalizedResistance p n)
      (environmentMeasure p)
    exact (normalizedTailWeight_indep_right p n threshold).integrable_mul
      (integrable_normalizedTailWeight p n threshold)
      (integrable_rightNormalizedResistance p n)
  calc
    resistanceParallelCorrection p n =
        ∫ environment, normalizedResistanceParallelDescendant p n environment
          ∂environmentMeasure p := rfl
    _ ≤ ∫ environment,
          (threshold + normalizedTailWeight p n threshold environment *
            rightNormalizedResistance p n environment)
          ∂environmentMeasure p := by
      apply integral_mono
        (integrable_normalizedResistanceParallelDescendant p n)
        ((integrable_const threshold).add hproduct)
      intro environment
      let left := leftNormalizedResistance p n environment
      let right := rightNormalizedResistance p n environment
      have hleft : 0 < left := normalizedResistance_pos p n _
      have hright : 0 < right := normalizedResistance_pos p n _
      have hleLeft : left * right / (left + right) ≤ left := by
        apply (div_le_iff₀ (add_pos hleft hright)).2
        nlinarith
      have hleRight : left * right / (left + right) ≤ right := by
        apply (div_le_iff₀ (add_pos hleft hright)).2
        nlinarith
      change left * right / (left + right) ≤
        threshold + (if threshold ≤ left then 1 else 0) * right
      by_cases htail : threshold ≤ left
      · simp only [htail, ↓reduceIte, one_mul]
        linarith
      · simp only [htail, ↓reduceIte, zero_mul, add_zero]
        exact hleLeft.trans (le_of_not_ge htail)
    _ = threshold +
        (environmentMeasure p).real
          {environment | threshold ≤ leftNormalizedResistance p n environment} := by
      rw [integral_add (integrable_const threshold) hproduct, integral_const,
        integral_normalizedTailWeight_mul_right]
      simp only [smul_eq_mul, probReal_univ, one_mul]

private theorem leftNormalizedResistance_tail_tendsto_zero
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) {threshold : ℝ} (hthreshold : 0 < threshold) :
    Tendsto
      (fun n : ℕ ↦
        (environmentMeasure (modelParameter p)).real
          {environment |
            threshold ≤ leftNormalizedResistance (modelParameter p) n environment})
      atTop (𝓝 0) := by
  have hbase := normalizedResistance_ae_tendsto_zero_of_gammaR_gt_vR'
    hpMem hp hgap
  have hleft :
      ∀ᵐ environment ∂environmentMeasure (modelParameter p),
        Tendsto
          (fun n : ℕ ↦
            leftNormalizedResistance (modelParameter p) n environment)
          atTop (𝓝 0) := by
    let subtreeMap := subtreeShift_measurePreserving
      (modelParameter p) [false]
    have hpull := subtreeMap.quasiMeasurePreserving.ae hbase
    simpa only [leftNormalizedResistance, Environment.subtree] using hpull
  have hinMeasure : TendstoInMeasure (environmentMeasure (modelParameter p))
      (fun n ↦ leftNormalizedResistance (modelParameter p) n) atTop 0 :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (measurable_leftNormalizedResistance
        (modelParameter p) n).aestronglyMeasurable) hleft
  have htail :=
    (tendstoInMeasure_iff_measureReal_norm.mp hinMeasure) threshold hthreshold
  convert htail using 1
  funext n
  congr 1
  ext environment
  simp only [mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
  change threshold ≤ normalizedResistance (modelParameter p) n
      (Environment.subtree [false] environment) ↔
    threshold ≤ |normalizedResistance (modelParameter p) n
      (Environment.subtree [false] environment)|
  rw [abs_of_pos (normalizedResistance_pos (modelParameter p) n _)]

/-- Under the strict annealed/sample speed gap, the normalized parallel correction vanishes. -/
theorem resistanceParallelCorrection_tendsto_zero_of_gammaR_gt_vR
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    Tendsto (resistanceParallelCorrection (modelParameter p)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hthreshold : 0 < epsilon / 2 := half_pos hepsilon
  have htail := leftNormalizedResistance_tail_tendsto_zero
    hpMem hp hgap hthreshold
  have hevent : ∀ᶠ n in atTop,
      (environmentMeasure (modelParameter p)).real
          {environment |
            epsilon / 2 ≤
              leftNormalizedResistance (modelParameter p) n environment} <
        epsilon / 2 :=
    (tendsto_order.1 htail).2 _ hthreshold
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, fun n hnN ↦ ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (resistanceParallelCorrection_nonneg (modelParameter p) n)]
  calc
    resistanceParallelCorrection (modelParameter p) n ≤ epsilon / 2 +
        (environmentMeasure (modelParameter p)).real
          {environment |
            epsilon / 2 ≤
              leftNormalizedResistance (modelParameter p) n environment} :=
      resistanceParallelCorrection_le_threshold_add_tail
        (modelParameter p) n hthreshold.le
    _ < epsilon / 2 + epsilon / 2 := by linarith
    _ = epsilon := by ring

/-- The first-moment ratio is exactly the root-series contribution plus the normalized harmonic
correction. -/
theorem firstMoment_resistance_ratio_eq (p : unitInterval) (n : ℕ) :
    firstMoment p .resistance (n + 1) / firstMoment p .resistance n =
      2 * (p : ℝ) + (1 - (p : ℝ)) * resistanceParallelCorrection p n := by
  rw [firstMoment_resistance_succ_exact]
  field_simp [firstMoment_ne_zero p .resistance n]

/-- In the strict-gap branch, successive resistance first moments have ratio `2p`. -/
theorem firstMoment_resistance_ratio_tendsto_two_p
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    Tendsto
      (fun n : ℕ ↦
        firstMoment (modelParameter p) .resistance (n + 1) /
          firstMoment (modelParameter p) .resistance n)
      atTop (𝓝 (2 * p)) := by
  have hcorrection :=
    resistanceParallelCorrection_tendsto_zero_of_gammaR_gt_vR hpMem hp hgap
  have hlimit := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
      2 * (modelParameter p : ℝ)) atTop
        (𝓝 (2 * (modelParameter p : ℝ)))).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
      1 - (modelParameter p : ℝ)) atTop
        (𝓝 (1 - (modelParameter p : ℝ)))).mul hcorrection)
  convert hlimit using 1
  · funext n
    exact firstMoment_resistance_ratio_eq (modelParameter p) n
  · rw [modelParameter_coe_of_mem hpMem]
    simp

theorem log_firstMoment_resistance_ratio_tendsto_log_two_p
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    Tendsto
      (fun n : ℕ ↦ Real.log
        (firstMoment (modelParameter p) .resistance (n + 1) /
          firstMoment (modelParameter p) .resistance n))
      atTop (𝓝 (Real.log (2 * p))) := by
  exact (Real.continuousAt_log (mul_ne_zero (by norm_num) hp0.ne')).tendsto.comp
    (firstMoment_resistance_ratio_tendsto_two_p hpMem hp hgap)

private theorem sum_log_firstMoment_resistance_ratio
    (p : unitInterval) (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.log
      (firstMoment p .resistance (i + 1) /
        firstMoment p .resistance i)) =
      Real.log (firstMoment p .resistance n) := by
  induction n with
  | zero => simp [firstMoment]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih,
        Real.log_div (firstMoment_ne_zero p .resistance (n + 1))
          (firstMoment_ne_zero p .resistance n)]
      ring

private theorem normalizedLogFirstMoment_resistance_eq_cesaro
    (p : unitInterval) (n : ℕ) :
    normalizedLogFirstMoment p .resistance n =
      ((((n + 1 : ℕ) : ℝ)⁻¹) *
        ∑ i ∈ Finset.range (n + 1), Real.log
          (firstMoment p .resistance (i + 1) /
            firstMoment p .resistance i)) := by
  rw [sum_log_firstMoment_resistance_ratio, normalizedLogFirstMoment]
  field_simp
  push_cast
  rfl

/-- The strict branch of the first-moment dichotomy: Cesàro averaging identifies the annealed
exponent with `log (2p)`. -/
theorem gammaR_eq_log_two_p_of_gt_vR
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp : p < 1 / 2)
    (hgap : vR p < gammaR p) :
    gammaR p = Real.log (2 * p) := by
  have hlogRatio := log_firstMoment_resistance_ratio_tendsto_log_two_p
    hpMem hp0 hp hgap
  have hcesaro := hlogRatio.cesaro
  have hshift := (tendsto_add_atTop_iff_nat 1).2 hcesaro
  have hnormalized : Tendsto
      (normalizedLogFirstMoment (modelParameter p) .resistance)
      atTop (𝓝 (Real.log (2 * p))) := by
    convert hshift using 1
    funext n
    rw [normalizedLogFirstMoment_resistance_eq_cesaro]
  exact tendsto_nhds_unique (normalizedLogFirstMoment_tendsto_gammaR p) hnormalized

/-! ## Assembly of the strict subcritical dichotomy -/

theorem normalizedMeanLog_resistance_tendsto_vR_subcritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2) :
    Tendsto (normalizedMeanLog (modelParameter p) .resistance)
      atTop (𝓝 (vR p)) := by
  have hcomplementMem : 1 - p ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hpMem.1, hpMem.2]
  have hcomplementSuper : 1 / 2 < 1 - p := by linarith
  have hunitSuper :
      (1 / 2 : ℝ) < (modelParameter (1 - p) : ℝ) := by
    simpa only [modelParameter_coe_of_mem hcomplementMem] using hcomplementSuper
  have hmean := normalizedMeanLog_tendsto_chosenMeanLimit_supercritical
    (modelParameter (1 - p)) .resistance hunitSuper
  have hmean' : Tendsto
      (normalizedMeanLog (modelParameter (1 - p)) .resistance)
      atTop (𝓝 (vR (1 - p))) := by
    simpa only [vR] using hmean
  rw [modelParameter_one_sub hpMem] at hmean'
  have hneg := hmean'.neg
  convert hneg using 1
  · funext n
    rw [normalizedMeanLog_resistance_symm]
    simp
  · rw [vR_one_sub p hpMem]
    ring_nf

theorem normalizedMeanLog_le_normalizedLogFirstMoment
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    normalizedMeanLog p mode n ≤ normalizedLogFirstMoment p mode n := by
  rw [normalizedMeanLog, normalizedLogFirstMoment]
  exact div_le_div_of_nonneg_right (meanLog_le_log_firstMoment p mode (n + 1))
    (by positivity)

theorem vR_le_gammaR_subcritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp : p < 1 / 2) :
    vR p ≤ gammaR p :=
  le_of_tendsto_of_tendsto'
    (normalizedMeanLog_resistance_tendsto_vR_subcritical hpMem hp)
    (normalizedLogFirstMoment_tendsto_gammaR p)
    (fun n ↦ normalizedMeanLog_le_normalizedLogFirstMoment
      (modelParameter p) .resistance n)

/-- The series branch alone gives the universal lower bound `log (2p)` on the resistance
first-moment exponent. -/
theorem log_two_p_le_gammaR
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) :
    Real.log (2 * p) ≤ gammaR p := by
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds
    (normalizedLogFirstMoment_tendsto_gammaR p)
  intro n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [normalizedLogFirstMoment]
  apply (le_div_iff₀ hden).2
  have hbase : 0 < 2 * (modelParameter p : ℝ) := by
    rw [modelParameter_coe_of_mem hpMem]
    positivity
  have hbound :=
    (firstMoment_geometric_bounds (modelParameter p) .resistance (n + 1)).1
  have hlog := Real.log_le_log (pow_pos hbase _) hbound
  rw [Real.log_pow] at hlog
  rw [modelParameter_coe_of_mem hpMem] at hlog
  push_cast at hlog
  nlinarith

/-- Complete internal strict-subcritical first-moment formula. -/
theorem gammaR_eq_max_vR_log_two_p_subcritical
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp : p < 1 / 2) :
    gammaR p = max (vR p) (Real.log (2 * p)) := by
  have hv := vR_le_gammaR_subcritical hpMem hp
  have hlog := log_two_p_le_gammaR hpMem hp0
  have hmax : max (vR p) (Real.log (2 * p)) ≤ gammaR p := max_le hv hlog
  apply le_antisymm
  · by_cases hle : gammaR p ≤ vR p
    · exact hle.trans (le_max_left _ _)
    · have hgap : vR p < gammaR p := lt_of_not_ge hle
      rw [gammaR_eq_log_two_p_of_gt_vR hpMem hp0 hp hgap]
      exact le_max_right _ _
  · exact hmax

/-! ## Source-facing all-parameter wrappers -/

theorem vD_eq_zero_of_le_half (hcrit : gammaD (1 / 2) = 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    vD p = 0 := by
  rw [vD]
  exact chosenSequentialLimit_eq
    (normalizedMeanLog_distance_tendsto_zero
      (gammaD_eq_zero_of_le_half hcrit hp0 hp))

theorem distance_subcritical_convergesASAndL1_vD
    (hcrit : gammaD (1 / 2) = 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    ConvergesASAndL1AtLinearRate p .distance (vD p) := by
  rw [vD_eq_zero_of_le_half hcrit hp0 hp]
  exact distance_subcritical_convergesASAndL1 hcrit hp0 hp

theorem vR_half : vR (1 / 2) = 0 := by
  have h := vR_one_sub (1 / 2)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  norm_num at h
  linarith

theorem resistance_critical_convergesASAndL1_vR
    (hcrit : gammaD (1 / 2) = 0) :
    ConvergesASAndL1AtLinearRate (1 / 2) .resistance (vR (1 / 2)) := by
  rw [vR_half]
  exact resistance_critical_convergesASAndL1 hcrit

theorem firstMoment_resistance_le_distance (p : unitInterval) (n : ℕ) :
    firstMoment p .resistance n ≤ firstMoment p .distance n := by
  rw [firstMoment, firstMoment]
  apply integral_mono (integrable_Z p .resistance n) (integrable_Z p .distance n)
  intro environment
  exact resistanceValue_le_distanceValue n environment

theorem normalizedLogFirstMoment_resistance_le_distance
    (p : unitInterval) (n : ℕ) :
    normalizedLogFirstMoment p .resistance n ≤
      normalizedLogFirstMoment p .distance n := by
  rw [normalizedLogFirstMoment, normalizedLogFirstMoment]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.log_le_log (firstMoment_pos p .resistance (n + 1))
    (firstMoment_resistance_le_distance p (n + 1))

theorem gammaR_le_gammaD (p : ℝ) : gammaR p ≤ gammaD p :=
  le_of_tendsto_of_tendsto'
    (normalizedLogFirstMoment_tendsto_gammaR p)
    (normalizedLogFirstMoment_tendsto_gammaD p)
    (fun n ↦ normalizedLogFirstMoment_resistance_le_distance
      (modelParameter p) n)

theorem gammaR_half (hcrit : gammaD (1 / 2) = 0) :
    gammaR (1 / 2) = 0 := by
  have hlower := log_two_p_le_gammaR
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (by norm_num)
  have hupper := (gammaR_le_gammaD (1 / 2)).trans_eq hcrit
  norm_num at hlower
  exact le_antisymm hupper hlower

theorem gammaD_eq_vD_all (hcrit : gammaD (1 / 2) = 0)
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) :
    gammaD p = vD p := by
  by_cases hp : p ≤ 1 / 2
  · rw [gammaD_eq_zero_of_le_half hcrit hpMem.1 hp,
      vD_eq_zero_of_le_half hcrit hpMem.1 hp]
  · exact gammaD_eq_vD_supercritical hpMem (lt_of_not_ge hp)

theorem gammaR_eq_vR_supercritical_or_critical
    (hcrit : gammaD (1 / 2) = 0) {p : ℝ}
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) : gammaR p = vR p := by
  rcases hp.eq_or_lt with rfl | hpStrict
  · rw [gammaR_half hcrit, vR_half]
  · exact gammaR_eq_vR_supercritical ⟨(by linarith), hp1⟩ hpStrict

theorem gammaR_eq_max_vR_log_two_p_all_positive
    (hcrit : gammaD (1 / 2) = 0) {p : ℝ}
    (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) :
    gammaR p = max (vR p) (Real.log (2 * p)) := by
  rcases lt_trichotomy p (1 / 2) with hp | rfl | hp
  · exact gammaR_eq_max_vR_log_two_p_subcritical hpMem hp0 hp
  · rw [gammaR_half hcrit, vR_half]
    norm_num
  · have heq := gammaR_eq_vR_supercritical hpMem hp
    have hlog := log_two_p_le_gammaR hpMem hp0
    rw [heq] at hlog ⊢
    exact (max_eq_left hlog).symm

/-- Exact `EReal`/`paperLog` form used by the source-facing first-moment theorem. -/
theorem gammaR_ereal_eq_max_vR_paperLog
    (hcrit : gammaD (1 / 2) = 0) {p : ℝ}
    (hpMem : p ∈ Icc (0 : ℝ) 1) :
    (gammaR p : EReal) = max (vR p : EReal) (paperLog (2 * p)) := by
  by_cases hpZero : p = 0
  · subst p
    simp [gammaR_zero, vR_zero]
  · have hp0 : 0 < p := lt_of_le_of_ne hpMem.1 (Ne.symm hpZero)
    rw [gammaR_eq_max_vR_log_two_p_all_positive hcrit hpMem hp0,
      paperLog_of_pos (mul_pos (by norm_num) hp0)]
    norm_cast

/-- The a.s./`L¹` half of the first source theorem, assembled by the three parameter ranges. -/
theorem allParameters_convergesASAndL1
    (hcrit : gammaD (1 / 2) = 0) {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) :
    ConvergesASAndL1AtLinearRate p .distance (vD p) ∧
      ConvergesASAndL1AtLinearRate p .resistance (vR p) := by
  rcases lt_trichotomy p (1 / 2) with hp | rfl | hp
  · exact ⟨distance_subcritical_convergesASAndL1_vD hcrit hpMem.1 hp.le,
      resistance_subcritical_convergesASAndL1 hpMem hp⟩
  · exact ⟨distance_subcritical_convergesASAndL1_vD hcrit (by norm_num) le_rfl,
      resistance_critical_convergesASAndL1_vR hcrit⟩
  · exact ⟨distance_convergesASAndL1_supercritical hpMem hp,
      resistance_convergesASAndL1_supercritical hpMem hp⟩

theorem log_two_p_le_gammaD
    {p : ℝ} (hpMem : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) :
    Real.log (2 * p) ≤ gammaD p := by
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds
    (normalizedLogFirstMoment_tendsto_gammaD p)
  intro n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [normalizedLogFirstMoment]
  apply (le_div_iff₀ hden).2
  have hbase : 0 < 2 * (modelParameter p : ℝ) := by
    rw [modelParameter_coe_of_mem hpMem]
    positivity
  have hbound :=
    (firstMoment_geometric_bounds (modelParameter p) .distance (n + 1)).1
  have hlog := Real.log_le_log (pow_pos hbase _) hbound
  rw [Real.log_pow] at hlog
  rw [modelParameter_coe_of_mem hpMem] at hlog
  push_cast at hlog
  nlinarith

theorem normalizedLogFirstMoment_le_log_two
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    normalizedLogFirstMoment p mode n ≤ Real.log 2 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [normalizedLogFirstMoment]
  apply (div_le_iff₀ hden).2
  have hbound := (firstMoment_geometric_bounds p mode (n + 1)).2
  have hlog := Real.log_le_log (firstMoment_pos p mode (n + 1)) hbound
  rw [Real.log_pow] at hlog
  push_cast at hlog
  nlinarith

theorem gammaD_le_log_two (p : ℝ) : gammaD p ≤ Real.log 2 :=
  le_of_tendsto_of_tendsto'
    (normalizedLogFirstMoment_tendsto_gammaD p) tendsto_const_nhds
    (fun n ↦ normalizedLogFirstMoment_le_log_two
      (modelParameter p) .distance n)

theorem gammaR_le_log_two (p : ℝ) : gammaR p ≤ Real.log 2 :=
  le_of_tendsto_of_tendsto'
    (normalizedLogFirstMoment_tendsto_gammaR p) tendsto_const_nhds
    (fun n ↦ normalizedLogFirstMoment_le_log_two
      (modelParameter p) .resistance n)

theorem supercritical_logarithmic_speed_bounds
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    Real.log (2 * p) ≤ vD p ∧ vD p ≤ Real.log 2 ∧
      Real.log (2 * p) ≤ vR p ∧ vR p ≤ Real.log 2 := by
  have hpMem : p ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hp1⟩
  have hD := gammaD_eq_vD_supercritical hpMem hp
  have hR := gammaR_eq_vR_supercritical hpMem hp
  constructor
  · simpa only [hD] using log_two_p_le_gammaD hpMem (by linarith)
  constructor
  · simpa only [hD] using gammaD_le_log_two p
  constructor
  · simpa only [hR] using log_two_p_le_gammaR hpMem (by linarith)
  · simpa only [hR] using gammaR_le_log_two p

/-- Complete first source theorem modulo its single critical distance input. -/
theorem logarithmicSpeeds_of_critical_input
    (hcrit : gammaD (1 / 2) = 0) : LogarithmicSpeedsStatement := by
  refine ⟨?_, ?_, ?_, vR_half, ?_⟩
  · intro p hpMem
    exact allParameters_convergesASAndL1 hcrit hpMem
  · intro p hp0 hp
    exact vD_eq_zero_of_le_half hcrit hp0 hp
  · intro p hpMem
    exact vR_one_sub p hpMem
  · intro p hp hp1
    exact supercritical_logarithmic_speed_bounds hp hp1

/-- Complete second source theorem modulo the same critical distance input. -/
theorem firstMomentLogarithmicRates_of_critical_input
    (hcrit : gammaD (1 / 2) = 0) : FirstMomentLogarithmicRatesStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _
    exact ⟨normalizedLogFirstMoment_tendsto_gammaD p,
      normalizedLogFirstMoment_tendsto_gammaR p⟩
  · intro p hpMem
    exact gammaD_eq_vD_all hcrit hpMem
  · intro p hpMem
    exact gammaR_ereal_eq_max_vR_paperLog hcrit hpMem
  · intro p hp hp1
    exact gammaR_eq_vR_supercritical_or_critical hcrit hp hp1

end SeriesParallel.MainText
