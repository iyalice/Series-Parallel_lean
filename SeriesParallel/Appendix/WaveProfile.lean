import SeriesParallel.Appendix.Profiles

/-!
# Full-line profile consequences

This module continues B3 after the inverse-coordinate construction.  It keeps the
endpoint-ratio arguments separate from the later compactness and measure arguments.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-- The left ratio in `eq:appendix-tail-ratios`, pulled back from the linear branch at
`u=1`. -/
theorem waveDensity_div_profile_tendsto_atBot {input : MainInput} {lambda : ℝ}
    {W Phi : ℝ → ℝ} (hlambda : 0 < lambda)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hone : HasLinearBranchAtOne lambda W) :
    Tendsto (fun z ↦ waveDensity input W Phi z / Phi z) atBot
      (𝓝 (input.beta / lambda)) := by
  have hPhiGT : Tendsto Phi atBot (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hPhi.2.2.2.2.2.1,
      Filter.Eventually.of_forall fun z ↦ (hPhi.2.2.1 z).1⟩
  have hreflect : Tendsto (fun z : ℝ ↦ 1 - Phi z) atBot (𝓝[<] (1 : ℝ)) :=
    tendsto_one_sub_nhdsGT_zero_nhdsLT_one.comp hPhiGT
  have hcomp := hone.comp_tendsto hreflect
  have hequiv : (fun z : ℝ ↦ W (1 - Phi z)) ~[atBot]
      (fun z : ℝ ↦ Phi z / lambda) := by
    refine (hcomp.congr_left (Filter.Eventually.of_forall fun z ↦ ?_)).congr_right
      (Filter.Eventually.of_forall fun z ↦ ?_)
    · rfl
    · simp only [Function.comp_apply]
      ring
  have hdenom : ∀ᶠ z in atBot, Phi z / lambda ≠ 0 :=
    Filter.Eventually.of_forall fun z ↦
      div_ne_zero (hPhi.2.2.1 z).1.ne' hlambda.ne'
  have hratio : Tendsto (fun z : ℝ ↦ W (1 - Phi z) / (Phi z / lambda)) atBot
      (𝓝 1) := (isEquivalent_iff_tendsto_one hdenom).mp hequiv
  have hscaled := (tendsto_const_nhds (x := input.beta / lambda)).mul hratio
  have hscaled' : Tendsto
      (fun z : ℝ ↦ (input.beta / lambda) *
        (W (1 - Phi z) / (Phi z / lambda))) atBot
      (𝓝 (input.beta / lambda)) := by
    simpa only [one_mul, mul_one] using hscaled
  apply (tendsto_congr' ?_).2 hscaled'
  exact Filter.Eventually.of_forall fun z ↦ by
    unfold waveDensity
    field_simp [hlambda.ne', (hPhi.2.2.1 z).1.ne']

/-- The right ratio in `eq:appendix-tail-ratios`, pulled back from the linear branch at
`u=0`. -/
theorem waveDensity_div_one_sub_profile_tendsto_atTop {input : MainInput}
    {lambda : ℝ} {W Phi : ℝ → ℝ} (hlambda : 0 < lambda)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hzero : HasLinearBranchAtZero lambda W) :
    Tendsto (fun z ↦ waveDensity input W Phi z / (1 - Phi z)) atTop
      (𝓝 (input.beta / lambda)) := by
  have hPhiLT : Tendsto Phi atTop (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hPhi.2.2.2.2.2.2,
      Filter.Eventually.of_forall fun z ↦ (hPhi.2.2.1 z).2⟩
  have hreflect : Tendsto (fun z : ℝ ↦ 1 - Phi z) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_one_sub_nhdsLT_one_nhdsGT_zero.comp hPhiLT
  have hcomp := hzero.comp_tendsto hreflect
  have hequiv : (fun z : ℝ ↦ W (1 - Phi z)) ~[atTop]
      (fun z : ℝ ↦ (1 - Phi z) / lambda) := by
    refine (hcomp.congr_left (Filter.Eventually.of_forall fun z ↦ ?_)).congr_right
      (Filter.Eventually.of_forall fun z ↦ ?_)
    · rfl
    · rfl
  have hdenom : ∀ᶠ z in atTop, (1 - Phi z) / lambda ≠ 0 :=
    Filter.Eventually.of_forall fun z ↦
      div_ne_zero (sub_ne_zero.mpr (hPhi.2.2.1 z).2.ne') hlambda.ne'
  have hratio : Tendsto
      (fun z : ℝ ↦ W (1 - Phi z) / ((1 - Phi z) / lambda)) atTop
      (𝓝 1) := (isEquivalent_iff_tendsto_one hdenom).mp hequiv
  have hscaled := (tendsto_const_nhds (x := input.beta / lambda)).mul hratio
  have hscaled' : Tendsto
      (fun z : ℝ ↦ (input.beta / lambda) *
        (W (1 - Phi z) / ((1 - Phi z) / lambda))) atTop
      (𝓝 (input.beta / lambda)) := by
    simpa only [one_mul, mul_one] using hscaled
  apply (tendsto_congr' ?_).2 hscaled'
  exact Filter.Eventually.of_forall fun z ↦ by
    unfold waveDensity
    field_simp [hlambda.ne', sub_ne_zero.mpr (hPhi.2.2.1 z).2.ne']

/-- All three differentiated density identities in B3, obtained from the pointwise
chain-rule helpers in `Profiles`. -/
theorem waveDensity_derivative_identities {input : MainInput}
    {W W1 W2 W3 Phi : ℝ → ℝ}
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hW : ∀ u ∈ openUnitInterval, HasDerivAt W (W1 u) u)
    (hW1 : ∀ u ∈ openUnitInterval, HasDerivAt W1 (W2 u) u)
    (hW2 : ∀ u ∈ openUnitInterval, HasDerivAt W2 (W3 u) u) :
    WaveDensityDerivativeIdentities input W W1 W2 W3 Phi
      (waveDensity input W Phi) := by
  have hreflect : ∀ z, 1 - Phi z ∈ openUnitInterval := by
    intro z
    exact ⟨by linarith [(hPhi.2.2.1 z).2], by linarith [(hPhi.2.2.1 z).1]⟩
  have hq1 : deriv (waveDensity input W Phi) = waveDensityD1 input W W1 Phi := by
    funext z
    exact (waveDensity_hasDerivAt (hPhi.2.2.2.2.1 z)
      (hW (1 - Phi z) (hreflect z))).deriv
  have hq2 : deriv (waveDensityD1 input W W1 Phi) =
      waveDensityD2 input W W1 W2 Phi := by
    funext z
    exact (waveDensityD1_hasDerivAt (hPhi.2.2.2.2.1 z)
      (hW (1 - Phi z) (hreflect z))
      (hW1 (1 - Phi z) (hreflect z))).deriv
  have hq3 : deriv (waveDensityD2 input W W1 W2 Phi) =
      waveDensityD3 input W W1 W2 W3 Phi := by
    funext z
    exact (waveDensityD2_hasDerivAt (hPhi.2.2.2.2.1 z)
      (hW (1 - Phi z) (hreflect z))
      (hW1 (1 - Phi z) (hreflect z))
      (hW2 (1 - Phi z) (hreflect z))).deriv
  have hiter1 : iteratedDeriv 1 (waveDensity input W Phi) =
      waveDensityD1 input W W1 Phi := by
    calc
      iteratedDeriv 1 (waveDensity input W Phi) =
          deriv (iteratedDeriv 0 (waveDensity input W Phi)) := by
            rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (waveDensity input W Phi) := by rw [iteratedDeriv_zero]
      _ = waveDensityD1 input W W1 Phi := hq1
  have hiter2 : iteratedDeriv 2 (waveDensity input W Phi) =
      waveDensityD2 input W W1 W2 Phi := by
    calc
      iteratedDeriv 2 (waveDensity input W Phi) =
          deriv (iteratedDeriv 1 (waveDensity input W Phi)) := by
            rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (waveDensityD1 input W W1 Phi) := by rw [hiter1]
      _ = waveDensityD2 input W W1 W2 Phi := hq2
  have hiter3 : iteratedDeriv 3 (waveDensity input W Phi) =
      waveDensityD3 input W W1 W2 W3 Phi := by
    calc
      iteratedDeriv 3 (waveDensity input W Phi) =
          deriv (iteratedDeriv 2 (waveDensity input W Phi)) := by
            rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (waveDensityD2 input W W1 W2 Phi) := by rw [hiter2]
      _ = waveDensityD3 input W W1 W2 W3 Phi := hq3
  refine
    { qValue := fun _ ↦ rfl
      first := ?_
      second := ?_
      third := ?_ }
  · intro z
    exact congrFun hq1 z
  · intro z
    change iteratedDeriv 2 (waveDensity input W Phi) z =
      waveDensityD2 input W W1 W2 Phi z
    exact congrFun hiter2 z
  · intro z
    change iteratedDeriv 3 (waveDensity input W Phi) z =
      waveDensityD3 input W W1 W2 W3 Phi z
    exact congrFun hiter3 z

end SeriesParallel.Appendix
