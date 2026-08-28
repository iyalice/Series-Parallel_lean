import SeriesParallel.Appendix.WaveProfile

/-!
# Quantitative estimates for the full-line profile

This module completes the elementary estimate step in B3.  The tail-ratio limits
give exponential bounds by applying the one-dimensional monotonicity interfaces to
logarithmic integrating factors.  The exact differentiated density identities then
turn uniform bounds on `W'`, `W W''`, and `W^2 W'''` into relative bounds through
third order.
-/

open Asymptotics Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

private theorem exists_left_exponential_bound_of_ratio {input : MainInput}
    {W Phi : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hratio : ∀ᶠ z in atBot,
      c < waveDensity input W Phi z / Phi z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ≤ 0, Phi z ≤ C * Real.exp (c * z) := by
  obtain ⟨A, hA⟩ := eventually_atBot.1 hratio
  let a : ℝ := min A 0
  let F : ℝ → ℝ := fun z ↦ Real.log (Phi z) - c * z
  have haA : a ≤ A := min_le_left _ _
  have ha0 : a ≤ 0 := min_le_right _ _
  have hPhiRange : ∀ z, Phi z ∈ Ioo (0 : ℝ) 1 := hPhi.2.2.1
  have hPhiPhase : ∀ z,
      HasDerivAt Phi (waveDensity input W Phi z) z := by
    intro z
    simpa only [wavePhaseRhs, waveDensity] using hPhi.2.2.2.2.1 z
  have hFderiv : ∀ z, HasDerivAt F
      (waveDensity input W Phi z / Phi z - c) z := by
    intro z
    have hlog := (Real.hasDerivAt_log (hPhiRange z).1.ne').comp z (hPhiPhase z)
    have hlinear := (hasDerivAt_id z).const_mul c
    have hFeq : F = (Real.log ∘ Phi) - fun y : ℝ ↦ c * id y := by
      funext y
      simp [F]
    rw [hFeq]
    apply (hlog.sub hlinear).congr_deriv
    simp only [div_eq_mul_inv]
    ring
  refine ⟨Real.exp (F a) + Real.exp (-c * a), by positivity, ?_⟩
  intro z hz0
  by_cases hza : z ≤ a
  · have hmono : MonotoneOn F (Icc z a) :=
      ManualInterfaces.MI06_monotoneOn_of_deriv_nonneg hza
        (fun y _ ↦ (hFderiv y).continuousAt.continuousWithinAt) (by
          intro y hy
          refine ⟨waveDensity input W Phi y / Phi y - c, hFderiv y, ?_⟩
          exact sub_nonneg.mpr (le_of_lt (hA y (le_trans hy.2.le haA))))
    have hFle : F z ≤ F a :=
      hmono ⟨le_rfl, hza⟩ ⟨hza, le_rfl⟩ hza
    have hlogle : Real.log (Phi z) ≤ F a + c * z := by
      dsimp only [F] at hFle ⊢
      linarith
    have hexp := Real.exp_le_exp.mpr hlogle
    rw [Real.exp_log (hPhiRange z).1, Real.exp_add] at hexp
    exact hexp.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le)
  · have haz : a ≤ z := (lt_of_not_ge hza).le
    have hexpmono : Real.exp (c * a) ≤ Real.exp (c * z) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left haz hc.le)
    have hone : (1 : ℝ) = Real.exp (-c * a) * Real.exp (c * a) := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      Phi z ≤ 1 := (hPhiRange z).2.le
      _ = Real.exp (-c * a) * Real.exp (c * a) := hone
      _ ≤ Real.exp (-c * a) * Real.exp (c * z) :=
        mul_le_mul_of_nonneg_left hexpmono (Real.exp_pos _).le
      _ ≤ (Real.exp (F a) + Real.exp (-c * a)) * Real.exp (c * z) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.exp_pos _).le)
          (Real.exp_pos _).le

private theorem exists_right_exponential_bound_of_ratio {input : MainInput}
    {W Phi : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hratio : ∀ᶠ z in atTop,
      c < waveDensity input W Phi z / (1 - Phi z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ≥ 0, 1 - Phi z ≤ C * Real.exp (-c * z) := by
  obtain ⟨B, hB⟩ := eventually_atTop.1 hratio
  let b : ℝ := max B 0
  let G : ℝ → ℝ := fun z ↦ Real.log (1 - Phi z) + c * z
  have hBb : B ≤ b := le_max_left _ _
  have h0b : 0 ≤ b := le_max_right _ _
  have hPhiRange : ∀ z, Phi z ∈ Ioo (0 : ℝ) 1 := hPhi.2.2.1
  have hPhiPhase : ∀ z,
      HasDerivAt Phi (waveDensity input W Phi z) z := by
    intro z
    simpa only [wavePhaseRhs, waveDensity] using hPhi.2.2.2.2.1 z
  have hGderiv : ∀ z, HasDerivAt G
      (-waveDensity input W Phi z / (1 - Phi z) + c) z := by
    intro z
    have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - Phi y)
        (-waveDensity input W Phi z) z := by
      simpa using (hPhiPhase z).const_sub 1
    have hlog := (Real.hasDerivAt_log
      (sub_ne_zero.mpr (hPhiRange z).2.ne')).comp z honeSub
    have hlinear := (hasDerivAt_id z).const_mul c
    have hGeq : G =
        (Real.log ∘ fun y : ℝ ↦ 1 - Phi y) + fun y : ℝ ↦ c * id y := by
      funext y
      simp [G]
    rw [hGeq]
    apply (hlog.add hlinear).congr_deriv
    simp only [div_eq_mul_inv]
    ring
  refine ⟨Real.exp (G b) + Real.exp (c * b), by positivity, ?_⟩
  intro z hz0
  by_cases hbz : b ≤ z
  · have hanti : AntitoneOn G (Icc b z) :=
      ManualInterfaces.MI06_antitoneOn_of_deriv_nonpos hbz
        (fun y _ ↦ (hGderiv y).continuousAt.continuousWithinAt) (by
          intro y hy
          refine ⟨-waveDensity input W Phi y / (1 - Phi y) + c,
            hGderiv y, ?_⟩
          calc
            -waveDensity input W Phi y / (1 - Phi y) + c =
                c - waveDensity input W Phi y / (1 - Phi y) := by ring
            _ ≤ 0 := sub_nonpos.mpr
              (le_of_lt (hB y (le_trans hBb hy.1.le))))
    have hGle : G z ≤ G b :=
      hanti ⟨le_rfl, hbz⟩ ⟨hbz, le_rfl⟩ hbz
    have hlogle : Real.log (1 - Phi z) ≤ G b + (-c * z) := by
      dsimp only [G] at hGle ⊢
      linarith
    have hexp := Real.exp_le_exp.mpr hlogle
    rw [Real.exp_log (sub_pos.mpr (hPhiRange z).2), Real.exp_add] at hexp
    exact hexp.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le)
  · have hzb : z ≤ b := (lt_of_not_ge hbz).le
    have hexpmono : Real.exp (-c * b) ≤ Real.exp (-c * z) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hone : (1 : ℝ) = Real.exp (c * b) * Real.exp (-c * b) := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      1 - Phi z ≤ 1 := by linarith [(hPhiRange z).1]
      _ = Real.exp (c * b) * Real.exp (-c * b) := hone
      _ ≤ Real.exp (c * b) * Real.exp (-c * z) :=
        mul_le_mul_of_nonneg_left hexpmono (Real.exp_pos _).le
      _ ≤ (Real.exp (G b) + Real.exp (c * b)) * Real.exp (-c * z) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.exp_pos _).le)
          (Real.exp_pos _).le

/-- Positive two-sided tail ratios force the two exponential profile bounds in B3. -/
theorem hasTwoSidedExponentialTails_of_tail_ratios {input : MainInput}
    {W Phi : ℝ → ℝ} {rho : ℝ} (hrho : 0 < rho)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hleft : Tendsto (fun z ↦ waveDensity input W Phi z / Phi z) atBot
      (nhds rho))
    (hright : Tendsto
      (fun z ↦ waveDensity input W Phi z / (1 - Phi z)) atTop
      (nhds rho)) :
    HasTwoSidedExponentialTails Phi := by
  let c : ℝ := rho / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  have hcrho : c < rho := by dsimp only [c]; linarith
  have hleftEventually : ∀ᶠ z in atBot,
      c < waveDensity input W Phi z / Phi z :=
    (tendsto_order.1 hleft).1 c hcrho
  have hrightEventually : ∀ᶠ z in atTop,
      c < waveDensity input W Phi z / (1 - Phi z) :=
    (tendsto_order.1 hright).1 c hcrho
  obtain ⟨Cleft, hCleft, hleftBound⟩ :=
    exists_left_exponential_bound_of_ratio hc hPhi hleftEventually
  obtain ⟨Cright, hCright, hrightBound⟩ :=
    exists_right_exponential_bound_of_ratio hc hPhi hrightEventually
  refine ⟨c, max Cleft Cright, hc,
    hCleft.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro z hz
    exact (hleftBound z hz).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.exp_pos _).le)
  · intro z hz
    exact (hrightBound z hz).trans (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.exp_pos _).le)

/-- The branch asymptotics proved in `WaveProfile` imply the exponential tails
claimed in B3. -/
theorem waveProfile_hasTwoSidedExponentialTails {input : MainInput}
    {lambda : ℝ} {W Phi : ℝ → ℝ} (hlambda : 0 < lambda)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hzero : HasLinearBranchAtZero lambda W)
    (hone : HasLinearBranchAtOne lambda W) :
    HasTwoSidedExponentialTails Phi := by
  exact hasTwoSidedExponentialTails_of_tail_ratios
    (div_pos input.beta_pos hlambda) hPhi
    (waveDensity_div_profile_tendsto_atBot hlambda hPhi hone)
    (waveDensity_div_one_sub_profile_tendsto_atTop hlambda hPhi hzero)

/-- Exact density identities plus uniform bounds on the three relative `W` terms
give the full-line relative density bounds through order three. -/
theorem fullLineRelativeDerivativeBounds_of_uniform_W_bounds {input : MainInput}
    {W W1 W2 W3 Phi q : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hbound1 : ∀ u ∈ openUnitInterval, |W1 u| ≤ K)
    (hbound2 : ∀ u ∈ openUnitInterval, |W u * W2 u| ≤ K)
    (hbound3 : ∀ u ∈ openUnitInterval, |W u ^ 2 * W3 u| ≤ K)
    (hids : WaveDensityDerivativeIdentities input W W1 W2 W3 Phi q) :
    FullLineRelativeDerivativeBounds q := by
  let M : ℝ := input.beta * K + input.beta ^ 2 * (K ^ 2 + K) +
    input.beta ^ 3 * (K ^ 3 + 4 * K ^ 2 + K)
  have hKtwo : 0 ≤ K ^ 2 := sq_nonneg K
  have hKthree : 0 ≤ K ^ 3 := pow_nonneg hK 3
  have hpoly2 : 0 ≤ K ^ 2 + K := add_nonneg hKtwo hK
  have hpoly3 : 0 ≤ K ^ 3 + 4 * K ^ 2 + K :=
    add_nonneg (add_nonneg hKthree (mul_nonneg (by norm_num) hKtwo)) hK
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact add_nonneg
      (add_nonneg (mul_nonneg input.beta_pos.le hK)
        (mul_nonneg (sq_nonneg input.beta) hpoly2))
      (mul_nonneg (pow_nonneg input.beta_pos.le 3) hpoly3)
  refine ⟨M, hM, ?_⟩
  intro j hj1 hj3 z
  have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  have hu : 1 - Phi z ∈ openUnitInterval :=
    ⟨by linarith [(hPhi.2.2.1 z).2], by linarith [(hPhi.2.2.1 z).1]⟩
  have hWu : 0 < W (1 - Phi z) := hpos _ hu
  have hqpos : 0 < q z := by
    rw [hids.qValue z]
    exact mul_pos input.beta_pos hWu
  have hE2 :
      |W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z)| ≤
        K ^ 2 + K := by
    calc
      |W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z)| ≤
          |W1 (1 - Phi z) ^ 2| + |W (1 - Phi z) * W2 (1 - Phi z)| :=
        abs_add_le _ _
      _ ≤ K ^ 2 + K := add_le_add (by
        simpa only [abs_pow] using
          pow_le_pow_left₀ (abs_nonneg (W1 (1 - Phi z))) (hbound1 _ hu) 2)
        (hbound2 _ hu)
  have hproduct :
      |W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z)| ≤ K ^ 2 := by
    rw [show W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) =
      W1 (1 - Phi z) * (W (1 - Phi z) * W2 (1 - Phi z)) by ring, abs_mul]
    simpa only [pow_two] using mul_le_mul (hbound1 _ hu) (hbound2 _ hu)
      (abs_nonneg _) hK
  have hE3 :
      |W1 (1 - Phi z) ^ 3 +
        4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
        W (1 - Phi z) ^ 2 * W3 (1 - Phi z)| ≤
        K ^ 3 + 4 * K ^ 2 + K := by
    calc
      |W1 (1 - Phi z) ^ 3 +
          4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
          W (1 - Phi z) ^ 2 * W3 (1 - Phi z)| ≤
          |W1 (1 - Phi z) ^ 3 +
            4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z)| +
            |W (1 - Phi z) ^ 2 * W3 (1 - Phi z)| := abs_add_le _ _
      _ ≤ (|W1 (1 - Phi z) ^ 3| +
            |4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z)|) +
            |W (1 - Phi z) ^ 2 * W3 (1 - Phi z)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (K ^ 3 + 4 * K ^ 2) + K := by
        apply add_le_add
        · apply add_le_add
          · simpa only [abs_pow] using
              pow_le_pow_left₀ (abs_nonneg (W1 (1 - Phi z))) (hbound1 _ hu) 3
          · have hfour := mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ 4 by norm_num)
            simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num),
              mul_assoc] using hfour
        · exact hbound3 _ hu
      _ = K ^ 3 + 4 * K ^ 2 + K := by ring
  rcases hj with rfl | rfl | rfl
  · rw [show iteratedDeriv 1 q = deriv q by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [hids.first z, hids.qValue z]
    have hcoef : input.beta * |W1 (1 - Phi z)| ≤ M := by
      have hfirst : input.beta * |W1 (1 - Phi z)| ≤ input.beta * K :=
        mul_le_mul_of_nonneg_left (hbound1 _ hu) input.beta_pos.le
      have hsecond : 0 ≤ input.beta ^ 2 * (K ^ 2 + K) :=
        mul_nonneg (sq_nonneg input.beta) hpoly2
      have hthird : 0 ≤ input.beta ^ 3 * (K ^ 3 + 4 * K ^ 2 + K) :=
        mul_nonneg (pow_nonneg input.beta_pos.le 3) hpoly3
      dsimp only [M]
      linarith
    calc
      |-input.beta ^ 2 * W (1 - Phi z) * W1 (1 - Phi z)| =
          (input.beta * W (1 - Phi z)) *
            (input.beta * |W1 (1 - Phi z)|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_of_pos input.beta_pos,
          abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (1 - Phi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (1 - Phi z)) := by ring
  · rw [hids.second z, hids.qValue z]
    have hcoef : input.beta ^ 2 *
        |W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z)| ≤ M := by
      have hmiddle := mul_le_mul_of_nonneg_left hE2 (sq_nonneg input.beta)
      have hfirst : 0 ≤ input.beta * K := mul_nonneg input.beta_pos.le hK
      have hthird : 0 ≤ input.beta ^ 3 * (K ^ 3 + 4 * K ^ 2 + K) :=
        mul_nonneg (pow_nonneg input.beta_pos.le 3) hpoly3
      dsimp only [M]
      linarith
    calc
      |input.beta ^ 3 * W (1 - Phi z) *
          (W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z))| =
          (input.beta * W (1 - Phi z)) *
            (input.beta ^ 2 *
              |W1 (1 - Phi z) ^ 2 + W (1 - Phi z) * W2 (1 - Phi z)|) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos input.beta_pos, abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (1 - Phi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (1 - Phi z)) := by ring
  · rw [hids.third z, hids.qValue z]
    have hcoef : input.beta ^ 3 *
        |W1 (1 - Phi z) ^ 3 +
          4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
          W (1 - Phi z) ^ 2 * W3 (1 - Phi z)| ≤ M := by
      have hlast := mul_le_mul_of_nonneg_left hE3 (pow_nonneg input.beta_pos.le 3)
      have hfirst : 0 ≤ input.beta * K := mul_nonneg input.beta_pos.le hK
      have hsecond : 0 ≤ input.beta ^ 2 * (K ^ 2 + K) :=
        mul_nonneg (sq_nonneg input.beta) hpoly2
      dsimp only [M]
      linarith
    calc
      |-input.beta ^ 4 * W (1 - Phi z) *
          (W1 (1 - Phi z) ^ 3 +
            4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
            W (1 - Phi z) ^ 2 * W3 (1 - Phi z))| =
          (input.beta * W (1 - Phi z)) *
            (input.beta ^ 3 *
              |W1 (1 - Phi z) ^ 3 +
                4 * W (1 - Phi z) * W1 (1 - Phi z) * W2 (1 - Phi z) +
                W (1 - Phi z) ^ 2 * W3 (1 - Phi z)|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_of_pos input.beta_pos,
          abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (1 - Phi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (1 - Phi z)) := by ring

/-- The pointwise derivative hypotheses from B3 feed directly into the uniform
relative-bound theorem. -/
theorem waveDensity_fullLineRelativeDerivativeBounds {input : MainInput}
    {W W1 W2 W3 Phi : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hPhi : IsNormalizedWaveProfile input W Phi)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hW : ∀ u ∈ openUnitInterval, HasDerivAt W (W1 u) u)
    (hW1 : ∀ u ∈ openUnitInterval, HasDerivAt W1 (W2 u) u)
    (hW2 : ∀ u ∈ openUnitInterval, HasDerivAt W2 (W3 u) u)
    (hbound1 : ∀ u ∈ openUnitInterval, |W1 u| ≤ K)
    (hbound2 : ∀ u ∈ openUnitInterval, |W u * W2 u| ≤ K)
    (hbound3 : ∀ u ∈ openUnitInterval, |W u ^ 2 * W3 u| ≤ K) :
    FullLineRelativeDerivativeBounds (waveDensity input W Phi) := by
  exact fullLineRelativeDerivativeBounds_of_uniform_W_bounds hK hPhi hpos
    hbound1 hbound2 hbound3
    (waveDensity_derivative_identities hPhi hW hW1 hW2)

/-- A single constant controls the three relative `W` terms throughout `(0,1)`. -/
def RelativeDerivativeBoundsOnUnitInterval (W : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ openUnitInterval,
    |deriv W u| + |W u * iteratedDeriv 2 W u| +
      |W u ^ 2 * iteratedDeriv 3 W u| ≤ C

/-- The two endpoint estimates and smoothness on the open interval combine, by a
maximum on the intervening compact interval, into one uniform relative bound. -/
theorem relativeDerivativeBoundsOnUnitInterval_of_endpoint_regularities
    {lambda : ℝ} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hleft : LeftLinearBranchRegularity lambda W)
    (hright : RightLinearBranchRegularity lambda W) :
    RelativeDerivativeBoundsOnUnitInterval W := by
  rcases hleft.relativeDerivativeBounds with
    ⟨etaZero, hetaZero, CZero, hCZero, hzeroBound⟩
  rcases hright.relativeDerivativeBounds with
    ⟨etaOne, hetaOne, COne, hCOne, honeBound⟩
  let deltaZero : ℝ := min (etaZero / 2) (1 / 4)
  let deltaOne : ℝ := min (etaOne / 2) (1 / 4)
  have hdeltaZeroPos : 0 < deltaZero := by
    dsimp only [deltaZero]
    exact lt_min (half_pos hetaZero) (by norm_num)
  have hdeltaOnePos : 0 < deltaOne := by
    dsimp only [deltaOne]
    exact lt_min (half_pos hetaOne) (by norm_num)
  have hdeltaZeroEta : deltaZero < etaZero := by
    calc
      deltaZero ≤ etaZero / 2 := min_le_left _ _
      _ < etaZero := half_lt_self hetaZero
  have hdeltaOneEta : deltaOne < etaOne := by
    calc
      deltaOne ≤ etaOne / 2 := min_le_left _ _
      _ < etaOne := half_lt_self hetaOne
  have hdeltaZeroQuarter : deltaZero ≤ 1 / 4 := min_le_right _ _
  have hdeltaOneQuarter : deltaOne ≤ 1 / 4 := min_le_right _ _
  have hmiddleOrder : deltaZero ≤ 1 - deltaOne := by
    nlinarith
  have hmiddleStrict : deltaZero < 1 - deltaOne := by
    nlinarith
  let middle : Set ℝ := Icc deltaZero (1 - deltaOne)
  have hmiddleSubset : middle ⊆ openUnitInterval := by
    intro u hu
    change u ∈ Icc deltaZero (1 - deltaOne) at hu
    exact ⟨hdeltaZeroPos.trans_le hu.1, by linarith [hu.2, hdeltaOnePos]⟩
  have hWmiddleInfinity : ContDiffOn ℝ ∞ W middle := hW.mono hmiddleSubset
  have hWmiddle : ContDiffOn ℝ 4 W middle :=
    contDiffOn_infty.mp hWmiddleInfinity 4
  have hmiddleUnique : UniqueDiffOn ℝ middle := by
    exact uniqueDiffOn_Icc hmiddleStrict
  let B : ℝ → ℝ := fun u ↦
    |iteratedDerivWithin 1 W middle u| +
      |W u * iteratedDerivWithin 2 W middle u| +
      |W u ^ 2 * iteratedDerivWithin 3 W middle u|
  have hBcontinuous : ContinuousOn B middle := by
    have hWc := hWmiddle.continuousOn
    have h1 := hWmiddle.continuousOn_iteratedDerivWithin (m := 1)
      (by norm_num) hmiddleUnique
    have h2 := hWmiddle.continuousOn_iteratedDerivWithin (m := 2)
      (by norm_num) hmiddleUnique
    have h3 := hWmiddle.continuousOn_iteratedDerivWithin (m := 3)
      (by norm_num) hmiddleUnique
    dsimp only [B]
    exact h1.abs.add (hWc.mul h2).abs |>.add ((hWc.pow 2).mul h3).abs
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show middle.Nonempty from ⟨deltaZero, ⟨le_rfl, hmiddleOrder⟩⟩)
    hBcontinuous
  let CMiddle : ℝ := B x
  have hCMiddle : 0 ≤ CMiddle := by
    dsimp only [CMiddle, B]
    positivity
  have hmiddleBound : ∀ u ∈ middle,
      |deriv W u| + |W u * iteratedDeriv 2 W u| +
        |W u ^ 2 * iteratedDeriv 3 W u| ≤ CMiddle := by
    intro u hu
    have huOpen : u ∈ openUnitInterval := hmiddleSubset hu
    have hWat : ContDiffAt ℝ ∞ W u :=
      (hW u huOpen).contDiffAt (isOpen_Ioo.mem_nhds huOpen)
    have heq (m : ℕ) (_hm : m ≤ 4) :
        iteratedDerivWithin m W middle u = iteratedDeriv m W u :=
      iteratedDerivWithin_eq_iteratedDeriv hmiddleUnique
        (contDiffAt_infty.mp hWat m) hu
    have hbound := hmax hu
    change B u ≤ B x at hbound
    dsimp only [CMiddle, B] at hbound ⊢
    rw [heq 1 (by norm_num), heq 2 (by norm_num), heq 3 (by norm_num),
      iteratedDeriv_one] at hbound
    exact hbound
  let C : ℝ := max CZero (max COne CMiddle)
  refine ⟨C, hCZero.trans (le_max_left _ _), ?_⟩
  intro u hu
  by_cases hleftRegion : u ≤ deltaZero
  · have hbound := hzeroBound u
      ⟨hu.1, hleftRegion.trans hdeltaZeroEta.le⟩
    exact hbound.trans (le_max_left _ _)
  · by_cases hrightRegion : 1 - deltaOne ≤ u
    · have hbound := honeBound u
        ⟨by linarith [hdeltaOneEta.le], hu.2⟩
      exact hbound.trans ((le_max_left COne CMiddle).trans (le_max_right _ _))
    · have huMiddle : u ∈ middle := by
        exact ⟨(le_of_not_ge hleftRegion), (le_of_not_ge hrightRegion)⟩
      exact (hmiddleBound u huMiddle).trans
        ((le_max_right COne CMiddle).trans (le_max_right _ _))

private theorem hasDerivAt_iteratedDeriv_of_contDiffAt_for_profile
    {H : ℝ → ℝ} {x : ℝ} (m : ℕ)
    (hH : ContDiffAt ℝ (m + 1) H x) :
    HasDerivAt (iteratedDeriv m H) (iteratedDeriv (m + 1) H x) x := by
  induction m generalizing H with
  | zero =>
      simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.zero_add] using
        (hH.differentiableAt (by norm_num)).hasDerivAt
  | succ m ih =>
      rw [iteratedDeriv_succ', show m + 1 + 1 = (m + 1) + 1 by omega,
        iteratedDeriv_succ']
      apply ih
      exact hH.derivWithin (m := m + 1) (by norm_num)

/-- Endpoint branch regularity supplies all uniform `W` bounds needed for the B3
density estimate, with the middle interval handled by compactness. -/
theorem waveDensity_fullLineRelativeDerivativeBounds_of_endpoint_regularities
    {input : MainInput} {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hleft : LeftLinearBranchRegularity lambda W)
    (hright : RightLinearBranchRegularity lambda W)
    (hPhi : IsNormalizedWaveProfile input W Phi) :
    FullLineRelativeDerivativeBounds (waveDensity input W Phi) := by
  rcases relativeDerivativeBoundsOnUnitInterval_of_endpoint_regularities
    hW hleft hright with ⟨K, hK, hbound⟩
  have hW0 : ∀ u ∈ openUnitInterval, HasDerivAt W (deriv W u) u := by
    intro u hu
    have hWatInfinity : ContDiffAt ℝ ∞ W u :=
      (hW u hu).contDiffAt (isOpen_Ioo.mem_nhds hu)
    have hWat : ContDiffAt ℝ 1 W u := contDiffAt_infty.mp hWatInfinity 1
    simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.zero_add] using
      hasDerivAt_iteratedDeriv_of_contDiffAt_for_profile 0 hWat
  have hW1 : ∀ u ∈ openUnitInterval,
      HasDerivAt (deriv W) (iteratedDeriv 2 W u) u := by
    intro u hu
    have hWatInfinity : ContDiffAt ℝ ∞ W u :=
      (hW u hu).contDiffAt (isOpen_Ioo.mem_nhds hu)
    have hWat : ContDiffAt ℝ 2 W u := contDiffAt_infty.mp hWatInfinity 2
    simpa only [iteratedDeriv_one] using
      hasDerivAt_iteratedDeriv_of_contDiffAt_for_profile 1 hWat
  have hW2 : ∀ u ∈ openUnitInterval,
      HasDerivAt (iteratedDeriv 2 W) (iteratedDeriv 3 W u) u := by
    intro u hu
    have hWatInfinity : ContDiffAt ℝ ∞ W u :=
      (hW u hu).contDiffAt (isOpen_Ioo.mem_nhds hu)
    have hWat : ContDiffAt ℝ 3 W u := contDiffAt_infty.mp hWatInfinity 3
    simpa only [show 2 + 1 = 3 by norm_num] using
      hasDerivAt_iteratedDeriv_of_contDiffAt_for_profile 2 hWat
  apply waveDensity_fullLineRelativeDerivativeBounds hK hPhi hpos hW0 hW1 hW2
  · intro u hu
    have hb := hbound u hu
    nlinarith [abs_nonneg (W u * iteratedDeriv 2 W u),
      abs_nonneg (W u ^ 2 * iteratedDeriv 3 W u)]
  · intro u hu
    have hb := hbound u hu
    nlinarith [abs_nonneg (deriv W u),
      abs_nonneg (W u ^ 2 * iteratedDeriv 3 W u)]
  · intro u hu
    have hb := hbound u hu
    nlinarith [abs_nonneg (deriv W u),
      abs_nonneg (W u * iteratedDeriv 2 W u)]

end SeriesParallel.Appendix
