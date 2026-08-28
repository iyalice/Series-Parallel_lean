import SeriesParallel.Appendix.HardEdgeConsequences

/-!
# Quantitative estimates for the hard-edge profile

This module proves the right exponential tail and the relative derivative estimate
from the exact one-sided chain-rule identities used in B4.
-/

open Asymptotics Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

private theorem exists_hardEdge_right_exponential_bound_of_ratio
    {input : MainInput} {W Psi : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hratio : ∀ᶠ z in atTop,
      c < hardEdgeDensity input W Psi z / (1 - Psi z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Ici (0 : ℝ),
      1 - Psi z ≤ C * Real.exp (-c * z) := by
  obtain ⟨B, hB⟩ := eventually_atTop.1 hratio
  let b : ℝ := max B 1
  let G : ℝ → ℝ := fun z ↦ Real.log (1 - Psi z) + c * z
  have hBb : B ≤ b := le_max_left _ _
  have hOneb : 1 ≤ b := le_max_right _ _
  have h0b : 0 ≤ b := zero_le_one.trans hOneb
  have hmaps : MapsTo Psi (Ici (0 : ℝ)) (Ico (0 : ℝ) 1) := hPsi.2.2.1
  have hGderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt G
      (-hardEdgeDensity input W Psi z / (1 - Psi z) + c) z := by
    intro z hz
    change 0 < z at hz
    have hzIci : z ∈ Ici (0 : ℝ) := by
      change 0 ≤ z
      exact hz.le
    have hPsiPhase : HasDerivAt Psi (hardEdgeDensity input W Psi z) z := by
      simpa only [hardEdgePhaseRhs, hardEdgeDensity] using hPsi.2.2.2.2.2.1 z hz
    have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - Psi y)
        (-hardEdgeDensity input W Psi z) z := by
      simpa using hPsiPhase.const_sub 1
    have hlog := (Real.hasDerivAt_log
      (sub_ne_zero.mpr (hmaps hzIci).2.ne')).comp z honeSub
    have hlinear := (hasDerivAt_id z).const_mul c
    have hGeq : G =
        (Real.log ∘ fun y : ℝ ↦ 1 - Psi y) + fun y : ℝ ↦ c * id y := by
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
        (fun y hy ↦ (hGderiv y
          (show y ∈ Ioi (0 : ℝ) from (zero_lt_one.trans_le hOneb).trans_le hy.1))
          |>.continuousAt.continuousWithinAt)
        (by
          intro y hy
          refine ⟨-hardEdgeDensity input W Psi y / (1 - Psi y) + c,
            hGderiv y (show y ∈ Ioi (0 : ℝ) from
              (zero_lt_one.trans_le hOneb).trans hy.1), ?_⟩
          calc
            -hardEdgeDensity input W Psi y / (1 - Psi y) + c =
                c - hardEdgeDensity input W Psi y / (1 - Psi y) := by ring
            _ ≤ 0 := sub_nonpos.mpr
              (le_of_lt (hB y (le_trans hBb hy.1.le))))
    have hGle : G z ≤ G b :=
      hanti ⟨le_rfl, hbz⟩ ⟨hbz, le_rfl⟩ hbz
    have hlogle : Real.log (1 - Psi z) ≤ G b + (-c * z) := by
      dsimp only [G] at hGle ⊢
      linarith
    have hexp := Real.exp_le_exp.mpr hlogle
    rw [Real.exp_log (sub_pos.mpr (hmaps hz0).2), Real.exp_add] at hexp
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
      1 - Psi z ≤ 1 := by linarith [(hmaps hz0).1]
      _ = Real.exp (c * b) * Real.exp (-c * b) := hone
      _ ≤ Real.exp (c * b) * Real.exp (-c * z) :=
        mul_le_mul_of_nonneg_left hexpmono (Real.exp_pos _).le
      _ ≤ (Real.exp (G b) + Real.exp (c * b)) * Real.exp (-c * z) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.exp_pos _).le)
          (Real.exp_pos _).le

/-- A positive limiting hard-edge tail ratio gives the right exponential bound. -/
theorem hasRightExponentialTail_of_tail_ratio {input : MainInput}
    {W Psi : ℝ → ℝ} {rho : ℝ} (hrho : 0 < rho)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hratio : Tendsto
      (fun z ↦ hardEdgeDensity input W Psi z / (1 - Psi z)) atTop
      (nhds rho)) :
    HasRightExponentialTail Psi := by
  let c : ℝ := rho / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  have hcrho : c < rho := by dsimp only [c]; linarith
  have heventually : ∀ᶠ z in atTop,
      c < hardEdgeDensity input W Psi z / (1 - Psi z) :=
    (tendsto_order.1 hratio).1 c hcrho
  obtain ⟨C, hC, hbound⟩ :=
    exists_hardEdge_right_exponential_bound_of_ratio hc hPsi heventually
  exact ⟨c, C, hc, hC, hbound⟩

/-- The linear branch at `u=1` supplies the exponential tail in B4. -/
theorem hardEdgeProfile_hasRightExponentialTail {input : MainInput}
    {lambda : ℝ} {W Psi : ℝ → ℝ} (hlambda : 0 < lambda)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hone : HasLinearBranchAtOne lambda W) :
    HasRightExponentialTail Psi := by
  exact hasRightExponentialTail_of_tail_ratio (div_pos input.beta_pos hlambda)
    hPsi (hardEdgeDensity_div_one_sub_profile_tendsto_atTop hlambda hPsi hone)

/-- One-sided chain rules give all three exact differentiated hard-edge identities.
The derivative functions `W1`, `W2`, and `W3` are allowed to be one-sided at zero. -/
theorem hardEdgeDensity_derivative_identities {input : MainInput}
    {W W1 W2 W3 Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hW : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W (W1 u) (Ico 0 1) u)
    (hW1 : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W1 (W2 u) (Ico 0 1) u)
    (hW2 : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W2 (W3 u) (Ico 0 1) u) :
    HardEdgeDensityDerivativeIdentities input W W1 W2 W3 Psi
      (hardEdgeDensity input W Psi) := by
  let s : Set ℝ := Ici 0
  have hsUnique : UniqueDiffOn ℝ s := by
    simpa only [s] using uniqueDiffOn_Ici (0 : ℝ)
  have hmapsIco : MapsTo Psi s (Ico (0 : ℝ) 1) := hPsi.2.2.1
  have hPsiWithin : ∀ z ∈ s,
      HasDerivWithinAt Psi (hardEdgeDensity input W Psi z) s z := by
    intro z hz
    have hzle : 0 ≤ z := hz
    rcases eq_or_lt_of_le hzle with rfl | hzpos
    · simpa only [s, hardEdgePhaseRhs, hardEdgeDensity] using hPsi.2.2.2.2.1
    · exact (by
        simpa only [s, hardEdgePhaseRhs, hardEdgeDensity] using
          (hPsi.2.2.2.2.2.1 z hzpos).hasDerivWithinAt)
  have hq : ∀ z ∈ s, HasDerivWithinAt (hardEdgeDensity input W Psi)
      (hardEdgeDensityD1 input W W1 Psi z) s z := by
    intro z hz
    have hcomp := (hW (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hscaled := hcomp.const_mul input.beta
    apply hscaled.congr_deriv
    simp only [hardEdgeDensity, hardEdgeDensityD1]
    ring
  have hD1 : ∀ z ∈ s, HasDerivWithinAt
      (hardEdgeDensityD1 input W W1 Psi)
      (hardEdgeDensityD2 input W W1 W2 Psi z) s z := by
    intro z hz
    have hWc := (hW (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hW1c := (hW1 (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hscaled := (hWc.mul hW1c).const_mul (input.beta ^ 2)
    have hraw : HasDerivWithinAt
        (fun x : ℝ ↦ input.beta ^ 2 * ((W ∘ Psi) * (W1 ∘ Psi)) x)
        (hardEdgeDensityD2 input W W1 W2 Psi z) s z := by
      apply hscaled.congr_deriv
      simp only [Function.comp_apply, hardEdgeDensity, hardEdgeDensityD2]
      ring
    convert hraw using 1
    funext x
    unfold hardEdgeDensityD1
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  have hD2 : ∀ z ∈ s, HasDerivWithinAt
      (hardEdgeDensityD2 input W W1 W2 Psi)
      (hardEdgeDensityD3 input W W1 W2 W3 Psi z) s z := by
    intro z hz
    have hWc := (hW (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hW1c := (hW1 (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hW2c := (hW2 (Psi z) (hmapsIco hz)).comp z (hPsiWithin z hz) hmapsIco
    have hbracket := (hW1c.pow 2).add (hWc.mul hW2c)
    have hscaled := (hWc.mul hbracket).const_mul (input.beta ^ 3)
    have hraw : HasDerivWithinAt
        (fun x : ℝ ↦ input.beta ^ 3 *
          (((W ∘ Psi) * ((W1 ∘ Psi) ^ 2 + (W ∘ Psi) * (W2 ∘ Psi))) x))
        (hardEdgeDensityD3 input W W1 W2 W3 Psi z) s z := by
      apply hscaled.congr_deriv
      simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        hardEdgeDensity, hardEdgeDensityD3]
      ring
    convert hraw using 1
    funext x
    unfold hardEdgeDensityD2
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  have hfirst : EqOn
      (iteratedDerivWithin 1 (hardEdgeDensity input W Psi) s)
      (hardEdgeDensityD1 input W W1 Psi) s := by
    intro z hz
    rw [iteratedDerivWithin_one]
    exact (hq z hz).derivWithin (hsUnique z hz)
  have hsecond : EqOn
      (iteratedDerivWithin 2 (hardEdgeDensity input W Psi) s)
      (hardEdgeDensityD2 input W W1 W2 Psi) s := by
    intro z hz
    rw [show 2 = 1 + 1 by norm_num, iteratedDerivWithin_succ]
    rw [derivWithin_congr hfirst (hfirst hz)]
    exact (hD1 z hz).derivWithin (hsUnique z hz)
  have hthird : EqOn
      (iteratedDerivWithin 3 (hardEdgeDensity input W Psi) s)
      (hardEdgeDensityD3 input W W1 W2 W3 Psi) s := by
    intro z hz
    rw [show 3 = 2 + 1 by norm_num, iteratedDerivWithin_succ]
    rw [derivWithin_congr hsecond (hsecond hz)]
    exact (hD2 z hz).derivWithin (hsUnique z hz)
  refine
    { qValue := fun z hz ↦ rfl
      first := ?_
      second := ?_
      third := ?_ }
  · intro z hz
    exact hfirst hz
  · intro z hz
    exact hsecond hz
  · intro z hz
    exact hthird hz

/-- Uniform bounds on `W1`, `W W2`, and `W² W3` imply the B4 relative density
bounds once the exact one-sided identities are available. -/
theorem halfLineRelativeDerivativeBounds_of_uniform_W_bounds {input : MainInput}
    {W W1 W2 W3 Psi q : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hbound1 : ∀ u ∈ Ico (0 : ℝ) 1, |W1 u| ≤ K)
    (hbound2 : ∀ u ∈ Ico (0 : ℝ) 1, |W u * W2 u| ≤ K)
    (hbound3 : ∀ u ∈ Ico (0 : ℝ) 1, |W u ^ 2 * W3 u| ≤ K)
    (hids : HardEdgeDensityDerivativeIdentities input W W1 W2 W3 Psi q) :
    HalfLineRelativeDerivativeBounds q := by
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
  intro j hj1 hj3 z hz
  have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  have hu : Psi z ∈ Ico (0 : ℝ) 1 := hPsi.2.2.1 hz
  have hWu : 0 < W (Psi z) := hpos _ hu
  have hE2 : |W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z)| ≤ K ^ 2 + K := by
    calc
      |W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z)| ≤
          |W1 (Psi z) ^ 2| + |W (Psi z) * W2 (Psi z)| := abs_add_le _ _
      _ ≤ K ^ 2 + K := add_le_add (by
        simpa only [abs_pow] using
          pow_le_pow_left₀ (abs_nonneg (W1 (Psi z))) (hbound1 _ hu) 2)
        (hbound2 _ hu)
  have hproduct : |W (Psi z) * W1 (Psi z) * W2 (Psi z)| ≤ K ^ 2 := by
    rw [show W (Psi z) * W1 (Psi z) * W2 (Psi z) =
      W1 (Psi z) * (W (Psi z) * W2 (Psi z)) by ring, abs_mul]
    simpa only [pow_two] using mul_le_mul (hbound1 _ hu) (hbound2 _ hu)
      (abs_nonneg _) hK
  have hE3 : |W1 (Psi z) ^ 3 +
      4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
      W (Psi z) ^ 2 * W3 (Psi z)| ≤ K ^ 3 + 4 * K ^ 2 + K := by
    calc
      |W1 (Psi z) ^ 3 + 4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
          W (Psi z) ^ 2 * W3 (Psi z)| ≤
          |W1 (Psi z) ^ 3 + 4 * W (Psi z) * W1 (Psi z) * W2 (Psi z)| +
            |W (Psi z) ^ 2 * W3 (Psi z)| := abs_add_le _ _
      _ ≤ (|W1 (Psi z) ^ 3| +
            |4 * W (Psi z) * W1 (Psi z) * W2 (Psi z)|) +
            |W (Psi z) ^ 2 * W3 (Psi z)| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (K ^ 3 + 4 * K ^ 2) + K := by
        apply add_le_add
        · apply add_le_add
          · simpa only [abs_pow] using
              pow_le_pow_left₀ (abs_nonneg (W1 (Psi z))) (hbound1 _ hu) 3
          · have hfour := mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ 4 by norm_num)
            simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num),
              mul_assoc] using hfour
        · exact hbound3 _ hu
      _ = K ^ 3 + 4 * K ^ 2 + K := by ring
  rcases hj with rfl | rfl | rfl
  · rw [hids.first z hz, hids.qValue z hz]
    have hcoef : input.beta * |W1 (Psi z)| ≤ M := by
      have hfirst := mul_le_mul_of_nonneg_left (hbound1 _ hu) input.beta_pos.le
      have hsecond : 0 ≤ input.beta ^ 2 * (K ^ 2 + K) :=
        mul_nonneg (sq_nonneg input.beta) hpoly2
      have hthird : 0 ≤ input.beta ^ 3 * (K ^ 3 + 4 * K ^ 2 + K) :=
        mul_nonneg (pow_nonneg input.beta_pos.le 3) hpoly3
      dsimp only [M]
      linarith
    calc
      |input.beta ^ 2 * W (Psi z) * W1 (Psi z)| =
          (input.beta * W (Psi z)) * (input.beta * |W1 (Psi z)|) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos input.beta_pos, abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (Psi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (Psi z)) := by ring
  · rw [hids.second z hz, hids.qValue z hz]
    have hcoef : input.beta ^ 2 *
        |W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z)| ≤ M := by
      have hmiddle := mul_le_mul_of_nonneg_left hE2 (sq_nonneg input.beta)
      have hfirst : 0 ≤ input.beta * K := mul_nonneg input.beta_pos.le hK
      have hthird : 0 ≤ input.beta ^ 3 * (K ^ 3 + 4 * K ^ 2 + K) :=
        mul_nonneg (pow_nonneg input.beta_pos.le 3) hpoly3
      dsimp only [M]
      linarith
    calc
      |input.beta ^ 3 * W (Psi z) *
          (W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z))| =
          (input.beta * W (Psi z)) *
            (input.beta ^ 2 * |W1 (Psi z) ^ 2 + W (Psi z) * W2 (Psi z)|) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos input.beta_pos, abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (Psi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (Psi z)) := by ring
  · rw [hids.third z hz, hids.qValue z hz]
    have hcoef : input.beta ^ 3 * |W1 (Psi z) ^ 3 +
        4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
        W (Psi z) ^ 2 * W3 (Psi z)| ≤ M := by
      have hlast := mul_le_mul_of_nonneg_left hE3 (pow_nonneg input.beta_pos.le 3)
      have hfirst : 0 ≤ input.beta * K := mul_nonneg input.beta_pos.le hK
      have hsecond : 0 ≤ input.beta ^ 2 * (K ^ 2 + K) :=
        mul_nonneg (sq_nonneg input.beta) hpoly2
      dsimp only [M]
      linarith
    calc
      |input.beta ^ 4 * W (Psi z) *
          (W1 (Psi z) ^ 3 + 4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
            W (Psi z) ^ 2 * W3 (Psi z))| =
          (input.beta * W (Psi z)) *
            (input.beta ^ 3 * |W1 (Psi z) ^ 3 +
              4 * W (Psi z) * W1 (Psi z) * W2 (Psi z) +
              W (Psi z) ^ 2 * W3 (Psi z)|) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos input.beta_pos, abs_of_pos hWu]
        ring
      _ ≤ (input.beta * W (Psi z)) * M :=
        mul_le_mul_of_nonneg_left hcoef (mul_pos input.beta_pos hWu).le
      _ = M * (input.beta * W (Psi z)) := by ring

/-- The one-sided derivative hypotheses and the three uniform `W` bounds give the
hard-edge relative density estimate directly. -/
theorem hardEdgeDensity_halfLineRelativeDerivativeBounds {input : MainInput}
    {W W1 W2 W3 Psi : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hW : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W (W1 u) (Ico 0 1) u)
    (hW1 : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W1 (W2 u) (Ico 0 1) u)
    (hW2 : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W2 (W3 u) (Ico 0 1) u)
    (hbound1 : ∀ u ∈ Ico (0 : ℝ) 1, |W1 u| ≤ K)
    (hbound2 : ∀ u ∈ Ico (0 : ℝ) 1, |W u * W2 u| ≤ K)
    (hbound3 : ∀ u ∈ Ico (0 : ℝ) 1, |W u ^ 2 * W3 u| ≤ K) :
    HalfLineRelativeDerivativeBounds (hardEdgeDensity input W Psi) := by
  exact halfLineRelativeDerivativeBounds_of_uniform_W_bounds hK hPsi hpos
    hbound1 hbound2 hbound3
    (hardEdgeDensity_derivative_identities hPsi hW hW1 hW2)

/-- A single constant controls the one-sided relative `W` derivatives on `[0,1)`. -/
def RelativeDerivativeBoundsOnHalfOpenUnitInterval (W : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Ico (0 : ℝ) 1,
    |iteratedDerivWithin 1 W (Ico 0 1) u| +
      |W u * iteratedDerivWithin 2 W (Ico 0 1) u| +
      |W u ^ 2 * iteratedDerivWithin 3 W (Ico 0 1) u| ≤ C

/-- Smoothness at the hard edge, the right-endpoint B2 estimate, and a compact
middle interval give the uniform three-term bound required in B4. -/
theorem relativeDerivativeBoundsOnHalfOpenUnitInterval_of_rightEndpointRegularity
    {lambda : ℝ} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hright : RightLinearBranchRegularity lambda W) :
    RelativeDerivativeBoundsOnHalfOpenUnitInterval W := by
  rcases hright.relativeDerivativeBounds with
    ⟨eta, heta, CRight, hCRight, hrightBound⟩
  let delta : ℝ := min (eta / 2) (1 / 2)
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact lt_min (half_pos heta) (by norm_num)
  have hdeltaEta : delta < eta := by
    calc
      delta ≤ eta / 2 := min_le_left _ _
      _ < eta := half_lt_self heta
  have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
  let compactPart : Set ℝ := Icc 0 (1 - delta)
  have hcompactSubset : compactPart ⊆ Ico (0 : ℝ) 1 := by
    intro u hu
    change u ∈ Icc (0 : ℝ) (1 - delta) at hu
    exact ⟨hu.1, by linarith [hu.2, hdeltaPos]⟩
  have hWthree : ContDiffOn ℝ 3 W (Ico (0 : ℝ) 1) :=
    contDiffOn_infty.mp hW 3
  have hunique : UniqueDiffOn ℝ (Ico (0 : ℝ) 1) :=
    uniqueDiffOn_Ico (0 : ℝ) 1
  let B : ℝ → ℝ := fun u ↦
    |iteratedDerivWithin 1 W (Ico 0 1) u| +
      |W u * iteratedDerivWithin 2 W (Ico 0 1) u| +
      |W u ^ 2 * iteratedDerivWithin 3 W (Ico 0 1) u|
  have hBcontinuous : ContinuousOn B compactPart := by
    have hWc := hWthree.continuousOn
    have h1 := hWthree.continuousOn_iteratedDerivWithin (m := 1)
      (by norm_num) hunique
    have h2 := hWthree.continuousOn_iteratedDerivWithin (m := 2)
      (by norm_num) hunique
    have h3 := hWthree.continuousOn_iteratedDerivWithin (m := 3)
      (by norm_num) hunique
    dsimp only [B]
    exact (h1.abs.add (hWc.mul h2).abs |>.add ((hWc.pow 2).mul h3).abs).mono
      hcompactSubset
  have hcompactNonempty : compactPart.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : ℝ) ∈ Icc 0 (1 - delta)
    constructor
    · exact le_rfl
    · linarith
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hcompactNonempty hBcontinuous
  let CCompact : ℝ := B x
  have hCCompact : 0 ≤ CCompact := by
    dsimp only [CCompact, B]
    positivity
  have hcompactBound : ∀ u ∈ compactPart, B u ≤ CCompact := by
    intro u hu
    have hbound := hmax hu
    change B u ≤ B x at hbound
    exact hbound
  let C : ℝ := max CCompact CRight
  refine ⟨C, hCCompact.trans (le_max_left _ _), ?_⟩
  intro u hu
  by_cases hrightRegion : 1 - delta ≤ u
  · have huOpen : u ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hrightRegion, hdeltaHalf], hu.2⟩
    have hWat : ContDiffAt ℝ ∞ W u :=
      ((hW.mono Ioo_subset_Ico_self) u huOpen).contDiffAt
        (isOpen_Ioo.mem_nhds huOpen)
    have heq (m : ℕ) : iteratedDerivWithin m W (Ico 0 1) u =
        iteratedDeriv m W u :=
      iteratedDerivWithin_eq_iteratedDeriv hunique
        (contDiffAt_infty.mp hWat m) hu
    have hraw := hrightBound u ⟨by linarith [hdeltaEta.le], hu.2⟩
    rw [heq 1, heq 2, heq 3, iteratedDeriv_one] at ⊢
    exact hraw.trans (le_max_right _ _)
  · have huCompact : u ∈ compactPart := ⟨hu.1, le_of_not_ge hrightRegion⟩
    exact (hcompactBound u huCompact).trans (le_max_left _ _)

/-- The source-level right endpoint regularity supplies both the one-sided chain-rule
witnesses and all global `W` bounds needed for the B4 density estimate. -/
theorem hardEdgeDensity_halfLineRelativeDerivativeBounds_of_rightEndpointRegularity
    {input : MainInput} {lambda : ℝ} {W Psi : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hright : RightLinearBranchRegularity lambda W)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    HalfLineRelativeDerivativeBounds (hardEdgeDensity input W Psi) := by
  let s : Set ℝ := Ico 0 1
  let W1 : ℝ → ℝ := iteratedDerivWithin 1 W s
  let W2 : ℝ → ℝ := iteratedDerivWithin 2 W s
  let W3 : ℝ → ℝ := iteratedDerivWithin 3 W s
  have hunique : UniqueDiffOn ℝ s := by
    simpa only [s] using uniqueDiffOn_Ico (0 : ℝ) 1
  have hwitness (u : ℝ) (hu : u ∈ s) (m : ℕ) (hm : m ≤ 2) :
      HasDerivWithinAt (iteratedDerivWithin m W s)
        (iteratedDerivWithin (m + 1) W s u) s u := by
    have hthree : ContDiffWithinAt ℝ 3 W s u :=
      contDiffWithinAt_infty.mp (hW u hu) 3
    have hinsert : UniqueDiffOn ℝ (insert u s) := by
      rw [insert_eq_of_mem hu]
      exact hunique
    have hdifferentiable := hthree.differentiableWithinAt_iteratedDerivWithin
      (m := m) (by norm_num; omega) hinsert
    apply hdifferentiable.hasDerivWithinAt.congr_deriv
    rw [iteratedDerivWithin_succ]
  have hWderiv : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W (W1 u) (Ico 0 1) u := by
    intro u hu
    simpa only [s, W1, iteratedDerivWithin_zero] using hwitness u hu 0 (by norm_num)
  have hW1deriv : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W1 (W2 u) (Ico 0 1) u := by
    intro u hu
    simpa only [s, W1, W2] using hwitness u hu 1 (by norm_num)
  have hW2deriv : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt W2 (W3 u) (Ico 0 1) u := by
    intro u hu
    simpa only [s, W2, W3] using hwitness u hu 2 (by norm_num)
  rcases relativeDerivativeBoundsOnHalfOpenUnitInterval_of_rightEndpointRegularity
    hW hright with ⟨K, hK, hbound⟩
  apply hardEdgeDensity_halfLineRelativeDerivativeBounds hK hPsi hpos
    hWderiv hW1deriv hW2deriv
  · intro u hu
    have hb := hbound u hu
    dsimp only [W1, s]
    nlinarith [abs_nonneg (W u * iteratedDerivWithin 2 W (Ico 0 1) u),
      abs_nonneg (W u ^ 2 * iteratedDerivWithin 3 W (Ico 0 1) u)]
  · intro u hu
    have hb := hbound u hu
    dsimp only [W2, s]
    nlinarith [abs_nonneg (iteratedDerivWithin 1 W (Ico 0 1) u),
      abs_nonneg (W u ^ 2 * iteratedDerivWithin 3 W (Ico 0 1) u)]
  · intro u hu
    have hb := hbound u hu
    dsimp only [W3, s]
    nlinarith [abs_nonneg (iteratedDerivWithin 1 W (Ico 0 1) u),
      abs_nonneg (W u * iteratedDerivWithin 2 W (Ico 0 1) u)]

/-- Source-facing specialization of the compactness bridge to the subcritical
canonical transform. -/
theorem WSolution_hardEdgeDensity_halfLineRelativeDerivativeBounds
    {input : MainInput} {lambda : ℝ} {Psi : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar)
    (hright : RightLinearBranchRegularity lambda (WSolution lambda hlambda))
    (hPsi : IsNormalizedHardEdgeProfile input (WSolution lambda hlambda) Psi) :
    HalfLineRelativeDerivativeBounds
      (hardEdgeDensity input (WSolution lambda hlambda) Psi) := by
  exact hardEdgeDensity_halfLineRelativeDerivativeBounds_of_rightEndpointRegularity
    (WSolution_contDiffOn_infty_Ico_of_lt_lambdaStar hlambda hsubcritical)
    (WSolution_pos_Ico_of_lt_lambdaStar hlambda hsubcritical) hright hPsi

end SeriesParallel.Appendix
