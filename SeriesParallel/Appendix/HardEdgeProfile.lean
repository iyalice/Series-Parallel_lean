import SeriesParallel.Appendix.Profiles

/-!
# The normalized hard-edge phase

This module constructs the one-sided inverse of `halfLineCoordinate`.  Uniqueness is
deliberately stated as equality on `[0,∞)`: the defining predicate places no conditions
on negative arguments.
-/

open Asymptotics Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

@[simp]
theorem halfLineCoordinate_zero (input : MainInput) (W : ℝ → ℝ) :
    halfLineCoordinate input W 0 = 0 := by
  simp [halfLineCoordinate]

/-- The right logarithmic divergence of the hard-edge coordinate, coming from the
linear branch of `W` at `u=1`. -/
theorem halfLineCoordinate_tendsto_atTop {input : MainInput} {lambda : ℝ}
    {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hlinear : HasLinearBranchAtOne lambda W) :
    Tendsto (halfLineCoordinate input W) (𝓝[<] (1 : ℝ)) atTop := by
  have hbeta : (fun _ : ℝ ↦ input.beta) ~[𝓝[<] (1 : ℝ)]
      (fun _ : ℝ ↦ input.beta) := IsEquivalent.refl
  have hmul := hbeta.mul hlinear
  have hequiv : (fun s : ℝ ↦ input.beta * W s) ~[𝓝[<] (1 : ℝ)]
      (fun s : ℝ ↦ (input.beta / lambda) * (1 - s)) := by
    refine hmul.congr ?_ ?_
    · intro s
      dsimp
      field_simp [hlambda.ne']
    · intro s
      dsimp
      field_simp [hlambda.ne']
  have hgtZero : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s :=
    (show ∀ᶠ s in 𝓝 (1 : ℝ), s ∈ Ioi 0 from
      Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hcontinuous : ContinuousOn (fun s : ℝ ↦ input.beta * W s) (Ico 0 1) :=
    continuousOn_const.mul hW.continuousOn
  have hpositive : ∀ s ∈ Ico (0 : ℝ) 1, 0 < input.beta * W s := by
    intro s hs
    exact mul_pos input.beta_pos (hpos s hs)
  change Tendsto (fun v : ℝ ↦
    ∫ s in (0 : ℝ)..v, (input.beta * W s)⁻¹) (𝓝[<] (1 : ℝ)) atTop
  exact logarithmicIntegralDivergenceRight_of_continuousOn_pos
    (fun s : ℝ ↦ input.beta * W s) (input.beta / lambda) 0
    (div_pos input.beta_pos hlambda) (by norm_num) hcontinuous hpositive hequiv

theorem halfLineCoordinate_derivWithin_pos_zero {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    0 < derivWithin (halfLineCoordinate input W) (Ici 0) 0 := by
  rw [(halfLineCoordinate_hasDerivWithinAt_zero hW hpos).derivWithin
    (uniqueDiffWithinAt_Ici (0 : ℝ))]
  unfold halfLineCoordinateIntegrand
  exact inv_pos.mpr (mul_pos input.beta_pos (hpos 0 ⟨le_rfl, zero_lt_one⟩))

theorem halfLineCoordinate_deriv_pos {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) {v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (halfLineCoordinate input W) v := by
  rw [(halfLineCoordinate_hasDerivAt hW hpos hv).deriv]
  unfold halfLineCoordinateIntegrand
  exact inv_pos.mpr (mul_pos input.beta_pos (hpos v ⟨hv.1.le, hv.2⟩))

/-- The coordinate itself is strictly increasing on its half-open domain. -/
theorem halfLineCoordinate_strictMonoOn {input : MainInput} {W : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    StrictMonoOn (halfLineCoordinate input W) (Ico (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico (0 : ℝ) 1)
  · exact (halfLineCoordinate_contDiffOn_Ico hW hpos).continuousOn
  · rw [interior_Ico]
    intro v hv
    exact halfLineCoordinate_deriv_pos hW hpos hv

private theorem halfOpenInverse_tendsto_atTop_one {theta inverse : ℝ → ℝ}
    (hmaps : MapsTo inverse (Ici (0 : ℝ)) (Ico (0 : ℝ) 1))
    (hleftInverse : ∀ v ∈ Ico (0 : ℝ) 1, inverse (theta v) = v)
    (hinverseStrict : StrictMonoOn inverse (Ici (0 : ℝ)))
    (hthetaStrict : StrictMonoOn theta (Ico (0 : ℝ) 1))
    (hthetaZero : theta 0 = 0) :
    Tendsto inverse atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let e : ℝ := (max a 0 + 1) / 2
    have hmaxlt : max a (0 : ℝ) < 1 := max_lt ha zero_lt_one
    have hepos : 0 < e := by
      have hmaxnonneg : 0 ≤ max a (0 : ℝ) := le_max_right _ _
      dsimp only [e]
      nlinarith
    have heltOne : e < 1 := by
      dsimp only [e]
      nlinarith
    have haelt : a < e := by
      have hale : a ≤ max a (0 : ℝ) := le_max_left _ _
      dsimp only [e]
      nlinarith
    have hthetaPos : 0 < theta e := by
      calc
        0 = theta 0 := hthetaZero.symm
        _ < theta e := hthetaStrict ⟨le_rfl, zero_lt_one⟩
          ⟨hepos.le, heltOne⟩ hepos
    filter_upwards [eventually_gt_atTop (theta e)] with z hz
    calc
      a < e := haelt
      _ = inverse (theta e) := (hleftInverse e ⟨hepos.le, heltOne⟩).symm
      _ < inverse z := hinverseStrict hthetaPos.le (hthetaPos.trans hz).le hz
  · intro b hb
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact (hmaps hz).2.trans hb

/-- The inverse-coordinate construction of the normalized hard-edge phase.  The
uniqueness conclusion is only on `[0,∞)`, exactly where the profile predicate is
defined. -/
theorem exists_normalizedHardEdgeProfile_uniqueOn {input : MainInput} {lambda : ℝ}
    {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hlinear : HasLinearBranchAtOne lambda W) :
    ∃ Psi : ℝ → ℝ, IsNormalizedHardEdgeProfile input W Psi ∧
      ∀ Phi : ℝ → ℝ, IsExactHardEdgeProfile input W Phi →
        EqOn Phi Psi (Ici (0 : ℝ)) := by
  let theta : ℝ → ℝ := halfLineCoordinate input W
  have hthetaZero : theta 0 = 0 := halfLineCoordinate_zero input W
  have hthetaSmooth : ContDiffOn ℝ ∞ theta (Ico (0 : ℝ) 1) :=
    halfLineCoordinate_contDiffOn_Ico hW hpos
  have hthetaContinuous : ContinuousOn theta (Ico (0 : ℝ) 1) :=
    hthetaSmooth.continuousOn
  have hthetaDerivZero : 0 < derivWithin theta (Ici 0) 0 :=
    halfLineCoordinate_derivWithin_pos_zero hW hpos
  have hthetaDeriv : ∀ v ∈ Ioo (0 : ℝ) 1, 0 < deriv theta v := by
    intro v hv
    exact halfLineCoordinate_deriv_pos hW hpos hv
  have hthetaInfinity : Tendsto theta (𝓝[<] (1 : ℝ)) atTop :=
    halfLineCoordinate_tendsto_atTop hlambda hW hpos hlinear
  rcases ManualInterfaces.MI08_half_open_global_inverse theta hthetaZero
      hthetaContinuous hthetaSmooth hthetaDerivZero hthetaDeriv hthetaInfinity with
    ⟨Psi, hmaps, hPsiZero, hleftInverse, hrightInverse, hPsiSmooth,
      hPsiDeriv, hPsiDerivZero⟩
  have hPsiPos : ∀ z ∈ Ioi (0 : ℝ), 0 < Psi z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hzIci : z ∈ Ici (0 : ℝ) := hzpos.le
    have hnonneg : 0 ≤ Psi z := (hmaps hzIci).1
    exact lt_of_le_of_ne hnonneg fun heq ↦ by
      have hright := hrightInverse z hzIci
      rw [← heq, hthetaZero] at hright
      exact hzpos.ne' hright.symm
  have hPsiPhaseZero :
      HasDerivWithinAt Psi (hardEdgePhaseRhs input W Psi 0) (Ici 0) 0 := by
    have htheta := halfLineCoordinate_hasDerivWithinAt_zero (input := input) hW hpos
    apply hPsiDerivZero.congr_deriv
    rw [htheta.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))]
    unfold halfLineCoordinateIntegrand hardEdgePhaseRhs
    rw [hPsiZero, inv_inv]
  have hPsiPhase : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivAt Psi (hardEdgePhaseRhs input W Psi z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hzIci : z ∈ Ici (0 : ℝ) := hzpos.le
    have hPsiRange : Psi z ∈ Ioo (0 : ℝ) 1 :=
      ⟨hPsiPos z hz, (hmaps hzIci).2⟩
    have htheta := halfLineCoordinate_hasDerivAt (input := input) hW hpos hPsiRange
    apply (hPsiDeriv z hz).congr_deriv
    rw [htheta.deriv]
    unfold halfLineCoordinateIntegrand hardEdgePhaseRhs
    rw [inv_inv]
  have hPsiStrict : StrictMonoOn Psi (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hPsiSmooth.continuousOn
    rw [interior_Ici]
    intro z hz
    have hzpos : 0 < z := hz
    have hzIci : z ∈ Ici (0 : ℝ) := hzpos.le
    rw [(hPsiPhase z hz).deriv]
    unfold hardEdgePhaseRhs
    exact mul_pos input.beta_pos (hpos (Psi z) (hmaps hzIci))
  have hthetaStrict : StrictMonoOn theta (Ico (0 : ℝ) 1) :=
    halfLineCoordinate_strictMonoOn hW hpos
  have hPsiInfinity : Tendsto Psi atTop (𝓝 1) :=
    halfOpenInverse_tendsto_atTop_one hmaps hleftInverse hPsiStrict hthetaStrict
      hthetaZero
  have hPsiProfile : IsNormalizedHardEdgeProfile input W Psi :=
    ⟨hPsiSmooth, hPsiStrict, hmaps, hPsiZero, hPsiPhaseZero, hPsiPhase,
      hPsiInfinity⟩
  refine ⟨Psi, hPsiProfile, ?_⟩
  intro Phi hPhi
  have hPhiStrict : StrictMonoOn Phi (Ici (0 : ℝ)) := hPhi.strictMonoOn hpos
  have hPhiMaps : MapsTo Phi (Ici (0 : ℝ)) (Ico (0 : ℝ) 1) := hPhi.2.1
  have hPhiZero : Phi 0 = 0 := hPhi.2.2.1
  have hPhiPhaseZero :
      HasDerivWithinAt Phi (hardEdgePhaseRhs input W Phi 0) (Ici 0) 0 :=
    hPhi.2.2.2.1
  have hPhiPhase : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivAt Phi (hardEdgePhaseRhs input W Phi z) z :=
    hPhi.2.2.2.2.1
  let error : ℝ → ℝ := fun z ↦ theta (Phi z) - z
  have hPhiMapsIci : MapsTo Phi (Ici (0 : ℝ)) (Ici (0 : ℝ)) :=
    fun z hz ↦ (hPhiMaps hz).1
  have herrorDeriv : ∀ z ∈ Ici (0 : ℝ),
      HasDerivWithinAt error 0 (Ici (0 : ℝ)) z := by
    intro z hz
    have hzle : 0 ≤ z := hz
    rcases eq_or_lt_of_le hzle with rfl | hzpos
    · have htheta := halfLineCoordinate_hasDerivWithinAt_zero (input := input) hW hpos
      have hthetaAtPhiZero : HasDerivWithinAt theta
          (halfLineCoordinateIntegrand input W 0) (Ici 0) (Phi 0) := by
        simpa only [theta, hPhiZero] using htheta
      have hcomp := hthetaAtPhiZero.comp 0 hPhiPhaseZero hPhiMapsIci
      have hone : HasDerivWithinAt (fun z : ℝ ↦ theta (Phi z)) 1 (Ici 0) 0 := by
        apply hcomp.congr_deriv
        unfold halfLineCoordinateIntegrand hardEdgePhaseRhs
        rw [hPhiZero, inv_mul_cancel₀]
        exact mul_ne_zero input.beta_ne_zero
          (hpos 0 ⟨le_rfl, zero_lt_one⟩).ne'
      change HasDerivWithinAt ((fun x : ℝ ↦ theta (Phi x)) - id) 0 (Ici 0) 0
      simpa only [sub_self] using
        hone.sub (hasDerivWithinAt_id (x := (0 : ℝ)) (Ici 0))
    · have hPhiPos : 0 < Phi z := by
        have hstrictValue := hPhiStrict (show (0 : ℝ) ∈ Ici 0 by simp) hz hzpos
        simpa only [hPhiZero] using hstrictValue
      have hPhiRange : Phi z ∈ Ioo (0 : ℝ) 1 :=
        ⟨hPhiPos, (hPhiMaps hz).2⟩
      have htheta := halfLineCoordinate_hasDerivAt (input := input) hW hpos hPhiRange
      have hcomp := htheta.comp z (hPhiPhase z hzpos)
      have hone : HasDerivAt (fun z : ℝ ↦ theta (Phi z)) 1 z := by
        apply hcomp.congr_deriv
        unfold halfLineCoordinateIntegrand hardEdgePhaseRhs
        rw [inv_mul_cancel₀]
        exact mul_ne_zero input.beta_ne_zero (hpos (Phi z)
          ⟨hPhiPos.le, (hPhiMaps hz).2⟩).ne'
      change HasDerivWithinAt ((fun x : ℝ ↦ theta (Phi x)) - id) 0 (Ici 0) z
      have herrorAt : HasDerivAt ((fun x : ℝ ↦ theta (Phi x)) - id) 0 z := by
        simpa only [sub_self] using hone.sub (hasDerivAt_id z)
      exact herrorAt.hasDerivWithinAt
  intro z hz
  have hbound := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) herrorDeriv (fun _ _ ↦ by simp) (show (0 : ℝ) ∈ Ici 0 by simp) hz
  have herrorEq : error z = error 0 := by
    have hnorm : ‖error z - error 0‖ = 0 :=
      le_antisymm (by simpa using hbound) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have herrorZero : error 0 = 0 := by
    simp [error, hPhiZero, hthetaZero]
  have hcoordinate : theta (Phi z) = z := by
    have : error z = 0 := herrorEq.trans herrorZero
    dsimp only [error] at this
    linarith
  calc
    Phi z = Psi (theta (Phi z)) := (hleftInverse (Phi z) (hPhiMaps hz)).symm
    _ = Psi z := by rw [hcoordinate]

/-- Exact source-facing B4 existence and uniqueness.  The constructed profile retains
the stronger internal regularity, while uniqueness ranges over precisely the monotone
half-line candidates stated in the source and is only `EqOn` on `[0,∞)`. -/
theorem exists_exactHardEdgeProfile_uniqueOn {input : MainInput} {lambda : ℝ}
    {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hlinear : HasLinearBranchAtOne lambda W) :
    ∃ Psi : ℝ → ℝ, IsExactHardEdgeProfile input W Psi ∧
      ∀ Phi : ℝ → ℝ, IsExactHardEdgeProfile input W Phi →
        EqOn Phi Psi (Ici (0 : ℝ)) := by
  rcases exists_normalizedHardEdgeProfile_uniqueOn hlambda hW hpos hlinear with
    ⟨Psi, hPsi, hunique⟩
  exact ⟨Psi, hPsi.toExact, hunique⟩

end SeriesParallel.Appendix
