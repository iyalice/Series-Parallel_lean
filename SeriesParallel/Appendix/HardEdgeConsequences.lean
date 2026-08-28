import SeriesParallel.Appendix.HardEdgeProfile
import SeriesParallel.Appendix.ProfileMeasures

/-!
# Consequences for the hard-edge profile
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-- The subcritical canonical transform is one-sided `C∞` on all of `[0,1)`. -/
theorem WSolution_contDiffOn_infty_Ico_of_lt_lambdaStar {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ContDiffOn ℝ ∞ (WSolution lambda hlambda) (Ico (0 : ℝ) 1) := by
  have hleft := WSolution_contDiffOn_infty_zero_of_lt_lambdaStar hlambda hsubcritical
  have hinterior := WSolution_contDiffOn_infty_interior lambda hlambda
  intro u hu
  rcases eq_or_lt_of_le hu.1 with rfl | hupos
  · have h0 := hleft 0 ⟨le_rfl, by norm_num⟩
    apply h0.congr_set
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    apply propext
    constructor
    · intro h
      exact ⟨h.1, hx.trans (by norm_num)⟩
    · intro h
      exact ⟨h.1, hx.le⟩
  · exact (hinterior u ⟨hupos, hu.2⟩).contDiffAt
      (isOpen_Ioo.mem_nhds ⟨hupos, hu.2⟩) |>.contDiffWithinAt

/-- The ratio `qλ/(1-Psiλ)` at the right endpoint, as stated in B4. -/
theorem hardEdgeDensity_div_one_sub_profile_tendsto_atTop {input : MainInput}
    {lambda : ℝ} {W Psi : ℝ → ℝ} (hlambda : 0 < lambda)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hone : HasLinearBranchAtOne lambda W) :
    Tendsto (fun z ↦ hardEdgeDensity input W Psi z / (1 - Psi z)) atTop
      (𝓝 (input.beta / lambda)) := by
  have hPsiLT : Tendsto Psi atTop (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hPsi.2.2.2.2.2.2
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
      exact (hPsi.2.2.1 hz).2
  have hcomp := hone.comp_tendsto hPsiLT
  have hequiv : (fun z : ℝ ↦ W (Psi z)) ~[atTop]
      (fun z : ℝ ↦ (1 - Psi z) / lambda) := by
    refine (hcomp.congr_left (Filter.Eventually.of_forall fun z ↦ ?_)).congr_right
      (Filter.Eventually.of_forall fun z ↦ ?_)
    · rfl
    · rfl
  have hdenom : ∀ᶠ z in atTop, (1 - Psi z) / lambda ≠ 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact div_ne_zero (sub_ne_zero.mpr (hPsi.2.2.1 hz).2.ne') hlambda.ne'
  have hratio : Tendsto (fun z : ℝ ↦ W (Psi z) / ((1 - Psi z) / lambda))
      atTop (𝓝 1) := (isEquivalent_iff_tendsto_one hdenom).mp hequiv
  have hscaled := (tendsto_const_nhds (x := input.beta / lambda)).mul hratio
  have hscaled' : Tendsto
      (fun z : ℝ ↦ (input.beta / lambda) *
        (W (Psi z) / ((1 - Psi z) / lambda))) atTop
      (𝓝 (input.beta / lambda)) := by
    simpa only [one_mul, mul_one] using hscaled
  apply (tendsto_congr' ?_).2 hscaled'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
  unfold hardEdgeDensity
  field_simp [hlambda.ne', sub_ne_zero.mpr (hPsi.2.2.1 hz).2.ne']

/-- The subcritical canonical branch gives the hard-edge profile equation on the
closed half-line, with the derivative at zero interpreted from the right. -/
theorem WSolution_hardEdgeProfileEquation {input : MainInput} {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar)
    {Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input (WSolution lambda hlambda) Psi) :
    ∀ z ∈ Ici (0 : ℝ),
      input.a * hardEdgeDensity input (WSolution lambda hlambda) Psi z *
          derivWithin (hardEdgeDensity input (WSolution lambda hlambda) Psi)
            (Ici 0) z +
          2 * Psi z * (1 - Psi z) =
        input.kappa lambda *
          hardEdgeDensity input (WSolution lambda hlambda) Psi z := by
  intro z hz
  have hmaps : MapsTo Psi (Ici (0 : ℝ)) (Ici (0 : ℝ)) :=
    fun x hx ↦ (hPsi.2.2.1 hx).1
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with rfl | hzpos
  · have hW0pos := WSolution_zero_pos_of_lt_lambdaStar hlambda hsubcritical
    have hW0 := WSolution_hasDerivWithinAt_zero_of_lt_lambdaStar
      hlambda hsubcritical
    have hode :
        WSolution lambda hlambda (Psi 0) ^ 2 *
              (lambda / WSolution lambda hlambda 0) -
            lambda * WSolution lambda hlambda (Psi 0) +
            Psi 0 * (1 - Psi 0) = 0 := by
      rw [hPsi.2.2.2.1]
      (field_simp [hW0pos.ne']; ring)
    exact hardEdgeProfileEquationWithin_of_phase_of_wODE
      (show (0 : ℝ) ∈ Ici 0 by simp) hPsi.2.2.2.2.1 hmaps
      (by simpa only [hPsi.2.2.2.1] using hW0) hode
  · have hPsiRange : Psi z ∈ openUnitInterval := by
      have hstrict := hPsi.2.1 (show (0 : ℝ) ∈ Ici 0 by simp) hz hzpos
      exact ⟨by simpa only [hPsi.2.2.2.1] using hstrict,
        (hPsi.2.2.1 hz).2⟩
    have hWode := WSolution_satisfiesWODEAt lambda hlambda (Psi z) hPsiRange
    exact hardEdgeProfileEquationWithin_of_phase_of_wODE hz
      (hPsi.2.2.2.2.2.1 z hzpos).hasDerivWithinAt hmaps
      hWode.1.hasDerivAt.hasDerivWithinAt (by
        simpa only [wODEValue] using hWode.2)

end SeriesParallel.Appendix
