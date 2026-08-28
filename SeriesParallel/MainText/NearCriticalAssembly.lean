/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.DiffusionCoefficientClosedForm
import SeriesParallel.MainText.MainTextStatementContract
import SeriesParallel.Appendix.AdmissibleHalfline
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Near-critical source assembly

This module first identifies the source-facing boundary-value problem with the appendix's
canonical representative.  The intrinsic speed asymptotics are assembled below once both
barriers are available.
-/

open Asymptotics Filter Set
open scoped Topology

namespace SeriesParallel.MainText

/-- Forgetting the canonical extension gives the literal source boundary-value problem. -/
theorem sourceWSolution_of_appendixBoundarySolution
    {lambda : ℝ} {W : ℝ → ℝ}
    (hW : SeriesParallel.Appendix.IsWBoundarySolution lambda W) :
    SourceWSolution lambda W := by
  rcases hW with ⟨_, hcontinuous, hcontDiff, hode, hboundary⟩
  refine ⟨?_, ?_, ?_, ?_, hboundary.1, hboundary.2.1⟩
  · simpa only [SeriesParallel.Appendix.unitInterval] using hcontinuous
  · simpa only [SeriesParallel.Appendix.openUnitInterval] using hcontDiff
  · intro u hu
    have hodeAt := hode u (by
      simpa only [SeriesParallel.Appendix.openUnitInterval] using hu)
    simpa only [SeriesParallel.Appendix.wODEValue] using hodeAt.2
  · intro u hu
    exact hboundary.2.2 u (by
      simpa only [SeriesParallel.Appendix.openUnitInterval] using hu)

/-- Canonicalizing a literal source solution recovers the appendix boundary predicate. -/
theorem appendixBoundarySolution_of_sourceWSolution
    {lambda : ℝ} {W : ℝ → ℝ} (hW : SourceWSolution lambda W) :
    SeriesParallel.Appendix.IsWBoundarySolution lambda
      (SeriesParallel.Appendix.canonicalUnitExtension W) := by
  rcases hW with ⟨hcontinuous, hcontDiff, hode, hpositive, hzero, hone⟩
  let Wc := SeriesParallel.Appendix.canonicalUnitExtension W
  have heqIcc : EqOn Wc W (Icc (0 : ℝ) 1) := by
    simpa only [Wc, SeriesParallel.Appendix.unitInterval] using
      SeriesParallel.Appendix.canonicalUnitExtension_eq_on_unitInterval W
  have hcontinuousC : ContinuousOn Wc (Icc (0 : ℝ) 1) :=
    hcontinuous.congr heqIcc
  have hcontDiffC : ContDiffOn ℝ 1 Wc (Ioo (0 : ℝ) 1) :=
    hcontDiff.congr fun _ hu ↦ heqIcc ⟨hu.1.le, hu.2.le⟩
  refine ⟨SeriesParallel.Appendix.canonicalUnitExtension_isCanonical W,
    ?_, ?_, ?_, ?_⟩
  · simpa only [SeriesParallel.Appendix.unitInterval] using hcontinuousC
  · simpa only [SeriesParallel.Appendix.openUnitInterval] using hcontDiffC
  · intro u huAppendix
    have hu : u ∈ Ioo (0 : ℝ) 1 := by
      simpa only [SeriesParallel.Appendix.openUnitInterval] using huAppendix
    have heqNhds : Wc =ᶠ[𝓝 u] W :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hu) fun x hx ↦
        heqIcc ⟨hx.1.le, hx.2.le⟩
    have hdifferentiable : DifferentiableAt ℝ Wc u :=
      ((hcontDiffC u hu).differentiableWithinAt (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hu)
    refine ⟨hdifferentiable, ?_⟩
    change Wc u ^ 2 * deriv Wc u - lambda * Wc u + u * (1 - u) = 0
    rw [heqIcc ⟨hu.1.le, hu.2.le⟩, heqNhds.deriv_eq]
    exact hode u hu
  · refine ⟨?_, ?_, ?_⟩
    · change Wc 0 = 0
      rw [heqIcc (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
      exact hzero
    · change Wc 1 = 0
      rw [heqIcc (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
      exact hone
    · intro u huAppendix
      have hu : u ∈ Ioo (0 : ℝ) 1 := by
        simpa only [SeriesParallel.Appendix.openUnitInterval] using huAppendix
      change 0 < Wc u
      rw [heqIcc ⟨hu.1.le, hu.2.le⟩]
      exact hpositive u hu

/-- The literal source admissible set is exactly the appendix shooting admissible set. -/
theorem mainAdmissible_eq_appendixAdmissible :
    mainAdmissible = SeriesParallel.Appendix.admissibleSet := by
  ext lambda
  constructor
  · rintro ⟨hlambda, W, hW⟩
    exact SeriesParallel.Appendix.mem_admissibleSet_of_boundarySolution hlambda
      (appendixBoundarySolution_of_sourceWSolution hW)
  · rintro ⟨hlambda, hzero⟩
    refine ⟨hlambda, SeriesParallel.Appendix.WSolution lambda hlambda, ?_⟩
    exact sourceWSolution_of_appendixBoundarySolution
      (SeriesParallel.Appendix.WSolution_isBoundarySolution hlambda hzero)

theorem mainAdmissible_eq_Ici_lambdaStar :
    mainAdmissible = Ici SeriesParallel.Appendix.lambdaStar := by
  rw [mainAdmissible_eq_appendixAdmissible,
    SeriesParallel.Appendix.admissibleSet_eq_Ici_lambdaStar]

/-- The appendix critical parameter is the least literal source-admissible parameter. -/
theorem lambdaStar_isLeast_mainAdmissible :
    IsLeast mainAdmissible SeriesParallel.Appendix.lambdaStar := by
  rw [mainAdmissible_eq_Ici_lambdaStar]
  exact isLeast_Ici

theorem nearCriticalConstant_pos :
    0 < 2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar := by
  exact mul_pos (mul_pos (by norm_num) (Real.cbrt_pos.2 zetaThree_pos))
    SeriesParallel.Appendix.lambdaStar_pos

theorem nearCriticalScale_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < nearCriticalScale delta := by
  rw [nearCriticalScale]
  exact mul_pos nearCriticalConstant_pos (Real.rpow_pos_of_pos hdelta _)

theorem eventually_nearCriticalScale_pos :
    ∀ᶠ delta in 𝓝[>] (0 : ℝ), 0 < nearCriticalScale delta := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact nearCriticalScale_pos hdelta

/-! ## A reusable strict squeeze criterion -/

theorem tendsto_ratio_one_of_eventually_between
    {l : Filter ℝ} {f g : ℝ → ℝ}
    (hg : ∀ᶠ x in l, 0 < g x)
    (hlower : ∀ a : ℝ, a < 1 → ∀ᶠ x in l, a * g x < f x)
    (hupper : ∀ b : ℝ, 1 < b → ∀ᶠ x in l, f x < b * g x) :
    Tendsto (f / g) l (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hg, hlower a ha] with x hgx hfx
    exact (lt_div_iff₀ hgx).2 hfx
  · intro b hb
    filter_upwards [hg, hupper b hb] with x hgx hfx
    exact (div_lt_iff₀ hgx).2 hfx

theorem isEquivalent_of_eventually_between
    {l : Filter ℝ} {f g : ℝ → ℝ}
    (hg : ∀ᶠ x in l, 0 < g x)
    (hlower : ∀ a : ℝ, a < 1 → ∀ᶠ x in l, a * g x < f x)
    (hupper : ∀ b : ℝ, 1 < b → ∀ᶠ x in l, f x < b * g x) :
    f ~[l] g := by
  apply isEquivalent_of_tendsto_one
  exact tendsto_ratio_one_of_eventually_between hg hlower hupper

/-- Letting the profile and translation parameters approach their critical values turns the
strict barrier family into an asymptotic equivalence. -/
theorem isEquivalent_of_parameter_barriers
    {f : ℝ → ℝ} {kappaFactor lambda0 : ℝ}
    (hkappaFactor : 0 < kappaFactor) (hlambda0 : 0 < lambda0)
    (hupper : ∀ lambda kappa : ℝ,
      lambda0 < lambda → kappaFactor * lambda < kappa →
        ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), f epsilon < kappa * epsilon ^ 2)
    (hlower : ∀ lambda kappa : ℝ,
      0 < lambda → lambda < lambda0 → 0 < kappa →
        kappa < kappaFactor * lambda →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), kappa * epsilon ^ 2 < f epsilon) :
    f ~[𝓝[>] (0 : ℝ)]
      (fun epsilon : ℝ ↦ kappaFactor * lambda0 * epsilon ^ 2) := by
  apply isEquivalent_of_eventually_between
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact mul_pos (mul_pos hkappaFactor hlambda0) (sq_pos_of_pos hepsilon)
  · intro a ha
    by_cases ha0 : a ≤ 0
    · let lambda := lambda0 / 2
      let kappa := kappaFactor * lambda / 2
      have hlambda : 0 < lambda := by dsimp [lambda]; linarith
      have hlambdaLt : lambda < lambda0 := by dsimp [lambda]; linarith
      have hkappa : 0 < kappa := by dsimp [kappa]; positivity
      have hkappaLt : kappa < kappaFactor * lambda := by
        dsimp [kappa]
        nlinarith [mul_pos hkappaFactor hlambda]
      filter_upwards [self_mem_nhdsWithin,
        hlower lambda kappa hlambda hlambdaLt hkappa hkappaLt]
        with epsilon hepsilon hbound
      have hleft : a * (kappaFactor * lambda0 * epsilon ^ 2) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg ha0
          (mul_nonneg (mul_pos hkappaFactor hlambda0).le (sq_nonneg epsilon))
      exact hleft.trans_lt
        (lt_trans (mul_pos hkappa (sq_pos_of_pos hepsilon)) hbound)
    · have haPos : 0 < a := lt_of_not_ge ha0
      let lambda := ((a + 1) / 2) * lambda0
      let target := a * kappaFactor * lambda0
      let kappa := (target + kappaFactor * lambda) / 2
      have hlambda : 0 < lambda := by
        dsimp [lambda]
        positivity
      have hlambdaLt : lambda < lambda0 := by
        dsimp [lambda]
        nlinarith [hlambda0]
      have htargetLt : target < kappaFactor * lambda := by
        dsimp [target, lambda]
        nlinarith [mul_pos hkappaFactor hlambda0]
      have hkappa : 0 < kappa := by
        dsimp [kappa, target]
        positivity
      have hkappaLt : kappa < kappaFactor * lambda := by
        dsimp [kappa]
        linarith
      filter_upwards [self_mem_nhdsWithin,
        hlower lambda kappa hlambda hlambdaLt hkappa hkappaLt]
        with epsilon hepsilon hbound
      have hscale : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
      have htargetKappa : a * kappaFactor * lambda0 < kappa := by
        dsimp [kappa, target]
        linarith
      have htarget :
          a * (kappaFactor * lambda0 * epsilon ^ 2) <
            kappa * epsilon ^ 2 := by
        rw [show a * (kappaFactor * lambda0 * epsilon ^ 2) =
          (a * kappaFactor * lambda0) * epsilon ^ 2 by ring]
        exact mul_lt_mul_of_pos_right htargetKappa hscale
      exact htarget.trans hbound
  · intro b hb
    let lambda := ((b + 1) / 2) * lambda0
    let target := b * kappaFactor * lambda0
    let kappa := (kappaFactor * lambda + target) / 2
    have hlambdaGt : lambda0 < lambda := by
      dsimp [lambda]
      nlinarith [hlambda0]
    have hlambdaTarget : kappaFactor * lambda < target := by
      dsimp [lambda, target]
      nlinarith [mul_pos hkappaFactor hlambda0]
    have hkappaGt : kappaFactor * lambda < kappa := by
      dsimp [kappa]
      linarith
    filter_upwards [self_mem_nhdsWithin,
      hupper lambda kappa hlambdaGt hkappaGt]
      with epsilon hepsilon hbound
    have hscale : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hkappaTarget : kappa < b * kappaFactor * lambda0 := by
      dsimp [kappa, target]
      linarith
    calc
      f epsilon < kappa * epsilon ^ 2 := hbound
      _ < b * (kappaFactor * lambda0 * epsilon ^ 2) := by
        rw [show b * (kappaFactor * lambda0 * epsilon ^ 2) =
          (b * kappaFactor * lambda0) * epsilon ^ 2 by ring]
        exact mul_lt_mul_of_pos_right hkappaTarget hscale

/-- Non-strict barrier conclusions suffice because the requested translation parameter can be
replaced by its midpoint with the profile coefficient. -/
theorem isEquivalent_of_parameter_barriers_le
    {f : ℝ → ℝ} {kappaFactor lambda0 : ℝ}
    (hkappaFactor : 0 < kappaFactor) (hlambda0 : 0 < lambda0)
    (hupper : ∀ lambda kappa : ℝ,
      lambda0 < lambda → kappaFactor * lambda < kappa →
        ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), f epsilon ≤ kappa * epsilon ^ 2)
    (hlower : ∀ lambda kappa : ℝ,
      0 < lambda → lambda < lambda0 → 0 < kappa →
        kappa < kappaFactor * lambda →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), kappa * epsilon ^ 2 ≤ f epsilon) :
    f ~[𝓝[>] (0 : ℝ)]
      (fun epsilon : ℝ ↦ kappaFactor * lambda0 * epsilon ^ 2) := by
  apply isEquivalent_of_parameter_barriers hkappaFactor hlambda0
  · intro lambda kappa hlambda hkappa
    let kappa' := (kappaFactor * lambda + kappa) / 2
    have hkappa'Left : kappaFactor * lambda < kappa' := by
      dsimp [kappa']
      linarith
    have hkappa'Right : kappa' < kappa := by
      dsimp [kappa']
      linarith
    filter_upwards [self_mem_nhdsWithin,
      hupper lambda kappa' hlambda hkappa'Left]
      with epsilon hepsilon hbound
    exact hbound.trans_lt
      (mul_lt_mul_of_pos_right hkappa'Right (sq_pos_of_pos hepsilon))
  · intro lambda kappa hlambda hlambda0' hkappa hkappaUpper
    let kappa' := (kappa + kappaFactor * lambda) / 2
    have hkappa'Pos : 0 < kappa' := by
      dsimp [kappa']
      nlinarith [mul_pos hkappaFactor hlambda]
    have hkappa'Left : kappa < kappa' := by
      dsimp [kappa']
      linarith
    have hkappa'Right : kappa' < kappaFactor * lambda := by
      dsimp [kappa']
      linarith
    filter_upwards [self_mem_nhdsWithin,
      hlower lambda kappa' hlambda hlambda0' hkappa'Pos hkappa'Right]
      with epsilon hepsilon hbound
    exact (mul_lt_mul_of_pos_right hkappa'Left
      (sq_pos_of_pos hepsilon)).trans_le hbound

/-! ## Cubic reparameterization of the right-hand asymptotics -/

theorem tendsto_cbrt_nhdsGT_zero :
    Tendsto Real.cbrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous : ContinuousWithinAt Real.cbrt (Ioi 0) 0 :=
      Real.continuous_cbrt.continuousWithinAt
    simpa only [ContinuousWithinAt, Real.cbrt_zero] using hcontinuous
  · filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact Real.cbrt_pos.mpr hdelta

theorem tendsto_cube_nhdsGT_zero :
    Tendsto (fun epsilon : ℝ ↦ epsilon ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous : ContinuousWithinAt (fun epsilon : ℝ ↦ epsilon ^ 3)
        (Ioi 0) 0 := (continuous_id.pow 3).continuousWithinAt
    simpa only [ContinuousWithinAt, zero_pow (by norm_num : 3 ≠ 0)] using hcontinuous
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    change 0 < epsilon ^ 3
    exact pow_pos hepsilon 3

theorem cbrt_sq_eq_rpow_two_thirds {delta : ℝ} (hdelta : 0 < delta) :
    Real.cbrt delta ^ 2 = Real.rpow delta ((2 : ℝ) / 3) := by
  rw [Real.cbrt, if_neg (not_lt.mpr hdelta.le)]
  rw [← Real.rpow_mul_natCast hdelta.le (1 / 3 : ℝ) 2]
  norm_num

/-- A barrier theorem in the cubic parameter covers every positive `delta`, not a subsequence. -/
theorem isEquivalent_nhdsGT_zero_of_cube
    {f : ℝ → ℝ} {constant : ℝ}
    (h : (fun epsilon : ℝ ↦ f (epsilon ^ 3)) ~[𝓝[>] (0 : ℝ)]
      fun epsilon : ℝ ↦ constant * epsilon ^ 2) :
    f ~[𝓝[>] (0 : ℝ)]
      (fun delta : ℝ ↦ constant * Real.rpow delta ((2 : ℝ) / 3)) := by
  have hcomposed := h.comp_tendsto tendsto_cbrt_nhdsGT_zero
  apply (hcomposed.congr_left ?_).congr_right
  · filter_upwards [self_mem_nhdsWithin] with delta hdelta
    change constant * Real.cbrt delta ^ 2 =
      constant * Real.rpow delta ((2 : ℝ) / 3)
    rw [cbrt_sq_eq_rpow_two_thirds hdelta]
  · exact Eventually.of_forall fun delta ↦ by
      change f (Real.cbrt delta ^ 3) = f delta
      rw [Real.cbrt_cube]

/-! ## The elementary negative-side first-moment comparison -/

theorem log_one_sub_two_mul_isEquivalent :
    (fun delta : ℝ ↦ Real.log (1 - 2 * delta)) ~[𝓝[>] (0 : ℝ)]
      (fun delta : ℝ ↦ -2 * delta) := by
  have hinner : HasDerivAt (fun delta : ℝ ↦ 1 - 2 * delta) (-2) 0 := by
    simpa using HasDerivAt.const_sub (1 : ℝ) ((hasDerivAt_id 0).const_mul 2)
  have hderiv : HasDerivAt
      (fun delta : ℝ ↦ Real.log (1 - 2 * delta)) (-2) 0 := by
    simpa using hinner.log (by norm_num : (1 - 2 * (0 : ℝ)) ≠ 0)
  apply isEquivalent_of_tendsto_one
  have hslope := hderiv.tendsto_slope_zero_right
  have hscaled := hslope.div_const (-2)
  convert hscaled using 1
  · funext delta
    by_cases hdelta : delta = 0
    · simp [hdelta]
    · simp only [Pi.div_apply, zero_add, mul_zero, sub_zero,
        Real.log_one, smul_eq_mul]
      field_simp [hdelta]
  · norm_num

theorem tendsto_delta_div_nearCriticalScale :
    Tendsto (fun delta : ℝ ↦ delta / nearCriticalScale delta)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcbrt : Tendsto Real.cbrt (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_cbrt_nhdsGT_zero.mono_right inf_le_left
  have hdiv := hcbrt.div_const
    (2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar)
  have heq : (fun delta : ℝ ↦ delta / nearCriticalScale delta) =ᶠ[
      𝓝[>] (0 : ℝ)] fun delta ↦
        Real.cbrt delta /
          (2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    rw [nearCriticalScale, ← cbrt_sq_eq_rpow_two_thirds hdelta]
    have hcbrtPos : 0 < Real.cbrt delta := Real.cbrt_pos.2 hdelta
    field_simp [hcbrtPos.ne', nearCriticalConstant_pos.ne']
    nth_rewrite 1 [← Real.cbrt_cube delta]
    ring
  simpa using (tendsto_congr' heq).2 hdiv

theorem eventually_neg_lt_log_one_sub_two_mul_of_equivalent
    {f : ℝ → ℝ} (hf : f ~[𝓝[>] (0 : ℝ)] nearCriticalScale) :
    ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      -f delta < Real.log (1 - 2 * delta) := by
  have hscaleNe : ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      nearCriticalScale delta ≠ 0 :=
    eventually_nearCriticalScale_pos.mono fun _ h ↦ h.ne'
  have hfratio : Tendsto (f / nearCriticalScale)
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hscaleNe).1 hf
  have hlinearNe : ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      (-2 : ℝ) * delta ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact mul_ne_zero (by norm_num) hdelta.ne'
  have hlogRatio : Tendsto
      ((fun delta : ℝ ↦ Real.log (1 - 2 * delta)) /
        (fun delta : ℝ ↦ -2 * delta))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hlinearNe).1
      log_one_sub_two_mul_isEquivalent
  have htwiceSmall : Tendsto
      (fun delta : ℝ ↦ 2 * (delta / nearCriticalScale delta))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_delta_div_nearCriticalScale.const_mul 2
  have hlogSmallRaw := hlogRatio.mul htwiceSmall
  have hlogSmall : Tendsto
      (fun delta : ℝ ↦
        -Real.log (1 - 2 * delta) / nearCriticalScale delta)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun delta : ℝ ↦
        -Real.log (1 - 2 * delta) / nearCriticalScale delta) =ᶠ[
        𝓝[>] (0 : ℝ)] fun delta ↦
          (((fun x : ℝ ↦ Real.log (1 - 2 * x)) /
              fun x : ℝ ↦ -2 * x) delta) *
            (2 * (delta / nearCriticalScale delta)) := by
      filter_upwards [self_mem_nhdsWithin] with delta hdelta
      have hdeltaNe : delta ≠ 0 := hdelta.ne'
      have hscaleNe' : nearCriticalScale delta ≠ 0 :=
        (nearCriticalScale_pos hdelta).ne'
      simp only [Pi.div_apply]
      field_simp [hdeltaNe, hscaleNe']
    simpa only [one_mul] using (tendsto_congr' heq).2 hlogSmallRaw
  have hratioOrder :=
    hlogSmall.eventually_lt hfratio (by norm_num : (0 : ℝ) < 1)
  filter_upwards [self_mem_nhdsWithin, hratioOrder]
    with delta hdelta horder
  have hscalePos := nearCriticalScale_pos hdelta
  change -Real.log (1 - 2 * delta) / nearCriticalScale delta <
    f delta / nearCriticalScale delta at horder
  have hmul := (div_lt_div_iff_of_pos_right hscalePos).1 horder
  linarith

theorem max_neg_isEquivalent_log_one_sub_two_mul
    {f g : ℝ → ℝ} (hf : f ~[𝓝[>] (0 : ℝ)] nearCriticalScale)
    (hg : ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      g delta = max (-f delta) (Real.log (1 - 2 * delta))) :
    g ~[𝓝[>] (0 : ℝ)] (fun delta : ℝ ↦ -2 * delta) := by
  apply log_one_sub_two_mul_isEquivalent.congr_left
  filter_upwards [hg,
    eventually_neg_lt_log_one_sub_two_mul_of_equivalent hf]
    with delta hgamma hdominates
  rw [hgamma, max_eq_right hdominates.le]

end SeriesParallel.MainText
