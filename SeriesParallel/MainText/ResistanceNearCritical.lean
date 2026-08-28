/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.NearCriticalAssembly
import SeriesParallel.MainText.RemainingParameters
import SeriesParallel.MainText.UpperBarrier
import SeriesParallel.MainText.LowerBarrier

/-!
# Resistance near-critical assembly

This module keeps the resistance-only near-critical proof separate from the distance
critical input.  The concrete profile barriers are connected below once their final
global estimates are available.
-/

open Asymptotics Filter Set
open scoped Topology

namespace SeriesParallel.MainText

/-- Exact resistance duality around the critical parameter. -/
theorem vR_nearCritical_duality :
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      vR (1 / 2 + delta) = -vR (1 / 2 - delta) := by
  intro delta hdelta hdeltaHalf
  have hp : 1 / 2 - delta ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hduality := vR_one_sub (1 / 2 - delta) hp
  have honeSub : 1 - (1 / 2 - delta) = 1 / 2 + delta := by ring
  rw [honeSub] at hduality
  exact hduality

/-- The strict-supercritical identity transfers the intrinsic speed asymptotics to
the first-moment resistance exponent without a critical distance input. -/
theorem gammaR_plus_isEquivalent_of_vR
    (hv : (fun delta : ℝ ↦ vR (1 / 2 + delta)) ~[𝓝[>] (0 : ℝ)]
      nearCriticalScale) :
    (fun delta : ℝ ↦ gammaR (1 / 2 + delta)) ~[𝓝[>] (0 : ℝ)]
      nearCriticalScale := by
  apply hv.congr_left
  have hhalf : ∀ᶠ delta in 𝓝[>] (0 : ℝ), delta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with delta hdelta hdeltaHalf
  have hdeltaPos : 0 < delta := hdelta
  exact (gammaR_eq_vR_supercritical (p := 1 / 2 + delta)
    ⟨by linarith, by linarith⟩ (by linarith)).symm

/-- Complementarity and the strict-subcritical first-moment formula select the
linear logarithmic branch on the negative side. -/
theorem gammaR_minus_isEquivalent_of_vR
    (hv : (fun delta : ℝ ↦ vR (1 / 2 + delta)) ~[𝓝[>] (0 : ℝ)]
      nearCriticalScale) :
    (fun delta : ℝ ↦ gammaR (1 / 2 - delta)) ~[𝓝[>] (0 : ℝ)]
      (fun delta : ℝ ↦ -2 * delta) := by
  apply max_neg_isEquivalent_log_one_sub_two_mul hv
  have hhalf : ∀ᶠ delta in 𝓝[>] (0 : ℝ), delta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with delta hdelta hdeltaHalf
  have hdeltaPos : 0 < delta := hdelta
  have hpMem : 1 / 2 - delta ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hformula := gammaR_eq_max_vR_log_two_p_subcritical
    (p := 1 / 2 - delta) hpMem (by linarith) (by linarith)
  have hduality := vR_nearCritical_duality delta hdeltaPos hdeltaHalf.le
  calc
    gammaR (1 / 2 - delta) =
        max (vR (1 / 2 - delta)) (Real.log (2 * (1 / 2 - delta))) :=
      hformula
    _ = max (-vR (1 / 2 + delta)) (Real.log (1 - 2 * delta)) := by
      congr 2
      · linarith
      · ring

/-! ## Abstract assembly from the two parameterized barriers -/

/-- The two cubic-parameter barrier families imply the full right-filter intrinsic
near-critical asymptotic after rewriting the internally computed profile scale. -/
theorem vR_plus_isEquivalent_of_diffusion_barriers
    (hupper : ∀ lambda kappa : ℝ,
      SeriesParallel.Appendix.lambdaStar < lambda →
        diffusionMainInput.kappa lambda < kappa →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
            vR (1 / 2 + epsilon ^ 3) ≤ kappa * epsilon ^ 2)
    (hlower : ∀ lambda kappa : ℝ,
      0 < lambda → lambda < SeriesParallel.Appendix.lambdaStar →
        0 < kappa → kappa < diffusionMainInput.kappa lambda →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
            kappa * epsilon ^ 2 ≤ vR (1 / 2 + epsilon ^ 3)) :
    (fun delta : ℝ ↦ vR (1 / 2 + delta)) ~[𝓝[>] (0 : ℝ)]
      nearCriticalScale := by
  have hkappaFactor : 0 < 2 * Real.cbrt zetaThree := by
    exact mul_pos (by norm_num) (Real.cbrt_pos.2 zetaThree_pos)
  have hcube := isEquivalent_of_parameter_barriers_le
    hkappaFactor SeriesParallel.Appendix.lambdaStar_pos
    (fun lambda kappa hlambda hkappa ↦
      hupper lambda kappa hlambda (by
        simpa only [diffusionMainInput_kappa_eq] using hkappa))
    (fun lambda kappa hlambda hlambdaStar hkappa hkappaUpper ↦
      hlower lambda kappa hlambda hlambdaStar hkappa (by
        simpa only [diffusionMainInput_kappa_eq] using hkappaUpper))
  have hdelta := isEquivalent_nhdsGT_zero_of_cube
    (f := fun delta : ℝ ↦ vR (1 / 2 + delta))
    (constant :=
      2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar) hcube
  change (fun delta : ℝ ↦ vR (1 / 2 + delta)) ~[𝓝[>] (0 : ℝ)]
    (fun delta : ℝ ↦
      2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar *
        Real.rpow delta ((2 : ℝ) / 3))
  exact hdelta

/-- Once the two pure-resistance barrier families are supplied, every field of the
source-facing near-critical statement follows internally. -/
theorem resistanceSpeedNearCritical_of_diffusion_barriers
    (hupper : ∀ lambda kappa : ℝ,
      SeriesParallel.Appendix.lambdaStar < lambda →
        diffusionMainInput.kappa lambda < kappa →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
            vR (1 / 2 + epsilon ^ 3) ≤ kappa * epsilon ^ 2)
    (hlower : ∀ lambda kappa : ℝ,
      0 < lambda → lambda < SeriesParallel.Appendix.lambdaStar →
        0 < kappa → kappa < diffusionMainInput.kappa lambda →
          ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
            kappa * epsilon ^ 2 ≤ vR (1 / 2 + epsilon ^ 3)) :
    ResistanceSpeedNearCriticalStatement := by
  have hv := vR_plus_isEquivalent_of_diffusion_barriers hupper hlower
  exact ⟨SeriesParallel.Appendix.lambdaStar_pos,
    lambdaStar_isLeast_mainAdmissible, vR_nearCritical_duality, hv,
    gammaR_plus_isEquivalent_of_vR hv,
    gammaR_minus_isEquivalent_of_vR hv⟩

/-! ## Concrete hard-edge lower family and the source theorem -/

/-- The global hard-edge CDF barrier, its iteration, and resistance duality give
the lower cubic-parameter speed family required by the squeeze. -/
theorem kappa_sq_le_vR_half_add_cube_eventually
    (lambda kappa : ℝ) (hlambda : 0 < lambda)
    (hsubcritical : lambda < SeriesParallel.Appendix.lambdaStar)
    (hkappa : 0 < kappa)
    (hstrict : kappa < diffusionMainInput.kappa lambda) :
    ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      kappa * epsilon ^ 2 ≤ vR (1 / 2 + epsilon ^ 3) := by
  let W := SeriesParallel.Appendix.WSolution lambda hlambda
  obtain ⟨Psi, hprofile, _hunique⟩ :=
    diffusion_hard_edge_distribution hlambda hsubcritical
  obtain ⟨epsilonBarrier, hepsilonBarrier, hbarrier⟩ :=
    hard_edge_global_lower_barrier hprofile hkappa hstrict
  let epsilon0 := min epsilonBarrier (1 / 2)
  have hepsilon0 : 0 < epsilon0 :=
    lt_min hepsilonBarrier (by norm_num)
  have heventuallySmall : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      epsilon < epsilon0 :=
    (eventually_lt_nhds hepsilon0).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, heventuallySmall] with epsilon
    hepsilon hepsilonSmall
  have hepsilonBarrierSmall : epsilon < epsilonBarrier :=
    hepsilonSmall.trans_le (min_le_left _ _)
  have hepsilonHalf : epsilon < 1 / 2 :=
    hepsilonSmall.trans_le (min_le_right _ _)
  have hcubeLt : epsilon ^ 3 < (1 / 2 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hepsilonHalf hepsilon.le (by norm_num)
  have hcube : epsilon ^ 3 ≤ 1 / 2 := by
    calc
      epsilon ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := hcubeLt.le
      _ ≤ 1 / 2 := by norm_num
  have hpMem := half_sub_cube_mem_unitInterval hepsilon hcube
  let p := modelParameter (1 / 2 - epsilon ^ 3)
  have hp : (p : ℝ) = 1 / 2 - epsilon ^ 3 := by
    dsimp only [p]
    exact modelParameter_coe_of_mem hpMem
  have hglobal := hbarrier p epsilon hepsilon hepsilonBarrierSmall hp
  apply kappa_sq_le_vR_half_add_cube hprofile hepsilon hcube
  simpa only [p] using hglobal

/-- The exact source-facing resistance near-critical theorem.  Its proof path is
purely resistance-based and does not use the critical distance input. -/
theorem resistanceSpeedNearCritical : ResistanceSpeedNearCriticalStatement :=
  resistanceSpeedNearCritical_of_diffusion_barriers
    vR_half_add_cube_le_kappa_sq_eventually
    kappa_sq_le_vR_half_add_cube_eventually

end SeriesParallel.MainText
