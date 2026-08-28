import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import SeriesParallel.MainText.LogGates
import SeriesParallel.MainTextInterface

/-!
# The diffusion coefficient

This file defines the coefficient
`a = 2 * ∫ r in Set.Ioi 0, (h r) ^ 2 + r * h r` from the main text.  Its
integrability and strict positivity are proved directly, so the concrete input passed to the
appendix does not depend on the separate closed-form evaluation of the integral.
-/

namespace SeriesParallel.MainText

open MeasureTheory Set

/-- The real value `ζ(3)`, represented by its absolutely convergent positive series. -/
noncomputable def zetaThree : ℝ :=
  ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 3

theorem summable_zetaThree : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 3) := by
  have h := (Real.summable_one_div_nat_pow (p := 3)).2 (by omega)
  refine (h.comp_injective Nat.succ_injective).congr (fun n ↦ ?_)
  simp only [Function.comp_apply, Nat.cast_succ]

theorem zetaThree_pos : 0 < zetaThree := by
  unfold zetaThree
  exact summable_zetaThree.tsum_pos (fun n ↦ by positivity) 0 (by norm_num)

/-- The series definition above is the real value of mathlib's complex Riemann zeta function. -/
theorem ofReal_zetaThree : (zetaThree : ℂ) = riemannZeta 3 := by
  unfold zetaThree
  rw [Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (3 : ℂ)) (by norm_num)]
  congr 1
  funext n
  norm_cast
  push_cast
  change (1 : ℂ) / ((n : ℂ) + 1) ^ 3 = (1 : ℂ) / ((n : ℂ) + 1) ^ 3
  rfl

/-- The integrand in the main-text definition of the diffusion coefficient. -/
noncomputable def diffusionIntegrand (r : ℝ) : ℝ :=
  h r ^ 2 + r * h r

/-- The diffusion coefficient `a` from `eq:a-zeta`. -/
noncomputable def diffusionCoefficient : ℝ :=
  2 * ∫ r in Ioi 0, diffusionIntegrand r

theorem continuous_h : Continuous h := by
  unfold h
  exact (continuous_const.add (Real.continuous_exp.comp continuous_neg)).log
    (fun r ↦ (add_pos zero_lt_one (Real.exp_pos (-r))).ne')

theorem continuous_diffusionIntegrand : Continuous diffusionIntegrand := by
  exact continuous_h.pow 2 |>.add (continuous_id.mul continuous_h)

/-- The elementary exponential bound used to control the improper integral. -/
theorem h_le_exp_neg (r : ℝ) : h r ≤ Real.exp (-r) := by
  unfold h
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-r) by positivity)
  linarith

theorem diffusionIntegrand_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ diffusionIntegrand r := by
  unfold diffusionIntegrand
  exact add_nonneg (sq_nonneg (h r)) (mul_nonneg hr (h_nonneg r))

theorem diffusionIntegrand_pos {r : ℝ} (hr : 0 ≤ r) : 0 < diffusionIntegrand r := by
  unfold diffusionIntegrand
  have hh := h_pos r
  exact add_pos_of_pos_of_nonneg (pow_pos hh 2) (mul_nonneg hr hh.le)

/-- The defining integrand is Lebesgue integrable on `(0, ∞)`. -/
theorem diffusionIntegrand_integrableOn : IntegrableOn diffusionIntegrand (Ioi 0) := by
  have hexp : IntegrableOn (fun r : ℝ ↦ Real.exp (-r)) (Ioi 0) :=
    integrableOn_exp_neg_Ioi 0
  have hrExp : IntegrableOn (fun r : ℝ ↦ r * Real.exp (-r)) (Ioi 0) := by
    have hgamma := Real.GammaIntegral_convergent (show 0 < (2 : ℝ) by positivity)
    convert hgamma using 1
    funext r
    rw [show (2 : ℝ) - 1 = 1 by linarith, Real.rpow_one, mul_comm]
  apply Integrable.mono' (hexp.add hrExp)
  · exact continuous_diffusionIntegrand.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    have hh0 : 0 ≤ h r := h_nonneg r
    have hhe : h r ≤ Real.exp (-r) := h_le_exp_neg r
    have he1 : Real.exp (-r) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hh1 : h r ≤ 1 := hhe.trans he1
    have hhSq : h r ^ 2 ≤ Real.exp (-r) := by
      calc
        h r ^ 2 = h r * h r := pow_two (h r)
        _ ≤ h r * 1 := mul_le_mul_of_nonneg_left hh1 hh0
        _ = h r := mul_one (h r)
        _ ≤ Real.exp (-r) := hhe
    rw [Real.norm_eq_abs, abs_of_nonneg (diffusionIntegrand_nonneg hr0)]
    unfold diffusionIntegrand
    exact add_le_add hhSq (mul_le_mul_of_nonneg_left hhe hr0)

theorem diffusionIntegrand_hasFiniteIntegral :
    HasFiniteIntegral diffusionIntegrand (volume.restrict (Ioi 0)) :=
  diffusionIntegrand_integrableOn.hasFiniteIntegral

/-- The integral in the definition of `diffusionCoefficient` is strictly positive. -/
theorem integral_diffusionIntegrand_pos : 0 < ∫ r in Ioi 0, diffusionIntegrand r := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] diffusionIntegrand := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact diffusionIntegrand_nonneg hr.le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg diffusionIntegrand_integrableOn]
  have hsupp : Function.support diffusionIntegrand ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro r hr
    rw [Function.mem_support]
    exact (diffusionIntegrand_pos hr.le).ne'
  rw [hsupp, Real.volume_Ioi]
  exact bot_lt_top

theorem diffusionCoefficient_pos : 0 < diffusionCoefficient := by
  unfold diffusionCoefficient
  exact mul_pos (by positivity) integral_diffusionIntegrand_pos

/-- The concrete positive coefficient supplied to the already-formalized appendix. -/
noncomputable def diffusionMainInput : MainInput where
  a := diffusionCoefficient
  a_pos := diffusionCoefficient_pos

@[simp]
theorem diffusionMainInput_a : diffusionMainInput.a = diffusionCoefficient := rfl

end SeriesParallel.MainText
