import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import SeriesParallel.MainText.DiffusionCoefficient

/-!
# Closed form of the diffusion coefficient

This file evaluates the main-text diffusion coefficient internally, without an external
calculation interface.
-/

namespace SeriesParallel.MainText

open Filter MeasureTheory Set
open scoped Topology

/-- The logarithmic moment used after expanding `-log (1 - u)` into nonnegative terms. -/
theorem integral_pow_mul_neg_log (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ n * (-Real.log x)) = 1 / (n + 1 : ℝ) ^ 2 := by
  let m : ℝ := n + 1
  let F : ℝ → ℝ := fun x ↦ x ^ (n + 1) * (1 / m ^ 2 - Real.log x / m)
  have hm : 0 < m := by
    dsimp [m]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := F) (fa := 0) (fb := 1 / m ^ 2) (by norm_num : (0 : ℝ) < 1)]
  · simp [m]
  · intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hpow := hasDerivAt_pow (n + 1) x
    have hlog := Real.hasDerivAt_log hx0
    have hinner := (hasDerivAt_const x (1 / m ^ 2)).sub (hlog.div_const m)
    refine (hpow.mul hinner).congr_deriv ?_
    dsimp [m]
    field_simp [hx0]
    push_cast
    ring
  · have hlog : IntervalIntegrable (fun x : ℝ ↦ -Real.log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'.neg
    simpa only [Pi.pow_apply, id_eq, neg_mul, neg_neg] using
      hlog.continuousOn_mul (continuousOn_id.pow n)
  · have hxpow :
        Tendsto (fun x : ℝ ↦ x ^ (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hpow0 : Tendsto (fun x : ℝ ↦ x ^ (n + 1)) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hid : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0) := tendsto_id
        simpa only [zero_pow (Nat.succ_ne_zero n)] using hid.pow (n + 1)
      exact hpow0.mono_left inf_le_left
    have hlogpow :
        Tendsto (fun x : ℝ ↦ x ^ (n + 1) * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero
        (show 0 < (n + 1 : ℝ) by positivity)
      refine h.congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast x (n + 1)]
      ring
    have hlim := (hxpow.div_const (m ^ 2)).sub (hlogpow.div_const m)
    convert hlim using 1 <;> simp [F, mul_sub, div_eq_mul_inv, mul_assoc]
  · have hFcont : ContinuousAt F 1 := by
      dsimp [F]
      exact (continuousAt_id.pow (n + 1)).mul
        (continuousAt_const.sub ((Real.continuousAt_log one_ne_zero).div_const m))
    simpa [F] using tendsto_nhdsWithin_of_tendsto_nhds hFcont.tendsto

/-- A term in the logarithmic moment expansion. -/
noncomputable def logMomentTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * (-Real.log x) / (n + 1 : ℝ)

theorem logMomentTerm_nonneg (n : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ logMomentTerm n x := by
  unfold logMomentTerm
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  exact div_nonneg (mul_nonneg (pow_nonneg hx.1.le n) (neg_nonneg.mpr hlog)) (by positivity)

theorem integrableOn_logMomentTerm (n : ℕ) :
    IntegrableOn (logMomentTerm n) (Ioo (0 : ℝ) 1) := by
  have hlog : IntervalIntegrable (fun x : ℝ ↦ -Real.log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.neg
  have hbase : IntervalIntegrable (fun x : ℝ ↦ x ^ n * (-Real.log x)) volume 0 1 := by
    simpa only [Pi.pow_apply, id_eq, neg_mul, neg_neg] using
      hlog.continuousOn_mul (continuousOn_id.pow n)
  refine IntegrableOn.congr_set_ae (t := Ioc 0 1) ?_ Ioo_ae_eq_Ioc
  change IntegrableOn
    (fun x : ℝ ↦ x ^ n * (-Real.log x) / (n + 1 : ℝ)) (Ioc 0 1)
  simpa only [div_eq_mul_inv] using
    (hbase.mul_const ((n + 1 : ℝ)⁻¹)).1

theorem integral_logMomentTerm (n : ℕ) :
    (∫ x in Ioo (0 : ℝ) 1, logMomentTerm n x) = 1 / (n + 1 : ℝ) ^ 3 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  unfold logMomentTerm
  rw [intervalIntegral.integral_div, integral_pow_mul_neg_log]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem hasSum_logMomentTerm {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasSum (fun n : ℕ ↦ logMomentTerm n x)
      (Real.log x * Real.log (1 - x) / x) := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have habs : |x| < 1 := by
    rw [abs_of_pos hx.1]
    exact hx.2
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one habs).mul_left
    (-Real.log x / x)
  have hlim :
      (-Real.log x / x) * (-Real.log (1 - x)) =
        Real.log x * Real.log (1 - x) / x := by
    field_simp [hx0]
  rw [← hlim]
  refine hs.congr_fun ?_
  intro n
  unfold logMomentTerm
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hx0, hn]
  rw [pow_succ]
  ring

/-- The full logarithmic moment is the positive series defining `ζ(3)`. -/
theorem integral_log_mul_log_one_sub_div :
    (∫ x in Ioo (0 : ℝ) 1, Real.log x * Real.log (1 - x) / x) = zetaThree := by
  have hnorm (n : ℕ) :
      (∫ x in Ioo (0 : ℝ) 1, ‖logMomentTerm n x‖) =
        1 / (n + 1 : ℝ) ^ 3 := by
    rw [← integral_logMomentTerm]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_of_nonneg (logMomentTerm_nonneg n hx)]
  have hsum : Summable
      (fun n : ℕ ↦ ∫ x in Ioo (0 : ℝ) 1, ‖logMomentTerm n x‖) := by
    simpa only [hnorm] using summable_zetaThree
  have hTonelli := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) integrableOn_logMomentTerm hsum
  calc
    (∫ x in Ioo (0 : ℝ) 1, Real.log x * Real.log (1 - x) / x) =
        ∫ x in Ioo (0 : ℝ) 1, ∑' n : ℕ, logMomentTerm n x := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
          exact (hasSum_logMomentTerm hx).tsum_eq.symm
    _ = ∑' n : ℕ, ∫ x in Ioo (0 : ℝ) 1, logMomentTerm n x := hTonelli.symm
    _ = zetaThree := by
      simp_rw [integral_logMomentTerm]
      rfl

/-- The one-sided logarithmic kernel whose integral is `ζ(3)`. -/
noncomputable def logKernel (x : ℝ) : ℝ :=
  Real.log x * Real.log (1 - x) / x

/-- The symmetric kernel produced by the logistic change of variables. -/
noncomputable def symmetricLogKernel (x : ℝ) : ℝ :=
  Real.log x * Real.log (1 - x) / (x * (1 - x))

theorem integral_logKernel :
    (∫ x in Ioo (0 : ℝ) 1, logKernel x) = zetaThree := by
  simpa only [logKernel] using integral_log_mul_log_one_sub_div

theorem integrableOn_logKernel : IntegrableOn logKernel (Ioo (0 : ℝ) 1) := by
  by_contra h
  have hzero : (∫ x in Ioo (0 : ℝ) 1, logKernel x) = 0 := integral_undef h
  rw [integral_logKernel] at hzero
  exact zetaThree_pos.ne' hzero

theorem intervalIntegrable_logKernel :
    IntervalIntegrable logKernel volume (0 : ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  exact integrableOn_logKernel

theorem symmetricLogKernel_eq {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    symmetricLogKernel x = logKernel x + logKernel (1 - x) := by
  unfold symmetricLogKernel logKernel
  rw [show 1 - (1 - x) = x by ring]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  ring

/-- Symmetry and partial fractions reduce the half-interval kernel to the full moment. -/
theorem integral_symmetricLogKernel_half :
    (∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), symmetricLogKernel x) = zetaThree := by
  have hleft : IntervalIntegrable logKernel volume (0 : ℝ) (1 / 2 : ℝ) :=
    intervalIntegrable_logKernel.mono_set (by
      intro x hx
      norm_num [uIcc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2])
  have hright : IntervalIntegrable logKernel volume (1 / 2 : ℝ) 1 :=
    intervalIntegrable_logKernel.mono_set (by
      intro x hx
      norm_num [uIcc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2])
  have hcompFull : IntervalIntegrable (fun x : ℝ ↦ logKernel (1 - x)) volume 0 1 := by
    simpa using (intervalIntegrable_logKernel.comp_sub_left 1).symm
  have hcomp :
      IntervalIntegrable (fun x : ℝ ↦ logKernel (1 - x)) volume 0 (1 / 2) :=
    hcompFull.mono_set (by
      intro x hx
      norm_num [uIcc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2])
  calc
    (∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), symmetricLogKernel x) =
        ∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ),
          (logKernel x + logKernel (1 - x)) := by
            apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
            intro x hx
            exact symmetricLogKernel_eq hx.1.ne' (by linarith [hx.2])
    _ = (∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), logKernel x) +
        ∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), logKernel (1 - x) :=
      intervalIntegral.integral_add hleft hcomp
    _ = (∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), logKernel x) +
        ∫ x : ℝ in (1 / 2 : ℝ)..1, logKernel x := by
      rw [intervalIntegral.integral_comp_sub_left]
      norm_num
    _ = ∫ x : ℝ in (0 : ℝ)..1, logKernel x :=
      intervalIntegral.integral_add_adjacent_intervals hleft hright
    _ = ∫ x in Ioo (0 : ℝ) 1, logKernel x := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ = zetaThree := integral_logKernel

/-- The decreasing logistic coordinate used in the change of variables. -/
noncomputable def logistic (r : ℝ) : ℝ :=
  Real.sigmoid (-r)

/-- Its derivative, recorded separately for the interval substitution theorem. -/
noncomputable def logisticDeriv (r : ℝ) : ℝ :=
  -logistic r * (1 - logistic r)

theorem logistic_pos (r : ℝ) : 0 < logistic r := by
  exact Real.sigmoid_pos (-r)

theorem logistic_lt_one (r : ℝ) : logistic r < 1 := by
  exact Real.sigmoid_lt_one (-r)

@[simp]
theorem logistic_zero : logistic 0 = 1 / 2 := by
  norm_num [logistic, Real.sigmoid_zero]

theorem logisticDeriv_eq (r : ℝ) :
    logisticDeriv r = -logistic r * (1 - logistic r) := rfl

theorem hasDerivAt_logistic (r : ℝ) :
    HasDerivAt logistic (logisticDeriv r) r := by
  have hd := (Real.hasDerivAt_sigmoid (-r)).comp r (hasDerivAt_neg r)
  rw [show logistic = Real.sigmoid ∘ Neg.neg by rfl]
  refine hd.congr_deriv ?_
  unfold logisticDeriv logistic
  ring

theorem continuous_logisticDeriv : Continuous logisticDeriv := by
  unfold logisticDeriv logistic
  have hc : Continuous (fun r : ℝ ↦ Real.sigmoid (-r)) :=
    continuous_sigmoid.comp continuous_neg
  exact hc.neg.mul (continuous_const.sub hc)

theorem log_logistic (r : ℝ) : Real.log (logistic r) = -r - h r := by
  have hfactor :
      1 + Real.exp r = Real.exp r * (1 + Real.exp (-r)) := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  rw [logistic, Real.sigmoid_def, neg_neg, Real.log_inv, hfactor,
    Real.log_mul (Real.exp_ne_zero r) (by positivity), Real.log_exp, h]
  ring

theorem log_one_sub_logistic (r : ℝ) :
    Real.log (1 - logistic r) = -h r := by
  have heq : 1 - logistic r = (1 + Real.exp (-r))⁻¹ := by
    unfold logistic
    rw [Real.sigmoid_def, neg_neg]
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  rw [heq, Real.log_inv, h]

theorem symmetricLogKernel_logistic_mul_deriv (r : ℝ) :
    symmetricLogKernel (logistic r) * logisticDeriv r = -diffusionIntegrand r := by
  have hu0 : logistic r ≠ 0 := (logistic_pos r).ne'
  have hu1 : 1 - logistic r ≠ 0 := by linarith [logistic_lt_one r]
  rw [logisticDeriv_eq]
  unfold symmetricLogKernel diffusionIntegrand
  rw [log_logistic, log_one_sub_logistic]
  field_simp [hu0, hu1]
  ring

theorem continuousOn_symmetricLogKernel :
    ContinuousOn symmetricLogKernel (Ioo (0 : ℝ) 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold symmetricLogKernel
  have hlogx : ContinuousAt Real.log x := Real.continuousAt_log hx.1.ne'
  have hone : 1 - x ≠ 0 := by linarith [hx.2]
  have hlogOne : ContinuousAt (fun y : ℝ ↦ Real.log (1 - y)) x :=
    (Real.continuousAt_log hone).comp (continuousAt_const.sub continuousAt_id)
  have hden : x * (1 - x) ≠ 0 := mul_ne_zero hx.1.ne' hone
  exact (hlogx.mul hlogOne).div
    (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)) hden

/-- Exact finite-interval logistic substitution for the defining integrand. -/
theorem integral_diffusionIntegrand_zero_to (R : ℝ) :
    (∫ r : ℝ in (0 : ℝ)..R, diffusionIntegrand r) =
      ∫ u : ℝ in logistic R..(1 / 2 : ℝ), symmetricLogKernel u := by
  have hg : ContinuousOn symmetricLogKernel (logistic '' uIcc (0 : ℝ) R) := by
    apply continuousOn_symmetricLogKernel.mono
    rintro u ⟨r, -, rfl⟩
    exact ⟨logistic_pos r, logistic_lt_one r⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := R) (f := logistic) (f' := logisticDeriv)
    (g := symmetricLogKernel) (fun r _ ↦ hasDerivAt_logistic r)
    continuous_logisticDeriv.continuousOn hg
  calc
    (∫ r : ℝ in (0 : ℝ)..R, diffusionIntegrand r) =
        ∫ r : ℝ in (0 : ℝ)..R,
          -((symmetricLogKernel ∘ logistic) r * logisticDeriv r) := by
            apply intervalIntegral.integral_congr
            intro r _hr
            change diffusionIntegrand r =
              -(symmetricLogKernel (logistic r) * logisticDeriv r)
            rw [symmetricLogKernel_logistic_mul_deriv]
            ring
    _ = -(∫ r : ℝ in (0 : ℝ)..R,
          (symmetricLogKernel ∘ logistic) r * logisticDeriv r) :=
      intervalIntegral.integral_neg
    _ = -(∫ u : ℝ in logistic 0..logistic R, symmetricLogKernel u) :=
      congrArg Neg.neg hsub
    _ = ∫ u : ℝ in logistic R..logistic 0, symmetricLogKernel u := by
      exact (intervalIntegral.integral_symm (f := symmetricLogKernel)
        (logistic 0) (logistic R)).symm
    _ = ∫ u : ℝ in logistic R..(1 / 2 : ℝ), symmetricLogKernel u := by
      rw [logistic_zero]

theorem intervalIntegrable_symmetricLogKernel_half :
    IntervalIntegrable symmetricLogKernel volume (0 : ℝ) (1 / 2 : ℝ) := by
  apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
  rw [integral_symmetricLogKernel_half]
  exact zetaThree_pos.ne'

theorem tendsto_logistic_atTop : Tendsto logistic atTop (𝓝 0) := by
  unfold logistic
  exact Real.tendsto_sigmoid_atBot.comp tendsto_neg_atTop_atBot

/-- The improper defining integral equals the internally evaluated logarithmic moment. -/
theorem integral_diffusionIntegrand_eq_zetaThree :
    (∫ r in Ioi (0 : ℝ), diffusionIntegrand r) = zetaThree := by
  let k : ℝ → ℝ := fun a ↦
    ∫ u : ℝ in a..(1 / 2 : ℝ), symmetricLogKernel u
  have hkernelIcc :
      IntegrableOn symmetricLogKernel (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      intervalIntegrable_symmetricLogKernel_half
  have hkernelUIcc :
      IntegrableOn symmetricLogKernel (uIcc (0 : ℝ) (1 / 2 : ℝ)) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hkernelIcc
  have hprimitive : ContinuousOn k (uIcc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact intervalIntegral.continuousOn_primitive_interval_left
      hkernelUIcc
  have hlogisticMem : ∀ᶠ r : ℝ in atTop, logistic r ∈ uIcc (0 : ℝ) (1 / 2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    constructor
    · exact (logistic_pos r).le
    · rw [← logistic_zero]
      unfold logistic
      exact Real.sigmoid_le (by linarith)
  have hlogisticWithin :
      Tendsto logistic atTop (𝓝[uIcc (0 : ℝ) (1 / 2 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_logistic_atTop, hlogisticMem⟩
  have hk : Tendsto (fun R : ℝ ↦ k (logistic R)) atTop (𝓝 (k 0)) := by
    exact (hprimitive 0 left_mem_uIcc).tendsto.comp hlogisticWithin
  have hkz : Tendsto (fun R : ℝ ↦ k (logistic R)) atTop (𝓝 zetaThree) := by
    simpa only [k, integral_symmetricLogKernel_half] using hk
  have hfinite :
      (fun R : ℝ ↦ ∫ r : ℝ in (0 : ℝ)..R, diffusionIntegrand r) =
        fun R : ℝ ↦ k (logistic R) := by
    funext R
    exact integral_diffusionIntegrand_zero_to R
  rw [← hfinite] at hkz
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 diffusionIntegrand_integrableOn tendsto_id)
    hkz

/-- The exact closed form `a = 2 ζ(3)` from the main text. -/
theorem diffusionCoefficient_eq_two_mul_zetaThree :
    diffusionCoefficient = 2 * zetaThree := by
  unfold diffusionCoefficient
  rw [integral_diffusionIntegrand_eq_zetaThree]

/-- The concrete profile scale rewritten in the source's `ζ(3)` normalization. -/
theorem diffusionMainInput_kappa_eq (lambda : ℝ) :
    diffusionMainInput.kappa lambda = 2 * Real.cbrt zetaThree * lambda := by
  have hbetaPos : 0 < diffusionMainInput.beta := diffusionMainInput.beta_pos
  have hcbrtPos : 0 < Real.cbrt zetaThree :=
    Real.cbrt_pos.mpr zetaThree_pos
  have hcube :
      (diffusionMainInput.beta * Real.cbrt zetaThree) ^ 3 = (1 : ℝ) ^ 3 := by
    rw [mul_pow, diffusionMainInput.beta_cube, Real.cbrt_cube,
      diffusionMainInput_a, diffusionCoefficient_eq_two_mul_zetaThree]
    field_simp [zetaThree_pos.ne']
  have hproduct :
      diffusionMainInput.beta * Real.cbrt zetaThree = 1 := by
    exact (pow_left_inj₀ (mul_nonneg hbetaPos.le hcbrtPos.le)
      zero_le_one (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  have hcbrtEq : Real.cbrt zetaThree = 1 / diffusionMainInput.beta := by
    apply (eq_div_iff diffusionMainInput.beta_ne_zero).2
    rw [mul_comm]
    exact hproduct
  unfold MainInput.kappa
  rw [hcbrtEq]
  ring

end SeriesParallel.MainText
