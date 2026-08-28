/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.CDFOperator
import SeriesParallel.MainText.DiffusionCoefficientClosedForm
import SeriesParallel.MainText.ProfileFacade

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weighted consistency for the near-critical profiles

This file isolates the local analytic estimates used by both barriers.  The physical
hard-edge density, its zero extension, and its positive analytic extension are kept as
separate functions throughout.
-/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.MainText

open SeriesParallel.Appendix

/-- The part of the relative derivative hypothesis used in the consistency proof. -/
def RelativeC3Bound (q : ℝ → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z : ℝ,
    |iteratedDeriv j q z| ≤ M * q z

theorem deriv_bound_of_relativeC3 {q : ℝ → ℝ} {M : ℝ}
    (hrelative : RelativeC3Bound q M) (z : ℝ) :
    |deriv q z| ≤ M * q z := by
  simpa only [show iteratedDeriv 1 q z = deriv q z by
    rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] using
      hrelative.2 1 (by omega) (by omega) z

/-- A positive density with a relative first-derivative bound has a Lipschitz logarithm. -/
theorem log_density_lipschitz {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (x y : ℝ) :
    |Real.log (q y) - Real.log (q x)| ≤ M * |y - x| := by
  have hqDiff : Differentiable ℝ q := hsmooth.differentiable (by norm_num)
  have hlogDiff : Differentiable ℝ (fun z ↦ Real.log (q z)) := by
    intro z
    exact (Real.differentiableAt_log (hpos z).ne').comp z (hqDiff z)
  have hlogDeriv (z : ℝ) :
      deriv (fun u ↦ Real.log (q u)) z = deriv q z / q z := by
    exact ((hqDiff z).hasDerivAt.log (hpos z).ne').deriv
  have hbound (z : ℝ) : ‖deriv (fun u ↦ Real.log (q u)) z‖ ≤ M := by
    rw [hlogDeriv, Real.norm_eq_abs, abs_div, abs_of_pos (hpos z)]
    exact (div_le_iff₀ (hpos z)).2 (deriv_bound_of_relativeC3 hrelative z)
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun z _ ↦ hlogDiff z) (fun z _ ↦ hbound z)
    (show x ∈ (Set.univ : Set ℝ) by simp) (show y ∈ (Set.univ : Set ℝ) by simp)
  simpa only [Real.norm_eq_abs] using h

/-- Exponentiating the logarithmic Lipschitz estimate gives the relative shift bound. -/
theorem density_shift_bounds {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (z y : ℝ) :
    Real.exp (-M * |y|) * q z ≤ q (z + y) ∧
      q (z + y) ≤ Real.exp (M * |y|) * q z := by
  have hlog := log_density_lipschitz hsmooth hpos hrelative z (z + y)
  rw [show z + y - z = y by ring] at hlog
  constructor
  · calc
      Real.exp (-M * |y|) * q z =
          Real.exp (Real.log (q z) - M * |y|) := by
        rw [Real.exp_sub, Real.exp_log (hpos z)]
        rw [show -M * |y| = -(M * |y|) by ring, Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ ≤ Real.exp (Real.log (q (z + y))) := by
        apply Real.exp_le_exp.mpr
        linarith [neg_le_of_abs_le hlog]
      _ = q (z + y) := Real.exp_log (hpos (z + y))
  · calc
      q (z + y) = Real.exp (Real.log (q (z + y))) :=
        (Real.exp_log (hpos (z + y))).symm
      _ ≤ Real.exp (Real.log (q z) + M * |y|) := by
        apply Real.exp_le_exp.mpr
        linarith [le_of_abs_le hlog]
      _ = Real.exp (M * |y|) * q z := by
        rw [Real.exp_add, Real.exp_log (hpos z)]
        ring

/-- Unit mass on a set containing `[z,z+1]` turns the relative shift estimate into
the pointwise bound `q(z)^2 ≤ exp(M) q(z)`. -/
theorem density_sq_le_exp_of_mass {q : ℝ → ℝ} {M : ℝ} {S : Set ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hintegrable : IntegrableOn q S)
    (hmass : (∫ u in S, q u) = 1) {z : ℝ}
    (hinterval : Icc z (z + 1) ⊆ S) :
    q z ^ 2 ≤ Real.exp M * q z := by
  have hM : 0 ≤ M := hrelative.1
  have hpoint : ∀ u ∈ Icc z (z + 1), Real.exp (-M) * q z ≤ q u := by
    intro u hu
    have habs : |u - z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    calc
      Real.exp (-M) * q z ≤ Real.exp (-M * |u - z|) * q z := by
        apply mul_le_mul_of_nonneg_right _ (hpos z).le
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ q (z + (u - z)) :=
        (density_shift_bounds hsmooth hpos hrelative z (u - z)).1
      _ = q u := by ring_nf
  have hconstIntegrable :
      IntegrableOn (fun _ : ℝ ↦ Real.exp (-M) * q z) (Icc z (z + 1)) := by
    exact integrableOn_const measure_Icc_lt_top.ne
  have hqInterval : IntegrableOn q (Icc z (z + 1)) :=
    hintegrable.mono_set hinterval
  have hlower :
      Real.exp (-M) * q z ≤ ∫ u in Icc z (z + 1), q u := by
    calc
      Real.exp (-M) * q z =
          ∫ _u in Icc z (z + 1), Real.exp (-M) * q z := by
        simp
      _ ≤ ∫ u in Icc z (z + 1), q u := by
        apply setIntegral_mono_on hconstIntegrable hqInterval measurableSet_Icc
        exact hpoint
  have hrestricted : (∫ u in Icc z (z + 1), q u) ≤ 1 := by
    calc
      (∫ u in Icc z (z + 1), q u) ≤ ∫ u in S, q u := by
        apply setIntegral_mono_set hintegrable
        · filter_upwards with u
          exact (hpos u).le
        · exact Filter.Eventually.of_forall fun u hu ↦ hinterval hu
      _ = 1 := hmass
  have hqUpper : q z ≤ Real.exp M := by
    have hproduct : Real.exp M * Real.exp (-M) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      q z = Real.exp M * (Real.exp (-M) * q z) := by
        rw [← mul_assoc, hproduct, one_mul]
      _ ≤ Real.exp M * 1 :=
        mul_le_mul_of_nonneg_left (hlower.trans hrestricted) (Real.exp_pos M).le
      _ = Real.exp M := mul_one _
  nlinarith [hpos z]

theorem full_line_density_sq_le_exp {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hintegrable : Integrable q)
    (hmass : (∫ u, q u) = 1) (z : ℝ) :
    q z ^ 2 ≤ Real.exp M * q z := by
  have hmass' : (∫ u in (Set.univ : Set ℝ), q u) = 1 := by simpa
  simpa using density_sq_le_exp_of_mass
    hsmooth hpos hrelative hintegrable.integrableOn hmass'
      (show Icc z (z + 1) ⊆ (Set.univ : Set ℝ) by simp)

theorem half_line_density_sq_le_exp {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hintegrable : IntegrableOn q (Ici 0))
    (hmass : (∫ u in Ici (0 : ℝ), q u) = 1) {z : ℝ} (hz : 0 ≤ z) :
    q z ^ 2 ≤ Real.exp M * q z := by
  exact density_sq_le_exp_of_mass hsmooth hpos hrelative hintegrable hmass
    (fun u hu ↦ by exact hz.trans hu.1)

/-! ## The one-dimensional product used under the weighted integrals -/

/-- `Q_{s,r}(t)=q(ξ+ts)q(ξ+t(s+r))`. -/
noncomputable def weightedProduct
    (q : ℝ → ℝ) (xi s r t : ℝ) : ℝ :=
  q (xi + t * s) * q (xi + t * (s + r))

theorem iteratedDeriv_density_affine {q : ℝ → ℝ} {n : ℕ}
    (hsmooth : ContDiff ℝ n q) (xi s t : ℝ) :
    iteratedDeriv n (fun u ↦ q (xi + u * s)) t =
      s ^ n * iteratedDeriv n q (xi + t * s) := by
  let shifted : ℝ → ℝ := fun u ↦ q (xi + u)
  have hshifted : ContDiff ℝ n shifted := by
    dsimp only [shifted]
    fun_prop
  have hmul := congrFun (iteratedDeriv_comp_const_mul hshifted s) t
  have hshift := congrFun (iteratedDeriv_comp_const_add n q xi) (s * t)
  rw [hshift] at hmul
  simpa only [shifted, mul_comm] using hmul

theorem iteratedDeriv_weightedProduct {q : ℝ → ℝ} {n : ℕ}
    (hsmooth : ContDiff ℝ n q) (xi s r t : ℝ) :
    iteratedDeriv n (weightedProduct q xi s r) t =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) *
          (s ^ i * iteratedDeriv i q (xi + t * s)) *
          ((s + r) ^ (n - i) *
            iteratedDeriv (n - i) q (xi + t * (s + r))) := by
  let left : ℝ → ℝ := fun u ↦ q (xi + u * s)
  let right : ℝ → ℝ := fun u ↦ q (xi + u * (s + r))
  have hleft : ContDiff ℝ n left := by
    dsimp only [left]
    fun_prop
  have hright : ContDiff ℝ n right := by
    dsimp only [right]
    fun_prop
  change iteratedDeriv n (left * right) t = _
  rw [iteratedDeriv_mul hleft.contDiffAt hright.contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_density_affine (hsmooth.of_le (by exact_mod_cast hin))]
  rw [iteratedDeriv_density_affine
    (hsmooth.of_le (by exact_mod_cast Nat.sub_le n i))]

theorem deriv_weightedProduct_zero {q : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 3 q) (xi s r : ℝ) :
    deriv (weightedProduct q xi s r) 0 =
      (2 * s + r) * q xi * deriv q xi := by
  have h := iteratedDeriv_weightedProduct
    (n := 1) (hsmooth.of_le (by norm_num)) xi s r 0
  rw [show iteratedDeriv 1 (weightedProduct q xi s r) 0 =
      deriv (weightedProduct q xi s r) 0 by
    rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, zero_add, Nat.sub_zero,
    Nat.choose_self, Nat.cast_ofNat, Nat.sub_self, iteratedDeriv_zero, mul_zero,
    add_zero, zero_mul] at h
  have hfirst : iteratedDeriv 1 q xi = deriv q xi := by
    rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hfirst] at h
  nlinarith

theorem third_deriv_weightedProduct {q : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 3 q) (xi s r t : ℝ) :
    iteratedDeriv 3 (weightedProduct q xi s r) t =
      s ^ 3 * iteratedDeriv 3 q (xi + t * s) *
          q (xi + t * (s + r)) +
        3 * s ^ 2 * (s + r) * iteratedDeriv 2 q (xi + t * s) *
          deriv q (xi + t * (s + r)) +
        3 * s * (s + r) ^ 2 * deriv q (xi + t * s) *
          iteratedDeriv 2 q (xi + t * (s + r)) +
        (s + r) ^ 3 * q (xi + t * s) *
          iteratedDeriv 3 q (xi + t * (s + r)) := by
  have h := iteratedDeriv_weightedProduct hsmooth xi s r t
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, zero_add,
    Nat.choose, Nat.cast_ofNat, Nat.reduceSub, iteratedDeriv_zero, add_zero] at h
  rw [show iteratedDeriv 1 q = deriv q by
    funext z
    rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] at h
  rw [h]
  ring

/-! ## A symmetric third-order Taylor estimate -/

private theorem taylorWithinEval_two_eq {Q : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 3 Q) {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Q 2 (uIcc 0 x) 0 x =
      Q 0 + deriv Q 0 * x + iteratedDeriv 2 Q 0 * x ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := uniqueDiffOn_uIcc hx.symm
  have hzero : (0 : ℝ) ∈ uIcc 0 x := left_mem_uIcc
  have hwithin0 : iteratedDerivWithin 0 Q (uIcc 0 x) 0 =
      iteratedDeriv 0 Q 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hsmooth.contDiffAt.of_le (by norm_num)) hzero
  have hwithin1 : iteratedDerivWithin 1 Q (uIcc 0 x) 0 =
      iteratedDeriv 1 Q 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hsmooth.contDiffAt.of_le (by norm_num)) hzero
  have hwithin2 : iteratedDerivWithin 2 Q (uIcc 0 x) 0 =
      iteratedDeriv 2 Q 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hsmooth.contDiffAt.of_le (by norm_num)) hzero
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hwithin0, hwithin1, hwithin2,
    iteratedDeriv_zero]
  ring

/-- Taylor at `±ε`, with the even terms cancelled explicitly. -/
theorem symmetric_taylor_three {Q : ℝ → ℝ} (hsmooth : ContDiff ℝ 3 Q)
    {epsilon B : ℝ} (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hthird : ∀ t, |t| < epsilon → |iteratedDeriv 3 Q t| ≤ B) :
    |Q epsilon - Q (-epsilon) - 2 * epsilon * deriv Q 0| ≤
      B * epsilon ^ 3 / 3 := by
  obtain ⟨tp, htp, hp⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Q) (x := epsilon) (x₀ := 0) (n := 2) hepsilon.ne
      hsmooth.contDiffOn
  obtain ⟨tm, htm, hm⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Q) (x := -epsilon) (x₀ := 0) (n := 2)
      (neg_ne_zero.mpr hepsilon.ne').symm hsmooth.contDiffOn
  have htpAbs : |tp| < epsilon := by
    rw [uIoo_of_le hepsilon.le] at htp
    rw [abs_lt]
    exact ⟨by linarith [htp.1], htp.2⟩
  have htmAbs : |tm| < epsilon := by
    rw [uIoo_of_ge (by linarith : -epsilon ≤ (0 : ℝ))] at htm
    rw [abs_lt]
    exact ⟨htm.1, by linarith [htm.2]⟩
  rw [taylorWithinEval_two_eq hsmooth hepsilon.ne'] at hp
  rw [taylorWithinEval_two_eq hsmooth (neg_ne_zero.mpr hepsilon.ne')] at hm
  have hremainder :
      Q epsilon - Q (-epsilon) - 2 * epsilon * deriv Q 0 =
        iteratedDeriv 3 Q tp * epsilon ^ 3 / 6 -
          iteratedDeriv 3 Q tm * (-epsilon) ^ 3 / 6 := by
    norm_num at hp hm
    nlinarith
  rw [hremainder]
  calc
    |iteratedDeriv 3 Q tp * epsilon ^ 3 / 6 -
        iteratedDeriv 3 Q tm * (-epsilon) ^ 3 / 6| ≤
        |iteratedDeriv 3 Q tp * epsilon ^ 3 / 6| +
          |iteratedDeriv 3 Q tm * (-epsilon) ^ 3 / 6| := abs_sub _ _
    _ ≤ B * epsilon ^ 3 / 6 + B * epsilon ^ 3 / 6 := by
      apply add_le_add
      · rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hepsilon.le 3)]
        norm_num
        gcongr
        exact hthird tp htpAbs
      · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_pos hepsilon]
        norm_num
        gcongr
        exact hthird tm htmAbs
    _ = B * epsilon ^ 3 / 3 := by ring

theorem iteratedDeriv_le_augmented {q : ℝ → ℝ} {M : ℝ}
    (hpos : ∀ z, 0 < q z) (hrelative : RelativeC3Bound q M)
    {j : ℕ} (hj : j ≤ 3) (z : ℝ) :
    |iteratedDeriv j q z| ≤ (M + 1) * q z := by
  by_cases hj0 : j = 0
  · subst j
    simp only [iteratedDeriv_zero, abs_of_pos (hpos z)]
    nlinarith [hrelative.1, hpos z]
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    exact (hrelative.2 j hj1 hj z).trans (by
      nlinarith [hrelative.1, hpos z])

/-- The explicit Leibniz formula and relative derivative bounds give a polynomial
third-derivative envelope before any use of log-Lipschitz. -/
theorem third_deriv_weightedProduct_relative_bound {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi s r t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr0 : 0 ≤ r) :
    |iteratedDeriv 3 (weightedProduct q xi s r) t| ≤
      8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
        q (xi + t * s) * q (xi + t * (s + r)) := by
  let A := q (xi + t * s)
  let B := q (xi + t * (s + r))
  let D := M + 1
  let L := 1 + r
  have hA : 0 < A := hpos _
  have hB : 0 < B := hpos _
  have hD : 1 ≤ D := by dsimp only [D]; linarith [hrelative.1]
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hsL : s ≤ L := by dsimp only [L]; linarith
  have hsr0 : 0 ≤ s + r := by linarith
  have hsrL : s + r ≤ L := by dsimp only [L]; linarith
  have hscale0 : s ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hs0 hsL 3
  have hscale1 : s ^ 2 * (s + r) ≤ L ^ 3 := by
    calc
      s ^ 2 * (s + r) ≤ L ^ 2 * L := by gcongr
      _ = L ^ 3 := by ring
  have hscale2 : s * (s + r) ^ 2 ≤ L ^ 3 := by
    calc
      s * (s + r) ^ 2 ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
  have hscale3 : (s + r) ^ 3 ≤ L ^ 3 :=
    pow_le_pow_left₀ hsr0 hsrL 3
  have hd0A : |A| ≤ D * A := by
    rw [abs_of_pos hA]
    nlinarith [hD, hA]
  have hd0B : |B| ≤ D * B := by
    rw [abs_of_pos hB]
    nlinarith [hD, hB]
  have hd1A : |deriv q (xi + t * s)| ≤ D * A := by
    have hd := iteratedDeriv_le_augmented hpos hrelative (j := 1)
      (by omega) (xi + t * s)
    rw [show iteratedDeriv 1 q (xi + t * s) = deriv q (xi + t * s) by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] at hd
    simpa only [A, D] using hd
  have hd1B : |deriv q (xi + t * (s + r))| ≤ D * B := by
    have hd := iteratedDeriv_le_augmented hpos hrelative (j := 1)
      (by omega) (xi + t * (s + r))
    rw [show iteratedDeriv 1 q (xi + t * (s + r)) =
        deriv q (xi + t * (s + r)) by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] at hd
    simpa only [B, D] using hd
  have hd2A : |iteratedDeriv 2 q (xi + t * s)| ≤ D * A :=
    iteratedDeriv_le_augmented hpos hrelative (by omega) _
  have hd2B : |iteratedDeriv 2 q (xi + t * (s + r))| ≤ D * B :=
    iteratedDeriv_le_augmented hpos hrelative (by omega) _
  have hd3A : |iteratedDeriv 3 q (xi + t * s)| ≤ D * A :=
    iteratedDeriv_le_augmented hpos hrelative (by omega) _
  have hd3B : |iteratedDeriv 3 q (xi + t * (s + r))| ≤ D * B :=
    iteratedDeriv_le_augmented hpos hrelative (by omega) _
  have ht0 :
      |s ^ 3 * iteratedDeriv 3 q (xi + t * s) * B| ≤
        D ^ 2 * L ^ 3 * A * B := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0 3)]
    calc
      s ^ 3 * |iteratedDeriv 3 q (xi + t * s)| * |B| ≤
          L ^ 3 * (D * A) * (D * B) := by gcongr
      _ = D ^ 2 * L ^ 3 * A * B := by ring
  have ht1 :
      |3 * s ^ 2 * (s + r) * iteratedDeriv 2 q (xi + t * s) *
          deriv q (xi + t * (s + r))| ≤
        3 * D ^ 2 * L ^ 3 * A * B := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0 2),
      abs_of_nonneg hsr0]
    norm_num
    calc
      3 * s ^ 2 * (s + r) * |iteratedDeriv 2 q (xi + t * s)| *
          |deriv q (xi + t * (s + r))| =
        3 * (s ^ 2 * (s + r)) * |iteratedDeriv 2 q (xi + t * s)| *
          |deriv q (xi + t * (s + r))| := by ring
      _ ≤ 3 * L ^ 3 * (D * A) * (D * B) := by gcongr
      _ = 3 * D ^ 2 * L ^ 3 * A * B := by ring
  have ht2 :
      |3 * s * (s + r) ^ 2 * deriv q (xi + t * s) *
          iteratedDeriv 2 q (xi + t * (s + r))| ≤
        3 * D ^ 2 * L ^ 3 * A * B := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0,
      abs_of_nonneg (pow_nonneg hsr0 2)]
    norm_num
    calc
      3 * s * (s + r) ^ 2 * |deriv q (xi + t * s)| *
          |iteratedDeriv 2 q (xi + t * (s + r))| =
        3 * (s * (s + r) ^ 2) * |deriv q (xi + t * s)| *
          |iteratedDeriv 2 q (xi + t * (s + r))| := by ring
      _ ≤ 3 * L ^ 3 * (D * A) * (D * B) := by gcongr
      _ = 3 * D ^ 2 * L ^ 3 * A * B := by ring
  have ht3 :
      |(s + r) ^ 3 * A * iteratedDeriv 3 q (xi + t * (s + r))| ≤
        D ^ 2 * L ^ 3 * A * B := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hsr0 3)]
    calc
      (s + r) ^ 3 * |A| * |iteratedDeriv 3 q (xi + t * (s + r))| ≤
          L ^ 3 * (D * A) * (D * B) := by gcongr
      _ = D ^ 2 * L ^ 3 * A * B := by ring
  rw [third_deriv_weightedProduct hsmooth]
  have htriangle : ∀ a b c d : ℝ,
      |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
    intro a b c d
    calc
      |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ (|a + b| + |c|) + |d| := by gcongr; exact abs_add_le _ _
      _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add_le _ _
  calc
    |s ^ 3 * iteratedDeriv 3 q (xi + t * s) * B +
        3 * s ^ 2 * (s + r) * iteratedDeriv 2 q (xi + t * s) *
          deriv q (xi + t * (s + r)) +
        3 * s * (s + r) ^ 2 * deriv q (xi + t * s) *
          iteratedDeriv 2 q (xi + t * (s + r)) +
        (s + r) ^ 3 * A * iteratedDeriv 3 q (xi + t * (s + r))| ≤
      D ^ 2 * L ^ 3 * A * B + 3 * D ^ 2 * L ^ 3 * A * B +
        3 * D ^ 2 * L ^ 3 * A * B + D ^ 2 * L ^ 3 * A * B :=
      (htriangle _ _ _ _).trans (add_le_add (add_le_add (add_le_add ht0 ht1) ht2) ht3)
    _ = 8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
        q (xi + t * s) * q (xi + t * (s + r)) := by
      dsimp only [A, B, D, L]
      ring

/-! ## The fixed integrable envelopes -/

/-- The only polynomial-exponential moment needed in the cubic remainder. -/
noncomputable def cubicExponentialMoment : ℝ :=
  ∫ r in Ici (0 : ℝ), (1 + r) ^ 3 * Real.exp (-r / 2)

theorem cubicExponentialEnvelope_integrableOn :
    IntegrableOn (fun r : ℝ ↦ (1 + r) ^ 3 * Real.exp (-r / 2))
      (Ici 0) := by
  have hzero : IntegrableOn (fun r : ℝ ↦ Real.exp (-r / 2))
      (Ioi 0) := by
    have h : IntegrableOn
        (fun r : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * r ^ (1 : ℝ)))
        (Ioi 0) := .of_integral_ne_zero (by
        rw [integral_exp_neg_mul_rpow (by positivity) (by positivity)]
        positivity)
    apply h.congr
    filter_upwards with r
    rw [Real.rpow_one]
    congr 1 <;> ring
  have hcubic : IntegrableOn
      (fun r : ℝ ↦ r ^ 3 * Real.exp (-r / 2)) (Ioi 0) := by
    have h : IntegrableOn
        (fun r : ℝ ↦ r ^ (3 : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * r ^ (1 : ℝ)))
        (Ioi 0) := .of_integral_ne_zero (by
        rw [integral_rpow_mul_exp_neg_mul_rpow
          (by positivity) (by norm_num) (by positivity)]
        positivity)
    apply h.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.rpow_one]
    rw [show -(1 / 2 : ℝ) * r = -r / 2 by ring]
    congr 1
    simpa using Real.rpow_natCast r 3
  have hdom : IntegrableOn
      (fun r : ℝ ↦ 4 * (Real.exp (-r / 2) +
        r ^ 3 * Real.exp (-r / 2))) (Ioi 0) :=
    (hzero.add hcubic).const_mul 4
  have htarget : IntegrableOn
      (fun r : ℝ ↦ (1 + r) ^ 3 * Real.exp (-r / 2)) (Ioi 0) := by
    apply Integrable.mono' hdom
    · fun_prop
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := hr.le
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · have hpoly : (1 + r) ^ 3 ≤ 4 * (1 + r ^ 3) := by
          have hfactor : 0 ≤ 3 * (r + 1) * (r - 1) ^ 2 :=
            mul_nonneg (mul_nonneg (by positivity) (by linarith))
              (sq_nonneg (r - 1))
          nlinarith
        calc
          (1 + r) ^ 3 * Real.exp (-r / 2) ≤
              4 * (1 + r ^ 3) * Real.exp (-r / 2) := by
            gcongr
          _ = 4 * (Real.exp (-r / 2) +
              r ^ 3 * Real.exp (-r / 2)) := by ring
      · exact mul_nonneg (pow_nonneg (by linarith) 3) (Real.exp_pos _).le
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 htarget

theorem cubicExponentialMoment_nonneg : 0 ≤ cubicExponentialMoment := by
  unfold cubicExponentialMoment
  exact integral_nonneg_of_ae (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
    have hr0 : 0 ≤ r := hr
    exact mul_nonneg (pow_nonneg (by linarith) 3) (Real.exp_pos _).le)

theorem exponentialEnvelope_integrableOn :
    IntegrableOn (fun r : ℝ ↦ Real.exp (-r / 2)) (Ici 0) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi).2
  have h : IntegrableOn
      (fun r : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * r ^ (1 : ℝ)))
      (Ioi 0) := .of_integral_ne_zero (by
      rw [integral_exp_neg_mul_rpow (by positivity) (by positivity)]
      positivity)
  apply h.congr
  filter_upwards with r
  rw [Real.rpow_one]
  congr 1 <;> ring

noncomputable def exponentialMoment : ℝ :=
  ∫ r in Ici (0 : ℝ), Real.exp (-r / 2)

theorem exponentialMoment_nonneg : 0 ≤ exponentialMoment := by
  unfold exponentialMoment
  exact integral_nonneg_of_ae (by
    filter_upwards
    exact fun r ↦ (Real.exp_pos (-r / 2)).le)

/-- Measurability of an interval integral whose upper endpoint is `h r`. -/
theorem aestronglyMeasurable_kernelInterval
    {F : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ ↦ F p.1 p.2)) :
    AEStronglyMeasurable (fun r ↦ ∫ s in (0 : ℝ)..h r, F r s) := by
  let A : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ h p.1}
  have hA : MeasurableSet A := by
    apply (measurableSet_lt measurable_const measurable_snd).inter
    exact measurableSet_le measurable_snd
      (continuous_h.measurable.comp measurable_fst)
  have hindicator : StronglyMeasurable
      (A.indicator fun p : ℝ × ℝ ↦ F p.1 p.2) :=
    hF.stronglyMeasurable.indicator hA
  have hintegral :=
    hindicator.integral_prod_right' (ν := (volume : Measure ℝ))
  apply hintegral.aestronglyMeasurable.congr
  filter_upwards with r
  rw [intervalIntegral.integral_of_le (h_nonneg r)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioc (0 : ℝ) (h r)
  · simp only [Set.indicator_of_mem hs, A]
    rw [Set.indicator_of_mem]
    exact hs
  · simp only [Set.indicator_of_notMem hs, A]
    rw [Set.indicator_of_notMem]
    exact hs

theorem aestronglyMeasurable_kernelInterval_of_stronglyMeasurable
    {F : ℝ → ℝ → ℝ}
    (hF : StronglyMeasurable (fun p : ℝ × ℝ ↦ F p.1 p.2)) :
    AEStronglyMeasurable (fun r ↦ ∫ s in (0 : ℝ)..h r, F r s) := by
  let A : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ h p.1}
  have hA : MeasurableSet A := by
    apply (measurableSet_lt measurable_const measurable_snd).inter
    exact measurableSet_le measurable_snd
      (continuous_h.measurable.comp measurable_fst)
  have hindicator : StronglyMeasurable
      (A.indicator fun p : ℝ × ℝ ↦ F p.1 p.2) :=
    hF.indicator hA
  have hintegral :=
    hindicator.integral_prod_right' (ν := (volume : Measure ℝ))
  apply hintegral.aestronglyMeasurable.congr
  filter_upwards with r
  rw [intervalIntegral.integral_of_le (h_nonneg r)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioc (0 : ℝ) (h r)
  · simp only [Set.indicator_of_mem hs, A]
    rw [Set.indicator_of_mem]
    exact hs
  · simp only [Set.indicator_of_notMem hs, A]
    rw [Set.indicator_of_notMem]
    exact hs

/-! ## Pointwise bounds uniform in the phase centre -/

/-- A positive small-parameter threshold depending only on the relative bound. -/
noncomputable def relativeConsistencyEpsilon (M : ℝ) : ℝ :=
  1 / (4 * (M + 1))

theorem relativeConsistencyEpsilon_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < relativeConsistencyEpsilon M := by
  unfold relativeConsistencyEpsilon
  positivity

theorem small_exponential_kernel_bound {M epsilon r : ℝ}
    (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M) (hr : 0 ≤ r) :
    h r * Real.exp (2 * M * epsilon * (1 + r)) ≤
      Real.exp (1 / 2) * Real.exp (-r / 2) := by
  have hcoef : 2 * M * epsilon < 1 / 2 := by
    unfold relativeConsistencyEpsilon at hsmall
    have hden : 0 < 4 * (M + 1) := by positivity
    have hepsBound : epsilon * (4 * (M + 1)) < 1 :=
      (lt_div_iff₀ hden).mp (by simpa [one_div] using hsmall)
    nlinarith [mul_nonneg hM hepsilon.le]
  calc
    h r * Real.exp (2 * M * epsilon * (1 + r)) ≤
        Real.exp (-r) * Real.exp (2 * M * epsilon * (1 + r)) := by
      gcongr
      exact h_le_exp_neg r
    _ ≤ Real.exp (-r) * Real.exp ((1 / 2) * (1 + r)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hcoef.le (by linarith))
    _ = Real.exp (1 / 2) * Real.exp (-r / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- Both shifted factors are controlled by the density at the centre. -/
theorem weightedProduct_shift_bound {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi s r t epsilon : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr0 : 0 ≤ r)
    (ht : |t| ≤ epsilon) :
    weightedProduct q xi s r t ≤
      Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 := by
  have hM : 0 ≤ M := hrelative.1
  have hepsilon : 0 ≤ epsilon := (abs_nonneg t).trans ht
  have hL : 0 ≤ 1 + r := by linarith
  have hsr0 : 0 ≤ s + r := by linarith
  have hsr1 : s + r ≤ 1 + r := by linarith
  have hts : |t * s| ≤ epsilon * (1 + r) := by
    rw [abs_mul, abs_of_nonneg hs0]
    calc
      |t| * s ≤ epsilon * s := by gcongr
      _ ≤ epsilon * (1 + r) :=
        mul_le_mul_of_nonneg_left (by linarith) hepsilon
  have htsr : |t * (s + r)| ≤ epsilon * (1 + r) := by
    rw [abs_mul, abs_of_nonneg hsr0]
    calc
      |t| * (s + r) ≤ epsilon * (s + r) := by gcongr
      _ ≤ epsilon * (1 + r) := by gcongr
  let A := M * epsilon * (1 + r)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hleft : q (xi + t * s) ≤ Real.exp A * q xi := by
    calc
      q (xi + t * s) ≤ Real.exp (M * |t * s|) * q xi :=
        (density_shift_bounds hsmooth hpos hrelative xi (t * s)).2
      _ ≤ Real.exp A * q xi := by
        apply mul_le_mul_of_nonneg_right _ (hpos xi).le
        apply Real.exp_le_exp.mpr
        dsimp only [A]
        calc
          M * |t * s| ≤ M * (epsilon * (1 + r)) :=
            mul_le_mul_of_nonneg_left hts hM
          _ = M * epsilon * (1 + r) := by ring
  have hright : q (xi + t * (s + r)) ≤ Real.exp A * q xi := by
    calc
      q (xi + t * (s + r)) ≤
          Real.exp (M * |t * (s + r)|) * q xi :=
        (density_shift_bounds hsmooth hpos hrelative xi
          (t * (s + r))).2
      _ ≤ Real.exp A * q xi := by
        apply mul_le_mul_of_nonneg_right _ (hpos xi).le
        apply Real.exp_le_exp.mpr
        dsimp only [A]
        calc
          M * |t * (s + r)| ≤ M * (epsilon * (1 + r)) :=
            mul_le_mul_of_nonneg_left htsr hM
          _ = M * epsilon * (1 + r) := by ring
  unfold weightedProduct
  calc
    q (xi + t * s) * q (xi + t * (s + r)) ≤
        (Real.exp A * q xi) * (Real.exp A * q xi) := by
      exact mul_le_mul hleft hright (hpos _).le
        (mul_nonneg (Real.exp_pos A).le (hpos xi).le)
    _ = (Real.exp A * Real.exp A) * q xi ^ 2 := by ring
    _ = Real.exp (A + A) * q xi ^ 2 := by rw [Real.exp_add]
    _ = Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 := by
      dsimp only [A]
      congr 1
      ring

/-- The symmetric Taylor remainder for `Q_{s,r}`, before integration in `s,r`. -/
theorem weightedProduct_symmetric_remainder_bound
    {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi s r epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r) :
    |weightedProduct q xi s r epsilon -
        weightedProduct q xi s r (-epsilon) -
        2 * epsilon * (2 * s + r) * q xi * deriv q xi| ≤
      8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
        Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 *
        epsilon ^ 3 / 3 := by
  let B := 8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
    Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hQ : ContDiff ℝ 3 (weightedProduct q xi s r) := by
    unfold weightedProduct
    fun_prop
  have hthird : ∀ t, |t| < epsilon →
      |iteratedDeriv 3 (weightedProduct q xi s r) t| ≤ B := by
    intro t ht
    have hraw := third_deriv_weightedProduct_relative_bound
      hsmooth hpos hrelative hs0 hs1 hr0 (xi := xi) (t := t)
    have hshift := weightedProduct_shift_bound hsmooth hpos hrelative
      hs0 hs1 hr0 (le_of_lt ht) (xi := xi)
    calc
      |iteratedDeriv 3 (weightedProduct q xi s r) t| ≤
          8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
            q (xi + t * s) * q (xi + t * (s + r)) := hraw
      _ = 8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
          weightedProduct q xi s r t := by
        unfold weightedProduct
        ring
      _ ≤ 8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
          (Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2) := by
        gcongr
      _ = B := by
        dsimp only [B]
        ring
  have htaylor := symmetric_taylor_three hQ hepsilon hB hthird
  rw [deriv_weightedProduct_zero hsmooth] at htaylor
  simpa only [B, mul_assoc] using htaylor

/-! ## The two weighted crossing integrals -/

noncomputable def weightedIplus
    (q : ℝ → ℝ) (epsilon xi : ℝ) : ℝ :=
  epsilon ^ 2 * ∫ r in Ici (0 : ℝ),
    ∫ s in (0 : ℝ)..h r, weightedProduct q xi s r epsilon

noncomputable def weightedIminus
    (q : ℝ → ℝ) (epsilon xi : ℝ) : ℝ :=
  epsilon ^ 2 * ∫ r in Ici (0 : ℝ),
    ∫ s in (0 : ℝ)..h r, weightedProduct q xi s r (-epsilon)

noncomputable def weightedRemainder
    (q : ℝ → ℝ) (epsilon xi r s : ℝ) : ℝ :=
  weightedProduct q xi s r epsilon -
    weightedProduct q xi s r (-epsilon) -
    2 * epsilon * (2 * s + r) * q xi * deriv q xi

theorem h_le_one {r : ℝ} (hr : 0 ≤ r) : h r ≤ 1 := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
  exact (h_le_log_two hr).trans (by norm_num at hlog ⊢; linarith)

theorem weightedProduct_kernel_integrableOn
    {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi epsilon t : ℝ}
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M)
    (ht : |t| ≤ epsilon) :
    IntegrableOn
      (fun r ↦ ∫ s in (0 : ℝ)..h r,
        weightedProduct q xi s r t) (Ici 0) := by
  let D : ℝ := Real.exp (1 / 2) * q xi ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hdom : IntegrableOn
      (fun r : ℝ ↦ D * Real.exp (-r / 2)) (Ici 0) :=
    exponentialEnvelope_integrableOn.const_mul D
  apply Integrable.mono' hdom
  · apply (aestronglyMeasurable_kernelInterval (F := fun r s ↦
      weightedProduct q xi s r t) ?_).mono_measure
      Measure.restrict_le_self
    unfold weightedProduct
    fun_prop
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
    have hr0 : 0 ≤ r := hr
    have hnorm :
        |∫ s in (0 : ℝ)..h r, weightedProduct q xi s r t| ≤
          (Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2) * h r := by
      have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s ↦ weightedProduct q xi s r t)
        (C := Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2)
        (fun s hs ↦ by
          rw [uIoc_of_le (h_nonneg r)] at hs
          rw [Real.norm_eq_abs, abs_of_pos]
          · exact weightedProduct_shift_bound hsmooth hpos hrelative
              hs.1.le (hs.2.trans (h_le_one hr0)) hr0 ht
          · unfold weightedProduct
            exact mul_pos (hpos _) (hpos _))
      simpa only [Real.norm_eq_abs, sub_zero,
        abs_of_nonneg (h_nonneg r)] using hinterval
    rw [Real.norm_eq_abs]
    calc
      |∫ s in (0 : ℝ)..h r, weightedProduct q xi s r t| ≤
          Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 * h r :=
        hnorm
      _ = q xi ^ 2 *
          (h r * Real.exp (2 * M * epsilon * (1 + r))) := by ring
      _ ≤ q xi ^ 2 *
          (Real.exp (1 / 2) * Real.exp (-r / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (small_exponential_kernel_bound hrelative.1 hepsilon hsmall hr0)
          (sq_nonneg (q xi))
      _ = D * Real.exp (-r / 2) := by
        dsimp only [D]
        ring

theorem intervalIntegral_linearKernel (r : ℝ) :
    (∫ s in (0 : ℝ)..h r, (2 * s + r)) = diffusionIntegrand r := by
  have hlinear : IntervalIntegrable (fun s : ℝ ↦ 2 * s) volume 0 (h r) := by
    exact (continuous_const.mul continuous_id).intervalIntegrable 0 (h r)
  have hconst : IntervalIntegrable (fun _s : ℝ ↦ r) volume 0 (h r) := by
    exact continuous_const.intervalIntegrable 0 (h r)
  rw [intervalIntegral.integral_add hlinear hconst]
  rw [show (fun s : ℝ ↦ 2 * s) = fun s ↦ s * 2 by
    funext s
    ring]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  unfold diffusionIntegrand
  ring

theorem integral_linearKernel :
    (∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r, (2 * s + r)) =
      diffusionCoefficient / 2 := by
  rw [setIntegral_congr_fun measurableSet_Ici
    (fun r _hr ↦ intervalIntegral_linearKernel r)]
  rw [integral_Ici_eq_integral_Ioi]
  unfold diffusionCoefficient
  ring

theorem weightedDifference_remainder_identity
    {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M) :
    weightedIplus q epsilon xi - weightedIminus q epsilon xi -
        diffusionCoefficient * epsilon ^ 3 * q xi * deriv q xi =
      epsilon ^ 2 * ∫ r in Ici (0 : ℝ),
        ∫ s in (0 : ℝ)..h r, weightedRemainder q epsilon xi r s := by
  let P : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..h r,
    weightedProduct q xi s r epsilon
  let N : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..h r,
    weightedProduct q xi s r (-epsilon)
  let L : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..h r,
    2 * epsilon * (2 * s + r) * q xi * deriv q xi
  have hP : IntegrableOn P (Ici 0) := by
    dsimp only [P]
    exact weightedProduct_kernel_integrableOn hsmooth hpos hrelative
      hepsilon hsmall (by rw [abs_of_pos hepsilon])
  have hN : IntegrableOn N (Ici 0) := by
    dsimp only [N]
    exact weightedProduct_kernel_integrableOn hsmooth hpos hrelative
      hepsilon hsmall (by rw [abs_neg, abs_of_pos hepsilon])
  have hinnerLinear (r : ℝ) :
      L r = (2 * epsilon * q xi * deriv q xi) *
        diffusionIntegrand r := by
    dsimp only [L]
    calc
      (∫ s in (0 : ℝ)..h r,
          2 * epsilon * (2 * s + r) * q xi * deriv q xi) =
          ∫ s in (0 : ℝ)..h r,
            (2 * epsilon * q xi * deriv q xi) * (2 * s + r) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        ring
      _ = (2 * epsilon * q xi * deriv q xi) *
          ∫ s in (0 : ℝ)..h r, (2 * s + r) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (2 * epsilon * q xi * deriv q xi) *
          diffusionIntegrand r := by
        rw [intervalIntegral_linearKernel]
  have hdiffusionIci : IntegrableOn diffusionIntegrand (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      diffusionIntegrand_integrableOn
  have hL : IntegrableOn L (Ici 0) := by
    apply (hdiffusionIci.const_mul
      (2 * epsilon * q xi * deriv q xi)).congr
    filter_upwards with r
    exact (hinnerLinear r).symm
  have hlead : epsilon ^ 2 * (∫ r in Ici (0 : ℝ), L r) =
      diffusionCoefficient * epsilon ^ 3 * q xi * deriv q xi := by
    rw [setIntegral_congr_fun measurableSet_Ici
      (fun r _hr ↦ hinnerLinear r)]
    rw [integral_const_mul]
    rw [integral_Ici_eq_integral_Ioi]
    unfold diffusionCoefficient
    ring
  have hinner (r : ℝ) :
      P r - N r - L r =
        ∫ s in (0 : ℝ)..h r, weightedRemainder q epsilon xi r s := by
    have hPc : Continuous
        (fun s ↦ weightedProduct q xi s r epsilon) := by
      unfold weightedProduct
      fun_prop
    have hNc : Continuous
        (fun s ↦ weightedProduct q xi s r (-epsilon)) := by
      unfold weightedProduct
      fun_prop
    have hLc : Continuous
        (fun s ↦ 2 * epsilon * (2 * s + r) * q xi * deriv q xi) := by
      fun_prop
    dsimp only [P, N, L]
    rw [← intervalIntegral.integral_sub
      (hPc.intervalIntegrable 0 (h r))
      (hNc.intervalIntegrable 0 (h r))]
    rw [← intervalIntegral.integral_sub
      ((hPc.intervalIntegrable 0 (h r)).sub
        (hNc.intervalIntegrable 0 (h r)))
      (hLc.intervalIntegrable 0 (h r))]
    apply intervalIntegral.integral_congr
    intro s _hs
    rfl
  have hPN : (∫ r in Ici (0 : ℝ), (P r - N r)) =
      (∫ r in Ici (0 : ℝ), P r) - ∫ r in Ici (0 : ℝ), N r := by
    simpa only [Pi.sub_apply] using integral_sub hP hN
  have hPNL : (∫ r in Ici (0 : ℝ), (P r - N r - L r)) =
      (∫ r in Ici (0 : ℝ), (P r - N r)) -
        ∫ r in Ici (0 : ℝ), L r := by
    simpa only [Pi.sub_apply] using integral_sub (hP.sub hN) hL
  unfold weightedIplus weightedIminus
  rw [← hlead]
  calc
    epsilon ^ 2 * (∫ r in Ici (0 : ℝ), P r) -
          epsilon ^ 2 * (∫ r in Ici (0 : ℝ), N r) -
          epsilon ^ 2 * (∫ r in Ici (0 : ℝ), L r) =
        epsilon ^ 2 *
          ((∫ r in Ici (0 : ℝ), P r) -
            (∫ r in Ici (0 : ℝ), N r) -
            (∫ r in Ici (0 : ℝ), L r)) := by ring
    _ = epsilon ^ 2 *
        ∫ r in Ici (0 : ℝ), (P r - N r - L r) := by
      rw [hPNL, hPN]
    _ = epsilon ^ 2 * ∫ r in Ici (0 : ℝ),
        ∫ s in (0 : ℝ)..h r,
          weightedRemainder q epsilon xi r s := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ici
      intro r _hr
      exact hinner r

noncomputable def weightedDifferenceConstant (M K : ℝ) : ℝ :=
  8 * (M + 1) ^ 2 * Real.exp (1 / 2) * K *
    cubicExponentialMoment

/-- Explicit integrated symmetric-Taylor estimate at a fixed phase centre. -/
theorem weightedIntegral_difference_bound
    {q : ℝ → ℝ} {M K : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hK : 0 ≤ K)
    {xi epsilon : ℝ} (hsq : q xi ^ 2 ≤ K * q xi)
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M) :
    |weightedIplus q epsilon xi - weightedIminus q epsilon xi -
        diffusionCoefficient * epsilon ^ 3 * q xi * deriv q xi| ≤
      weightedDifferenceConstant M K * epsilon ^ 5 * q xi := by
  let A : ℝ := 8 * (M + 1) ^ 2 * epsilon ^ 3 * q xi ^ 2
  let G : ℝ := A * Real.exp (1 / 2)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hGIntegrable : IntegrableOn
      (fun r : ℝ ↦ G * ((1 + r) ^ 3 * Real.exp (-r / 2)))
      (Ici 0) := cubicExponentialEnvelope_integrableOn.const_mul G
  have houter :
      |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
          weightedRemainder q epsilon xi r s| ≤
        G * cubicExponentialMoment := by
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le
      hGIntegrable (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
        have hr0 : 0 ≤ r := hr
        have hL0 : 0 ≤ (1 + r) ^ 3 := pow_nonneg (by linarith) 3
        let C : ℝ := 8 * (M + 1) ^ 2 * (1 + r) ^ 3 *
          Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 *
          epsilon ^ 3
        have hC : 0 ≤ C := by
          dsimp only [C]
          positivity
        have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun s ↦ weightedRemainder q epsilon xi r s)
          (C := C / 3) (fun s hs ↦ by
            rw [uIoc_of_le (h_nonneg r)] at hs
            rw [Real.norm_eq_abs]
            exact weightedProduct_symmetric_remainder_bound
              hsmooth hpos hrelative hepsilon hs.1.le
                (hs.2.trans (h_le_one hr0)) hr0)
        have hbase :
            |∫ s in (0 : ℝ)..h r,
                weightedRemainder q epsilon xi r s| ≤
              (C / 3) * h r := by
          simpa only [Real.norm_eq_abs, sub_zero,
            abs_of_nonneg (h_nonneg r)] using hinterval
        rw [Real.norm_eq_abs]
        calc
          |∫ s in (0 : ℝ)..h r,
              weightedRemainder q epsilon xi r s| ≤
              (C / 3) * h r := hbase
          _ ≤ C * h r := by
            exact mul_le_mul_of_nonneg_right (by nlinarith) (h_nonneg r)
          _ = A * (1 + r) ^ 3 *
              (h r * Real.exp (2 * M * epsilon * (1 + r))) := by
            dsimp only [A, C]
            ring
          _ ≤ A * (1 + r) ^ 3 *
              (Real.exp (1 / 2) * Real.exp (-r / 2)) := by
            exact mul_le_mul_of_nonneg_left
              (small_exponential_kernel_bound hrelative.1 hepsilon
                hsmall hr0)
              (mul_nonneg hA hL0)
          _ = G * ((1 + r) ^ 3 * Real.exp (-r / 2)) := by
            dsimp only [G]
            ring)
    calc
      |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
          weightedRemainder q epsilon xi r s| ≤
          ∫ r in Ici (0 : ℝ),
            G * ((1 + r) ^ 3 * Real.exp (-r / 2)) := by
        simpa only [Real.norm_eq_abs] using hnorm
      _ = G * cubicExponentialMoment := by
        rw [integral_const_mul]
        rfl
  rw [weightedDifference_remainder_identity hsmooth hpos hrelative
    hepsilon hsmall]
  rw [abs_mul, abs_of_nonneg (sq_nonneg epsilon)]
  calc
    epsilon ^ 2 *
        |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
          weightedRemainder q epsilon xi r s| ≤
        epsilon ^ 2 * (G * cubicExponentialMoment) := by
      gcongr
    _ = (epsilon ^ 2 * 8 * (M + 1) ^ 2 * epsilon ^ 3 *
        Real.exp (1 / 2) * cubicExponentialMoment) * q xi ^ 2 := by
      dsimp only [G, A]
      ring
    _ ≤ (epsilon ^ 2 * 8 * (M + 1) ^ 2 * epsilon ^ 3 *
        Real.exp (1 / 2) * cubicExponentialMoment) * (K * q xi) := by
      apply mul_le_mul_of_nonneg_left hsq
      exact mul_nonneg (by positivity) cubicExponentialMoment_nonneg
    _ = weightedDifferenceConstant M K * epsilon ^ 5 * q xi := by
      unfold weightedDifferenceConstant
      ring

/-- Absolute bound for either sign of the shifted product integral. -/
theorem weightedProduct_doubleIntegral_abs_bound
    {q : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) {xi epsilon t : ℝ}
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M)
    (ht : |t| ≤ epsilon) :
    |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
        weightedProduct q xi s r t| ≤
      Real.exp (1 / 2) * q xi ^ 2 * exponentialMoment := by
  let D : ℝ := Real.exp (1 / 2) * q xi ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hdom : IntegrableOn
      (fun r : ℝ ↦ D * Real.exp (-r / 2)) (Ici 0) :=
    exponentialEnvelope_integrableOn.const_mul D
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hdom (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
    have hr0 : 0 ≤ r := hr
    have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s ↦ weightedProduct q xi s r t)
      (C := Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2)
      (fun s hs ↦ by
        rw [uIoc_of_le (h_nonneg r)] at hs
        rw [Real.norm_eq_abs, abs_of_pos]
        · exact weightedProduct_shift_bound hsmooth hpos hrelative
            hs.1.le (hs.2.trans (h_le_one hr0)) hr0 ht
        · unfold weightedProduct
          exact mul_pos (hpos _) (hpos _))
    have hbase :
        |∫ s in (0 : ℝ)..h r, weightedProduct q xi s r t| ≤
          (Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2) *
            h r := by
      simpa only [Real.norm_eq_abs, sub_zero,
        abs_of_nonneg (h_nonneg r)] using hinterval
    rw [Real.norm_eq_abs]
    calc
      |∫ s in (0 : ℝ)..h r, weightedProduct q xi s r t| ≤
          Real.exp (2 * M * epsilon * (1 + r)) * q xi ^ 2 *
            h r := hbase
      _ = q xi ^ 2 *
          (h r * Real.exp (2 * M * epsilon * (1 + r))) := by ring
      _ ≤ q xi ^ 2 *
          (Real.exp (1 / 2) * Real.exp (-r / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (small_exponential_kernel_bound hrelative.1 hepsilon
            hsmall hr0) (sq_nonneg (q xi))
      _ = D * Real.exp (-r / 2) := by
        dsimp only [D]
        ring)
  calc
    |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
        weightedProduct q xi s r t| ≤
        ∫ r in Ici (0 : ℝ), D * Real.exp (-r / 2) := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ = D * exponentialMoment := by
      rw [integral_const_mul]
      rfl
    _ = Real.exp (1 / 2) * q xi ^ 2 * exponentialMoment := by
      rfl

noncomputable def weightedSumConstant (K : ℝ) : ℝ :=
  2 * Real.exp (1 / 2) * K * exponentialMoment

/-- The integrated sum is of order `ε² q(ξ)`, uniformly in the centre. -/
theorem weightedIntegral_sum_bound
    {q : ℝ → ℝ} {M K : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hK : 0 ≤ K)
    {xi epsilon : ℝ} (hsq : q xi ^ 2 ≤ K * q xi)
    (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M) :
    weightedIplus q epsilon xi + weightedIminus q epsilon xi ≤
      weightedSumConstant K * epsilon ^ 2 * q xi := by
  have hp := weightedProduct_doubleIntegral_abs_bound
    hsmooth hpos hrelative hepsilon hsmall
      (t := epsilon) (by rw [abs_of_pos hepsilon]) (xi := xi)
  have hn := weightedProduct_doubleIntegral_abs_bound
    hsmooth hpos hrelative hepsilon hsmall
      (t := -epsilon) (by rw [abs_neg, abs_of_pos hepsilon])
      (xi := xi)
  unfold weightedIplus weightedIminus
  calc
    epsilon ^ 2 *
          (∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
            weightedProduct q xi s r epsilon) +
        epsilon ^ 2 *
          (∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
            weightedProduct q xi s r (-epsilon)) ≤
        epsilon ^ 2 *
          |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
            weightedProduct q xi s r epsilon| +
        epsilon ^ 2 *
          |∫ r in Ici (0 : ℝ), ∫ s in (0 : ℝ)..h r,
            weightedProduct q xi s r (-epsilon)| := by
      gcongr <;> exact le_abs_self _
    _ ≤ epsilon ^ 2 *
          (Real.exp (1 / 2) * q xi ^ 2 * exponentialMoment) +
        epsilon ^ 2 *
          (Real.exp (1 / 2) * q xi ^ 2 * exponentialMoment) := by
      gcongr
    _ = (2 * epsilon ^ 2 * Real.exp (1 / 2) *
        exponentialMoment) * q xi ^ 2 := by ring
    _ ≤ (2 * epsilon ^ 2 * Real.exp (1 / 2) *
        exponentialMoment) * (K * q xi) := by
      apply mul_le_mul_of_nonneg_left hsq
      exact mul_nonneg (by positivity) exponentialMoment_nonneg
    _ = weightedSumConstant K * epsilon ^ 2 * q xi := by
      unfold weightedSumConstant
      ring

/-! ## Exact bridge to the CDF crossing-integral notation -/

def scaledDensity (q : ℝ → ℝ) (epsilon z0 y : ℝ) : ℝ :=
  epsilon * q (z0 + epsilon * y)

theorem Iplus_scaledDensity_eq_weightedIplus
    (q : ℝ → ℝ) (epsilon z0 x : ℝ) :
    Iplus (scaledDensity q epsilon z0) x =
      weightedIplus q epsilon (z0 + epsilon * x) := by
  unfold Iplus weightedIplus scaledDensity
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro r _hr
  change (∫ s in (0 : ℝ)..h r,
      epsilon * q (z0 + epsilon * (x + s)) *
        (epsilon * q (z0 + epsilon * (x + s + r)))) =
    epsilon ^ 2 * ∫ s in (0 : ℝ)..h r,
      weightedProduct q (z0 + epsilon * x) s r epsilon
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  unfold weightedProduct
  ring_nf

theorem Iminus_scaledDensity_eq_weightedIminus
    (q : ℝ → ℝ) (epsilon z0 x : ℝ) :
    Iminus (scaledDensity q epsilon z0) x =
      weightedIminus q epsilon (z0 + epsilon * x) := by
  unfold Iminus weightedIminus scaledDensity
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro r _hr
  change (∫ s in (0 : ℝ)..h r,
      epsilon * q (z0 + epsilon * (x - s)) *
        (epsilon * q (z0 + epsilon * (x - s - r)))) =
    epsilon ^ 2 * ∫ s in (0 : ℝ)..h r,
      weightedProduct q (z0 + epsilon * x) s r (-epsilon)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  unfold weightedProduct
  ring_nf

/-! ## Uniform consistency packages -/

/-- The common quantified form used by both the full-line and hard-edge profiles. -/
theorem weightedIntegral_consistency
    {q : ℝ → ℝ} {M K : ℝ}
    (hsmooth : ContDiff ℝ 3 q) (hpos : ∀ z, 0 < q z)
    (hrelative : RelativeC3Bound q M) (hK : 0 ≤ K)
    (hsq : ∀ xi, q xi ^ 2 ≤ K * q xi) :
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ xi epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        |weightedIplus q epsilon xi - weightedIminus q epsilon xi -
            diffusionCoefficient * epsilon ^ 3 * q xi * deriv q xi| ≤
          C * epsilon ^ 5 * q xi ∧
        weightedIplus q epsilon xi + weightedIminus q epsilon xi ≤
          C * epsilon ^ 2 * q xi := by
  let C := weightedDifferenceConstant M K + weightedSumConstant K + 1
  let epsilon0 := relativeConsistencyEpsilon M
  have hdiff0 : 0 ≤ weightedDifferenceConstant M K := by
    unfold weightedDifferenceConstant
    exact mul_nonneg (by positivity) cubicExponentialMoment_nonneg
  have hsum0 : 0 ≤ weightedSumConstant K := by
    unfold weightedSumConstant
    exact mul_nonneg (by positivity) exponentialMoment_nonneg
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact relativeConsistencyEpsilon_pos hrelative.1
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro xi epsilon hepsilon hsmall
  have hdiff := weightedIntegral_difference_bound hsmooth hpos hrelative
    hK (hsq xi) hepsilon hsmall
  have hsum := weightedIntegral_sum_bound hsmooth hpos hrelative
    hK (hsq xi) hepsilon hsmall
  constructor
  · exact hdiff.trans (by
      apply mul_le_mul_of_nonneg_right _ (hpos xi).le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hepsilon.le 5)
      dsimp only [C]
      linarith)
  · exact hsum.trans (by
      apply mul_le_mul_of_nonneg_right _ (hpos xi).le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hepsilon.le 2)
      dsimp only [C]
      linarith)

/-- `lem:weighted-consistency`, with constants independent of `x,z₀`. -/
theorem full_line_weighted_consistency
    {lambda : ℝ} {W Phi : ℝ → ℝ}
    (hprofile : IsWaveProfileConclusion diffusionMainInput lambda W Phi) :
    let q := waveDensity diffusionMainInput W Phi
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧
      ∀ x z0 epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        let xi := z0 + epsilon * x
        |Iplus (scaledDensity q epsilon z0) x -
            Iminus (scaledDensity q epsilon z0) x -
            diffusionMainInput.a * epsilon ^ 3 * q xi * deriv q xi| ≤
          C * epsilon ^ 5 * q xi ∧
        Iplus (scaledDensity q epsilon z0) x +
            Iminus (scaledDensity q epsilon z0) x ≤
          C * epsilon ^ 2 * q xi := by
  let q := waveDensity diffusionMainInput W Phi
  have hqEq : q = deriv Phi := by
    funext z
    exact (hprofile.2.1 z).symm
  have hsmooth : ContDiff ℝ 3 q := by
    rw [hqEq]
    have hPhi4 : ContDiff ℝ 4 Phi :=
      hprofile.1.1.of_le ENat.LEInfty.out
    exact hPhi4.deriv'
  have hpos : ∀ z, 0 < q z := hprofile.2.2.1
  obtain ⟨M, hM, hrel⟩ := full_line_relative_bounds hprofile
  have hrelative : RelativeC3Bound q M := ⟨hM, hrel⟩
  have hprobability := full_line_density_probability hprofile
  have hintegrable : Integrable q := hprobability.2.1
  have hmass : (∫ z, q z) = 1 := hprobability.2.2.1
  have hsq : ∀ xi, q xi ^ 2 ≤ Real.exp M * q xi :=
    full_line_density_sq_le_exp hsmooth hpos hrelative
      hintegrable hmass
  obtain ⟨C, epsilon0, hC, hepsilon0, hconsistency⟩ :=
    weightedIntegral_consistency hsmooth hpos hrelative
      (Real.exp_pos M).le hsq
  refine ⟨C, epsilon0, hC, hepsilon0, ?_⟩
  intro x z0 epsilon hepsilon hsmall
  have hbounds := hconsistency (z0 + epsilon * x) epsilon
    hepsilon hsmall
  rw [← Iplus_scaledDensity_eq_weightedIplus,
    ← Iminus_scaledDensity_eq_weightedIminus] at hbounds
  simpa only [diffusionMainInput_a] using hbounds

/-! ## Physical zero extension versus the analytic hard-edge extension -/

noncomputable def positiveZeroExtension (q : ℝ → ℝ) (z : ℝ) : ℝ :=
  if 0 < z then q z else 0

theorem positiveZeroExtension_congr_of_eqOn
    {q qbar : ℝ → ℝ} (heq : EqOn qbar q (Ici 0)) :
    positiveZeroExtension q = positiveZeroExtension qbar := by
  funext z
  by_cases hz : 0 < z
  · simp only [positiveZeroExtension, if_pos hz]
    exact (heq hz.le).symm
  · simp only [positiveZeroExtension, if_neg hz]

theorem positiveZeroExtension_nonneg {q : ℝ → ℝ}
    (hpos : ∀ z, 0 < q z) (z : ℝ) :
    0 ≤ positiveZeroExtension q z := by
  unfold positiveZeroExtension
  split_ifs
  · exact (hpos z).le
  · rfl

theorem positiveZeroExtension_le {q : ℝ → ℝ}
    (hpos : ∀ z, 0 < q z) (z : ℝ) :
    positiveZeroExtension q z ≤ q z := by
  unfold positiveZeroExtension
  split_ifs
  · exact le_rfl
  · exact (hpos z).le

theorem measurable_positiveZeroExtension {q : ℝ → ℝ}
    (hq : Measurable q) : Measurable (positiveZeroExtension q) := by
  unfold positiveZeroExtension
  exact hq.piecewise measurableSet_Ioi measurable_const

/-- At a nonnegative observation point, the physical and analytic plus integrals agree. -/
theorem Iplus_zeroExtension_scaled_eq_weightedIplus
    {q qbar : ℝ → ℝ} (heq : EqOn qbar q (Ici 0))
    {epsilon x : ℝ} (hepsilon : 0 < epsilon) (hx : 0 ≤ x) :
    Iplus (scaledDensity (positiveZeroExtension q) epsilon 0) x =
      weightedIplus qbar epsilon (epsilon * x) := by
  rw [positiveZeroExtension_congr_of_eqOn heq]
  rw [Iplus_scaledDensity_eq_weightedIplus]
  unfold weightedIplus
  congr 1
  apply setIntegral_congr_fun measurableSet_Ici
  intro r hr
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (h_nonneg r)
  intro s hs
  unfold weightedProduct positiveZeroExtension
  have harg1 : 0 < epsilon * x + epsilon * s := by
    nlinarith [mul_pos hepsilon hs.1]
  have harg2 : 0 < epsilon * x + epsilon * (s + r) := by
    have hr0 : 0 ≤ r := hr
    nlinarith [mul_pos hepsilon hs.1]
  simp only [zero_add]
  rw [if_pos harg1, if_pos harg2]

/-- The physical minus integral is bounded by the one formed with `qbar`. -/
theorem Iminus_zeroExtension_scaled_le_weightedIminus
    {q qbar : ℝ → ℝ} {M : ℝ}
    (heq : EqOn qbar q (Ici 0))
    (hsmooth : ContDiff ℝ 3 qbar) (hpos : ∀ z, 0 < qbar z)
    (hrelative : RelativeC3Bound qbar M)
    {epsilon x : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon < relativeConsistencyEpsilon M) :
    Iminus (scaledDensity (positiveZeroExtension q) epsilon 0) x ≤
      weightedIminus qbar epsilon (epsilon * x) := by
  rw [positiveZeroExtension_congr_of_eqOn heq]
  rw [Iminus_scaledDensity_eq_weightedIminus]
  simp only [zero_add]
  unfold weightedIminus
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg epsilon)
  let q0 := positiveZeroExtension qbar
  let xi := epsilon * x
  let P0 : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..h r,
    weightedProduct q0 xi s r (-epsilon)
  let Pbar : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..h r,
    weightedProduct qbar xi s r (-epsilon)
  have hq0Meas : Measurable q0 :=
    measurable_positiveZeroExtension hsmooth.continuous.measurable
  have hpairMeas : StronglyMeasurable
      (fun p : ℝ × ℝ ↦ weightedProduct q0 xi p.2 p.1 (-epsilon)) := by
    apply Measurable.stronglyMeasurable
    unfold weightedProduct
    apply Measurable.mul
    · apply hq0Meas.comp
      fun_prop
    · apply hq0Meas.comp
      fun_prop
  have hP0Meas : AEStronglyMeasurable P0 := by
    dsimp only [P0]
    exact aestronglyMeasurable_kernelInterval_of_stronglyMeasurable
      hpairMeas
  have hPbar : IntegrableOn Pbar (Ici 0) := by
    dsimp only [Pbar]
    exact weightedProduct_kernel_integrableOn hsmooth hpos hrelative
      hepsilon hsmall (by rw [abs_neg, abs_of_pos hepsilon])
  let D : ℝ := Real.exp (1 / 2) * qbar xi ^ 2
  have hdom : IntegrableOn
      (fun r : ℝ ↦ D * Real.exp (-r / 2)) (Ici 0) :=
    exponentialEnvelope_integrableOn.const_mul D
  have hP0 : IntegrableOn P0 (Ici 0) := by
    apply Integrable.mono' hdom
    · exact hP0Meas.mono_measure Measure.restrict_le_self
    · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
      have hr0 : 0 ≤ r := hr
      have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s ↦ weightedProduct q0 xi s r (-epsilon))
        (C := Real.exp (2 * M * epsilon * (1 + r)) * qbar xi ^ 2)
        (fun s hs ↦ by
          rw [uIoc_of_le (h_nonneg r)] at hs
          have hproduct0 : 0 ≤ weightedProduct q0 xi s r (-epsilon) := by
            unfold weightedProduct q0
            exact mul_nonneg
              (positiveZeroExtension_nonneg hpos _)
              (positiveZeroExtension_nonneg hpos _)
          rw [Real.norm_eq_abs, abs_of_nonneg hproduct0]
          calc
            weightedProduct q0 xi s r (-epsilon) ≤
                weightedProduct qbar xi s r (-epsilon) := by
              unfold weightedProduct q0
              exact mul_le_mul
                (positiveZeroExtension_le hpos _)
                (positiveZeroExtension_le hpos _)
                (positiveZeroExtension_nonneg hpos _)
                (hpos _).le
            _ ≤ Real.exp (2 * M * epsilon * (1 + r)) *
                qbar xi ^ 2 :=
              weightedProduct_shift_bound hsmooth hpos hrelative
                hs.1.le (hs.2.trans (h_le_one hr0)) hr0
                (by rw [abs_neg, abs_of_pos hepsilon]))
      have hbase : |P0 r| ≤
          (Real.exp (2 * M * epsilon * (1 + r)) * qbar xi ^ 2) *
            h r := by
        dsimp only [P0]
        simpa only [Real.norm_eq_abs, sub_zero,
          abs_of_nonneg (h_nonneg r)] using hinterval
      rw [Real.norm_eq_abs]
      calc
        |P0 r| ≤ Real.exp (2 * M * epsilon * (1 + r)) *
            qbar xi ^ 2 * h r := hbase
        _ = qbar xi ^ 2 *
            (h r * Real.exp (2 * M * epsilon * (1 + r))) := by ring
        _ ≤ qbar xi ^ 2 *
            (Real.exp (1 / 2) * Real.exp (-r / 2)) := by
          exact mul_le_mul_of_nonneg_left
            (small_exponential_kernel_bound hrelative.1 hepsilon
              hsmall hr0) (sq_nonneg (qbar xi))
        _ = D * Real.exp (-r / 2) := by
          dsimp only [D]
          ring
  apply setIntegral_mono_on hP0 hPbar measurableSet_Ici
  intro r hr
  have hr0 : 0 ≤ r := hr
  have hbarContinuous : Continuous
      (fun s ↦ weightedProduct qbar xi s r (-epsilon)) := by
    unfold weightedProduct
    fun_prop
  have hbarInt : IntervalIntegrable
      (fun s ↦ weightedProduct qbar xi s r (-epsilon)) volume 0 (h r) :=
    hbarContinuous.intervalIntegrable 0 (h r)
  have hzeroStrong : StronglyMeasurable
      (fun s ↦ weightedProduct q0 xi s r (-epsilon)) := by
    apply Measurable.stronglyMeasurable
    unfold weightedProduct
    apply Measurable.mul <;> apply hq0Meas.comp <;> fun_prop
  have hzeroInt : IntervalIntegrable
      (fun s ↦ weightedProduct q0 xi s r (-epsilon)) volume 0 (h r) := by
    apply hbarInt.mono_fun
    · exact hzeroStrong.aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
    · filter_upwards with s
      have hzero0 : 0 ≤ weightedProduct q0 xi s r (-epsilon) := by
        unfold weightedProduct q0
        exact mul_nonneg
          (positiveZeroExtension_nonneg hpos _)
          (positiveZeroExtension_nonneg hpos _)
      have hbar0 : 0 ≤ weightedProduct qbar xi s r (-epsilon) := by
        unfold weightedProduct
        exact mul_nonneg (hpos _).le (hpos _).le
      have hle : weightedProduct q0 xi s r (-epsilon) ≤
          weightedProduct qbar xi s r (-epsilon) := by
        unfold weightedProduct q0
        exact mul_le_mul
          (positiveZeroExtension_le hpos _)
          (positiveZeroExtension_le hpos _)
          (positiveZeroExtension_nonneg hpos _)
          (hpos _).le
      simpa only [Real.norm_eq_abs, abs_of_nonneg hzero0,
        abs_of_nonneg hbar0] using hle
  apply intervalIntegral.integral_mono_on (h_nonneg r)
    hzeroInt hbarInt
  intro s _hs
  unfold weightedProduct q0
  exact mul_le_mul
    (positiveZeroExtension_le hpos _)
    (positiveZeroExtension_le hpos _)
    (positiveZeroExtension_nonneg hpos _)
    (hpos _).le

end SeriesParallel.MainText
