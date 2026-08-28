import SeriesParallel.Appendix.FiniteAsymptoticODE
import SeriesParallel.Appendix.SubcriticalW
import SeriesParallel.Appendix.EndpointAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Regularity of the linear endpoint branches

This file formalizes the source material surrounding `lem:linear-branch-regularity`.
The endpoint expansions retain the two distinct quadratic coefficients, and the
reciprocal change of variables is recorded by explicit derivative identities through
order four.
-/

open Asymptotics Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

open SeriesParallel.ManualInterfaces

/-- The hypotheses of `lem:linear-branch-regularity` that are independent of
endpoint values.  In particular, this package also applies to the subcritical
shooting solution, whose left endpoint is strictly positive. -/
structure IsPositiveWSolution (lambda : ℝ) (W : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn W unitInterval
  contDiffOn_one : ContDiffOn ℝ 1 W openUnitInterval
  satisfiesWODEAt : ∀ u ∈ openUnitInterval, SatisfiesWODEAt lambda W u
  positive : ∀ u ∈ openUnitInterval, 0 < W u

/-- A two-point boundary solution supplies the endpoint-independent positive
solution package. -/
theorem IsWBoundarySolution.isPositiveWSolution {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsWBoundarySolution lambda W) : IsPositiveWSolution lambda W :=
  ⟨hsolution.2.1, hsolution.2.2.1, hsolution.2.2.2.1,
    hsolution.2.2.2.2.2.2⟩

/-! ## Rescaled equations -/

/-- The left-endpoint rescaling `Y(t) = t W(t⁻¹)`. -/
noncomputable def leftRescaling (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * W t⁻¹

/-- The right-endpoint rescaling `Ŷ(t) = t W(1 - t⁻¹)`. -/
noncomputable def rightRescaling (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * W (1 - t⁻¹)

/-- The autonomous term `F₀(y)=(1-λy)/y²` in `eq:Y-zero-equation`. -/
noncomputable def leftRescaledAutonomous (lambda y : ℝ) : ℝ :=
  (1 - lambda * y) / y ^ 2

/-- The order-`t⁻¹` term `G₀(y)=y-y⁻²` in `eq:Y-zero-equation`. -/
noncomputable def leftRescaledPerturbation (y : ℝ) : ℝ :=
  y - y⁻¹ ^ 2

/-- The autonomous term `F₁(y)=(λy-1)/y²` in `eq:Y-one-equation`. -/
noncomputable def rightRescaledAutonomous (lambda y : ℝ) : ℝ :=
  (lambda * y - 1) / y ^ 2

/-- The order-`t⁻¹` term `G₁(y)=y+y⁻²` in `eq:Y-one-equation`. -/
noncomputable def rightRescaledPerturbation (y : ℝ) : ℝ :=
  y + y⁻¹ ^ 2

private theorem leftRescaledAlgebra {lambda t w dw : ℝ} (ht : t ≠ 0) (hw : w ≠ 0)
    (hode : w ^ 2 * dw - lambda * w + t⁻¹ * (1 - t⁻¹) = 0) :
    w + t * (dw * -(t⁻¹ ^ 2)) =
      leftRescaledAutonomous lambda (t * w) +
        t⁻¹ * leftRescaledPerturbation (t * w) := by
  rw [leftRescaledAutonomous, leftRescaledPerturbation]
  field_simp [ht, hw] at hode ⊢
  nlinarith [hode]

private theorem rightRescaledAlgebra {lambda t w dw : ℝ} (ht : t ≠ 0) (hw : w ≠ 0)
    (hode : w ^ 2 * dw - lambda * w + (1 - t⁻¹) * (1 - (1 - t⁻¹)) = 0) :
    w + t * (dw * t⁻¹ ^ 2) =
      rightRescaledAutonomous lambda (t * w) +
        t⁻¹ * rightRescaledPerturbation (t * w) := by
  rw [rightRescaledAutonomous, rightRescaledPerturbation]
  field_simp [ht, hw] at hode ⊢
  nlinarith [hode]

/-- `eq:Y-zero-equation`, obtained directly from the W--ODE. -/
theorem rescaledLeftEquation {lambda : ℝ} {W : ℝ → ℝ} {t : ℝ} (ht : 1 < t)
    (hsolution : IsPositiveWSolution lambda W) :
    HasDerivAt (leftRescaling W)
      (leftRescaledAutonomous lambda (leftRescaling W t) +
        t⁻¹ * leftRescaledPerturbation (leftRescaling W t)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hu0 : 0 < t⁻¹ := inv_pos.mpr (lt_trans zero_lt_one ht)
  have hu1 : t⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one ht)).2 ht
  have hu : t⁻¹ ∈ openUnitInterval := ⟨hu0, hu1⟩
  have hode := hsolution.satisfiesWODEAt t⁻¹ hu
  have hW : HasDerivAt W (deriv W t⁻¹) t⁻¹ := hode.1.hasDerivAt
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(t⁻¹ ^ 2)) t := by
    exact (hasDerivAt_inv ht0).congr_deriv (by rw [inv_pow])
  have hscaled : HasDerivAt (leftRescaling W)
      (W t⁻¹ + t * (deriv W t⁻¹ * -(t⁻¹ ^ 2))) t := by
    change HasDerivAt (fun s : ℝ ↦ s * W s⁻¹)
      (W t⁻¹ + t * (deriv W t⁻¹ * -(t⁻¹ ^ 2))) t
    have h := (hasDerivAt_id t).mul (hW.comp t hinv)
    have h' : HasDerivAt (id * W ∘ Inv.inv)
        (W t⁻¹ + t * (deriv W t⁻¹ * -(t⁻¹ ^ 2))) t :=
      h.congr_deriv (by simp only [id_eq, Function.comp_apply, one_mul])
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  apply hscaled.congr_deriv
  have hWpos : 0 < W t⁻¹ := hsolution.positive t⁻¹ hu
  have hodeEq := hode.2
  dsimp only [wODEValue] at hodeEq
  exact leftRescaledAlgebra ht0 (ne_of_gt hWpos) hodeEq

/-- `eq:Y-one-equation`, obtained directly from the W--ODE. -/
theorem rescaledRightEquation {lambda : ℝ} {W : ℝ → ℝ} {t : ℝ} (ht : 1 < t)
    (hsolution : IsPositiveWSolution lambda W) :
    HasDerivAt (rightRescaling W)
      (rightRescaledAutonomous lambda (rightRescaling W t) +
        t⁻¹ * rightRescaledPerturbation (rightRescaling W t)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hinvpos : 0 < t⁻¹ := inv_pos.mpr (lt_trans zero_lt_one ht)
  have hinvlt : t⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one ht)).2 ht
  have hu : 1 - t⁻¹ ∈ openUnitInterval := by
    constructor <;> linarith
  have hode := hsolution.satisfiesWODEAt (1 - t⁻¹) hu
  have hW : HasDerivAt W (deriv W (1 - t⁻¹)) (1 - t⁻¹) := hode.1.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ ↦ 1 - s⁻¹) (t⁻¹ ^ 2) t := by
    exact ((hasDerivAt_const t 1).sub (hasDerivAt_inv ht0)).congr_deriv (by
      rw [zero_sub, neg_neg, inv_pow])
  have hscaled : HasDerivAt (rightRescaling W)
      (W (1 - t⁻¹) + t * (deriv W (1 - t⁻¹) * t⁻¹ ^ 2)) t := by
    change HasDerivAt (fun s : ℝ ↦ s * W (1 - s⁻¹))
      (W (1 - t⁻¹) + t * (deriv W (1 - t⁻¹) * t⁻¹ ^ 2)) t
    have h := (hasDerivAt_id t).mul (hW.comp t hinner)
    have h' : HasDerivAt (id * W ∘ fun s : ℝ ↦ 1 - s⁻¹)
        (W (1 - t⁻¹) + t * (deriv W (1 - t⁻¹) * t⁻¹ ^ 2)) t :=
      h.congr_deriv (by simp only [id_eq, Function.comp_apply, one_mul])
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  apply hscaled.congr_deriv
  have hWpos : 0 < W (1 - t⁻¹) := hsolution.positive (1 - t⁻¹) hu
  have hodeEq := hode.2
  dsimp only [wODEValue] at hodeEq
  exact rightRescaledAlgebra ht0 (ne_of_gt hWpos) hodeEq

/-- The limit accompanying `eq:Y-zero-equation`. -/
theorem leftRescaling_tendsto {lambda : ℝ} {W : ℝ → ℝ} (hlambda : lambda ≠ 0)
    (hlinear : HasLinearBranchAtZero lambda W) :
    Tendsto (leftRescaling W) atTop (𝓝 lambda⁻¹) := by
  have hcomp := hlinear.comp_tendsto tendsto_inv_atTop_nhdsGT_zero
  have hid : (fun t : ℝ ↦ t) ~[atTop] (fun t : ℝ ↦ t) := IsEquivalent.refl
  have hmul := hid.mul hcomp
  have hleft :
      (fun t : ℝ ↦ t * (W ∘ fun s : ℝ ↦ s⁻¹) t) =ᶠ[atTop] leftRescaling W :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  have hright :
      (fun t : ℝ ↦ t * ((fun u : ℝ ↦ u / lambda) ∘ fun s : ℝ ↦ s⁻¹) t) =ᶠ[atTop]
        (fun _ : ℝ ↦ lambda⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [Function.comp_apply]
    field_simp [ne_of_gt ht, hlambda]
  exact ((hmul.congr_left hleft).congr_right hright).tendsto_const

/-- The reciprocal approach to the right endpoint used in the right scaling limit. -/
theorem tendsto_one_sub_inv_atTop_nhdsLT_one :
    Tendsto (fun t : ℝ ↦ 1 - t⁻¹) atTop (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa only [mem_Iio] using sub_lt_self (1 : ℝ) (inv_pos.mpr ht)

/-- The limit accompanying `eq:Y-one-equation`. -/
theorem rightRescaling_tendsto {lambda : ℝ} {W : ℝ → ℝ} (hlambda : lambda ≠ 0)
    (hlinear : HasLinearBranchAtOne lambda W) :
    Tendsto (rightRescaling W) atTop (𝓝 lambda⁻¹) := by
  have hcomp := hlinear.comp_tendsto tendsto_one_sub_inv_atTop_nhdsLT_one
  have hid : (fun t : ℝ ↦ t) ~[atTop] (fun t : ℝ ↦ t) := IsEquivalent.refl
  have hmul := hid.mul hcomp
  have hleft :
      (fun t : ℝ ↦ t * (W ∘ fun s : ℝ ↦ 1 - s⁻¹) t) =ᶠ[atTop] rightRescaling W :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  have hright :
      (fun t : ℝ ↦ t * ((fun u : ℝ ↦ (1 - u) / lambda) ∘
        fun s : ℝ ↦ 1 - s⁻¹) t) =ᶠ[atTop] (fun _ : ℝ ↦ lambda⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [Function.comp_apply]
    field_simp [ne_of_gt ht, hlambda]
    ring
  exact ((hmul.congr_left hleft).congr_right hright).tendsto_const

/-! ## Instantiation data for the finite asymptotic ODE theorem -/

theorem leftRescaledAutonomous_contDiffOn (lambda : ℝ) :
    ContDiffOn ℝ 9 (leftRescaledAutonomous lambda) (Ioi (0 : ℝ)) := by
  intro y hy
  have hy0 : y ≠ 0 := hy.ne'
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
  unfold leftRescaledAutonomous
  fun_prop (disch := aesop)

theorem leftRescaledPerturbation_contDiffOn :
    ContDiffOn ℝ 9 leftRescaledPerturbation (Ioi (0 : ℝ)) := by
  intro y hy
  have hy0 : y ≠ 0 := hy.ne'
  unfold leftRescaledPerturbation
  fun_prop (disch := aesop)

theorem rightRescaledAutonomous_contDiffOn (lambda : ℝ) :
    ContDiffOn ℝ 9 (rightRescaledAutonomous lambda) (Ioi (0 : ℝ)) := by
  intro y hy
  have hy0 : y ≠ 0 := hy.ne'
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
  unfold rightRescaledAutonomous
  fun_prop (disch := aesop)

theorem rightRescaledPerturbation_contDiffOn :
    ContDiffOn ℝ 9 rightRescaledPerturbation (Ioi (0 : ℝ)) := by
  intro y hy
  have hy0 : y ≠ 0 := hy.ne'
  unfold rightRescaledPerturbation
  fun_prop (disch := aesop)

theorem leftRescaledAutonomous_at_fixedPoint {lambda : ℝ} (hlambda : 0 < lambda) :
    leftRescaledAutonomous lambda lambda⁻¹ = 0 := by
  unfold leftRescaledAutonomous
  field_simp [hlambda.ne']
  ring

theorem rightRescaledAutonomous_at_fixedPoint {lambda : ℝ} (hlambda : 0 < lambda) :
    rightRescaledAutonomous lambda lambda⁻¹ = 0 := by
  unfold rightRescaledAutonomous
  field_simp [hlambda.ne']
  ring

theorem leftRescaledAutonomous_deriv_fixedPoint {lambda : ℝ} (hlambda : 0 < lambda) :
    deriv (leftRescaledAutonomous lambda) lambda⁻¹ = -lambda ^ 3 := by
  let y : ℝ := lambda⁻¹
  have hy : y ≠ 0 := inv_ne_zero hlambda.ne'
  have hn : HasDerivAt (fun z : ℝ ↦ 1 - lambda * z) (-lambda) y := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id y).const_mul lambda).const_sub 1
  have hd : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hquot := hn.div hd (pow_ne_zero 2 hy)
  change deriv (fun z : ℝ ↦ (1 - lambda * z) / z ^ 2) y = -lambda ^ 3
  have hquot' := hquot.deriv
  change deriv (fun z : ℝ ↦ (1 - lambda * z) / z ^ 2) y = _ at hquot'
  rw [hquot']
  dsimp [y]
  field_simp [hlambda.ne']
  ring

theorem rightRescaledAutonomous_deriv_fixedPoint {lambda : ℝ} (hlambda : 0 < lambda) :
    deriv (rightRescaledAutonomous lambda) lambda⁻¹ = lambda ^ 3 := by
  let y : ℝ := lambda⁻¹
  have hy : y ≠ 0 := inv_ne_zero hlambda.ne'
  have hn : HasDerivAt (fun z : ℝ ↦ lambda * z - 1) lambda y := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id y).const_mul lambda).sub_const 1
  have hd : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hquot := hn.div hd (pow_ne_zero 2 hy)
  change deriv (fun z : ℝ ↦ (lambda * z - 1) / z ^ 2) y = lambda ^ 3
  have hquot' := hquot.deriv
  change deriv (fun z : ℝ ↦ (lambda * z - 1) / z ^ 2) y = _ at hquot'
  rw [hquot']
  dsimp [y]
  field_simp [hlambda.ne']
  ring

/-- The explicit left quadratic coefficient from B2.2. -/
theorem leftRescaled_firstCoefficient {lambda : ℝ} (hlambda : 0 < lambda) :
    -leftRescaledPerturbation lambda⁻¹ /
        deriv (leftRescaledAutonomous lambda) lambda⁻¹ =
      lambda⁻¹ ^ 4 - lambda⁻¹ := by
  rw [leftRescaledAutonomous_deriv_fixedPoint hlambda]
  unfold leftRescaledPerturbation
  field_simp [hlambda.ne']

/-- The explicit right quadratic coefficient from B2.5. -/
theorem rightRescaled_firstCoefficient {lambda : ℝ} (hlambda : 0 < lambda) :
    -rightRescaledPerturbation lambda⁻¹ /
        deriv (rightRescaledAutonomous lambda) lambda⁻¹ =
      -(lambda⁻¹ ^ 4 + lambda⁻¹) := by
  rw [rightRescaledAutonomous_deriv_fixedPoint hlambda]
  unfold rightRescaledPerturbation
  field_simp [hlambda.ne']

/-- A positive W-boundary solution is smooth on the open interval by the regular
positive divided vector field. -/
theorem IsPositiveWSolution.contDiffOn_infty_interior {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) :
    ContDiffOn ℝ ∞ W openUnitInterval := by
  apply MI09_ode_regularity_bootstrap_infty
    (positiveWField lambda) positiveWFieldDomain openUnitInterval W
  · exact isOpen_positiveWFieldDomain
  · exact positiveWField_contDiffOn lambda
  · exact isOpen_Ioo
  · intro u hu
    exact hsolution.positive u hu
  · intro u hu
    have hode := hsolution.satisfiesWODEAt u hu
    have hraw := hode.1.hasDerivAt
    apply hraw.congr_deriv
    unfold positiveWField
    have hWne := (hsolution.positive u hu).ne'
    have hodeEq := hode.2
    change W u ^ 2 * deriv W u - lambda * W u + u * (1 - u) = 0 at hodeEq
    field_simp [hWne]
    nlinarith [hodeEq]

theorem leftRescaling_isAsymptoticallyAutonomousSolution {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtZero lambda W) :
    IsAsymptoticallyAutonomousSolution (Ioi (0 : ℝ))
      (leftRescaledAutonomous lambda) leftRescaledPerturbation lambda⁻¹ 2
      (leftRescaling W) := by
  have hmap : MapsTo (leftRescaling W) (Ici (2 : ℝ)) (Ioi (0 : ℝ)) := by
    intro t ht
    change (2 : ℝ) ≤ t at ht
    have htpos : 0 < t := by linarith
    have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
    have hinvlt : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 (by linarith)
    exact mul_pos htpos (hsolution.positive t⁻¹ ⟨hinvpos, hinvlt⟩)
  have hinvSmooth : ContDiffOn ℝ 1 (fun t : ℝ ↦ t⁻¹) (Ici (2 : ℝ)) := by
    intro t ht
    apply (contDiffAt_inv ℝ ?_).contDiffWithinAt
    change (2 : ℝ) ≤ t at ht
    linarith
  have hinvMaps : MapsTo (fun t : ℝ ↦ t⁻¹) (Ici (2 : ℝ)) openUnitInterval := by
    intro t ht
    change (2 : ℝ) ≤ t at ht
    have htpos : 0 < t := by linarith
    exact ⟨inv_pos.mpr htpos, (inv_lt_one₀ htpos).2 (by linarith)⟩
  have hscaledSmooth : ContDiffOn ℝ 1 (leftRescaling W) (Ici (2 : ℝ)) := by
    unfold leftRescaling
    exact contDiffOn_id.mul (hsolution.contDiffOn_one.comp hinvSmooth hinvMaps)
  refine ⟨isOpen_Ioi, inv_pos.mpr hlambda, by norm_num, hmap, hscaledSmooth, ?_,
    leftRescaling_tendsto hlambda.ne' hlinear⟩
  intro t ht
  change (2 : ℝ) < t at ht
  have hrescaled := rescaledLeftEquation (hsolution := hsolution) (by linarith [ht])
  simpa only [asymptoticallyAutonomousRhs] using hrescaled

theorem rightRescaling_isAsymptoticallyAutonomousSolution {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtOne lambda W) :
    IsAsymptoticallyAutonomousSolution (Ioi (0 : ℝ))
      (rightRescaledAutonomous lambda) rightRescaledPerturbation lambda⁻¹ 2
      (rightRescaling W) := by
  have hmap : MapsTo (rightRescaling W) (Ici (2 : ℝ)) (Ioi (0 : ℝ)) := by
    intro t ht
    change (2 : ℝ) ≤ t at ht
    have htpos : 0 < t := by linarith
    have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
    have hinvlt : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 (by linarith)
    have hu : 1 - t⁻¹ ∈ openUnitInterval := by constructor <;> linarith
    exact mul_pos htpos (hsolution.positive (1 - t⁻¹) hu)
  have hinnerSmooth : ContDiffOn ℝ 1 (fun t : ℝ ↦ 1 - t⁻¹) (Ici (2 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      change (2 : ℝ) ≤ t at ht
      linarith
    exact ((contDiffAt_const (x := t) (c := (1 : ℝ))).sub
      (contDiffAt_inv ℝ ht0)).contDiffWithinAt
  have hinnerMaps : MapsTo (fun t : ℝ ↦ 1 - t⁻¹) (Ici (2 : ℝ))
      openUnitInterval := by
    intro t ht
    change (2 : ℝ) ≤ t at ht
    have htpos : 0 < t := by linarith
    have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
    have hinvlt : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 (by linarith)
    exact ⟨by linarith, by linarith⟩
  have hscaledSmooth : ContDiffOn ℝ 1 (rightRescaling W) (Ici (2 : ℝ)) := by
    unfold rightRescaling
    exact contDiffOn_id.mul (hsolution.contDiffOn_one.comp hinnerSmooth hinnerMaps)
  refine ⟨isOpen_Ioi, inv_pos.mpr hlambda, by norm_num, hmap, hscaledSmooth, ?_,
    rightRescaling_tendsto hlambda.ne' hlinear⟩
  intro t ht
  change (2 : ℝ) < t at ht
  have hrescaled := rescaledRightEquation (hsolution := hsolution) (by linarith [ht])
  simpa only [asymptoticallyAutonomousRhs] using hrescaled

/-- The left rescaling is smooth on every terminal region lying past `1`. -/
theorem leftRescaling_contDiffOn_infty {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) :
    ContDiffOn ℝ ∞ (leftRescaling W) (Ioi (1 : ℝ)) := by
  have hinv : ContDiffOn ℝ ∞ (fun t : ℝ ↦ t⁻¹) (Ioi (1 : ℝ)) := by
    intro t ht
    exact (contDiffAt_inv ℝ (by exact ne_of_gt (lt_trans zero_lt_one ht))).contDiffWithinAt
  have hmap : MapsTo (fun t : ℝ ↦ t⁻¹) (Ioi (1 : ℝ)) openUnitInterval := by
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    exact ⟨inv_pos.mpr ht0, (inv_lt_one₀ ht0).2 ht⟩
  unfold leftRescaling
  exact contDiffOn_id.mul
    (hsolution.contDiffOn_infty_interior.comp hinv hmap)

/-- The reflected right rescaling is smooth on every terminal region lying past `1`. -/
theorem rightRescaling_contDiffOn_infty {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) :
    ContDiffOn ℝ ∞ (rightRescaling W) (Ioi (1 : ℝ)) := by
  have hinner : ContDiffOn ℝ ∞ (fun t : ℝ ↦ 1 - t⁻¹) (Ioi (1 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    exact ((contDiffAt_const (x := t) (c := (1 : ℝ))).sub
      (contDiffAt_inv ℝ ht0)).contDiffWithinAt
  have hmap : MapsTo (fun t : ℝ ↦ 1 - t⁻¹) (Ioi (1 : ℝ))
      openUnitInterval := by
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hinvpos : 0 < t⁻¹ := inv_pos.mpr ht0
    have hinvlt : t⁻¹ < 1 := (inv_lt_one₀ ht0).2 ht
    exact ⟨by linarith, by linarith⟩
  unfold rightRescaling
  exact contDiffOn_id.mul
    (hsolution.contDiffOn_infty_interior.comp hinner hmap)

theorem approximation4_contDiffOn_infty (yStar : ℝ) (b : Fin 4 → ℝ) :
    ContDiffOn ℝ ∞ (approximation4 yStar b) (Ioi (1 : ℝ)) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  unfold approximation4
  fun_prop (disch := aesop)

/-- Smoothness of the finite-asymptotic remainder in the two rescalings. -/
theorem left_finiteAsymptoticRemainder_contDiffOn {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (b : Fin 4 → ℝ) :
    ContDiffOn ℝ 4
      (finiteAsymptoticRemainder (leftRescaling W) lambda⁻¹ b) (Ioi (1 : ℝ)) := by
  unfold finiteAsymptoticRemainder
  exact ((leftRescaling_contDiffOn_infty hsolution).of_le
    (WithTop.coe_le_coe.mpr (OrderTop.le_top _))).sub
    ((approximation4_contDiffOn_infty lambda⁻¹ b).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top _)))

theorem right_finiteAsymptoticRemainder_contDiffOn {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (b : Fin 4 → ℝ) :
    ContDiffOn ℝ 4
      (finiteAsymptoticRemainder (rightRescaling W) lambda⁻¹ b) (Ioi (1 : ℝ)) := by
  unfold finiteAsymptoticRemainder
  exact ((rightRescaling_contDiffOn_infty hsolution).of_le
    (WithTop.coe_le_coe.mpr (OrderTop.le_top _))).sub
    ((approximation4_contDiffOn_infty lambda⁻¹ b).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top _)))

/-! ## The transformed remainder and its four derivatives -/

/-- The reciprocal-coordinate remainder `E(r)=rR(r⁻¹)`. -/
noncomputable def transformedRemainder (R : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * R r⁻¹

/-- The displayed formula `E'=R(t)-tR'(t)`, with `t=r⁻¹`. -/
noncomputable def transformedRemainderD1 (R R1 : ℝ → ℝ) (r : ℝ) : ℝ :=
  R r⁻¹ - r⁻¹ * R1 r⁻¹

/-- The displayed formula `E''=t³R''(t)`. -/
noncomputable def transformedRemainderD2 (R2 : ℝ → ℝ) (r : ℝ) : ℝ :=
  r⁻¹ ^ 3 * R2 r⁻¹

/-- The displayed formula `E'''=-3t⁴R''(t)-t⁵R'''(t)`. -/
noncomputable def transformedRemainderD3 (R2 R3 : ℝ → ℝ) (r : ℝ) : ℝ :=
  -3 * r⁻¹ ^ 4 * R2 r⁻¹ - r⁻¹ ^ 5 * R3 r⁻¹

/-- The displayed formula `E⁽⁴⁾=12t⁵R''+8t⁶R'''+t⁷R⁽⁴⁾`. -/
noncomputable def transformedRemainderD4 (R2 R3 R4 : ℝ → ℝ) (r : ℝ) : ℝ :=
  12 * r⁻¹ ^ 5 * R2 r⁻¹ + 8 * r⁻¹ ^ 6 * R3 r⁻¹ +
    r⁻¹ ^ 7 * R4 r⁻¹

/-- The five-term polynomial used at either endpoint. -/
def endpointPolynomial (linear quadratic : ℝ) (higher : Fin 3 → ℝ) (r : ℝ) : ℝ :=
  linear * r + quadratic * r ^ 2 + ∑ j : Fin 3, higher j * r ^ (j.1 + 3)

/-- The three coefficients which become the cubic, quartic, and quintic endpoint
terms after multiplication by the reciprocal coordinate. -/
def endpointHigherCoefficients (b : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun j ↦ b ⟨j.1 + 1, by omega⟩

theorem leftRescaling_reconstruction {W : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0) :
    W r = r * leftRescaling W r⁻¹ := by
  unfold leftRescaling
  rw [inv_inv]
  field_simp [hr]

theorem rightRescaling_reconstruction {W : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0) :
    W (1 - r) = r * rightRescaling W r⁻¹ := by
  unfold rightRescaling
  rw [inv_inv]
  field_simp [hr]

theorem approximation4_reciprocal_identity (yStar : ℝ) (b : Fin 4 → ℝ)
    {r : ℝ} (_hr : r ≠ 0) :
    r * approximation4 yStar b r⁻¹ =
      endpointPolynomial yStar (b 0) (endpointHigherCoefficients b) r := by
  unfold approximation4 endpointPolynomial endpointHigherCoefficients
  simp only [Fin.sum_univ_succ, Fin.val_zero, zero_add, pow_one, Fin.val_succ,
    inv_inv, inv_pow]
  field_simp [_hr]
  ring
  congr 1

/-- Exact reconstruction of the left endpoint from a four-term rescaled expansion. -/
theorem leftEndpoint_reconstruction_from_finiteExpansion {lambda : ℝ} {W : ℝ → ℝ}
    (b : Fin 4 → ℝ) {r : ℝ} (hr : r ≠ 0) :
    W r = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
      transformedRemainder
        (finiteAsymptoticRemainder (leftRescaling W) lambda⁻¹ b) r := by
  rw [leftRescaling_reconstruction (W := W) hr]
  unfold transformedRemainder finiteAsymptoticRemainder
  calc
    r * leftRescaling W r⁻¹ =
        r * approximation4 lambda⁻¹ b r⁻¹ +
          r * (leftRescaling W r⁻¹ - approximation4 lambda⁻¹ b r⁻¹) := by ring
    _ = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
        r * (leftRescaling W r⁻¹ - approximation4 lambda⁻¹ b r⁻¹) := by
      rw [approximation4_reciprocal_identity lambda⁻¹ b hr]

/-- Exact reconstruction of the reflected right endpoint from its rescaled expansion. -/
theorem rightEndpoint_reconstruction_from_finiteExpansion {lambda : ℝ} {W : ℝ → ℝ}
    (b : Fin 4 → ℝ) {r : ℝ} (hr : r ≠ 0) :
    W (1 - r) = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
      transformedRemainder
        (finiteAsymptoticRemainder (rightRescaling W) lambda⁻¹ b) r := by
  rw [rightRescaling_reconstruction (W := W) hr]
  unfold transformedRemainder finiteAsymptoticRemainder
  calc
    r * rightRescaling W r⁻¹ =
        r * approximation4 lambda⁻¹ b r⁻¹ +
          r * (rightRescaling W r⁻¹ - approximation4 lambda⁻¹ b r⁻¹) := by ring
    _ = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
        r * (rightRescaling W r⁻¹ - approximation4 lambda⁻¹ b r⁻¹) := by
      rw [approximation4_reciprocal_identity lambda⁻¹ b hr]

theorem transformedRemainder_hasDerivAt {R R1 : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hR : HasDerivAt R (R1 r⁻¹) r⁻¹) :
    HasDerivAt (transformedRemainder R) (transformedRemainderD1 R R1 r) r := by
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(r⁻¹ ^ 2)) r := by
    exact (hasDerivAt_inv hr).congr_deriv (by rw [inv_pow])
  have h := (hasDerivAt_id r).mul (hR.comp r hinv)
  have heq : R r⁻¹ + r * (R1 r⁻¹ * -(r⁻¹ ^ 2)) =
      transformedRemainderD1 R R1 r := by
    rw [transformedRemainderD1]
    field_simp [hr]
    ring
  have hderiv :=
    h.congr_deriv (by simpa only [id_eq, Function.comp_apply, one_mul] using heq)
  have h' := hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact h'

theorem transformedRemainderD1_hasDerivAt {R R1 R2 : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hR : HasDerivAt R (R1 r⁻¹) r⁻¹)
    (hR1 : HasDerivAt R1 (R2 r⁻¹) r⁻¹) :
    HasDerivAt (transformedRemainderD1 R R1) (transformedRemainderD2 R2 r) r := by
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(r⁻¹ ^ 2)) r := by
    exact (hasDerivAt_inv hr).congr_deriv (by rw [inv_pow])
  have hleft := hR.comp r hinv
  have hright := hinv.mul (hR1.comp r hinv)
  have heq : R1 r⁻¹ * -(r⁻¹ ^ 2) -
      (-(r⁻¹ ^ 2) * R1 r⁻¹ + r⁻¹ * (R2 r⁻¹ * -(r⁻¹ ^ 2))) =
      transformedRemainderD2 R2 r := by
    rw [transformedRemainderD2]
    field_simp [hr]
    ring
  have h := (hleft.sub hright).congr_deriv (by
    simpa only [Function.comp_apply] using heq)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ ↦ rfl

theorem transformedRemainderD2_hasDerivAt {R2 R3 : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hR2 : HasDerivAt R2 (R3 r⁻¹) r⁻¹) :
    HasDerivAt (transformedRemainderD2 R2) (transformedRemainderD3 R2 R3 r) r := by
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(r⁻¹ ^ 2)) r := by
    exact (hasDerivAt_inv hr).congr_deriv (by rw [inv_pow])
  have h := (hinv.pow 3).mul (hR2.comp r hinv)
  have heq : 3 * r⁻¹ ^ (3 - 1) * -(r⁻¹ ^ 2) * R2 r⁻¹ +
      r⁻¹ ^ 3 * (R3 r⁻¹ * -(r⁻¹ ^ 2)) = transformedRemainderD3 R2 R3 r := by
    rw [transformedRemainderD3]
    simp only [inv_pow]
    field_simp [hr]
    ring
  have h' := h.congr_deriv (by
    simpa only [Function.comp_apply, Pi.pow_apply, Nat.cast_ofNat] using heq)
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ ↦ rfl

theorem transformedRemainderD3_hasDerivAt {R2 R3 R4 : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hR2 : HasDerivAt R2 (R3 r⁻¹) r⁻¹)
    (hR3 : HasDerivAt R3 (R4 r⁻¹) r⁻¹) :
    HasDerivAt (transformedRemainderD3 R2 R3)
      (transformedRemainderD4 R2 R3 R4 r) r := by
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(r⁻¹ ^ 2)) r := by
    exact (hasDerivAt_inv hr).congr_deriv (by rw [inv_pow])
  have hfirst := ((hinv.pow 4).mul (hR2.comp r hinv)).const_mul (-3)
  have hsecond := (hinv.pow 5).mul (hR3.comp r hinv)
  have heq : -3 * (4 * r⁻¹ ^ (4 - 1) * -(r⁻¹ ^ 2) * R2 r⁻¹ +
      r⁻¹ ^ 4 * (R3 r⁻¹ * -(r⁻¹ ^ 2))) -
      (5 * r⁻¹ ^ (5 - 1) * -(r⁻¹ ^ 2) * R3 r⁻¹ +
        r⁻¹ ^ 5 * (R4 r⁻¹ * -(r⁻¹ ^ 2))) =
      transformedRemainderD4 R2 R3 R4 r := by
    rw [transformedRemainderD4]
    simp only [inv_pow]
    field_simp [hr]
    ring
  have h := (hfirst.sub hsecond).congr_deriv (by
    simpa only [Function.comp_apply, Pi.pow_apply, Nat.cast_ofNat] using heq)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [transformedRemainderD3, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Function.comp_apply]
    ring

/-- Pulling an `atTop` derivative remainder estimate back by `r ↦ r⁻¹` turns
inverse powers into positive powers at the strict right filter of zero. -/
theorem iteratedDeriv_comp_inv_isBigO {R : ℝ → ℝ} {ell : ℕ}
    (hR : (fun t : ℝ ↦ iteratedDeriv ell R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)) :
    (fun r : ℝ ↦ iteratedDeriv ell R r⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ (5 + ell)) := by
  have hcomp := hR.comp_tendsto tendsto_inv_nhdsGT_zero
  apply hcomp.congr'
  · filter_upwards with r
    rfl
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := (show 0 < r from hr).ne'
    change ((r⁻¹) ^ (5 + ell))⁻¹ = r ^ (5 + ell)
    rw [← inv_pow, inv_inv]

/-- A reciprocal prefactor cancels the corresponding number of powers in the
pulled-back estimate. -/
theorem invPow_mul_iteratedDeriv_comp_inv_isBigO {R : ℝ → ℝ} {ell k : ℕ}
    (hk : k ≤ 5 + ell)
    (hR : (fun t : ℝ ↦ iteratedDeriv ell R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)) :
    (fun r : ℝ ↦ r⁻¹ ^ k * iteratedDeriv ell R r⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ (5 + ell - k)) := by
  have hpow : (fun r : ℝ ↦ r⁻¹ ^ k) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r⁻¹ ^ k) := isBigO_refl _ _
  have hmul := hpow.mul (iteratedDeriv_comp_inv_isBigO hR)
  apply hmul.congr'
  · filter_upwards with r
    rfl
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := (show 0 < r from hr).ne'
    rw [inv_pow, mul_comm, ← pow_sub₀ r hr0 hk]

theorem transformedRemainderD1_isBigO {R : ℝ → ℝ}
    (hR0 : R =O[atTop] (fun t : ℝ ↦ (t ^ 5)⁻¹))
    (hR1 : (fun t ↦ iteratedDeriv 1 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 6)⁻¹)) :
    transformedRemainderD1 R (iteratedDeriv 1 R) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 5) := by
  have hleft : (fun r : ℝ ↦ R r⁻¹) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ 5) := by
    simpa only [iteratedDeriv_zero, Nat.zero_add] using
      (iteratedDeriv_comp_inv_isBigO (ell := 0) hR0)
  have hright : (fun r : ℝ ↦ r⁻¹ * iteratedDeriv 1 R r⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 5) := by
    simpa only [pow_one, Nat.reduceAdd, Nat.reduceSub] using
      (invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 1) (k := 1)
        (by omega) hR1)
  change (fun r : ℝ ↦ R r⁻¹ - r⁻¹ * iteratedDeriv 1 R r⁻¹) =O[𝓝[>] (0 : ℝ)]
    (fun r : ℝ ↦ r ^ 5)
  exact hleft.sub hright

theorem transformedRemainderD2_isBigO {R : ℝ → ℝ}
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹)) :
    transformedRemainderD2 (iteratedDeriv 2 R) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 4) := by
  change (fun r : ℝ ↦ r⁻¹ ^ 3 * iteratedDeriv 2 R r⁻¹) =O[𝓝[>] (0 : ℝ)]
    (fun r : ℝ ↦ r ^ 4)
  simpa only [Nat.reduceAdd, Nat.reduceSub] using
    (invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 2) (k := 3)
      (by omega) hR2)

theorem transformedRemainderD3_isBigO {R : ℝ → ℝ}
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹))
    (hR3 : (fun t ↦ iteratedDeriv 3 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 8)⁻¹)) :
    transformedRemainderD3 (iteratedDeriv 2 R) (iteratedDeriv 3 R) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 3) := by
  have htwo := invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 2) (k := 4)
    (by omega) hR2
  have hthree := invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 3) (k := 5)
    (by omega) hR3
  apply ((htwo.const_mul_left (-3)).sub hthree).congr'
  · filter_upwards with r
    simp only [transformedRemainderD3]
    ring
  · filter_upwards with r
    rfl

theorem transformedRemainderD4_isBigO {R : ℝ → ℝ}
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹))
    (hR3 : (fun t ↦ iteratedDeriv 3 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 8)⁻¹))
    (hR4 : (fun t ↦ iteratedDeriv 4 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹)) :
    transformedRemainderD4 (iteratedDeriv 2 R) (iteratedDeriv 3 R)
      (iteratedDeriv 4 R) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ 2) := by
  have htwo := invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 2) (k := 5)
    (by omega) hR2
  have hthree := invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 3) (k := 6)
    (by omega) hR3
  have hfour := invPow_mul_iteratedDeriv_comp_inv_isBigO (ell := 4) (k := 7)
    (by omega) hR4
  apply (((htwo.const_mul_left 12).add (hthree.const_mul_left 8)).add hfour).congr'
  · filter_upwards with r
    simp only [transformedRemainderD4]
    ring
  · filter_upwards with r
    rfl

/-- The undifferentiated reciprocal remainder gains one power from the
reconstruction factor `r`. -/
theorem transformedRemainder_isBigO {R : ℝ → ℝ}
    (hR0 : R =O[atTop] (fun t : ℝ ↦ (t ^ 5)⁻¹)) :
    transformedRemainder R =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ 6) := by
  have hcomp : (fun r : ℝ ↦ R r⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 5) := by
    simpa only [iteratedDeriv_zero, Nat.zero_add] using
      (iteratedDeriv_comp_inv_isBigO (ell := 0) hR0)
  have hid : (fun r : ℝ ↦ r) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r) :=
    isBigO_refl _ _
  apply (hid.mul hcomp).congr'
  · filter_upwards with r
    rfl
  · filter_upwards with r
    ring

private noncomputable def reciprocalRadius (T : ℝ) : ℝ :=
  (max T 0 + 1)⁻¹

private theorem reciprocalRadius_pos (T : ℝ) : 0 < reciprocalRadius T := by
  unfold reciprocalRadius
  positivity

private theorem inv_gt_of_mem_reciprocalRadius {T r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) (reciprocalRadius T)) : T < r⁻¹ := by
  have hr' : r < (max T 0 + 1)⁻¹ := by
    simpa only [reciprocalRadius] using hr.2
  have hMlt : max T 0 + 1 < r⁻¹ := lt_inv_of_lt_inv₀ hr.1 hr'
  linarith [le_max_left T 0]

/-- On a sufficiently small reciprocal interval, the four displayed derivative
formulas are the actual iterated derivatives of the transformed remainder. -/
theorem transformedRemainder_iteratedDeriv_formulas {R : ℝ → ℝ} {T : ℝ}
    (hR : ContDiffOn ℝ 4 R (Ioi T)) :
    let eta := reciprocalRadius T
    EqOn (iteratedDeriv 1 (transformedRemainder R))
        (transformedRemainderD1 R (iteratedDeriv 1 R)) (Ioo 0 eta) ∧
      EqOn (iteratedDeriv 2 (transformedRemainder R))
        (transformedRemainderD2 (iteratedDeriv 2 R)) (Ioo 0 eta) ∧
      EqOn (iteratedDeriv 3 (transformedRemainder R))
        (transformedRemainderD3 (iteratedDeriv 2 R) (iteratedDeriv 3 R))
          (Ioo 0 eta) ∧
      EqOn (iteratedDeriv 4 (transformedRemainder R))
        (transformedRemainderD4 (iteratedDeriv 2 R) (iteratedDeriv 3 R)
          (iteratedDeriv 4 R)) (Ioo 0 eta) := by
  dsimp only
  let eta := reciprocalRadius T
  have hRat (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) eta) : ContDiffAt ℝ 4 R r⁻¹ := by
    have hrt : r⁻¹ ∈ Ioi T := inv_gt_of_mem_reciprocalRadius hr
    exact (hR r⁻¹ hrt).contDiffAt (isOpen_Ioi.mem_nhds hrt)
  have hRderiv (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) eta) (m : ℕ) (hm : m + 1 ≤ 4) :
      HasDerivAt (iteratedDeriv m R) (iteratedDeriv (m + 1) R r⁻¹) r⁻¹ := by
    have hdiffF := (hRat r hr).differentiableAt_iteratedFDeriv
      (m := m) (by exact_mod_cast hm)
    have hdiff : DifferentiableAt ℝ (iteratedDeriv m R) r⁻¹ := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm
        |>.comp_differentiableAt_iff).mpr hdiffF
    simpa only [← iteratedDeriv_succ] using hdiff.hasDerivAt
  have hE1 : EqOn (iteratedDeriv 1 (transformedRemainder R))
      (transformedRemainderD1 R (iteratedDeriv 1 R)) (Ioo 0 eta) := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have hzero := hRderiv r hr 0 (by norm_num)
    simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.zero_add] using
      (transformedRemainder_hasDerivAt hr0 hzero).deriv
  have hE2 : EqOn (iteratedDeriv 2 (transformedRemainder R))
      (transformedRemainderD2 (iteratedDeriv 2 R)) (Ioo 0 eta) := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have hzero := hRderiv r hr 0 (by norm_num)
    have hone := hRderiv r hr 1 (by norm_num)
    have hformula := transformedRemainderD1_hasDerivAt hr0 hzero hone
    have heventually : iteratedDeriv 1 (transformedRemainder R) =ᶠ[𝓝 r]
        transformedRemainderD1 R (iteratedDeriv 1 R) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
      exact hE1 hx
    calc
      iteratedDeriv 2 (transformedRemainder R) r =
          deriv (iteratedDeriv 1 (transformedRemainder R)) r := by
            rw [iteratedDeriv_succ]
      _ = deriv (transformedRemainderD1 R (iteratedDeriv 1 R)) r :=
        heventually.deriv_eq
      _ = transformedRemainderD2 (iteratedDeriv 2 R) r := hformula.deriv
  have hE3 : EqOn (iteratedDeriv 3 (transformedRemainder R))
      (transformedRemainderD3 (iteratedDeriv 2 R) (iteratedDeriv 3 R))
        (Ioo 0 eta) := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have htwo := hRderiv r hr 2 (by norm_num)
    have hformula := transformedRemainderD2_hasDerivAt hr0 htwo
    have heventually : iteratedDeriv 2 (transformedRemainder R) =ᶠ[𝓝 r]
        transformedRemainderD2 (iteratedDeriv 2 R) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
      exact hE2 hx
    calc
      iteratedDeriv 3 (transformedRemainder R) r =
          deriv (iteratedDeriv 2 (transformedRemainder R)) r := by
            rw [iteratedDeriv_succ]
      _ = deriv (transformedRemainderD2 (iteratedDeriv 2 R)) r :=
        heventually.deriv_eq
      _ = transformedRemainderD3 (iteratedDeriv 2 R) (iteratedDeriv 3 R) r :=
        hformula.deriv
  have hE4 : EqOn (iteratedDeriv 4 (transformedRemainder R))
      (transformedRemainderD4 (iteratedDeriv 2 R) (iteratedDeriv 3 R)
        (iteratedDeriv 4 R)) (Ioo 0 eta) := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have htwo := hRderiv r hr 2 (by norm_num)
    have hthree := hRderiv r hr 3 (by norm_num)
    have hformula := transformedRemainderD3_hasDerivAt hr0 htwo hthree
    have heventually : iteratedDeriv 3 (transformedRemainder R) =ᶠ[𝓝 r]
        transformedRemainderD3 (iteratedDeriv 2 R) (iteratedDeriv 3 R) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
      exact hE3 hx
    calc
      iteratedDeriv 4 (transformedRemainder R) r =
          deriv (iteratedDeriv 3 (transformedRemainder R)) r := by
            rw [iteratedDeriv_succ]
      _ = deriv (transformedRemainderD3 (iteratedDeriv 2 R)
          (iteratedDeriv 3 R)) r := heventually.deriv_eq
      _ = transformedRemainderD4 (iteratedDeriv 2 R) (iteratedDeriv 3 R)
          (iteratedDeriv 4 R) r := hformula.deriv
  exact ⟨hE1, hE2, hE3, hE4⟩

private noncomputable def endpointRemainderRadius (T : ℝ) : ℝ :=
  reciprocalRadius T / 2

private theorem endpointRemainderRadius_pos (T : ℝ) :
    0 < endpointRemainderRadius T := by
  unfold endpointRemainderRadius
  exact div_pos (reciprocalRadius_pos T) (by norm_num)

private theorem endpointRemainderRadius_lt_reciprocalRadius (T : ℝ) :
    endpointRemainderRadius T < reciprocalRadius T := by
  unfold endpointRemainderRadius
  nlinarith [reciprocalRadius_pos T]

private theorem Ioc_endpointRemainderRadius_subset_Ioo_reciprocalRadius (T : ℝ) :
    Ioc (0 : ℝ) (endpointRemainderRadius T) ⊆
      Ioo 0 (reciprocalRadius T) := by
  intro r hr
  exact ⟨hr.1, hr.2.trans_lt (endpointRemainderRadius_lt_reciprocalRadius T)⟩

/-- The transformed remainder is `C⁴` on a punctured one-sided interval whenever
the original remainder is `C⁴` on a terminal half-line. -/
theorem transformedRemainder_contDiffOn {R : ℝ → ℝ} {T : ℝ}
    (hR : ContDiffOn ℝ 4 R (Ioi T)) :
    ContDiffOn ℝ 4 (transformedRemainder R)
      (Ioc 0 (endpointRemainderRadius T)) := by
  have hinv : ContDiffOn ℝ 4 (fun r : ℝ ↦ r⁻¹)
      (Ioc 0 (endpointRemainderRadius T)) := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    exact (contDiffAt_inv ℝ hr0).contDiffWithinAt
  have hmap : MapsTo (fun r : ℝ ↦ r⁻¹)
      (Ioc 0 (endpointRemainderRadius T)) (Ioi T) := by
    intro r hr
    exact inv_gt_of_mem_reciprocalRadius
      (Ioc_endpointRemainderRadius_subset_Ioo_reciprocalRadius T hr)
  unfold transformedRemainder
  exact contDiffOn_id.mul (hR.comp hinv hmap)

private theorem eventuallyEqOn_Ioo_nhdsGT {f g : ℝ → ℝ} {eta : ℝ}
    (heta : 0 < eta) (hfg : EqOn f g (Ioo 0 eta)) :
    f =ᶠ[𝓝[>] (0 : ℝ)] g := by
  filter_upwards [Ioo_mem_nhdsGT heta] with r hr
  exact hfg hr

/-- The first transformed derivative inherits the exact fifth-order estimate. -/
theorem iteratedDeriv_transformedRemainder_one_isBigO {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR0 : R =O[atTop] (fun t : ℝ ↦ (t ^ 5)⁻¹))
    (hR1 : (fun t ↦ iteratedDeriv 1 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 6)⁻¹)) :
    (fun r ↦ iteratedDeriv 1 (transformedRemainder R) r) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 5) := by
  have hformula := (transformedRemainder_iteratedDeriv_formulas hRcont).1
  exact (transformedRemainderD1_isBigO hR0 hR1).congr'
    (eventuallyEqOn_Ioo_nhdsGT (reciprocalRadius_pos T) hformula).symm
    (Filter.EventuallyEq.rfl)

/-- The second transformed derivative inherits the exact fourth-order estimate. -/
theorem iteratedDeriv_transformedRemainder_two_isBigO {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹)) :
    (fun r ↦ iteratedDeriv 2 (transformedRemainder R) r) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 4) := by
  have hformula := (transformedRemainder_iteratedDeriv_formulas hRcont).2.1
  exact (transformedRemainderD2_isBigO hR2).congr'
    (eventuallyEqOn_Ioo_nhdsGT (reciprocalRadius_pos T) hformula).symm
    (Filter.EventuallyEq.rfl)

/-- The third transformed derivative inherits the exact third-order estimate. -/
theorem iteratedDeriv_transformedRemainder_three_isBigO {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹))
    (hR3 : (fun t ↦ iteratedDeriv 3 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 8)⁻¹)) :
    (fun r ↦ iteratedDeriv 3 (transformedRemainder R) r) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 3) := by
  have hformula := (transformedRemainder_iteratedDeriv_formulas hRcont).2.2.1
  exact (transformedRemainderD3_isBigO hR2 hR3).congr'
    (eventuallyEqOn_Ioo_nhdsGT (reciprocalRadius_pos T) hformula).symm
    (Filter.EventuallyEq.rfl)

/-- The fourth transformed derivative inherits the exact quadratic estimate. -/
theorem iteratedDeriv_transformedRemainder_four_isBigO {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR2 : (fun t ↦ iteratedDeriv 2 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 7)⁻¹))
    (hR3 : (fun t ↦ iteratedDeriv 3 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 8)⁻¹))
    (hR4 : (fun t ↦ iteratedDeriv 4 R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹)) :
    (fun r ↦ iteratedDeriv 4 (transformedRemainder R) r) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 2) := by
  have hformula := (transformedRemainder_iteratedDeriv_formulas hRcont).2.2.2
  exact (transformedRemainderD4_isBigO hR2 hR3 hR4).congr'
    (eventuallyEqOn_Ioo_nhdsGT (reciprocalRadius_pos T) hformula).symm
    (Filter.EventuallyEq.rfl)

/-- All five reciprocal-coordinate jet estimates in a uniform statement. -/
theorem iteratedDeriv_transformedRemainder_isBigO {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)) :
    ∀ ell : ℕ, ell ≤ 4 →
      (fun r ↦ iteratedDeriv ell (transformedRemainder R) r) =O[𝓝[>] (0 : ℝ)]
        (fun r : ℝ ↦ r ^ (6 - ell)) := by
  intro ell hell
  interval_cases ell
  · simpa only [iteratedDeriv_zero, Nat.reduceSub] using
      transformedRemainder_isBigO (hR 0 (by norm_num))
  · simpa only [Nat.reduceAdd, Nat.reduceSub] using
      iteratedDeriv_transformedRemainder_one_isBigO hRcont
        (hR 0 (by norm_num)) (hR 1 (by norm_num))
  · simpa only [Nat.reduceAdd, Nat.reduceSub] using
      iteratedDeriv_transformedRemainder_two_isBigO hRcont (hR 2 (by norm_num))
  · simpa only [Nat.reduceAdd, Nat.reduceSub] using
      iteratedDeriv_transformedRemainder_three_isBigO hRcont
        (hR 2 (by norm_num)) (hR 3 (by norm_num))
  · simpa only [Nat.reduceAdd, Nat.reduceSub] using
      iteratedDeriv_transformedRemainder_four_isBigO hRcont
        (hR 2 (by norm_num)) (hR 3 (by norm_num)) (hR 4 (by norm_num))

private theorem tendsto_pow_nhdsGT_zero (n : ℕ) (hn : 0 < n) :
    Tendsto (fun r : ℝ ↦ r ^ n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [zero_pow hn.ne'] using hid.pow n

/-- The reciprocal remainder and all its first four jets tend to zero at the
finite endpoint. -/
theorem iteratedDeriv_transformedRemainder_tendsto_zero {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)) :
    ∀ ell : ℕ, ell ≤ 4 →
      Tendsto (fun r ↦ iteratedDeriv ell (transformedRemainder R) r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro ell hell
  exact (iteratedDeriv_transformedRemainder_isBigO hRcont hR ell hell).trans_tendsto
    (tendsto_pow_nhdsGT_zero (6 - ell) (by omega))

/-- A zero right jet with limits through order four extends across the endpoint.
This is the endpoint-extension argument used below, proved internally from the
one-sided derivative extension theorem and the iterated-derivative criterion for
`ContDiffOn`. -/
private theorem exists_zeroJet_endpointExtension (E : ℝ → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hEsmooth : ContDiffOn ℝ 4 E (Ioc 0 eta))
    (hElimits : ∀ k : ℕ, k ≤ 4 →
      Tendsto (fun r ↦ iteratedDeriv k E r) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ extension : ℝ → ℝ,
      EqOn extension E (Ioc 0 eta) ∧
      ContDiffOn ℝ 4 extension (Icc 0 eta) ∧
      ∀ k : Fin 5, iteratedDerivWithin k extension (Ici 0) 0 = 0 := by
  let s : Set ℝ := Ioc 0 eta
  let S : Set ℝ := Icc 0 eta
  let J : ℕ → ℝ → ℝ := fun k x ↦
    if x ≤ 0 then 0 else iteratedDerivWithin k E s x
  let extension : ℝ → ℝ := J 0
  have hJzero : extension = fun x ↦ if x ≤ 0 then 0 else E x := by
    funext x
    simp [extension, J, iteratedDerivWithin_zero]
  have hWithinOrdEventually (k : ℕ) (hk : k ≤ 4) :
      (fun x ↦ iteratedDerivWithin k E s x) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun x ↦ iteratedDeriv k E x) := by
    filter_upwards [Ioo_mem_nhdsGT heta] with x hx
    have hsx : x ∈ s := ⟨hx.1, hx.2.le⟩
    have hsN : s ∈ 𝓝 x := Ioc_mem_nhds hx.1 hx.2
    have hAt : ContDiffAt ℝ k E x :=
      ((hEsmooth x hsx).contDiffAt hsN).of_le (by exact_mod_cast hk)
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioc (0 : ℝ) eta)
      hAt hsx
  have hJlim (k : ℕ) (hk : k ≤ 4) :
      Tendsto (J k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hEq : J k =ᶠ[𝓝[>] (0 : ℝ)] (fun x ↦ iteratedDeriv k E x) := by
      filter_upwards [Ioo_mem_nhdsGT heta, hWithinOrdEventually k hk] with x hx hwithin
      simp only [J, if_neg (not_le.mpr hx.1), hwithin]
    exact (hElimits k hk).congr' hEq.symm
  have hJcontZero (k : ℕ) (hk : k ≤ 4) :
      ContinuousWithinAt (J k) (Ici (0 : ℝ)) 0 := by
    have hright : ContinuousWithinAt (J k) (Ioi (0 : ℝ)) 0 := by
      simpa only [ContinuousWithinAt, J, if_pos le_rfl] using hJlim k hk
    rw [show Ici (0 : ℝ) = insert 0 (Ioi 0) by ext x; simp [le_iff_eq_or_lt]]
    exact hright.insert
  have hJderivInterior (k : ℕ) (hk : k < 4) (x : ℝ)
      (hx : x ∈ Ioo 0 eta) : HasDerivAt (J k) (J (k + 1) x) x := by
    have hsx : x ∈ s := ⟨hx.1, hx.2.le⟩
    have hsN : s ∈ 𝓝 x := Ioc_mem_nhds hx.1 hx.2
    have hdWithin := hEsmooth.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast hk) (uniqueDiffOn_Ioc (0 : ℝ) eta) x hsx
    have hdAt := hdWithin.differentiableAt hsN
    have hcoef : deriv (iteratedDerivWithin k E s) x =
        iteratedDerivWithin (k + 1) E s x := by
      rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hsN]
    have hlocal : J k =ᶠ[𝓝 x] iteratedDerivWithin k E s := by
      filter_upwards [Ioi_mem_nhds hx.1] with y hy
      change 0 < y at hy
      simp only [J, if_neg (not_le.mpr hy)]
    have hvalue : J (k + 1) x = iteratedDerivWithin (k + 1) E s x := by
      simp [J, not_le.mpr hx.1]
    exact (hdAt.hasDerivAt.congr_of_eventuallyEq hlocal).congr_deriv
      (by rw [hcoef, hvalue])
  have hJderivZero (k : ℕ) (hk : k < 4) :
      HasDerivWithinAt (J k) 0 (Ici (0 : ℝ)) 0 := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
    · intro x hx
      have hbase := hEsmooth.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk) (uniqueDiffOn_Ioc (0 : ℝ) eta) x hx
      have hsource : HasDerivWithinAt (iteratedDerivWithin k E s)
          (derivWithin (iteratedDerivWithin k E s) s x) s x :=
        hbase.hasDerivWithinAt
      exact (hsource.congr
        (fun y hy ↦ by simp [J, not_le.mpr hy.1])
        (by simp [J, not_le.mpr hx.1])).differentiableWithinAt
    · exact (hJcontZero k hk.le).mono (by
        intro x hx
        exact hx.1.le)
    · simpa only [s] using Ioc_mem_nhdsGT heta
    · have hderivEq : (fun x ↦ deriv (J k) x) =ᶠ[𝓝[>] (0 : ℝ)] J (k + 1) := by
        filter_upwards [Ioo_mem_nhdsGT heta] with x hx
        exact (hJderivInterior k hk x hx).deriv
      exact (hJlim (k + 1) (by omega)).congr' hderivEq.symm
  have hsetsAtPositive (x : ℝ) (hx : 0 < x) : s =ᶠ[𝓝 x] S := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change 0 < y at hy
    dsimp only [s, S]
    apply propext
    change (0 < y ∧ y ≤ eta) ↔ (0 ≤ y ∧ y ≤ eta)
    exact ⟨fun h ↦ ⟨h.1.le, h.2⟩, fun h ↦ ⟨hy, h.2⟩⟩
  have hJfunAtPositive (k : ℕ) (x : ℝ) (hx : 0 < x) :
      J k =ᶠ[𝓝[S] x] iteratedDerivWithin k E s := by
    have hpos : ∀ᶠ y in 𝓝[S] x, y ∈ Ioi (0 : ℝ) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioi (0 : ℝ) from Ioi_mem_nhds hx).filter_mono
        inf_le_left
    filter_upwards [hpos] with y hy
    change 0 < y at hy
    simp only [J, if_neg (not_le.mpr hy)]
  have hJcont : ∀ k ≤ 4, ContinuousOn (J k) S := by
    intro k hk x hxS
    by_cases hx0 : x = 0
    · subst x
      exact (hJcontZero k hk).mono (by
        intro y hy
        exact hy.1)
    · have hxpos : 0 < x := lt_of_le_of_ne hxS.1 (Ne.symm hx0)
      have hxs : x ∈ s := ⟨hxpos, hxS.2⟩
      have hsource := hEsmooth.continuousOn_iteratedDerivWithin
        (by exact_mod_cast hk) (uniqueDiffOn_Ioc (0 : ℝ) eta) x hxs
      have hsourceS := hsource.congr_set (hsetsAtPositive x hxpos)
      exact hsourceS.congr_of_eventuallyEq (hJfunAtPositive k x hxpos)
        (by simp [J, not_le.mpr hxpos, s])
  have hJderiv : ∀ k < 4, ∀ x ∈ S,
      HasDerivWithinAt (J k) (J (k + 1) x) S x := by
    intro k hk x hxS
    by_cases hx0 : x = 0
    · subst x
      simpa only [J, if_pos le_rfl] using
        (hJderivZero k hk).mono (by intro y hy; exact hy.1)
    · have hxpos : 0 < x := lt_of_le_of_ne hxS.1 (Ne.symm hx0)
      have hxs : x ∈ s := ⟨hxpos, hxS.2⟩
      have hbase := hEsmooth.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk) (uniqueDiffOn_Ioc (0 : ℝ) eta) x hxs
      have hsource : HasDerivWithinAt (iteratedDerivWithin k E s)
          (iteratedDerivWithin (k + 1) E s x) s x := by
        rw [iteratedDerivWithin_succ]
        exact hbase.hasDerivWithinAt
      have hsourceS := hsource.congr_set (hsetsAtPositive x hxpos)
      exact (hsourceS.congr_of_eventuallyEq (hJfunAtPositive k x hxpos)
        (by simp [J, not_le.mpr hxpos])).congr_deriv
          (by simp [J, not_le.mpr hxpos])
  have hiter : ∀ k ≤ 4, EqOn (iteratedDerivWithin k extension S) (J k) S := by
    intro k hk
    induction k with
    | zero => intro x hx; simp [extension, iteratedDerivWithin_zero]
    | succ k ih =>
        have hklt : k < 4 := by omega
        intro x hx
        rw [iteratedDerivWithin_succ]
        calc
          derivWithin (iteratedDerivWithin k extension S) S x =
              derivWithin (J k) S x :=
            derivWithin_congr (ih (by omega)) (ih (by omega) hx)
          _ = J (k + 1) x := (hJderiv k hklt x hx).derivWithin
            (uniqueDiffOn_Icc heta x hx)
  have hSmooth : ContDiffOn ℝ 4 extension S := by
    refine (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
      (f := extension) (n := 4) (uniqueDiffOn_Icc heta)).2 ⟨?_, ?_⟩
    · intro k hk
      exact (hJcont k hk).congr (hiter k hk)
    · intro k hk
      have hdiffJ : DifferentiableOn ℝ (J k) S := fun x hx ↦
        (hJderiv k hk x hx).differentiableWithinAt
      exact hdiffJ.congr (hiter k hk.le)
  have hsetsZero : S =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
    filter_upwards [Iio_mem_nhds heta] with x hx
    dsimp only [S]
    apply propext
    change (0 ≤ x ∧ x ≤ eta) ↔ 0 ≤ x
    constructor
    · exact fun h ↦ h.1
    · exact fun h ↦ ⟨h, hx.le⟩
  refine ⟨extension, ?_, hSmooth, ?_⟩
  · intro x hx
    rw [hJzero]
    simp [not_le.mpr hx.1]
  · intro k
    have hsetJet : iteratedDerivWithin k extension S 0 =
        iteratedDerivWithin k extension (Ici 0) 0 := by
      unfold iteratedDerivWithin
      rw [iteratedFDerivWithin_congr_set hsetsZero k]
    rw [← hsetJet]
    have hzeroMem : (0 : ℝ) ∈ S := by
      change 0 ≤ (0 : ℝ) ∧ 0 ≤ eta
      exact ⟨le_rfl, heta.le⟩
    rw [hiter k (Nat.le_of_lt_succ k.isLt) hzeroMem]
    simp [J]

/-- Endpoint extension applied to the reciprocal remainder. The returned extension is the
remainder used in the finite-endpoint expansion, so its genuine derivatives (not
merely the displayed punctured formulas) satisfy the required estimates. -/
theorem exists_transformedRemainder_extension {R : ℝ → ℝ} {T : ℝ}
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hR : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)) :
    ∃ eta > 0, ∃ extension : ℝ → ℝ,
      EqOn extension (transformedRemainder R) (Ioc 0 eta) ∧
        ContDiffOn ℝ 4 extension (Icc 0 eta) ∧
        (∀ ell : ℕ, ell ≤ 4 →
          (fun r ↦ iteratedDeriv ell extension r) =O[𝓝[>] (0 : ℝ)]
            (fun r : ℝ ↦ r ^ (6 - ell))) ∧
        ∀ k : Fin 5, iteratedDerivWithin k extension (Ici 0) 0 = 0 := by
  let eta := endpointRemainderRadius T
  have heta : 0 < eta := endpointRemainderRadius_pos T
  have hEsmooth : ContDiffOn ℝ 4 (transformedRemainder R) (Ioc 0 eta) := by
    simpa only [eta] using transformedRemainder_contDiffOn hRcont
  have hElimits : ∀ k : Fin 5,
      Tendsto (fun r ↦ iteratedDeriv k (transformedRemainder R) r)
        (𝓝[>] (0 : ℝ)) (𝓝 ((fun _ : Fin 5 ↦ (0 : ℝ)) k)) := by
    intro k
    simpa only using iteratedDeriv_transformedRemainder_tendsto_zero hRcont hR k
      (Nat.le_of_lt_succ k.isLt)
  have hElimitsNat : ∀ k : ℕ, k ≤ 4 →
      Tendsto (fun r ↦ iteratedDeriv k (transformedRemainder R) r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro k hk
    exact hElimits ⟨k, by omega⟩
  obtain ⟨extension, hextension, hextensionSmooth, hjets⟩ :=
    exists_zeroJet_endpointExtension (transformedRemainder R) eta heta
      hEsmooth hElimitsNat
  refine ⟨eta, heta, extension, hextension, hextensionSmooth, ?_, hjets⟩
  intro ell hell
  have hEqOpen : EqOn extension (transformedRemainder R) (Ioo 0 eta) := by
    intro r hr
    exact hextension ⟨hr.1, hr.2.le⟩
  have hEqDeriv : EqOn (iteratedDeriv ell extension)
      (iteratedDeriv ell (transformedRemainder R)) (Ioo 0 eta) :=
    hEqOpen.iteratedDeriv_of_isOpen isOpen_Ioo ell
  exact (iteratedDeriv_transformedRemainder_isBigO hRcont hR ell hell).congr'
    (eventuallyEqOn_Ioo_nhdsGT heta hEqDeriv).symm (Filter.EventuallyEq.rfl)

/-! ## Exact endpoint-expansion conclusions -/

/-- A differentiable endpoint expansion with precisely the source's remainder estimates. -/
def EndpointDifferentiableExpansion (f : ℝ → ℝ) (linear quadratic : ℝ) : Prop :=
  ∃ eta > 0, ∃ higher : Fin 3 → ℝ, ∃ remainder : ℝ → ℝ,
    EqOn f (fun r ↦ endpointPolynomial linear quadratic higher r + remainder r)
        (Ioc 0 eta) ∧
      ContDiffOn ℝ 4 remainder (Ioc 0 eta) ∧
      ∀ ell : ℕ, ell ≤ 4 →
        (fun r ↦ iteratedDeriv ell remainder r) =O[𝓝[>] 0]
          (fun r : ℝ ↦ r ^ (6 - ell))

/-- A finite asymptotic expansion of the left rescaling yields the complete
finite-endpoint differentiable expansion. -/
theorem leftEndpointDifferentiableExpansion_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    EndpointDifferentiableExpansion W lambda⁻¹ (hexpansion.coefficients 0) := by
  let R := finiteAsymptoticRemainder (leftRescaling W) lambda⁻¹
    hexpansion.coefficients
  have hRcont : ContDiffOn ℝ 4 R (Ioi (1 : ℝ)) := by
    simpa only [R] using
      left_finiteAsymptoticRemainder_contDiffOn hsolution hexpansion.coefficients
  have hRbigO : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
    simpa only [R] using hexpansion.derivativeRemainderBigO
  obtain ⟨eta, heta, extension, hextension, hextensionSmooth, hextensionBigO, _⟩ :=
    exists_transformedRemainder_extension hRcont hRbigO
  refine ⟨eta, heta, endpointHigherCoefficients hexpansion.coefficients,
    extension, ?_, hextensionSmooth.mono Ioc_subset_Icc_self, hextensionBigO⟩
  intro r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  calc
    W r = endpointPolynomial lambda⁻¹ (hexpansion.coefficients 0)
        (endpointHigherCoefficients hexpansion.coefficients) r +
        transformedRemainder R r := by
      simpa only [R] using leftEndpoint_reconstruction_from_finiteExpansion
        (lambda := lambda) (W := W) hexpansion.coefficients hr0
    _ = endpointPolynomial lambda⁻¹ (hexpansion.coefficients 0)
        (endpointHigherCoefficients hexpansion.coefficients) r + extension r := by
      rw [hextension hr]

/-- The corresponding construction for the reflected right endpoint. -/
theorem rightEndpointDifferentiableExpansion_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    EndpointDifferentiableExpansion (fun r ↦ W (1 - r)) lambda⁻¹
      (hexpansion.coefficients 0) := by
  let R := finiteAsymptoticRemainder (rightRescaling W) lambda⁻¹
    hexpansion.coefficients
  have hRcont : ContDiffOn ℝ 4 R (Ioi (1 : ℝ)) := by
    simpa only [R] using
      right_finiteAsymptoticRemainder_contDiffOn hsolution hexpansion.coefficients
  have hRbigO : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
    simpa only [R] using hexpansion.derivativeRemainderBigO
  obtain ⟨eta, heta, extension, hextension, hextensionSmooth, hextensionBigO, _⟩ :=
    exists_transformedRemainder_extension hRcont hRbigO
  refine ⟨eta, heta, endpointHigherCoefficients hexpansion.coefficients,
    extension, ?_, hextensionSmooth.mono Ioc_subset_Icc_self, hextensionBigO⟩
  intro r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  calc
    W (1 - r) = endpointPolynomial lambda⁻¹ (hexpansion.coefficients 0)
        (endpointHigherCoefficients hexpansion.coefficients) r +
        transformedRemainder R r := by
      simpa only [R] using rightEndpoint_reconstruction_from_finiteExpansion
        (lambda := lambda) (W := W) hexpansion.coefficients hr0
    _ = endpointPolynomial lambda⁻¹ (hexpansion.coefficients 0)
        (endpointHigherCoefficients hexpansion.coefficients) r + extension r := by
      rw [hextension hr]

theorem leftEndpointDifferentiableExpansion_exactQuadratic
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    EndpointDifferentiableExpansion W lambda⁻¹
      (lambda⁻¹ ^ 4 - lambda⁻¹) := by
  have h := leftEndpointDifferentiableExpansion_of_finiteAsymptoticExpansion
    hsolution hexpansion
  rw [hexpansion.firstCoefficient, leftRescaled_firstCoefficient hlambda] at h
  exact h

theorem rightEndpointDifferentiableExpansion_exactQuadratic
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    EndpointDifferentiableExpansion (fun r ↦ W (1 - r)) lambda⁻¹
      (-(lambda⁻¹ ^ 4 + lambda⁻¹)) := by
  have h := rightEndpointDifferentiableExpansion_of_finiteAsymptoticExpansion
    hsolution hexpansion
  rw [hexpansion.firstCoefficient, rightRescaled_firstCoefficient hlambda] at h
  exact h

/-- The MI16 extension also upgrades the original left-endpoint function itself
to one-sided `C⁴`, including the endpoint. -/
theorem leftEndpoint_localContDiffOn_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hzero : W 0 = 0)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    ∃ eta > 0, ContDiffOn ℝ 4 W (Icc 0 eta) := by
  let b := hexpansion.coefficients
  let R := finiteAsymptoticRemainder (leftRescaling W) lambda⁻¹ b
  have hRcont : ContDiffOn ℝ 4 R (Ioi (1 : ℝ)) := by
    simpa only [R, b] using left_finiteAsymptoticRemainder_contDiffOn hsolution b
  have hRbigO : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
    simpa only [R, b] using hexpansion.derivativeRemainderBigO
  obtain ⟨eta, heta, extension, hextension, hextensionSmooth, _hbigO, hjets⟩ :=
    exists_transformedRemainder_extension hRcont hRbigO
  have hextensionZero : extension 0 = 0 := by
    simpa [iteratedDerivWithin_zero] using hjets (0 : Fin 5)
  have hmodelSmooth : ContDiffOn ℝ 4
      (fun r ↦ endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
        extension r) (Icc 0 eta) := by
    apply ContDiffOn.add
    · intro r hr
      unfold endpointPolynomial endpointHigherCoefficients
      fun_prop
    · exact hextensionSmooth
  refine ⟨eta, heta, hmodelSmooth.congr ?_⟩
  intro r hr
  rcases hr.1.eq_or_lt with hr0 | hrpos
  · subst r
    simp [hzero, endpointPolynomial, endpointHigherCoefficients,
      hextensionZero]
  · have hrIoc : r ∈ Ioc 0 eta := ⟨hrpos, hr.2⟩
    calc
      W r = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
          transformedRemainder R r := by
        simpa only [R, b] using
          leftEndpoint_reconstruction_from_finiteExpansion b hrpos.ne'
      _ = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
          extension r := by rw [hextension hrIoc]

/-- The reflected endpoint enjoys the same one-sided `C⁴` conclusion. -/
theorem rightEndpoint_reflected_localContDiffOn_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hone : W 1 = 0)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    ∃ eta > 0, ContDiffOn ℝ 4 (fun r ↦ W (1 - r)) (Icc 0 eta) := by
  let b := hexpansion.coefficients
  let R := finiteAsymptoticRemainder (rightRescaling W) lambda⁻¹ b
  have hRcont : ContDiffOn ℝ 4 R (Ioi (1 : ℝ)) := by
    simpa only [R, b] using right_finiteAsymptoticRemainder_contDiffOn hsolution b
  have hRbigO : ∀ ell : ℕ, ell ≤ 4 →
      (fun t ↦ iteratedDeriv ell R t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
    simpa only [R, b] using hexpansion.derivativeRemainderBigO
  obtain ⟨eta, heta, extension, hextension, hextensionSmooth, _hbigO, hjets⟩ :=
    exists_transformedRemainder_extension hRcont hRbigO
  have hextensionZero : extension 0 = 0 := by
    simpa [iteratedDerivWithin_zero] using hjets (0 : Fin 5)
  have hmodelSmooth : ContDiffOn ℝ 4
      (fun r ↦ endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
        extension r) (Icc 0 eta) := by
    apply ContDiffOn.add
    · intro r hr
      unfold endpointPolynomial endpointHigherCoefficients
      fun_prop
    · exact hextensionSmooth
  refine ⟨eta, heta, hmodelSmooth.congr ?_⟩
  intro r hr
  rcases hr.1.eq_or_lt with hr0 | hrpos
  · subst r
    simp [hone, endpointPolynomial,
      endpointHigherCoefficients, hextensionZero]
  · have hrIoc : r ∈ Ioc 0 eta := ⟨hrpos, hr.2⟩
    calc
      W (1 - r) = endpointPolynomial lambda⁻¹ (b 0)
          (endpointHigherCoefficients b) r + transformedRemainder R r := by
        simpa only [R, b] using
          rightEndpoint_reconstruction_from_finiteExpansion b hrpos.ne'
      _ = endpointPolynomial lambda⁻¹ (b 0) (endpointHigherCoefficients b) r +
          extension r := by rw [hextension hrIoc]

theorem rightEndpoint_localContDiffOn_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hone : W 1 = 0)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    ∃ eta > 0, ContDiffOn ℝ 4 W (Icc (1 - eta) 1) := by
  obtain ⟨eta, heta, hreflected⟩ :=
    rightEndpoint_reflected_localContDiffOn_of_finiteAsymptoticExpansion
      hsolution hone hexpansion
  have hinner : ContDiffOn ℝ 4 (fun u : ℝ ↦ 1 - u) (Icc (1 - eta) 1) := by
    fun_prop
  have hmap : MapsTo (fun u : ℝ ↦ 1 - u) (Icc (1 - eta) 1) (Icc 0 eta) := by
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  refine ⟨eta, heta, ?_⟩
  exact (hreflected.comp hinner hmap).congr (fun u hu ↦ by
    dsimp only [Function.comp_apply]
    ring)

/-- One-sided endpoint regularity glued to the smooth interior. -/
theorem leftLinearBranch_contDiffOn {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hzero : W 0 = 0)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    ContDiffOn ℝ 4 W (Ico 0 1) := by
  obtain ⟨eta, heta, hlocal⟩ :=
    leftEndpoint_localContDiffOn_of_finiteAsymptoticExpansion hsolution hzero hexpansion
  let eps := min eta (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min heta (by norm_num)
  have hepsOne : eps < 1 := lt_of_le_of_lt (min_le_right eta (1 / 2 : ℝ)) (by norm_num)
  have hlocal' : ContDiffOn ℝ 4 W (Icc 0 eps) := by
    apply hlocal.mono
    intro u hu
    exact ⟨hu.1, hu.2.trans (min_le_left eta (1 / 2 : ℝ))⟩
  intro u hu
  rcases hu.1.eq_or_lt with hu0 | hupos
  · subst u
    have hmem : Icc (0 : ℝ) eps ∈ 𝓝[Ico (0 : ℝ) 1] 0 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds heps)] with x hx hxeps
      exact ⟨hx.1, hxeps.le⟩
    exact (hlocal' 0 ⟨le_rfl, heps.le⟩).mono_of_mem_nhdsWithin hmem
  · have huOpen : u ∈ openUnitInterval := ⟨hupos, hu.2⟩
    have hAt : ContDiffAt ℝ 4 W u :=
      ((hsolution.contDiffOn_infty_interior u huOpen).contDiffAt
        (isOpen_Ioo.mem_nhds huOpen)).of_le
          (WithTop.coe_le_coe.mpr (OrderTop.le_top _))
    exact hAt.contDiffWithinAt

theorem rightLinearBranch_contDiffOn {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hone : W 1 = 0)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    ContDiffOn ℝ 4 W (Ioc 0 1) := by
  obtain ⟨eta, heta, hlocal⟩ :=
    rightEndpoint_localContDiffOn_of_finiteAsymptoticExpansion hsolution hone hexpansion
  let eps := min eta (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min heta (by norm_num)
  have hlocal' : ContDiffOn ℝ 4 W (Icc (1 - eps) 1) := by
    have hepsle : eps ≤ eta := min_le_left eta (1 / 2 : ℝ)
    apply hlocal.mono
    intro u hu
    constructor
    · linarith [hu.1, hepsle]
    · exact hu.2
  intro u hu
  rcases hu.2.eq_or_lt with hu1 | hult
  · subst u
    have hmem : Icc (1 - eps) 1 ∈ 𝓝[Ioc (0 : ℝ) 1] 1 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith : 1 - eps < 1))]
        with x hx hxeps
      exact ⟨hxeps.le, hx.2⟩
    exact (hlocal' 1 ⟨by linarith, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  · have huOpen : u ∈ openUnitInterval := ⟨hu.1, hult⟩
    have hAt : ContDiffAt ℝ 4 W u :=
      ((hsolution.contDiffOn_infty_interior u huOpen).contDiffAt
        (isOpen_Ioo.mem_nhds huOpen)).of_le
          (WithTop.coe_le_coe.mpr (OrderTop.le_top _))
    exact hAt.contDiffWithinAt

private theorem pow_isBigO_pow_nhdsGT {p q : ℕ} (hpq : p ≤ q) :
    (fun r : ℝ ↦ r ^ q) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ p) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.1.le q),
    abs_of_nonneg (pow_nonneg hr.1.le p), one_mul]
  exact pow_le_pow_of_le_one hr.1.le hr.2 hpq

/-- The differentiable expansion immediately implies its second-order truncation. -/
theorem EndpointDifferentiableExpansion.secondOrder {f : ℝ → ℝ}
    {linear quadratic : ℝ}
    (h : EndpointDifferentiableExpansion f linear quadratic) :
    (fun r ↦ f r - linear * r - quadratic * r ^ 2) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ r ^ 3) := by
  obtain ⟨eta, heta, higher, remainder, hEq, _hcont, hR⟩ := h
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      (fun r : ℝ ↦ higher j * r ^ (j.1 + 3)) =O[𝓝[>] (0 : ℝ)]
        (fun r : ℝ ↦ r ^ 3) := by
    intro j _hj
    exact (pow_isBigO_pow_nhdsGT (show 3 ≤ j.1 + 3 by omega)).const_mul_left
      (higher j)
  have hsum : (fun r : ℝ ↦ ∑ j : Fin 3, higher j * r ^ (j.1 + 3))
      =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ 3) := by
    simpa only [Finset.sum_apply] using IsBigO.sum hterm
  have hrem : remainder =O[𝓝[>] (0 : ℝ)] (fun r : ℝ ↦ r ^ 3) := by
    have hzero := hR 0 (by norm_num)
    simpa only [iteratedDeriv_zero, Nat.reduceSub] using
      hzero.trans (pow_isBigO_pow_nhdsGT (show 3 ≤ 6 by norm_num))
  apply (hsum.add hrem).congr'
  · filter_upwards [Ioc_mem_nhdsGT heta] with r hr
    have heq := hEq hr
    unfold endpointPolynomial at heq
    rw [heq]
    ring
  · filter_upwards with r
    rfl

theorem leftEndpoint_secondOrder_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    (fun u ↦ W u - u / lambda - (lambda⁻¹ ^ 4 - lambda⁻¹) * u ^ 2)
      =O[𝓝[>] (0 : ℝ)] (fun u : ℝ ↦ u ^ 3) := by
  have h := (leftEndpointDifferentiableExpansion_exactQuadratic hlambda hsolution
    hexpansion).secondOrder
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem rightEndpoint_secondOrder_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    (fun u ↦ W u - (1 - u) / lambda +
      (lambda⁻¹ ^ 4 + lambda⁻¹) * (1 - u) ^ 2) =O[𝓝[<] (1 : ℝ)]
        (fun u : ℝ ↦ (1 - u) ^ 3) := by
  have hzero := (rightEndpointDifferentiableExpansion_exactQuadratic hlambda
    hsolution hexpansion).secondOrder
  have hcomp := hzero.comp_tendsto tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  apply hcomp.congr'
  · filter_upwards with u
    simp only [Function.comp_apply]
    field_simp [hlambda.ne']
    ring
  · filter_upwards with u
    rfl

/-- `eq:W-relative-derivative-bounds` at the left endpoint. -/
def RelativeDerivativeBoundsAtZero (W : ℝ → ℝ) : Prop :=
  ∃ eta > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Ioc 0 eta,
    |deriv W u| + |W u * iteratedDeriv 2 W u| +
      |W u ^ 2 * iteratedDeriv 3 W u| ≤ C

/-- `eq:W-relative-derivative-bounds` at the right endpoint. -/
def RelativeDerivativeBoundsAtOne (W : ℝ → ℝ) : Prop :=
  ∃ eta > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Ico (1 - eta) 1,
    |deriv W u| + |W u * iteratedDeriv 2 W u| +
      |W u ^ 2 * iteratedDeriv 3 W u| ≤ C

private noncomputable def relativeDerivativeExpressionWithin (W : ℝ → ℝ)
    (s : Set ℝ) (u : ℝ) : ℝ :=
  |iteratedDerivWithin 1 W s u| +
    |W u * iteratedDerivWithin 2 W s u| +
      |W u ^ 2 * iteratedDerivWithin 3 W s u|

private theorem relativeDerivativeExpressionWithin_continuousOn {W : ℝ → ℝ}
    {s : Set ℝ} (hW : ContDiffOn ℝ 4 W s) (hs : UniqueDiffOn ℝ s) :
    ContinuousOn (relativeDerivativeExpressionWithin W s) s := by
  have hWc := hW.continuousOn
  have h1 := hW.continuousOn_iteratedDerivWithin (m := 1) (by norm_num) hs
  have h2 := hW.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hs
  have h3 := hW.continuousOn_iteratedDerivWithin (m := 3) (by norm_num) hs
  unfold relativeDerivativeExpressionWithin
  exact h1.abs.add (hWc.mul h2).abs |>.add ((hWc.pow 2).mul h3).abs

theorem relativeDerivativeBoundsAtZero_of_contDiffOn {W : ℝ → ℝ} {eta : ℝ}
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hendpoint : ContDiffOn ℝ 4 W (Icc (0 : ℝ) eta))
    (hinterior : ContDiffOn ℝ 4 W (Ioo (0 : ℝ) 1)) :
    RelativeDerivativeBoundsAtZero W := by
  let B := relativeDerivativeExpressionWithin W (Icc (0 : ℝ) eta)
  have hBcont : ContinuousOn B (Icc (0 : ℝ) eta) :=
    relativeDerivativeExpressionWithin_continuousOn hendpoint
      (uniqueDiffOn_Icc heta)
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) eta).Nonempty from ⟨0, ⟨le_rfl, heta.le⟩⟩) hBcont
  refine ⟨eta, heta, B x, ?_, ?_⟩
  · dsimp only [B, relativeDerivativeExpressionWithin]
    positivity
  · intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) eta := ⟨hu.1.le, hu.2⟩
    have huOpen : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_lt hetaOne⟩
    have hWat : ContDiffAt ℝ 4 W u :=
      (hinterior u huOpen).contDiffAt (isOpen_Ioo.mem_nhds huOpen)
    have heq (m : ℕ) (hm : m ≤ 4) :
        iteratedDerivWithin m W (Icc (0 : ℝ) eta) u = iteratedDeriv m W u :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc heta)
        (hWat.of_le (by exact_mod_cast hm)) huIcc
    have hbound := hmax huIcc
    change B u ≤ B x at hbound
    dsimp only [B, relativeDerivativeExpressionWithin] at hbound ⊢
    rw [heq 1 (by norm_num), heq 2 (by norm_num), heq 3 (by norm_num),
      iteratedDeriv_one] at hbound
    exact hbound

theorem relativeDerivativeBoundsAtOne_of_contDiffOn {W : ℝ → ℝ} {eta : ℝ}
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hendpoint : ContDiffOn ℝ 4 W (Icc (1 - eta) 1))
    (hinterior : ContDiffOn ℝ 4 W (Ioo (0 : ℝ) 1)) :
    RelativeDerivativeBoundsAtOne W := by
  let B := relativeDerivativeExpressionWithin W (Icc (1 - eta) 1)
  have hleft : 1 - eta ≤ 1 := by linarith
  have hBcont : ContinuousOn B (Icc (1 - eta) 1) :=
    relativeDerivativeExpressionWithin_continuousOn hendpoint
      (uniqueDiffOn_Icc (by linarith))
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 - eta) 1).Nonempty from ⟨1, ⟨hleft, le_rfl⟩⟩) hBcont
  refine ⟨eta, heta, B x, ?_, ?_⟩
  · dsimp only [B, relativeDerivativeExpressionWithin]
    positivity
  · intro u hu
    have huIcc : u ∈ Icc (1 - eta) 1 := ⟨hu.1, hu.2.le⟩
    have huOpen : u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1, hetaOne], hu.2⟩
    have hWat : ContDiffAt ℝ 4 W u :=
      (hinterior u huOpen).contDiffAt (isOpen_Ioo.mem_nhds huOpen)
    have heq (m : ℕ) (hm : m ≤ 4) :
        iteratedDerivWithin m W (Icc (1 - eta) 1) u = iteratedDeriv m W u :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
        (hWat.of_le (by exact_mod_cast hm)) huIcc
    have hbound := hmax huIcc
    change B u ≤ B x at hbound
    dsimp only [B, relativeDerivativeExpressionWithin] at hbound ⊢
    rw [heq 1 (by norm_num), heq 2 (by norm_num), heq 3 (by norm_num),
      iteratedDeriv_one] at hbound
    exact hbound

/-- The complete left-endpoint conclusion, including
`λ⁻⁴-λ⁻¹` from `eq:W-expansion-zero`. -/
structure LeftLinearBranchRegularity (lambda : ℝ) (W : ℝ → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 4 W (Ico 0 1)
  differentiableExpansion :
    EndpointDifferentiableExpansion W lambda⁻¹ (lambda⁻¹ ^ 4 - lambda⁻¹)
  secondOrder :
    (fun u ↦ W u - u / lambda - (lambda⁻¹ ^ 4 - lambda⁻¹) * u ^ 2) =O[𝓝[>] 0]
      (fun u : ℝ ↦ u ^ 3)
  relativeDerivativeBounds : RelativeDerivativeBoundsAtZero W

/-- The complete right-endpoint conclusion, including
`-(λ⁻⁴+λ⁻¹)` from `eq:W-expansion-one`. -/
structure RightLinearBranchRegularity (lambda : ℝ) (W : ℝ → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 4 W (Ioc 0 1)
  differentiableExpansion : EndpointDifferentiableExpansion
    (fun r ↦ W (1 - r)) lambda⁻¹ (-(lambda⁻¹ ^ 4 + lambda⁻¹))
  secondOrder :
    (fun u ↦ W u - (1 - u) / lambda +
      (lambda⁻¹ ^ 4 + lambda⁻¹) * (1 - u) ^ 2) =O[𝓝[<] 1]
        (fun u : ℝ ↦ (1 - u) ^ 3)
  relativeDerivativeBounds : RelativeDerivativeBoundsAtOne W

/-- The source quantifies the two endpoint implications separately: an endpoint is
asserted only when its corresponding linear asymptotic is available. -/
structure LinearBranchRegularityConclusion (lambda : ℝ) (W : ℝ → ℝ) : Prop where
  atZero : HasLinearBranchAtZero lambda W → LeftLinearBranchRegularity lambda W
  atOne : HasLinearBranchAtOne lambda W → RightLinearBranchRegularity lambda W

theorem leftEndpoint_relativeDerivativeBounds_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hzero : W 0 = 0)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    RelativeDerivativeBoundsAtZero W := by
  obtain ⟨eta, heta, hlocal⟩ :=
    leftEndpoint_localContDiffOn_of_finiteAsymptoticExpansion hsolution hzero hexpansion
  let eps := min eta (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min heta (by norm_num)
  have hepsOne : eps < 1 := lt_of_le_of_lt (min_le_right eta (1 / 2 : ℝ)) (by norm_num)
  have hlocal' : ContDiffOn ℝ 4 W (Icc 0 eps) := by
    apply hlocal.mono
    intro u hu
    exact ⟨hu.1, hu.2.trans (min_le_left eta (1 / 2 : ℝ))⟩
  exact relativeDerivativeBoundsAtZero_of_contDiffOn heps hepsOne hlocal'
    ((hsolution.contDiffOn_infty_interior).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top _)))

theorem rightEndpoint_relativeDerivativeBounds_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W) (hone : W 1 = 0)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    RelativeDerivativeBoundsAtOne W := by
  obtain ⟨eta, heta, hlocal⟩ :=
    rightEndpoint_localContDiffOn_of_finiteAsymptoticExpansion hsolution hone hexpansion
  let eps := min eta (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min heta (by norm_num)
  have hepsOne : eps < 1 := lt_of_le_of_lt (min_le_right eta (1 / 2 : ℝ)) (by norm_num)
  have hlocal' : ContDiffOn ℝ 4 W (Icc (1 - eps) 1) := by
    have hepsle : eps ≤ eta := min_le_left eta (1 / 2 : ℝ)
    apply hlocal.mono
    intro u hu
    constructor
    · linarith [hu.1, hepsle]
    · exact hu.2
  exact relativeDerivativeBoundsAtOne_of_contDiffOn heps hepsOne hlocal'
    ((hsolution.contDiffOn_infty_interior).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top _)))

/-- B2 assembled from one invocation of the finite asymptotic ODE theorem at the
left rescaling. -/
theorem leftLinearBranchRegularity_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W) (hzero : W 0 = 0)
    (hexpansion : FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹) :
    LeftLinearBranchRegularity lambda W := by
  refine ⟨leftLinearBranch_contDiffOn hsolution hzero hexpansion,
    leftEndpointDifferentiableExpansion_exactQuadratic hlambda hsolution hexpansion,
    leftEndpoint_secondOrder_of_finiteAsymptoticExpansion hlambda hsolution hexpansion,
    leftEndpoint_relativeDerivativeBounds_of_finiteAsymptoticExpansion hsolution hzero
      hexpansion⟩

/-- The symmetric right-rescaling assembly. -/
theorem rightLinearBranchRegularity_of_finiteAsymptoticExpansion
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hsolution : IsPositiveWSolution lambda W) (hone : W 1 = 0)
    (hexpansion : FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    RightLinearBranchRegularity lambda W := by
  refine ⟨rightLinearBranch_contDiffOn hsolution hone hexpansion,
    rightEndpointDifferentiableExpansion_exactQuadratic hlambda hsolution hexpansion,
    rightEndpoint_secondOrder_of_finiteAsymptoticExpansion hlambda hsolution hexpansion,
    rightEndpoint_relativeDerivativeBounds_of_finiteAsymptoticExpansion hsolution hone
      hexpansion⟩

/-- Header-stable assembly point: once B1 supplies the two rescaled expansions,
no further analytic input is needed. -/
theorem linearBranchRegularity_of_expansions {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hzero : W 0 = 0) (hone : W 1 = 0)
    (hleft : HasLinearBranchAtZero lambda W →
      FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
        leftRescaledPerturbation (leftRescaling W) lambda⁻¹)
    (hright : HasLinearBranchAtOne lambda W →
      FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
        rightRescaledPerturbation (rightRescaling W) lambda⁻¹) :
    LinearBranchRegularityConclusion lambda W := by
  exact ⟨fun hlinear ↦ leftLinearBranchRegularity_of_finiteAsymptoticExpansion
      hlambda hsolution hzero (hleft hlinear),
    fun hlinear ↦ rightLinearBranchRegularity_of_finiteAsymptoticExpansion
      hlambda hsolution hone (hright hlinear)⟩

/-- The B1 expansion specialized to the left endpoint rescaling. -/
noncomputable def leftFiniteAsymptoticExpansion {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtZero lambda W) :
    FiniteAsymptoticExpansion (leftRescaledAutonomous lambda)
      leftRescaledPerturbation (leftRescaling W) lambda⁻¹ := by
  obtain ⟨hIopen, hyStar, hT0, hYmap, hYc1, hYode, hYlim⟩ :=
    leftRescaling_isAsymptoticallyAutonomousSolution hlambda hsolution hlinear
  exact finiteAsymptoticODE (leftRescaledAutonomous lambda) leftRescaledPerturbation
    (leftRescaling W) lambda⁻¹ 2 hIopen ordConnected_Ioi hyStar
    (leftRescaledAutonomous_contDiffOn lambda) leftRescaledPerturbation_contDiffOn
    (leftRescaledAutonomous_at_fixedPoint hlambda)
    (by
      rw [leftRescaledAutonomous_deriv_fixedPoint hlambda]
      exact neg_ne_zero.mpr (pow_ne_zero 3 hlambda.ne'))
    hT0 hYmap hYc1 hYode hYlim

/-- The B1 expansion specialized to the right endpoint rescaling. -/
noncomputable def rightFiniteAsymptoticExpansion {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtOne lambda W) :
    FiniteAsymptoticExpansion (rightRescaledAutonomous lambda)
      rightRescaledPerturbation (rightRescaling W) lambda⁻¹ := by
  obtain ⟨hIopen, hyStar, hT0, hYmap, hYc1, hYode, hYlim⟩ :=
    rightRescaling_isAsymptoticallyAutonomousSolution hlambda hsolution hlinear
  exact finiteAsymptoticODE (rightRescaledAutonomous lambda) rightRescaledPerturbation
    (rightRescaling W) lambda⁻¹ 2 hIopen ordConnected_Ioi hyStar
    (rightRescaledAutonomous_contDiffOn lambda) rightRescaledPerturbation_contDiffOn
    (rightRescaledAutonomous_at_fixedPoint hlambda)
    (by
      rw [rightRescaledAutonomous_deriv_fixedPoint hlambda]
      exact pow_ne_zero 3 hlambda.ne')
    hT0 hYmap hYc1 hYode hYlim

/-- The source-facing left half of `lem:linear-branch-regularity`. -/
theorem leftLinearBranchRegularity {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hzero : W 0 = 0) (hlinear : HasLinearBranchAtZero lambda W) :
    LeftLinearBranchRegularity lambda W := by
  exact leftLinearBranchRegularity_of_finiteAsymptoticExpansion hlambda hsolution hzero
    (leftFiniteAsymptoticExpansion hlambda hsolution hlinear)

/-- The source-facing right half of `lem:linear-branch-regularity`.  Unlike a
two-point boundary package, these hypotheses apply directly to the subcritical
shooting solution, for which `W 0 > 0` but `W 1 = 0`. -/
theorem rightLinearBranchRegularity {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W)
    (hone : W 1 = 0) (hlinear : HasLinearBranchAtOne lambda W) :
    RightLinearBranchRegularity lambda W := by
  exact rightLinearBranchRegularity_of_finiteAsymptoticExpansion hlambda hsolution hone
    (rightFiniteAsymptoticExpansion hlambda hsolution hlinear)

/-- The left linear asymptotic and continuity on the closed unit interval force the
endpoint value.  Thus `W 0 = 0` is a consequence, not a B2 hypothesis. -/
theorem HasLinearBranchAtZero.endpoint_eq_zero {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtZero lambda W) : W 0 = 0 := by
  have hmodel : Tendsto (fun u : ℝ ↦ u / lambda)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto (fun u : ℝ ↦ u / lambda) (𝓝 (0 : ℝ))
        (𝓝 ((0 : ℝ) / lambda)) := tendsto_id.div_const lambda
    simpa only [zero_div] using hfull.mono_left nhdsWithin_le_nhds
  have hWzero : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hlinear.symm.tendsto_nhds hmodel
  have hsets : Icc (0 : ℝ) 1 =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
    apply propext
    change (0 ≤ u ∧ u ≤ 1) ↔ 0 ≤ u
    constructor
    · exact fun h ↦ h.1
    · exact fun h ↦ ⟨h, hu.le⟩
  have hcontIci : ContinuousWithinAt W (Ici 0) 0 :=
    (hsolution.continuousOn 0 (by simp [unitInterval])).congr_set hsets
  have hWvalue : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) :=
    hcontIci.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  exact tendsto_nhds_unique hWvalue hWzero

/-- The right linear asymptotic and continuity on the closed unit interval force the
endpoint value.  Thus `W 1 = 0` is a consequence, not a B2 hypothesis. -/
theorem HasLinearBranchAtOne.endpoint_eq_zero {lambda : ℝ} {W : ℝ → ℝ}
    (hsolution : IsPositiveWSolution lambda W)
    (hlinear : HasLinearBranchAtOne lambda W) : W 1 = 0 := by
  have hmodel : Tendsto (fun u : ℝ ↦ (1 - u) / lambda)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto (fun u : ℝ ↦ (1 - u) / lambda) (𝓝 (1 : ℝ))
        (𝓝 ((1 - 1 : ℝ) / lambda)) :=
      (tendsto_const_nhds.sub tendsto_id).div_const lambda
    simpa only [sub_self, zero_div] using hfull.mono_left nhdsWithin_le_nhds
  have hWzero : Tendsto W (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    hlinear.symm.tendsto_nhds hmodel
  have hsets : Icc (0 : ℝ) 1 =ᶠ[𝓝 (1 : ℝ)] Iic 1 := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
    apply propext
    change (0 ≤ u ∧ u ≤ 1) ↔ u ≤ 1
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hu.le, h⟩
  have hcontIic : ContinuousWithinAt W (Iic 1) 1 :=
    (hsolution.continuousOn 1 (by simp [unitInterval])).congr_set hsets
  have hWvalue : Tendsto W (𝓝[<] (1 : ℝ)) (𝓝 (W 1)) :=
    hcontIic.tendsto.mono_left (nhdsWithin_mono 1 Iio_subset_Iic_self)
  exact tendsto_nhds_unique hWvalue hWzero

/-- Exact source-facing left implication of B2.  Its only mathematical hypotheses
are `0 < lambda` and `IsPositiveWSolution lambda W`. -/
theorem leftLinearBranchRegularity_source {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W) :
    HasLinearBranchAtZero lambda W → LeftLinearBranchRegularity lambda W := by
  intro hlinear
  exact leftLinearBranchRegularity hlambda hsolution
    (hlinear.endpoint_eq_zero hsolution) hlinear

/-- Exact source-facing right implication of B2.  Its only mathematical hypotheses
are `0 < lambda` and `IsPositiveWSolution lambda W`. -/
theorem rightLinearBranchRegularity_source {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W) :
    HasLinearBranchAtOne lambda W → RightLinearBranchRegularity lambda W := by
  intro hlinear
  exact rightLinearBranchRegularity hlambda hsolution
    (hlinear.endpoint_eq_zero hsolution) hlinear

/-- Exact two-implication package for `lem:linear-branch-regularity` (B2). -/
theorem linearBranchRegularity_source {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsPositiveWSolution lambda W) :
    LinearBranchRegularityConclusion lambda W :=
  ⟨leftLinearBranchRegularity_source hlambda hsolution,
    rightLinearBranchRegularity_source hlambda hsolution⟩

/-- The canonical shooting transform satisfies the endpoint-independent B2
hypotheses for every positive parameter. -/
theorem WSolution_isPositiveWSolution (lambda : ℝ) (hlambda : 0 < lambda) :
    IsPositiveWSolution lambda (WSolution lambda hlambda) :=
  ⟨WSolution_continuousOn lambda hlambda, WSolution_contDiffOn_one lambda hlambda,
    WSolution_satisfiesWODEAt lambda hlambda, WSolution_pos lambda hlambda⟩

/-- Direct right-endpoint regularity wrapper used by the subcritical profile. -/
theorem WSolution_rightLinearBranchRegularity (lambda : ℝ) (hlambda : 0 < lambda)
    (hlinear : HasLinearBranchAtOne lambda (WSolution lambda hlambda)) :
    RightLinearBranchRegularity lambda (WSolution lambda hlambda) :=
  rightLinearBranchRegularity hlambda (WSolution_isPositiveWSolution lambda hlambda)
    (WSolution_one lambda hlambda) hlinear

/-- `lem:linear-branch-regularity` for the two-point boundary solution API.  The
endpoint-specific theorems above are the broader source-facing interface. -/
theorem linearBranchRegularity {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsolution : IsWBoundarySolution lambda W) :
    LinearBranchRegularityConclusion lambda W := by
  let hpositive := hsolution.isPositiveWSolution
  exact linearBranchRegularity_of_expansions hlambda hpositive
    hsolution.2.2.2.2.1 hsolution.2.2.2.2.2.1
    (leftFiniteAsymptoticExpansion hlambda hpositive)
    (rightFiniteAsymptoticExpansion hlambda hpositive)

end SeriesParallel.Appendix
