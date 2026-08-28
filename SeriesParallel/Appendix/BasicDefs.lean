import SeriesParallel.RealCubeRoot
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Basic definitions for the two appendices

This file fixes the source-facing meanings of the two scalar ODEs, their boundary
conditions, the signed cube-root change of variables, the residual used in comparison
arguments, and the two possible left-endpoint asymptotic branches.  Functions are kept
as maps `ℝ → ℝ`; domains are recorded by explicit set predicates.
-/

open Asymptotics Filter Set
open scoped Topology

namespace SeriesParallel.Appendix

/-- The closed interval on which the shooting and boundary-value problems live. -/
def unitInterval : Set ℝ := Icc 0 1

/-- The open interval on which the appendix imposes the differential equations. -/
def openUnitInterval : Set ℝ := Ioo 0 1

/-- Clamp a real argument to `[0,1]`. -/
def unitClamp (t : ℝ) : ℝ := max 0 (min 1 t)

/-- Canonical representation of a function whose mathematical domain is `[0,1]`.
Outside that interval the representative is held constant at the nearest endpoint.  This
normalization lets source-level uniqueness on `[0,1]` be recorded by Lean's literal `∃!`
while all analytic hypotheses still name their domains explicitly. -/
def IsCanonicalUnitExtension (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, f t = f (unitClamp t)

theorem unitClamp_eq_self {t : ℝ} (ht : t ∈ unitInterval) : unitClamp t = t := by
  rcases ht with ⟨ht0, ht1⟩
  simp [unitClamp, ht0, ht1]

theorem unitClamp_mem_unitInterval (t : ℝ) : unitClamp t ∈ unitInterval := by
  constructor
  · exact le_max_left 0 (min 1 t)
  · exact max_le (by norm_num) (min_le_left 1 t)

@[simp]
theorem unitClamp_idempotent (t : ℝ) : unitClamp (unitClamp t) = unitClamp t :=
  unitClamp_eq_self (unitClamp_mem_unitInterval t)

/-- Reflection about the midpoint commutes with clamping to `[0,1]`. -/
theorem unitClamp_one_sub (t : ℝ) : unitClamp (1 - t) = 1 - unitClamp t := by
  by_cases ht0 : t ≤ 0
  · have ht1 : t ≤ 1 := ht0.trans (by norm_num)
    have hreflect : 1 ≤ 1 - t := by linarith
    simp [unitClamp, min_eq_right ht1, max_eq_left ht0,
      min_eq_left hreflect]
  · have ht0' : 0 ≤ t := le_of_not_ge ht0
    by_cases ht1 : t ≤ 1
    · have hreflect0 : 0 ≤ 1 - t := by linarith
      have hreflect1 : 1 - t ≤ 1 := by linarith
      rw [unitClamp_eq_self ⟨hreflect0, hreflect1⟩,
        unitClamp_eq_self ⟨ht0', ht1⟩]
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hreflect : 1 - t ≤ 0 := by linarith
      have hreflect1 : 1 - t ≤ 1 := by linarith
      simp [unitClamp, min_eq_left ht1', min_eq_right hreflect1,
        max_eq_left hreflect]

/-- Turn an arbitrary representative into the canonical constant endpoint extension. -/
def canonicalUnitExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ f (unitClamp t)

theorem canonicalUnitExtension_isCanonical (f : ℝ → ℝ) :
    IsCanonicalUnitExtension (canonicalUnitExtension f) := by
  intro t
  simp [canonicalUnitExtension]

theorem canonicalUnitExtension_eq_on_unitInterval (f : ℝ → ℝ) :
    EqOn (canonicalUnitExtension f) f unitInterval := by
  intro t ht
  simp [canonicalUnitExtension, unitClamp_eq_self ht]

theorem eq_of_eqOn_unitInterval_of_canonical {f g : ℝ → ℝ}
    (hf : IsCanonicalUnitExtension f) (hg : IsCanonicalUnitExtension g)
    (hfg : EqOn f g unitInterval) : f = g := by
  funext t
  rw [hf t, hg t]
  exact hfg (unitClamp_mem_unitInterval t)

/-- Right-hand side of `eq:y-ODE` / `eq:y-shooting`. -/
noncomputable def yRhs (lambda t y : ℝ) : ℝ :=
  3 * t * (1 - t) - 3 * lambda * Real.cbrt y

/-- The nonautonomous forcing in the shooting equation. -/
def shootingForcing (t : ℝ) : ℝ :=
  3 * t * (1 - t)

theorem yRhs_eq_forcing_sub (lambda t y : ℝ) :
    yRhs lambda t y = shootingForcing t - 3 * lambda * Real.cbrt y := rfl

/-- The shooting vector field is continuous even at `y=0`; this is why Peano applies. -/
theorem continuous_yRhs (lambda : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ yRhs lambda p.1 p.2) := by
  apply Continuous.sub
  · fun_prop
  · exact continuous_const.mul (Real.continuous_cbrt.comp continuous_snd)

theorem shootingForcing_nonneg {t : ℝ} (ht : t ∈ unitInterval) :
    0 ≤ shootingForcing t := by
  rcases ht with ⟨ht0, ht1⟩
  dsimp [shootingForcing]
  positivity

theorem shootingForcing_le_three_quarters {t : ℝ} (ht : t ∈ unitInterval) :
    shootingForcing t ≤ 3 / 4 := by
  rcases ht with ⟨ht0, ht1⟩
  dsimp [shootingForcing]
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- The shooting field satisfies the linear-growth estimate used by the finite-horizon
global Peano theorem. -/
theorem yRhs_abs_le_linear_growth {lambda : ℝ} (hlambda : 0 < lambda) {t : ℝ}
    (ht : t ∈ unitInterval) (y : ℝ) :
    |yRhs lambda t y| ≤ (3 / 4 + 3 * lambda) + 3 * lambda * |y| := by
  have hforcing_nonneg := shootingForcing_nonneg ht
  have hforcing_le := shootingForcing_le_three_quarters ht
  rw [yRhs_eq_forcing_sub]
  calc
    |shootingForcing t - 3 * lambda * Real.cbrt y| ≤
        |shootingForcing t| + |3 * lambda * Real.cbrt y| := abs_sub _ _
    _ = shootingForcing t + 3 * lambda * |Real.cbrt y| := by
      rw [abs_of_nonneg hforcing_nonneg, abs_mul, abs_mul, abs_of_nonneg, abs_of_pos hlambda]
      · norm_num
    _ ≤ 3 / 4 + 3 * lambda * (1 + |y|) := by
      exact add_le_add hforcing_le <|
        mul_le_mul_of_nonneg_left (Real.abs_cbrt_le_one_add_abs y) (by positivity)
    _ = (3 / 4 + 3 * lambda) + 3 * lambda * |y| := by ring

/-- `eq:y-ODE` at one interior point, expressed with an actual derivative witness. -/
def SatisfiesYODEAt (lambda : ℝ) (y : ℝ → ℝ) (t : ℝ) : Prop :=
  HasDerivAt y (yRhs lambda t (y t)) t

/-- A `C([0,1]) ∩ C¹((0,1))` solution of `eq:y-shooting`. -/
def IsShootingSolution (lambda : ℝ) (y : ℝ → ℝ) : Prop :=
  IsCanonicalUnitExtension y ∧
    ContinuousOn y unitInterval ∧
    ContDiffOn ℝ 1 y openUnitInterval ∧
    y 0 = 0 ∧
    ∀ t ∈ openUnitInterval, SatisfiesYODEAt lambda y t

/-- The boundary conditions in `eq:y-boundary`. -/
def SatisfiesYBoundary (y : ℝ → ℝ) : Prop :=
  y 0 = 0 ∧ y 1 = 0 ∧ ∀ t ∈ openUnitInterval, 0 < y t

/-- A solution of the transformed two-point boundary-value problem. -/
def IsYBoundarySolution (lambda : ℝ) (y : ℝ → ℝ) : Prop :=
  IsShootingSolution lambda y ∧ SatisfiesYBoundary y

/-- The left-hand side of `eq:W-ode`, with the derivative supplied explicitly. -/
def wODEValue (lambda w dw u : ℝ) : ℝ :=
  w ^ 2 * dw - lambda * w + u * (1 - u)

/-- `eq:W-ode` at one interior point. -/
def SatisfiesWODEAt (lambda : ℝ) (W : ℝ → ℝ) (u : ℝ) : Prop :=
  DifferentiableAt ℝ W u ∧ wODEValue lambda (W u) (deriv W u) u = 0

/-- The boundary and positivity conditions in `eq:W-boundary`. -/
def SatisfiesWBoundary (W : ℝ → ℝ) : Prop :=
  W 0 = 0 ∧ W 1 = 0 ∧ ∀ u ∈ openUnitInterval, 0 < W u

/-- A `C([0,1]) ∩ C¹((0,1))` positive solution of `eq:W-ode` and
`eq:W-boundary`. -/
def IsWBoundarySolution (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  IsCanonicalUnitExtension W ∧
    ContinuousOn W unitInterval ∧
    ContDiffOn ℝ 1 W openUnitInterval ∧
    (∀ u ∈ openUnitInterval, SatisfiesWODEAt lambda W u) ∧
    SatisfiesWBoundary W

/-- The cube transformation `y(t) = W(1-t)^3`. -/
def yOfW (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  W (1 - t) ^ 3

/-- The inverse transformation `W(u) = cbrt (y(1-u))`. -/
noncomputable def wOfY (y : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.cbrt (y (1 - u))

@[simp]
theorem yOfW_wOfY (y : ℝ → ℝ) (t : ℝ) : yOfW (wOfY y) t = y t := by
  simp [yOfW, wOfY]

@[simp]
theorem wOfY_yOfW (W : ℝ → ℝ) (u : ℝ) : wOfY (yOfW W) u = W u := by
  simp [wOfY, yOfW]

/-- Purely algebraic residual underlying the source's `𝓡_λ[w]`.  It is deliberately
unrestricted, so it can also be used on shifted intervals later in the appendix. -/
def residualValue (lambda w dw t : ℝ) : ℝ :=
  w ^ 2 * dw + lambda * w - t * (1 - t)

/-- Differentiating a cube supplies the derivative used in the residual identity. -/
theorem hasDerivAt_cube {w : ℝ → ℝ} {dw t : ℝ} (hw : HasDerivAt w dw t) :
    HasDerivAt (w ^ (3 : ℕ)) (3 * w t ^ 2 * dw) t := by
  simpa only [Nat.cast_ofNat, Nat.reduceSub] using hw.pow 3

/-- The algebraic identity following the source definition of `𝓡_λ[w]`:
`z' - (3t(1-t)-3λ z^(1/3)) = 3𝓡_λ[w]` for `z=w³`. -/
theorem cube_ode_defect_eq_three_residual (lambda : ℝ) (w dw t : ℝ) :
    3 * w ^ 2 * dw - yRhs lambda t (w ^ 3) =
      3 * residualValue lambda w dw t := by
  simp only [yRhs, residualValue, Real.cbrt_cube']
  ring

/-- A nonpositive residual gives the corresponding cube-root ODE subsolution
inequality, pointwise. -/
theorem cube_subsolution_of_residual_nonpos {lambda w dw t : ℝ}
    (hR : residualValue lambda w dw t ≤ 0) :
    3 * w ^ 2 * dw ≤ yRhs lambda t (w ^ 3) := by
  have h := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 3) hR
  rw [← cube_ode_defect_eq_three_residual] at h
  linarith

/-- A nonnegative residual gives the corresponding cube-root ODE supersolution
inequality, pointwise. -/
theorem cube_supersolution_of_residual_nonneg {lambda w dw t : ℝ}
    (hR : 0 ≤ residualValue lambda w dw t) :
    yRhs lambda t (w ^ 3) ≤ 3 * w ^ 2 * dw := by
  have h := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hR
  rw [← cube_ode_defect_eq_three_residual] at h
  linarith

/-- A cube-root subsolution on `[t₀,t₁]`, as in `lem:cuberoot-comparison`. -/
def IsCubeRootSubsolutionOn (a : ℝ → ℝ) (b : ℝ) (y : ℝ → ℝ)
    (t0 t1 : ℝ) : Prop :=
  ContinuousOn y (Icc t0 t1) ∧
    ∀ t ∈ Ioo t0 t1,
      ∃ dy : ℝ, HasDerivAt y dy t ∧ dy ≤ a t - b * Real.cbrt (y t)

/-- A cube-root supersolution on `[t₀,t₁]`, as in `lem:cuberoot-comparison`. -/
def IsCubeRootSupersolutionOn (a : ℝ → ℝ) (b : ℝ) (y : ℝ → ℝ)
    (t0 t1 : ℝ) : Prop :=
  ContinuousOn y (Icc t0 t1) ∧
    ∀ t ∈ Ioo t0 t1,
      ∃ dy : ℝ, HasDerivAt y dy t ∧ a t - b * Real.cbrt (y t) ≤ dy

/-- The source-facing `C([t₀,t₁]) ∩ C¹((t₀,t₁))` subsolution predicate.  The explicit
derivative witness prevents any use of the default value of `deriv` at a nonsmooth point. -/
def IsCubeRootC1SubsolutionOn (a : ℝ → ℝ) (b : ℝ) (y : ℝ → ℝ)
    (t0 t1 : ℝ) : Prop :=
  ContinuousOn y (Icc t0 t1) ∧
    ContDiffOn ℝ 1 y (Ioo t0 t1) ∧
    ∀ t ∈ Ioo t0 t1,
      ∃ dy : ℝ, HasDerivAt y dy t ∧ dy ≤ a t - b * Real.cbrt (y t)

/-- The source-facing `C([t₀,t₁]) ∩ C¹((t₀,t₁))` supersolution predicate. -/
def IsCubeRootC1SupersolutionOn (a : ℝ → ℝ) (b : ℝ) (y : ℝ → ℝ)
    (t0 t1 : ℝ) : Prop :=
  ContinuousOn y (Icc t0 t1) ∧
    ContDiffOn ℝ 1 y (Ioo t0 t1) ∧
    ∀ t ∈ Ioo t0 t1,
      ∃ dy : ℝ, HasDerivAt y dy t ∧ a t - b * Real.cbrt (y t) ≤ dy

theorem IsCubeRootC1SubsolutionOn.toSubsolutionOn {a y : ℝ → ℝ} {b t0 t1 : ℝ}
    (h : IsCubeRootC1SubsolutionOn a b y t0 t1) :
    IsCubeRootSubsolutionOn a b y t0 t1 :=
  ⟨h.1, h.2.2⟩

theorem IsCubeRootC1SupersolutionOn.toSupersolutionOn {a y : ℝ → ℝ} {b t0 t1 : ℝ}
    (h : IsCubeRootC1SupersolutionOn a b y t0 t1) :
    IsCubeRootSupersolutionOn a b y t0 t1 :=
  ⟨h.1, h.2.2⟩

/-- The zero function is the source's basic subsolution of the shooting equation. -/
theorem zero_isShootingSubsolution (lambda : ℝ) :
    IsCubeRootSubsolutionOn shootingForcing (3 * lambda) (fun _ : ℝ ↦ 0) 0 1 := by
  constructor
  · exact continuous_const.continuousOn
  · intro t ht
    refine ⟨0, hasDerivAt_const t 0, ?_⟩
    simp only [Real.cbrt_zero, mul_zero, sub_zero]
    exact shootingForcing_nonneg ⟨ht.1.le, ht.2.le⟩

/-- The linear branch in `eq:u0-linear`, using the strict right-hand filter at zero. -/
def HasLinearBranchAtZero (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  (fun u : ℝ ↦ W u) ~[𝓝[>] (0 : ℝ)] (fun u : ℝ ↦ u / lambda)

/-- The square-root branch in `eq:u0-sharp`, using the strict right-hand filter at zero. -/
def HasSharpBranchAtZero (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  (fun u : ℝ ↦ W u) ~[𝓝[>] (0 : ℝ)]
    (fun u : ℝ ↦ Real.sqrt (2 * lambda * u))

/-- The universal linear behavior at `u=1` from `lem:linear-u1`. -/
def HasLinearBranchAtOne (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  (fun u : ℝ ↦ W u) ~[𝓝[<] (1 : ℝ)] (fun u : ℝ ↦ (1 - u) / lambda)

/-- Both source alternatives, bundled as the exclusive disjunction required by
`lem:u0-dichotomy`. -/
def HasExactlyOneLeftBranch (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  Xor (HasLinearBranchAtZero lambda W) (HasSharpBranchAtZero lambda W)

end SeriesParallel.Appendix
