import SeriesParallel.Appendix.AdmissibleParameters
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Endpoint asymptotics of the shooting solution

This file formalizes the linear behavior at `u = 1` from `lem:linear-u1`.
The proof follows the source: cubes of the linear barriers `k t` are compared
with the shooting solution near its initial point.
-/

open Asymptotics Filter Set
open scoped Topology

namespace SeriesParallel.Appendix

/-- The source's endpoint barrier `w(t)=kt`. -/
def endpointLinearBarrier (k t : ℝ) : ℝ :=
  k * t

/-- The cube of the endpoint barrier, compared directly with `shootingY`. -/
def endpointLinearBarrierCube (k t : ℝ) : ℝ :=
  endpointLinearBarrier k t ^ 3

/-- The exact residual calculation in the proof of `lem:linear-u1`. -/
theorem endpointLinearBarrier_residual (lambda k t : ℝ) :
    residualValue lambda (endpointLinearBarrier k t) k t =
      t * (lambda * k - 1) + t ^ 2 * (k ^ 3 + 1) := by
  unfold residualValue endpointLinearBarrier
  ring

theorem endpointLinearBarrier_hasDerivAt (k t : ℝ) :
    HasDerivAt (endpointLinearBarrier k) k t := by
  exact hasDerivAt_const_mul k

theorem endpointLinearBarrierCube_hasDerivAt (k t : ℝ) :
    HasDerivAt (endpointLinearBarrierCube k)
      (3 * endpointLinearBarrier k t ^ 2 * k) t := by
  exact hasDerivAt_cube (endpointLinearBarrier_hasDerivAt k t)

/-- Every slope below `1/λ` gives a cubic subsolution on some right
neighborhood of zero. -/
theorem endpointLinearBarrierCube_isSubsolution {lambda k : ℝ} (hlambda : 0 < lambda)
    (hkpos : 0 < k) (hk : k < lambda⁻¹) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      IsCubeRootSubsolutionOn shootingForcing (3 * lambda)
        (endpointLinearBarrierCube k) 0 delta := by
  have hgap : 0 < 1 - lambda * k := by
    have hmul : lambda * k < lambda * lambda⁻¹ :=
      mul_lt_mul_of_pos_left hk hlambda
    rw [mul_inv_cancel₀ hlambda.ne'] at hmul
    linarith
  have hcoef : 0 < k ^ 3 + 1 := by positivity
  let delta := min 1 ((1 - lambda * k) / (2 * (k ^ 3 + 1)))
  have hdelta : 0 < delta := by
    apply lt_min
    · norm_num
    · positivity
  have hdelta_le : delta ≤ 1 := min_le_left _ _
  refine ⟨delta, hdelta, hdelta_le, ?_⟩
  constructor
  · exact (continuous_const.mul continuous_id).pow 3 |>.continuousOn
  · intro t ht
    refine ⟨3 * endpointLinearBarrier k t ^ 2 * k,
      endpointLinearBarrierCube_hasDerivAt k t, ?_⟩
    apply cube_subsolution_of_residual_nonpos
    rw [endpointLinearBarrier_residual]
    have htbound : t * (k ^ 3 + 1) < (1 - lambda * k) / 2 := calc
      t * (k ^ 3 + 1) < delta * (k ^ 3 + 1) :=
        mul_lt_mul_of_pos_right ht.2 hcoef
      _ ≤ ((1 - lambda * k) / (2 * (k ^ 3 + 1))) * (k ^ 3 + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hcoef.le
      _ = (1 - lambda * k) / 2 := by field_simp [hcoef.ne']
    calc
      t * (lambda * k - 1) + t ^ 2 * (k ^ 3 + 1) =
          t * (lambda * k - 1 + t * (k ^ 3 + 1)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1.le (by linarith)

/-- Every slope above `1/λ` gives a cubic supersolution on `[0,1]`. -/
theorem endpointLinearBarrierCube_isSupersolution {lambda k : ℝ}
    (hlambda : 0 < lambda) (hkpos : 0 < k) (hk : lambda⁻¹ < k) :
    IsCubeRootSupersolutionOn shootingForcing (3 * lambda)
      (endpointLinearBarrierCube k) 0 1 := by
  have hgap : 0 < lambda * k - 1 := by
    have hmul : lambda * lambda⁻¹ < lambda * k :=
      mul_lt_mul_of_pos_left hk hlambda
    rw [mul_inv_cancel₀ hlambda.ne'] at hmul
    linarith
  constructor
  · exact (continuous_const.mul continuous_id).pow 3 |>.continuousOn
  · intro t ht
    refine ⟨3 * endpointLinearBarrier k t ^ 2 * k,
      endpointLinearBarrierCube_hasDerivAt k t, ?_⟩
    apply cube_supersolution_of_residual_nonneg
    rw [endpointLinearBarrier_residual]
    exact add_nonneg (mul_nonneg ht.1.le hgap.le)
      (mul_nonneg (sq_nonneg t) (by positivity))

/-- A subcritical linear barrier lies below the shooting solution near zero. -/
theorem endpointLinearBarrierCube_le_shootingY {lambda k : ℝ} (hlambda : 0 < lambda)
    (hkpos : 0 < k) (hk : k < lambda⁻¹) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ t ∈ Icc 0 delta,
      endpointLinearBarrierCube k t ≤ shootingY lambda hlambda t := by
  obtain ⟨delta, hdelta, hdelta_le, hbarrier⟩ :=
    endpointLinearBarrierCube_isSubsolution hlambda hkpos hk
  have hy := shootingY_isSolution lambda hlambda
  have hycont : ContinuousOn (shootingY lambda hlambda) (Icc 0 delta) :=
    hy.2.1.mono fun t ht ↦ ⟨ht.1, ht.2.trans hdelta_le⟩
  have hyode : ∀ t ∈ Ioo 0 delta, SatisfiesYODEAt lambda
      (shootingY lambda hlambda) t := by
    intro t ht
    exact hy.2.2.2.2 t ⟨ht.1, ht.2.trans_le hdelta_le⟩
  refine ⟨delta, hdelta, hdelta_le, ?_⟩
  exact cuberoot_comparison hdelta ShootingAux.forcing_continuous.continuousOn
    (mul_pos (by norm_num) hlambda) hbarrier
    (ShootingAux.exact_supersolution hycont hyode)
    (by simp [hy.2.2.2.1, endpointLinearBarrierCube, endpointLinearBarrier])

/-- A supercritical linear barrier lies above the shooting solution on `[0,1]`. -/
theorem shootingY_le_endpointLinearBarrierCube {lambda k : ℝ} (hlambda : 0 < lambda)
    (hkpos : 0 < k) (hk : lambda⁻¹ < k) :
    ∀ t ∈ unitInterval, shootingY lambda hlambda t ≤ endpointLinearBarrierCube k t := by
  have hy := shootingY_isSolution lambda hlambda
  exact cuberoot_comparison (by norm_num) ShootingAux.forcing_continuous.continuousOn
    (mul_pos (by norm_num) hlambda)
    (ShootingAux.exact_subsolution hy.2.1 hy.2.2.2.2)
    (endpointLinearBarrierCube_isSupersolution hlambda hkpos hk)
    (by simp [hy.2.2.2.1, endpointLinearBarrierCube, endpointLinearBarrier])

/-- The cube root of the shooting solution, denoted `w_λ` in the source. -/
noncomputable def shootingRoot (lambda : ℝ) (hlambda : 0 < lambda) (t : ℝ) : ℝ :=
  Real.cbrt (shootingY lambda hlambda t)

theorem endpointLinearBarrier_le_shootingRoot {lambda k : ℝ} (hlambda : 0 < lambda)
    (hkpos : 0 < k) (hk : k < lambda⁻¹) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ t ∈ Icc 0 delta,
      endpointLinearBarrier k t ≤ shootingRoot lambda hlambda t := by
  obtain ⟨delta, hdelta, hdelta_le, hbound⟩ :=
    endpointLinearBarrierCube_le_shootingY hlambda hkpos hk
  refine ⟨delta, hdelta, hdelta_le, fun t ht ↦ ?_⟩
  have hcbrt := Real.strictMono_cbrt.monotone (hbound t ht)
  simpa only [endpointLinearBarrierCube, shootingRoot, Real.cbrt_cube'] using hcbrt

theorem shootingRoot_le_endpointLinearBarrier {lambda k : ℝ} (hlambda : 0 < lambda)
    (hkpos : 0 < k) (hk : lambda⁻¹ < k) :
    ∀ t ∈ unitInterval, shootingRoot lambda hlambda t ≤ endpointLinearBarrier k t := by
  intro t ht
  have hcbrt := Real.strictMono_cbrt.monotone
    (shootingY_le_endpointLinearBarrierCube hlambda hkpos hk t ht)
  simpa only [endpointLinearBarrierCube, shootingRoot, Real.cbrt_cube'] using hcbrt

/-- The quotient form of the source limit `w_λ(t)/t → 1/λ`. -/
theorem shootingRoot_div_t_tendsto (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun t ↦ shootingRoot lambda hlambda t / t) (𝓝[>] (0 : ℝ))
      (𝓝 lambda⁻¹) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let kLower := max (lambda⁻¹ - epsilon / 2) (lambda⁻¹ / 2)
  let kUpper := lambda⁻¹ + epsilon / 2
  have hinvpos : 0 < lambda⁻¹ := inv_pos.mpr hlambda
  have hkLowerPos : 0 < kLower := by
    exact lt_of_lt_of_le (half_pos hinvpos) (le_max_right _ _)
  have hkLower : kLower < lambda⁻¹ := by
    apply max_lt
    · linarith
    · linarith
  have hkUpperPos : 0 < kUpper := by
    dsimp [kUpper]
    linarith
  have hkUpper : lambda⁻¹ < kUpper := by
    dsimp [kUpper]
    linarith
  obtain ⟨delta, hdelta, hdelta_le, hlower⟩ :=
    endpointLinearBarrier_le_shootingRoot hlambda hkLowerPos hkLower
  have hlowerEventually : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      kLower ≤ shootingRoot lambda hlambda t / t := by
    filter_upwards [Ioc_mem_nhdsGT hdelta] with t ht
    rw [le_div_iff₀ ht.1]
    simpa only [endpointLinearBarrier] using hlower t ⟨ht.1.le, ht.2⟩
  have hupperEventually : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      shootingRoot lambda hlambda t / t ≤ kUpper := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [div_le_iff₀ ht.1]
    simpa only [endpointLinearBarrier] using
      shootingRoot_le_endpointLinearBarrier hlambda hkUpperPos hkUpper t
        ⟨ht.1.le, ht.2⟩
  filter_upwards [hlowerEventually, hupperEventually] with t htLower htUpper
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hkLowerBound : lambda⁻¹ - epsilon / 2 ≤ kLower := le_max_left _ _
    linarith
  · dsimp [kUpper] at htUpper
    linarith

/-- The asymptotic-equivalence form of the same initial-endpoint limit. -/
theorem shootingRoot_isEquivalent (lambda : ℝ) (hlambda : 0 < lambda) :
    (fun t ↦ shootingRoot lambda hlambda t) ~[𝓝[>] (0 : ℝ)]
      (fun t ↦ t / lambda) := by
  have hdenom : ∀ᶠ t in 𝓝[>] (0 : ℝ), t / lambda ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_ne_zero (ne_of_gt ht) hlambda.ne'
  rw [isEquivalent_iff_tendsto_one hdenom]
  have hratio := shootingRoot_div_t_tendsto lambda hlambda
  have hscaled := (tendsto_const_nhds (x := lambda)).mul hratio
  have heq : ((fun t ↦ shootingRoot lambda hlambda t) / fun t ↦ t / lambda) =ᶠ[
      𝓝[>] (0 : ℝ)] fun t ↦ lambda * (shootingRoot lambda hlambda t / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    change shootingRoot lambda hlambda t / (t / lambda) =
      lambda * (shootingRoot lambda hlambda t / t)
    field_simp [htpos.ne', hlambda.ne']
  exact (tendsto_congr' heq).2 (by
    simpa [mul_inv_cancel₀ hlambda.ne'] using hscaled)

@[simp]
theorem shootingRoot_zero (lambda : ℝ) (hlambda : 0 < lambda) :
    shootingRoot lambda hlambda 0 = 0 := by
  have hy := shootingY_isSolution lambda hlambda
  simp [shootingRoot, hy.2.2.2.1]

/-- The quotient limit is equivalently the right derivative of `w_λ` at zero. -/
theorem shootingRoot_hasDerivWithinAt_zero (lambda : ℝ) (hlambda : 0 < lambda) :
    HasDerivWithinAt (shootingRoot lambda hlambda) lambda⁻¹ (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨ht, htne⟩
      have ht' : 0 ≤ t := ht
      have htne' : t ≠ 0 := by simpa using htne
      exact lt_of_le_of_ne ht' (Ne.symm htne')
    · intro ht
      have ht' : 0 < t := ht
      constructor
      · exact ht'.le
      · simpa using ht'.ne'
  rw [hset]
  refine (tendsto_congr' ?_).2 (shootingRoot_div_t_tendsto lambda hlambda)
  exact Filter.Eventually.of_forall fun t ↦ by
    rw [slope_def_field, shootingRoot_zero]
    ring

/-- The shooting function itself has right derivative zero at its initial endpoint. -/
theorem shootingY_hasDerivWithinAt_zero (lambda : ℝ) (hlambda : 0 < lambda) :
    HasDerivWithinAt (shootingY lambda hlambda) 0 (Ici 0) 0 := by
  have hroot := shootingRoot_hasDerivWithinAt_zero lambda hlambda
  have hcube := hroot.pow 3
  have hcubeZero : HasDerivWithinAt (shootingRoot lambda hlambda ^ (3 : ℕ))
      0 (Ici 0) 0 := hcube.congr_deriv (by simp)
  apply hcubeZero.congr
  · intro t ht
    simp [shootingRoot]
  · simp [shootingRoot]

/-- The source's `W_λ(u)=cbrt(y_λ(1-u))`, defined here without any
admissibility assumption. -/
noncomputable def shootingW (lambda : ℝ) (hlambda : 0 < lambda) : ℝ → ℝ :=
  wOfY (shootingY lambda hlambda)

/-- Reflection sends a left-hand approach to one to a right-hand approach to zero. -/
theorem tendsto_one_sub_nhdsLT_one_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hfull : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hc : ContinuousAt (fun u : ℝ ↦ 1 - u) 1 := by fun_prop
      have hz : (1 : ℝ) - 1 = 0 := by norm_num
      rw [← hz]
      exact hc
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u < 1 := hu
    show 0 < 1 - u
    linarith

/-- `lem:linear-u1`: every positive parameter has the source's linear branch at `u=1`. -/
theorem linearAtOne (lambda : ℝ) (hlambda : 0 < lambda) :
    HasLinearBranchAtOne lambda (shootingW lambda hlambda) := by
  have hcomp := (shootingRoot_isEquivalent lambda hlambda).comp_tendsto
    tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  change (fun u ↦ shootingW lambda hlambda u) ~[𝓝[<] (1 : ℝ)]
    (fun u ↦ (1 - u) / lambda)
  refine (hcomp.congr_left ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun _ ↦ rfl
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

@[simp]
theorem shootingW_one (lambda : ℝ) (hlambda : 0 < lambda) :
    shootingW lambda hlambda 1 = 0 := by
  have hy := shootingY_isSolution lambda hlambda
  simp [shootingW, wOfY, hy.2.2.2.1]

/-- Differential form of `lem:linear-u1`: the left derivative at `u=1` is `-1/λ`. -/
theorem shootingW_hasDerivWithinAt_one (lambda : ℝ) (hlambda : 0 < lambda) :
    HasDerivWithinAt (shootingW lambda hlambda) (-lambda⁻¹) (Iic 1) 1 := by
  have hinner : HasDerivWithinAt (fun u : ℝ ↦ 1 - u) (-1) (Iic 1) 1 :=
    ((hasDerivAt_id (1 : ℝ)).const_sub 1).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ ↦ 1 - u) (Iic 1) (Ici 0) := by
    intro u hu
    have hu' : u ≤ 1 := hu
    exact sub_nonneg.mpr hu'
  have hcomp := (shootingRoot_hasDerivWithinAt_zero lambda hlambda).comp_of_eq
    1 hinner hmaps (by norm_num)
  have hcomp' : HasDerivWithinAt
      (shootingRoot lambda hlambda ∘ fun u : ℝ ↦ 1 - u)
      (-lambda⁻¹) (Iic 1) 1 := hcomp.congr_deriv (by ring)
  apply hcomp'.congr
  · intro u hu
    rfl
  · rfl

/-- Source-facing A5 statement for the canonical `WSolution` notation. -/
theorem WSolution_linearAtOne (lambda : ℝ) (hlambda : 0 < lambda) :
    HasLinearBranchAtOne lambda (WSolution lambda hlambda) := by
  simpa only [shootingW, WSolution] using linearAtOne lambda hlambda

theorem WSolution_hasDerivWithinAt_one (lambda : ℝ) (hlambda : 0 < lambda) :
    HasDerivWithinAt (WSolution lambda hlambda) (-lambda⁻¹) (Iic 1) 1 := by
  simpa only [shootingW, WSolution] using
    shootingW_hasDerivWithinAt_one lambda hlambda

end SeriesParallel.Appendix
