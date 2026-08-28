import SeriesParallel.Appendix.CubeRootComparison
import SeriesParallel.ManualInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The cube-root shooting family

This file formalizes `lem:property of y`: global existence and uniqueness, interior
positivity, strict reverse parameter order, and continuous dependence in the uniform norm.
-/

open Filter Set
open scoped Topology

namespace SeriesParallel.Appendix

namespace ShootingAux

theorem unitClamp_mem (t : ℝ) : unitClamp t ∈ unitInterval := by
  simp [unitClamp, unitInterval]

theorem unitClamp_idem (t : ℝ) : unitClamp (unitClamp t) = unitClamp t :=
  unitClamp_eq_self (unitClamp_mem t)

theorem unitClamp_eventuallyEq {t : ℝ} (ht : t ∈ openUnitInterval) :
    unitClamp =ᶠ[𝓝 t] id := by
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ht
  filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with s hs
  exact unitClamp_eq_self ⟨hs.1.le, hs.2.le⟩

theorem forcing_continuous : Continuous shootingForcing := by
  unfold shootingForcing
  fun_prop

theorem exact_subsolution {lambda t0 t1 : ℝ} {y : ℝ → ℝ}
    (hycont : ContinuousOn y (Icc t0 t1))
    (hyode : ∀ t ∈ Ioo t0 t1, SatisfiesYODEAt lambda y t) :
    IsCubeRootSubsolutionOn shootingForcing (3 * lambda) y t0 t1 := by
  refine ⟨hycont, ?_⟩
  intro t ht
  refine ⟨yRhs lambda t (y t), hyode t ht, ?_⟩
  simp [yRhs_eq_forcing_sub]

theorem exact_supersolution {lambda t0 t1 : ℝ} {y : ℝ → ℝ}
    (hycont : ContinuousOn y (Icc t0 t1))
    (hyode : ∀ t ∈ Ioo t0 t1, SatisfiesYODEAt lambda y t) :
    IsCubeRootSupersolutionOn shootingForcing (3 * lambda) y t0 t1 := by
  refine ⟨hycont, ?_⟩
  intro t ht
  refine ⟨yRhs lambda t (y t), hyode t ht, ?_⟩
  simp [yRhs_eq_forcing_sub]

/-- Direct finite-horizon Peano existence, followed by comparison uniqueness and the
canonical constant endpoint extension. -/
theorem shooting_existsUnique (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃! y : ℝ → ℝ, IsShootingSolution lambda y := by
  let field : ℝ × ℝ → ℝ := fun p ↦ yRhs lambda p.1 p.2
  have hfield : Continuous field := continuous_yRhs lambda
  have hA : 0 ≤ 3 / 4 + 3 * lambda := by positivity
  have hB : 0 ≤ 3 * lambda := by positivity
  have hgrowth : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y : ℝ,
      |field (t, y)| ≤ (3 / 4 + 3 * lambda) + 3 * lambda * |y| := by
    intro t ht y
    simpa [field, unitInterval] using yRhs_abs_le_linear_growth hlambda ht y
  obtain ⟨raw, hraw0, hrawCont, hrawODE⟩ :=
    ManualInterfaces.MI01_global_peano_on_compact_interval field (by norm_num)
      hfield.continuousOn hA hB hgrowth
  let canonical : ℝ → ℝ := canonicalUnitExtension raw
  have hcanonical : IsCanonicalUnitExtension canonical :=
    canonicalUnitExtension_isCanonical raw
  have hcanonicalEq : EqOn canonical raw unitInterval :=
    canonicalUnitExtension_eq_on_unitInterval raw
  have hcanonicalCont : ContinuousOn canonical unitInterval := by
    exact hrawCont.congr hcanonicalEq
  have hcanonicalODE : ∀ t ∈ openUnitInterval,
      SatisfiesYODEAt lambda canonical t := by
    intro t ht
    have heq : canonical =ᶠ[𝓝 t] raw := by
      filter_upwards [unitClamp_eventuallyEq ht] with s hs
      simp [canonical, canonicalUnitExtension, hs]
    simpa [field, SatisfiesYODEAt, canonical, canonicalUnitExtension,
      unitClamp_eq_self ⟨ht.1.le, ht.2.le⟩] using
      (hrawODE t ht).congr_of_eventuallyEq heq
  have hcanonicalC1 : ContDiffOn ℝ 1 canonical openUnitInterval := by
    change ContDiffOn ℝ 1 canonical (Ioo (0 : ℝ) 1)
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo (0 : ℝ) 1)]
    refine ⟨fun t ht ↦
      (hcanonicalODE t ht).differentiableAt.differentiableWithinAt, ?_⟩
    have hrhs : ContinuousOn (fun t ↦ yRhs lambda t (canonical t))
        openUnitInterval := by
      exact hfield.continuousOn.comp
        (continuousOn_id.prodMk (hcanonicalCont.mono Ioo_subset_Icc_self))
        (mapsTo_image (fun t ↦ (t, canonical t)) openUnitInterval)
    exact hrhs.congr fun t ht ↦ by
      rw [derivWithin_of_isOpen isOpen_Ioo ht, (hcanonicalODE t ht).deriv]
  have hcanonical0 : canonical 0 = 0 := by
    simpa [canonical, canonicalUnitExtension, unitClamp] using hraw0
  have hcanonicalSolution : IsShootingSolution lambda canonical :=
    ⟨hcanonical, hcanonicalCont, hcanonicalC1, hcanonical0, hcanonicalODE⟩
  refine ⟨canonical, hcanonicalSolution, ?_⟩
  intro z hz
  have hle : ∀ t ∈ unitInterval, z t ≤ canonical t :=
    cuberoot_comparison (by norm_num) forcing_continuous.continuousOn
      (mul_pos (by norm_num) hlambda)
      (exact_subsolution hz.2.1 hz.2.2.2.2)
      (exact_supersolution hcanonicalCont hcanonicalODE)
      (by rw [hz.2.2.2.1, hcanonical0])
  have hge : ∀ t ∈ unitInterval, canonical t ≤ z t :=
    cuberoot_comparison (by norm_num) forcing_continuous.continuousOn
      (mul_pos (by norm_num) hlambda)
      (exact_subsolution hcanonicalCont hcanonicalODE)
      (exact_supersolution hz.2.1 hz.2.2.2.2)
      (by rw [hz.2.2.2.1, hcanonical0])
  apply eq_of_eqOn_unitInterval_of_canonical hz.1 hcanonical
  intro t ht
  exact le_antisymm (hle t ht) (hge t ht)

end ShootingAux

/-! ## The canonical shooting solution -/

/-- Literal existence and uniqueness on `[0,1]`, with canonical constant extension outside
the interval. -/
theorem shooting_existsUnique (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃! y : ℝ → ℝ, IsShootingSolution lambda y :=
  ShootingAux.shooting_existsUnique lambda hlambda

/-- The unique shooting solution.  This choice is made only after proving literal `∃!`. -/
noncomputable def shootingY (lambda : ℝ) (hlambda : 0 < lambda) : ℝ → ℝ :=
  Classical.choose (shooting_existsUnique lambda hlambda)

/-- The selected shooting function satisfies the shooting problem. -/
theorem shootingY_isSolution (lambda : ℝ) (hlambda : 0 < lambda) :
    IsShootingSolution lambda (shootingY lambda hlambda) :=
  (shooting_existsUnique lambda hlambda).choose_spec.1

/-- Every canonical shooting solution is the selected one. -/
theorem shootingY_unique (lambda : ℝ) (hlambda : 0 < lambda) {y : ℝ → ℝ}
    (hy : IsShootingSolution lambda y) : y = shootingY lambda hlambda :=
  (shooting_existsUnique lambda hlambda).choose_spec.2 y hy

theorem shooting_solution_nonneg {lambda : ℝ} (hlambda : 0 < lambda) {y : ℝ → ℝ}
    (hy : IsShootingSolution lambda y) : ∀ t ∈ unitInterval, 0 ≤ y t := by
  have hzero_sub : IsCubeRootSubsolutionOn shootingForcing (3 * lambda)
      (fun _ ↦ 0) 0 1 := by
    refine ⟨continuous_const.continuousOn, ?_⟩
    intro t ht
    refine ⟨0, hasDerivAt_const t 0, ?_⟩
    simpa using shootingForcing_nonneg ⟨ht.1.le, ht.2.le⟩
  have hy_super := ShootingAux.exact_supersolution hy.2.1 hy.2.2.2.2
  exact cuberoot_comparison (by norm_num) ShootingAux.forcing_continuous.continuousOn
    (mul_pos (by norm_num) hlambda) hzero_sub hy_super (by rw [hy.2.2.2.1])

/-- `eq:y>0`: the shooting solution is strictly positive at every interior point. -/
theorem shootingY_pos (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ t ∈ openUnitInterval, 0 < shootingY lambda hlambda t := by
  let y := shootingY lambda hlambda
  have hy := shootingY_isSolution lambda hlambda
  have hynonneg := shooting_solution_nonneg hlambda hy
  intro t ht
  apply lt_of_le_of_ne (hynonneg t ⟨ht.1.le, ht.2.le⟩)
  intro hzero
  have hzero' : y t = 0 := hzero.symm
  have hlocal : IsLocalMin y t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [hzero']
    exact hynonneg s ⟨hs.1.le, hs.2.le⟩
  have hyode := hy.2.2.2.2 t ht
  have hderiv_zero := ManualInterfaces.MI06_deriv_eq_zero_at_local_extremum
    hyode (Or.inl hlocal)
  have hforce_pos : 0 < shootingForcing t := by
    dsimp [shootingForcing]
    nlinarith [ht.1, ht.2]
  have : yRhs lambda t (y t) = shootingForcing t := by
    simp [hzero', yRhs, shootingForcing]
  rw [this] at hderiv_zero
  linarith

/-- Increasing the positive shooting parameter weakly lowers the solution on the whole
closed interval. -/
theorem shootingY_antitone {lambda₁ lambda₂ : ℝ} (hlambda₁ : 0 < lambda₁)
    (horder : lambda₁ ≤ lambda₂) :
    ∀ t ∈ unitInterval,
      shootingY lambda₂ (hlambda₁.trans_le horder) t ≤ shootingY lambda₁ hlambda₁ t := by
  rcases horder.eq_or_lt with hEq | hlt
  · subst lambda₂
    intro t ht
    exact le_rfl
  · let y₁ := shootingY lambda₁ hlambda₁
    let y₂ := shootingY lambda₂ (hlambda₁.trans hlt)
    have hy₁ := shootingY_isSolution lambda₁ hlambda₁
    have hy₂ := shootingY_isSolution lambda₂ (hlambda₁.trans hlt)
    have hy₁nonneg := shooting_solution_nonneg hlambda₁ hy₁
    have hy₁super₂ :
        IsCubeRootSupersolutionOn shootingForcing (3 * lambda₂) y₁ 0 1 := by
      refine ⟨hy₁.2.1, ?_⟩
      intro t ht
      have hderiv := hy₁.2.2.2.2 t ht
      refine ⟨yRhs lambda₁ t (y₁ t), hderiv, ?_⟩
      have hcbrt : 0 ≤ Real.cbrt (y₁ t) :=
        Real.cbrt_nonneg.mpr (hy₁nonneg t ⟨ht.1.le, ht.2.le⟩)
      simp only [yRhs_eq_forcing_sub]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlt.le) hcbrt]
    exact cuberoot_comparison (by norm_num)
      ShootingAux.forcing_continuous.continuousOn
      (mul_pos (by norm_num) (hlambda₁.trans hlt))
      (ShootingAux.exact_subsolution hy₂.2.1 hy₂.2.2.2.2) hy₁super₂
      (by simp [hy₁.2.2.2.1, hy₂.2.2.2.1])

/-- `eq:shooting-strict-order`: increasing the positive parameter strictly lowers the
shooting solution at every interior point. -/
theorem shootingY_strictAnti {lambda₁ lambda₂ : ℝ} (hlambda₁ : 0 < lambda₁)
    (horder : lambda₁ < lambda₂) :
    ∀ t ∈ openUnitInterval,
      shootingY lambda₂ (hlambda₁.trans horder) t < shootingY lambda₁ hlambda₁ t := by
  let y₁ := shootingY lambda₁ hlambda₁
  let y₂ := shootingY lambda₂ (hlambda₁.trans horder)
  have hy₁ := shootingY_isSolution lambda₁ hlambda₁
  have hy₂ := shootingY_isSolution lambda₂ (hlambda₁.trans horder)
  have hy₁nonneg := shooting_solution_nonneg hlambda₁ hy₁
  have hy₁super₂ : IsCubeRootSupersolutionOn shootingForcing (3 * lambda₂) y₁ 0 1 := by
    refine ⟨hy₁.2.1, ?_⟩
    intro t ht
    have hderiv := hy₁.2.2.2.2 t ht
    refine ⟨yRhs lambda₁ t (y₁ t), hderiv, ?_⟩
    have hcbrt : 0 ≤ Real.cbrt (y₁ t) :=
      Real.cbrt_nonneg.mpr (hy₁nonneg t ⟨ht.1.le, ht.2.le⟩)
    simp only [yRhs_eq_forcing_sub]
    nlinarith [mul_nonneg (sub_nonneg.mpr horder.le) hcbrt]
  have hweak : ∀ t ∈ unitInterval, y₂ t ≤ y₁ t :=
    cuberoot_comparison (by norm_num) ShootingAux.forcing_continuous.continuousOn
      (mul_pos (by norm_num) (hlambda₁.trans horder))
      (ShootingAux.exact_subsolution hy₂.2.1 hy₂.2.2.2.2) hy₁super₂
      (by simp [y₁, y₂, hy₁.2.2.2.1, hy₂.2.2.2.1])
  intro t ht
  apply lt_of_le_of_ne (hweak t ⟨ht.1.le, ht.2.le⟩)
  intro heq
  let d : ℝ → ℝ := fun s ↦ y₁ s - y₂ s
  have hdlocal : IsLocalMin d t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    dsimp [d]
    rw [heq]
    simpa only [sub_self] using sub_nonneg.mpr (hweak s ⟨hs.1.le, hs.2.le⟩)
  have hy₁ode := hy₁.2.2.2.2 t ht
  have hy₂ode := hy₂.2.2.2.2 t ht
  have hdderiv : HasDerivAt d
      (yRhs lambda₁ t (y₁ t) - yRhs lambda₂ t (y₂ t)) t :=
    hy₁ode.sub hy₂ode
  have hd_zero := ManualInterfaces.MI06_deriv_eq_zero_at_local_extremum
    hdderiv (Or.inl hdlocal)
  have hy₁pos : 0 < y₁ t := shootingY_pos lambda₁ hlambda₁ t ht
  have hcbrt_pos : 0 < Real.cbrt (y₁ t) := Real.cbrt_pos.mpr hy₁pos
  have hy_eq : y₂ t = y₁ t := heq
  simp only [yRhs_eq_forcing_sub] at hd_zero
  rw [hy_eq] at hd_zero
  nlinarith [mul_pos (sub_pos.mpr horder) hcbrt_pos]

theorem shooting_solution_le_three_quarters {lambda : ℝ} (hlambda : 0 < lambda)
    {y : ℝ → ℝ} (hy : IsShootingSolution lambda y) :
    ∀ t ∈ unitInterval, y t ≤ 3 / 4 := by
  have hlinear_super : IsCubeRootSupersolutionOn shootingForcing (3 * lambda)
      (fun t ↦ (3 / 4) * t) 0 1 := by
    refine ⟨(continuous_const.mul continuous_id).continuousOn, ?_⟩
    intro t ht
    refine ⟨3 / 4, ?_, ?_⟩
    · simpa using (hasDerivAt_const t (3 / 4)).fun_mul (hasDerivAt_id t)
    · have hcbrt : 0 ≤ Real.cbrt ((3 / 4) * t) :=
        Real.cbrt_nonneg.mpr (mul_nonneg (by norm_num) ht.1.le)
      have hforce := shootingForcing_le_three_quarters ⟨ht.1.le, ht.2.le⟩
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hlambda.le) hcbrt]
  have hlinear := cuberoot_comparison (by norm_num)
    ShootingAux.forcing_continuous.continuousOn (mul_pos (by norm_num) hlambda)
    (ShootingAux.exact_subsolution hy.2.1 hy.2.2.2.2) hlinear_super
    (by rw [hy.2.2.2.1]; norm_num)
  intro t ht
  calc
    y t ≤ (3 / 4) * t := hlinear t ht
    _ ≤ 3 / 4 := by nlinarith [ht.1, ht.2]

/-! ## Direct parameter dependence in the uniform norm -/

noncomputable section

local instance : CompactSpace unitInterval :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- The shooting family regarded as continuous functions on the compact unit interval. -/
noncomputable def shootingYMap (lambda : {x : ℝ // 0 < x}) : C(unitInterval, ℝ) :=
  ⟨fun t ↦ shootingY lambda.1 lambda.2 t.1,
    continuousOn_iff_continuous_restrict.mp
      (shootingY_isSolution lambda.1 lambda.2).2.1⟩

/-- For ordered parameters, the solution difference is bounded by integrating the source's
one-sided derivative estimate from the common initial value. -/
theorem shootingY_ordered_parameter_bound {lambda₁ lambda₂ : ℝ}
    (hlambda₁ : 0 < lambda₁) (horder : lambda₁ ≤ lambda₂) :
    ∀ t ∈ unitInterval,
      shootingY lambda₁ hlambda₁ t - shootingY lambda₂ (hlambda₁.trans_le horder) t ≤
        3 * Real.cbrt (3 / 4) * (lambda₂ - lambda₁) * t := by
  let y₁ := shootingY lambda₁ hlambda₁
  let hlambda₂ : 0 < lambda₂ := hlambda₁.trans_le horder
  let y₂ := shootingY lambda₂ hlambda₂
  let L := 3 * Real.cbrt (3 / 4) * (lambda₂ - lambda₁)
  let adjusted : ℝ → ℝ := fun t ↦ y₁ t - y₂ t - L * t
  have hy₁ := shootingY_isSolution lambda₁ hlambda₁
  have hy₂ := shootingY_isSolution lambda₂ hlambda₂
  have hweak : ∀ t ∈ unitInterval, y₂ t ≤ y₁ t := by
    simpa [y₁, y₂, hlambda₂] using shootingY_antitone hlambda₁ horder
  have hy₂upper := shooting_solution_le_three_quarters hlambda₂ hy₂
  have hadjusted_cont : ContinuousOn adjusted unitInterval := by
    exact (hy₁.2.1.sub hy₂.2.1).sub (continuousOn_const.mul continuousOn_id)
  have hadjusted_deriv : ∀ t ∈ openUnitInterval,
      ∃ f' : ℝ, HasDerivAt adjusted f' t ∧ f' ≤ 0 := by
    intro t ht
    let c₁ := Real.cbrt (y₁ t)
    let c₂ := Real.cbrt (y₂ t)
    let cmax := Real.cbrt (3 / 4)
    have hcorder : c₂ ≤ c₁ := Real.strictMono_cbrt.monotone
      (hweak t ⟨ht.1.le, ht.2.le⟩)
    have hcmax : c₂ ≤ cmax := Real.strictMono_cbrt.monotone
      (hy₂upper t ⟨ht.1.le, ht.2.le⟩)
    have hdelta : 0 ≤ lambda₂ - lambda₁ := sub_nonneg.mpr horder
    have hfirst : -3 * lambda₁ * (c₁ - c₂) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hlambda₁]) (sub_nonneg.mpr hcorder)
    have hsecond : 3 * (lambda₂ - lambda₁) * c₂ ≤
        3 * (lambda₂ - lambda₁) * cmax :=
      mul_le_mul_of_nonneg_left hcmax (mul_nonneg (by norm_num) hdelta)
    have hfieldDiff :
        yRhs lambda₁ t (y₁ t) - yRhs lambda₂ t (y₂ t) =
          -3 * lambda₁ * (c₁ - c₂) + 3 * (lambda₂ - lambda₁) * c₂ := by
      dsimp [c₁, c₂]
      simp only [yRhs_eq_forcing_sub]
      ring
    let f' := yRhs lambda₁ t (y₁ t) - yRhs lambda₂ t (y₂ t) - L
    refine ⟨f', ?_, ?_⟩
    · have hlinear : HasDerivAt (fun s : ℝ ↦ L * s) L t := by
        simpa using (hasDerivAt_id t).const_mul L
      exact (hy₁.2.2.2.2 t ht).sub (hy₂.2.2.2.2 t ht) |>.sub hlinear
    · dsimp [f', L, cmax]
      rw [hfieldDiff]
      linarith
  have hanti : AntitoneOn adjusted unitInterval :=
    ManualInterfaces.MI06_antitoneOn_of_deriv_nonpos (by norm_num)
      hadjusted_cont hadjusted_deriv
  intro t ht
  have hbound := hanti (show (0 : ℝ) ∈ unitInterval by constructor <;> norm_num)
    ht ht.1
  simpa [adjusted, L, y₁, y₂, hy₁.2.2.2.1, hy₂.2.2.2.1] using hbound

/-- Pointwise parameter Lipschitz bound on the whole closed interval. -/
theorem shootingY_parameter_abs_bound
    (parameter₁ parameter₂ : {x : ℝ // 0 < x}) (t : ℝ) (ht : t ∈ unitInterval) :
    |shootingY parameter₁.1 parameter₁.2 t - shootingY parameter₂.1 parameter₂.2 t| ≤
      3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
  have hc : 0 ≤ 3 * Real.cbrt (3 / 4) := by
    exact mul_nonneg (by norm_num) (Real.cbrt_nonneg.mpr (by norm_num))
  rcases le_total parameter₁.1 parameter₂.1 with horder | horder
  · have hweak := shootingY_antitone parameter₁.2 horder t ht
    have hordered := shootingY_ordered_parameter_bound parameter₁.2 horder t ht
    rw [abs_of_nonneg (sub_nonneg.mpr hweak)]
    calc
      shootingY parameter₁.1 parameter₁.2 t - shootingY parameter₂.1 parameter₂.2 t ≤
          3 * Real.cbrt (3 / 4) * (parameter₂.1 - parameter₁.1) * t := hordered
      _ ≤ 3 * Real.cbrt (3 / 4) * (parameter₂.1 - parameter₁.1) := by
        have hdelta : 0 ≤ parameter₂.1 - parameter₁.1 := sub_nonneg.mpr horder
        nlinarith [mul_nonneg hc hdelta, ht.2]
      _ = 3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
        rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        ring
  · have hweak := shootingY_antitone parameter₂.2 horder t ht
    have hordered := shootingY_ordered_parameter_bound parameter₂.2 horder t ht
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hweak)]
    calc
      shootingY parameter₂.1 parameter₂.2 t - shootingY parameter₁.1 parameter₁.2 t ≤
          3 * Real.cbrt (3 / 4) * (parameter₁.1 - parameter₂.1) * t := hordered
      _ ≤ 3 * Real.cbrt (3 / 4) * (parameter₁.1 - parameter₂.1) := by
        have hdelta : 0 ≤ parameter₁.1 - parameter₂.1 := sub_nonneg.mpr horder
        nlinarith [mul_nonneg hc hdelta, ht.2]
      _ = 3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
        rw [abs_of_nonneg (sub_nonneg.mpr horder)]

/-- The pointwise estimate promoted to the sup metric of `C([0,1])`. -/
theorem shootingYMap_dist_le (parameter₁ parameter₂ : {x : ℝ // 0 < x}) :
    dist (shootingYMap parameter₁) (shootingYMap parameter₂) ≤
      3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
  have hnonneg : 0 ≤ 3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.cbrt_nonneg.mpr (by norm_num))) (abs_nonneg _)
  apply (ContinuousMap.dist_le hnonneg).2
  intro t
  simpa [shootingYMap, Real.dist_eq] using
    shootingY_parameter_abs_bound parameter₁ parameter₂ t.1 t.2

/-- The same estimate in the source's uniform-norm notation. -/
theorem shootingYMap_norm_sub_le (parameter₁ parameter₂ : {x : ℝ // 0 < x}) :
    ‖shootingYMap parameter₁ - shootingYMap parameter₂‖ ≤
      3 * Real.cbrt (3 / 4) * |parameter₁.1 - parameter₂.1| := by
  simpa [dist_eq_norm] using shootingYMap_dist_le parameter₁ parameter₂

/-- Continuous dependence in the uniform norm, proved directly from the parameter
Lipschitz estimate without compactness, dominated convergence, or subsequences. -/
theorem continuous_shootingYMap : Continuous shootingYMap := by
  rw [Metric.continuous_iff]
  intro parameter ε hε
  let C : ℝ := 3 * Real.cbrt (3 / 4)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num) (Real.cbrt_pos.mpr (by norm_num))
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro parameter' hdist
  calc
    dist (shootingYMap parameter') (shootingYMap parameter) ≤
        C * |parameter'.1 - parameter.1| := by
      simpa [C] using shootingYMap_dist_le parameter' parameter
    _ = C * dist parameter' parameter := by congr 1
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hdist hC
    _ = ε := by field_simp [hC.ne']

/-- Exact four-clause source-facing package for `lem:property of y`. -/
theorem shootingProperties :
    (∀ lambda, 0 < lambda → ∃! y : ℝ → ℝ, IsShootingSolution lambda y) ∧
    (∀ lambda (hlambda : 0 < lambda) t, t ∈ openUnitInterval →
      0 < shootingY lambda hlambda t) ∧
    (∀ lambda₁ lambda₂ (hlambda₁ : 0 < lambda₁) (horder : lambda₁ < lambda₂) t,
      t ∈ openUnitInterval →
        shootingY lambda₂ (hlambda₁.trans horder) t < shootingY lambda₁ hlambda₁ t) ∧
    Continuous shootingYMap := by
  have hanti : ∀ lambda₁ lambda₂ (hlambda₁ : 0 < lambda₁)
      (horder : lambda₁ < lambda₂) t, t ∈ openUnitInterval →
        shootingY lambda₂ (hlambda₁.trans horder) t < shootingY lambda₁ hlambda₁ t := by
    intro lambda₁ lambda₂ hlambda₁ horder
    exact shootingY_strictAnti hlambda₁ horder
  exact ⟨shooting_existsUnique, shootingY_pos, hanti, continuous_shootingYMap⟩

end

end SeriesParallel.Appendix
