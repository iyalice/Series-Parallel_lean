import SeriesParallel.Appendix.AdmissibleLowerBound
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The subcritical transformed solution

This file formalizes `prop:subcritical-W`.  Endpoint differentiability and
smoothness are one-sided statements on `Ici 0` and `Icc 0 η`; no differentiability
of the canonical constant extension across zero is asserted.
-/

open Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

open SeriesParallel.ManualInterfaces

/-- The regular vector field obtained by dividing the W--ODE by `W²`. -/
noncomputable def positiveWField (lambda : ℝ) (p : ℝ × ℝ) : ℝ :=
  (lambda * p.2 - p.1 * (1 - p.1)) / p.2 ^ 2

/-- The open half-plane on which the divided W--equation is smooth. -/
def positiveWFieldDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.2}

theorem isOpen_positiveWFieldDomain : IsOpen positiveWFieldDomain := by
  exact isOpen_lt continuous_const continuous_snd

theorem positiveWField_contDiffOn (lambda : ℝ) :
    ContDiffOn ℝ ∞ (positiveWField lambda) positiveWFieldDomain := by
  unfold positiveWField
  apply ContDiffOn.div
  · fun_prop
  · fun_prop
  · intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp)

/-- Below `lambdaStar`, the shooting solution cannot vanish at `t=1`. -/
theorem shootingY_one_pos_of_lt_lambdaStar {lambda : ℝ} (hlambda : 0 < lambda)
    (hsubcritical : lambda < lambdaStar) :
    0 < shootingY lambda hlambda 1 := by
  have hy := shootingY_isSolution lambda hlambda
  have hnonneg : 0 ≤ shootingY lambda hlambda 1 :=
    shooting_solution_nonneg hlambda hy 1 ⟨by norm_num, le_rfl⟩
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hmem : lambda ∈ admissibleSet := ⟨hlambda, hzero.symm⟩
  have hstar_le : lambdaStar ≤ lambda := csInf_le admissibleSet_bddBelow hmem
  linarith

/-- The subcritical transformed solution is already positive at its left endpoint. -/
theorem WSolution_zero_pos_of_lt_lambdaStar {lambda : ℝ} (hlambda : 0 < lambda)
    (hsubcritical : lambda < lambdaStar) :
    0 < WSolution lambda hlambda 0 := by
  rw [WSolution, wOfY]
  exact Real.cbrt_pos.mpr (by
    simpa only [sub_zero] using shootingY_one_pos_of_lt_lambdaStar hlambda hsubcritical)

/-- Positivity on the source interval `[0,1)`. -/
theorem WSolution_pos_Ico_of_lt_lambdaStar {lambda : ℝ} (hlambda : 0 < lambda)
    (hsubcritical : lambda < lambdaStar) :
    ∀ u ∈ Ico (0 : ℝ) 1, 0 < WSolution lambda hlambda u := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact WSolution_zero_pos_of_lt_lambdaStar hlambda hsubcritical
  · exact WSolution_pos lambda hlambda u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩

/-- The divided vector field is the actual derivative at every interior point. -/
theorem WSolution_hasDerivAt_positiveWField (lambda : ℝ) (hlambda : 0 < lambda)
    {u : ℝ} (hu : u ∈ openUnitInterval) :
    HasDerivAt (WSolution lambda hlambda)
      (positiveWField lambda (u, WSolution lambda hlambda u)) u := by
  exact WSolution_hasDerivAt lambda hlambda hu

/-- The derivative formula converges to `λ/W(0)` from the right. -/
theorem WSolution_deriv_tendsto_zero_of_lt_lambdaStar {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    Tendsto (fun u ↦ deriv (WSolution lambda hlambda) u) (𝓝[>] (0 : ℝ))
      (𝓝 (lambda / WSolution lambda hlambda 0)) := by
  let W := WSolution lambda hlambda
  have hW0pos : 0 < W 0 := WSolution_zero_pos_of_lt_lambdaStar hlambda hsubcritical
  have hcont := WSolution_continuousOn lambda hlambda
  have hcont0 : ContinuousWithinAt W unitInterval 0 :=
    hcont 0 ⟨le_rfl, by norm_num⟩
  have hfilter : (𝓝[>] (0 : ℝ)) ≤ 𝓝[unitInterval] (0 : ℝ) := by
    rw [nhdsWithin]
    refine le_inf inf_le_left ?_
    rw [le_principal_iff]
    exact mem_of_superset (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      Ioc_subset_Icc_self
  have hWlim : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) :=
    hcont0.mono_left hfilter
  have huid : Tendsto (fun u : ℝ ↦ u) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hpair : Tendsto (fun u : ℝ ↦ (u, W u)) (𝓝[>] (0 : ℝ)) (𝓝 (0, W 0)) :=
    huid.prodMk_nhds hWlim
  have hfieldAt : ContinuousAt (positiveWField lambda) (0, W 0) := by
    unfold positiveWField
    fun_prop (disch := aesop)
  have hfieldLimit : Tendsto
      (fun u ↦ positiveWField lambda (u, W u)) (𝓝[>] (0 : ℝ))
      (𝓝 (lambda / W 0)) := by
    have hcomp := hfieldAt.tendsto.comp hpair
    have hvalue : positiveWField lambda (0, W 0) = lambda / W 0 := by
      unfold positiveWField
      field_simp [hW0pos.ne']
      ring
    rw [← hvalue]
    apply Tendsto.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
    exact hcomp
  apply (tendsto_congr' ?_).2 hfieldLimit
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact (WSolution_hasDerivAt_positiveWField lambda hlambda hu).deriv

/-- The genuine right derivative at zero, obtained by extending the interior
derivative limit rather than differentiating the constant extension. -/
theorem WSolution_hasDerivWithinAt_zero_of_lt_lambdaStar {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    HasDerivWithinAt (WSolution lambda hlambda)
      (lambda / WSolution lambda hlambda 0) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := openUnitInterval)
  · intro u hu
    exact (WSolution_hasDerivAt lambda hlambda hu).differentiableAt.differentiableWithinAt
  · have hcont := WSolution_continuousOn lambda hlambda
    exact (hcont 0 ⟨le_rfl, by norm_num⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT (by norm_num)
  · exact WSolution_deriv_tendsto_zero_of_lt_lambdaStar hlambda hsubcritical

/-- The source's one-sided smooth extension at `u=0`, obtained from MI09 after
establishing the actual right derivative there. -/
theorem WSolution_contDiffOn_infty_zero_of_lt_lambdaStar {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ContDiffOn ℝ ∞ (WSolution lambda hlambda) (Icc 0 (1 / 2 : ℝ)) := by
  apply MI09_ode_regularity_bootstrap_one_sided
    (positiveWField lambda) positiveWFieldDomain
    (a := 0) (b := (1 / 2 : ℝ)) (by norm_num)
    (WSolution lambda hlambda)
    isOpen_positiveWFieldDomain (positiveWField_contDiffOn lambda)
  · intro u hu
    exact WSolution_pos_Ico_of_lt_lambdaStar hlambda hsubcritical u
      ⟨hu.1, hu.2.trans_lt (by norm_num)⟩
  · exact (WSolution_continuousOn lambda hlambda).mono (by
      intro u hu
      exact ⟨hu.1, hu.2.trans (by norm_num)⟩)
  · have hleft := WSolution_hasDerivWithinAt_zero_of_lt_lambdaStar
      hlambda hsubcritical
    apply hleft.congr_deriv
    unfold positiveWField
    have hW0ne : WSolution lambda hlambda 0 ≠ 0 :=
      (WSolution_zero_pos_of_lt_lambdaStar hlambda hsubcritical).ne'
    field_simp [hW0ne]
    ring
  · intro u hu
    exact WSolution_hasDerivAt_positiveWField lambda hlambda
      ⟨hu.1, hu.2.trans (by norm_num)⟩

/-- For every positive parameter, the canonical transform is smooth on the
open unit interval.  In particular this supplies the source-facing `C¹`
regularity required in A4 without asserting anything about the constant
extension to the left of zero. -/
theorem WSolution_contDiffOn_infty_openUnitInterval (lambda : ℝ)
    (hlambda : 0 < lambda) :
    ContDiffOn ℝ ∞ (WSolution lambda hlambda) openUnitInterval := by
  apply MI09_ode_regularity_bootstrap_infty
    (positiveWField lambda) positiveWFieldDomain openUnitInterval
      (WSolution lambda hlambda)
  · exact isOpen_positiveWFieldDomain
  · exact positiveWField_contDiffOn lambda
  · exact isOpen_Ioo
  · intro u hu
    exact WSolution_pos lambda hlambda u hu
  · intro u hu
    exact WSolution_hasDerivAt_positiveWField lambda hlambda hu

/-- Smoothness at the left endpoint is explicitly one-sided: the set is
`Ici 0`, so this does not claim ordinary two-sided `ContDiffAt` for the
canonical constant extension. -/
theorem WSolution_contDiffWithinAt_infty_zero_of_lt_lambdaStar {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ContDiffWithinAt ℝ ∞ (WSolution lambda hlambda) (Ici 0) 0 := by
  have hclosed :=
    WSolution_contDiffOn_infty_zero_of_lt_lambdaStar hlambda hsubcritical
  have hzero := hclosed 0 ⟨le_rfl, by norm_num⟩
  apply hzero.congr_set
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with u hu
  apply propext
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hu.le⟩

/-- Complete source-facing conclusion of `prop:subcritical-W`. -/
structure SubcriticalWConclusion (lambda : ℝ) (hlambda : 0 < lambda) : Prop where
  shootingEndpointPositive : 0 < shootingY lambda hlambda 1
  transformedLeftPositive : 0 < WSolution lambda hlambda 0
  transformedPositive : ∀ u ∈ Ico (0 : ℝ) 1, 0 < WSolution lambda hlambda u
  transformedRightZero : WSolution lambda hlambda 1 = 0
  transformedContinuous : ContinuousOn (WSolution lambda hlambda) unitInterval
  transformedCOne : ContDiffOn ℝ 1 (WSolution lambda hlambda) openUnitInterval
  transformedODE : ∀ u ∈ openUnitInterval,
    SatisfiesWODEAt lambda (WSolution lambda hlambda) u
  smoothAtLeft : ∃ eta > 0,
    ContDiffOn ℝ ∞ (WSolution lambda hlambda) (Icc 0 eta)
  smoothWithinAtLeft :
    ContDiffWithinAt ℝ ∞ (WSolution lambda hlambda) (Ici 0) 0
  leftDerivative : HasDerivWithinAt (WSolution lambda hlambda)
    (lambda / WSolution lambda hlambda 0) (Ici 0) 0

/-- `prop:subcritical-W`: every `0 < λ < lambdaStar` gives a positive transformed
solution on `[0,1)`, solving the W--ODE and smooth from the right at zero. -/
theorem subcriticalW {lambda : ℝ} (hlambda : 0 < lambda)
    (hsubcritical : lambda < lambdaStar) :
    SubcriticalWConclusion lambda hlambda := by
  refine
    { shootingEndpointPositive :=
        shootingY_one_pos_of_lt_lambdaStar hlambda hsubcritical
      transformedLeftPositive :=
        WSolution_zero_pos_of_lt_lambdaStar hlambda hsubcritical
      transformedPositive :=
        WSolution_pos_Ico_of_lt_lambdaStar hlambda hsubcritical
      transformedRightZero := WSolution_one lambda hlambda
      transformedContinuous := WSolution_continuousOn lambda hlambda
      transformedCOne :=
        (WSolution_contDiffOn_infty_openUnitInterval lambda hlambda).of_le
          (by norm_num)
      transformedODE := WSolution_satisfiesWODEAt lambda hlambda
      smoothAtLeft := ⟨1 / 2, by norm_num,
        WSolution_contDiffOn_infty_zero_of_lt_lambdaStar hlambda hsubcritical⟩
      smoothWithinAtLeft :=
        WSolution_contDiffWithinAt_infty_zero_of_lt_lambdaStar hlambda hsubcritical
      leftDerivative :=
        WSolution_hasDerivWithinAt_zero_of_lt_lambdaStar hlambda hsubcritical }

end SeriesParallel.Appendix
