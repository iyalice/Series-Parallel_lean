import SeriesParallel.Appendix.Shooting
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Admissible parameters

This module begins the formalization of `prop:Cstar-halfline`.  The first block contains
the source's explicit supersolution and the exact sharp cubic-polynomial estimate used to
show that every `λ ≥ √3/2` is admissible.
-/

open Set

namespace SeriesParallel.Appendix

/-- The explicit upper bound in `eq:rough-Cstar-bounds`. -/
noncomputable def lambdaUpper : ℝ := Real.sqrt 3 / 2

/-- Base of the source's lower-bound constant. -/
noncomputable def lambdaLowerBase : ℝ := 4 / (15 * Real.sqrt 2)

/-- The exact lower-bound constant `(4/(15√2))^(2/3)`, expressed with the signed
real cube root to make the intended real exponent unambiguous. -/
noncomputable def lambdaLower : ℝ := Real.cbrt lambdaLowerBase ^ 2

theorem lambdaUpper_pos : 0 < lambdaUpper := by
  unfold lambdaUpper
  positivity

theorem lambdaLowerBase_pos : 0 < lambdaLowerBase := by
  unfold lambdaLowerBase
  positivity

theorem lambdaLower_pos : 0 < lambdaLower := by
  unfold lambdaLower
  exact sq_pos_of_pos (Real.cbrt_pos.mpr lambdaLowerBase_pos)

/-- The signed-cube-root definition agrees with the source's real-power notation
`(4 / (15 * sqrt 2))^(2/3)` because the base is strictly positive. -/
theorem lambdaLower_eq_rpow :
    lambdaLower =
      Real.rpow (4 / (15 * Real.sqrt 2)) (2 / 3 : ℝ) := by
  have hbase : 0 ≤ 4 / (15 * Real.sqrt 2) := by positivity
  unfold lambdaLower lambdaLowerBase Real.cbrt
  rw [if_neg (not_lt.mpr hbase)]
  rw [← Real.rpow_mul_natCast hbase (1 / 3 : ℝ) 2]
  norm_num

/-- Cubing the lower-bound constant produces the rational value used in the
source's integral estimate. -/
theorem lambdaLower_cube : lambdaLower ^ 3 = 8 / 225 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  calc
    lambdaLower ^ 3 = (Real.cbrt lambdaLowerBase ^ 3) ^ 2 := by
      unfold lambdaLower
      ring
    _ = lambdaLowerBase ^ 2 := by rw [Real.cbrt_cube]
    _ = 8 / 225 := by
      unfold lambdaLowerBase
      field_simp [show Real.sqrt 2 ≠ 0 by positivity]
      nlinarith

/-- The source's admissible set `𝓐={λ>0 : y_λ(1)=0}`. -/
noncomputable def admissibleSet : Set ℝ :=
  {lambda : ℝ | ∃ hlambda : 0 < lambda, shootingY lambda hlambda 1 = 0}

/-- The same admissibility condition on the natural positive-parameter subtype. -/
noncomputable def positiveAdmissibleSet : Set {lambda : ℝ // 0 < lambda} :=
  {parameter | shootingY parameter.1 parameter.2 1 = 0}

/-- The source's `W_λ(u)=cbrt(y_λ(1-u))`. -/
noncomputable def WSolution (lambda : ℝ) (hlambda : 0 < lambda) : ℝ → ℝ :=
  wOfY (shootingY lambda hlambda)

theorem WSolution_one (lambda : ℝ) (hlambda : 0 < lambda) :
    WSolution lambda hlambda 1 = 0 := by
  have hy := shootingY_isSolution lambda hlambda
  simp [WSolution, wOfY, hy.2.2.2.1]

theorem WSolution_pos (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ u ∈ openUnitInterval, 0 < WSolution lambda hlambda u := by
  intro u hu
  apply Real.cbrt_pos.mpr
  apply shootingY_pos lambda hlambda (1 - u)
  exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

theorem WSolution_zero_of_admissible {lambda : ℝ} (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    WSolution lambda hlambda 0 = 0 := by
  simp [WSolution, wOfY, hadmissible]

/-- Differentiating the cube-root transform away from its zero endpoints. -/
theorem WSolution_hasDerivAt (lambda : ℝ) (hlambda : 0 < lambda)
    {u : ℝ} (hu : u ∈ openUnitInterval) :
    HasDerivAt (WSolution lambda hlambda)
      ((lambda * WSolution lambda hlambda u - u * (1 - u)) /
        WSolution lambda hlambda u ^ 2) u := by
  let y := shootingY lambda hlambda
  have hy := shootingY_isSolution lambda hlambda
  have hmirror : 1 - u ∈ openUnitInterval := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hypos : 0 < y (1 - u) := shootingY_pos lambda hlambda (1 - u) hmirror
  have hycomp : HasDerivAt (fun x : ℝ ↦ y (1 - x))
      (-(yRhs lambda (1 - u) (y (1 - u)))) u := by
    exact (hy.2.2.2.2 (1 - u) hmirror).comp_const_sub 1 u
  have hcbrt := ManualInterfaces.MI06_chain_rule hycomp
    (Real.hasDerivAt_cbrt hypos.ne')
  have hcbrt_value : Real.cbrt (y (1 - u)) = WSolution lambda hlambda u := by
    rfl
  rw [hcbrt_value] at hcbrt
  convert hcbrt using 1
  · ext x
    rfl
  · unfold yRhs
    rw [hcbrt_value]
    have hWne : WSolution lambda hlambda u ≠ 0 :=
      (WSolution_pos lambda hlambda u hu).ne'
    field_simp [hWne]
    ring

/-- The transformed shooting family satisfies `eq:W-ode` on the open interval. -/
theorem WSolution_satisfiesWODEAt (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ u ∈ openUnitInterval, SatisfiesWODEAt lambda (WSolution lambda hlambda) u := by
  intro u hu
  have hderiv := WSolution_hasDerivAt lambda hlambda hu
  refine ⟨hderiv.differentiableAt, ?_⟩
  rw [hderiv.deriv]
  unfold wODEValue
  have hWne : WSolution lambda hlambda u ≠ 0 :=
    (WSolution_pos lambda hlambda u hu).ne'
  field_simp [hWne]
  ring

theorem WSolution_isCanonical (lambda : ℝ) (hlambda : 0 < lambda) :
    IsCanonicalUnitExtension (WSolution lambda hlambda) := by
  intro u
  have hycanonical := (shootingY_isSolution lambda hlambda).1 (1 - u)
  unfold WSolution wOfY
  rw [← unitClamp_one_sub]
  exact congrArg Real.cbrt hycanonical

theorem WSolution_continuousOn (lambda : ℝ) (hlambda : 0 < lambda) :
    ContinuousOn (WSolution lambda hlambda) unitInterval := by
  have hy := shootingY_isSolution lambda hlambda
  have hmirror : MapsTo (fun u : ℝ ↦ 1 - u) unitInterval unitInterval := by
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hmirrorContinuous : ContinuousOn (fun u : ℝ ↦ 1 - u) unitInterval :=
    (continuous_const.sub continuous_id).continuousOn
  have hinner := hy.2.1.comp hmirrorContinuous hmirror
  unfold WSolution wOfY
  convert Real.continuous_cbrt.continuousOn.comp hinner
    (fun u hu ↦ mem_univ _) using 1
  ext u
  rfl

theorem WSolution_contDiffOn_one (lambda : ℝ) (hlambda : 0 < lambda) :
    ContDiffOn ℝ 1 (WSolution lambda hlambda) openUnitInterval := by
  change ContDiffOn ℝ 1 (WSolution lambda hlambda) (Ioo (0 : ℝ) 1)
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo (0 : ℝ) 1)]
  refine ⟨fun u hu ↦
    (WSolution_hasDerivAt lambda hlambda hu).differentiableAt.differentiableWithinAt, ?_⟩
  have hWcont : ContinuousOn (WSolution lambda hlambda) (Ioo (0 : ℝ) 1) :=
    (WSolution_continuousOn lambda hlambda).mono Ioo_subset_Icc_self
  let derivativeFormula : ℝ → ℝ := fun u ↦
    (lambda * WSolution lambda hlambda u - u * (1 - u)) /
      WSolution lambda hlambda u ^ 2
  have hformula : ContinuousOn derivativeFormula (Ioo (0 : ℝ) 1) := by
    apply ContinuousOn.div
    · exact (continuousOn_const.mul hWcont).sub
        (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    · exact hWcont.pow 2
    · intro u hu
      exact pow_ne_zero 2 ((WSolution_pos lambda hlambda u hu).ne')
  exact hformula.congr fun u hu ↦ by
    rw [derivWithin_of_isOpen isOpen_Ioo hu,
      (WSolution_hasDerivAt lambda hlambda hu).deriv]

/-- An admissible shooting parameter produces the source's positive two-point solution. -/
theorem WSolution_isBoundarySolution {lambda : ℝ} (hlambda : 0 < lambda)
    (hadmissible : shootingY lambda hlambda 1 = 0) :
    IsWBoundarySolution lambda (WSolution lambda hlambda) := by
  refine ⟨WSolution_isCanonical lambda hlambda,
    WSolution_continuousOn lambda hlambda,
    WSolution_contDiffOn_one lambda hlambda,
    WSolution_satisfiesWODEAt lambda hlambda, ?_⟩
  exact ⟨WSolution_zero_of_admissible hlambda hadmissible,
    WSolution_one lambda hlambda, WSolution_pos lambda hlambda⟩

theorem admissible_hasBoundarySolution {lambda : ℝ}
    (hadmissible : lambda ∈ admissibleSet) :
    ∃ hlambda : 0 < lambda, IsWBoundarySolution lambda (WSolution lambda hlambda) := by
  rcases hadmissible with ⟨hlambda, hzero⟩
  exact ⟨hlambda, WSolution_isBoundarySolution hlambda hzero⟩

/-- Cubing and reflecting any positive boundary solution recovers a shooting solution. -/
theorem yOfW_isShootingSolution {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) :
    IsShootingSolution lambda (yOfW W) := by
  have hcanonical : IsCanonicalUnitExtension (yOfW W) := by
    intro t
    unfold yOfW
    rw [← unitClamp_one_sub]
    exact congrArg (fun z : ℝ ↦ z ^ 3) (hW.1 (1 - t))
  have hmirrorIcc : MapsTo (fun t : ℝ ↦ 1 - t) unitInterval unitInterval := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmirrorIoo : MapsTo (fun t : ℝ ↦ 1 - t) openUnitInterval openUnitInterval := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcontinuous : ContinuousOn (yOfW W) unitInterval := by
    have hinner := hW.2.1.comp
      (continuous_const.sub continuous_id).continuousOn hmirrorIcc
    change ContinuousOn ((fun t : ℝ ↦ W (1 - t)) ^ (3 : ℕ)) unitInterval
    exact hinner.pow 3
  have hcontDiff : ContDiffOn ℝ 1 (yOfW W) openUnitInterval := by
    have hmirrorCD : ContDiffOn ℝ 1 (fun t : ℝ ↦ 1 - t) openUnitInterval :=
      (contDiff_const.sub contDiff_id).contDiffOn
    have hinner := hW.2.2.1.comp hmirrorCD hmirrorIoo
    change ContDiffOn ℝ 1 ((fun t : ℝ ↦ W (1 - t)) ^ (3 : ℕ)) openUnitInterval
    exact hinner.pow 3
  have hzero : yOfW W 0 = 0 := by
    simp [yOfW, hW.2.2.2.2.2.1]
  have hode : ∀ t ∈ openUnitInterval, SatisfiesYODEAt lambda (yOfW W) t := by
    intro t ht
    have hu : 1 - t ∈ openUnitInterval := hmirrorIoo ht
    have hwode := hW.2.2.2.1 (1 - t) hu
    have hwderiv : HasDerivAt W (deriv W (1 - t)) (1 - t) :=
      hwode.1.hasDerivAt
    have hmirrorDeriv : HasDerivAt (fun x : ℝ ↦ W (1 - x))
        (-(deriv W (1 - t))) t :=
      hwderiv.comp_const_sub 1 t
    have hsquare := ManualInterfaces.MI06_product_rule hmirrorDeriv hmirrorDeriv
    have hcubeRaw := ManualInterfaces.MI06_product_rule hsquare hmirrorDeriv
    have hcube : HasDerivAt (yOfW W)
        (3 * W (1 - t) ^ 2 * (-(deriv W (1 - t)))) t := by
      convert hcubeRaw using 1
      · ext x
        simp only [yOfW]
        ring
      · ring
    have hderivative :
        3 * W (1 - t) ^ 2 * (-(deriv W (1 - t))) =
          yRhs lambda t (yOfW W t) := by
      have heq := hwode.2
      unfold wODEValue at heq
      unfold yRhs yOfW
      rw [Real.cbrt_cube']
      nlinarith [heq]
    exact hcube.congr_deriv hderivative
  exact ⟨hcanonical, hcontinuous, hcontDiff, hzero, hode⟩

/-- The boundary-value solution at a fixed positive admissible parameter is unique. -/
theorem WBoundarySolution_unique {lambda : ℝ} (hlambda : 0 < lambda)
    {W : ℝ → ℝ} (hW : IsWBoundarySolution lambda W) :
    W = WSolution lambda hlambda := by
  have hyEq : yOfW W = shootingY lambda hlambda :=
    shootingY_unique lambda hlambda (yOfW_isShootingSolution hW)
  have htransformed := congrArg wOfY hyEq
  calc
    W = wOfY (yOfW W) := by
      funext u
      exact (wOfY_yOfW W u).symm
    _ = wOfY (shootingY lambda hlambda) := htransformed
    _ = WSolution lambda hlambda := rfl

theorem mem_admissibleSet_of_boundarySolution {lambda : ℝ} (hlambda : 0 < lambda)
    {W : ℝ → ℝ} (hW : IsWBoundarySolution lambda W) :
    lambda ∈ admissibleSet := by
  have hyEq : yOfW W = shootingY lambda hlambda :=
    shootingY_unique lambda hlambda (yOfW_isShootingSolution hW)
  refine ⟨hlambda, ?_⟩
  rw [← hyEq]
  simp [yOfW, hW.2.2.2.2.1]

/-- Source paragraph following the definition of `𝓐`, including literal uniqueness. -/
theorem mem_admissibleSet_iff_existsUnique_boundarySolution {lambda : ℝ}
    (hlambda : 0 < lambda) :
    lambda ∈ admissibleSet ↔ ∃! W : ℝ → ℝ, IsWBoundarySolution lambda W := by
  constructor
  · intro hadmissible
    have hzero : shootingY lambda hlambda 1 = 0 := by
      rcases hadmissible with ⟨hlambda', hzero⟩
      simpa only using hzero
    refine ⟨WSolution lambda hlambda,
      WSolution_isBoundarySolution hlambda hzero, ?_⟩
    intro W hW
    exact WBoundarySolution_unique hlambda hW
  · rintro ⟨W, hW, _⟩
    exact mem_admissibleSet_of_boundarySolution hlambda hW

theorem admissibleSet_bddBelow : BddBelow admissibleSet := by
  refine ⟨0, ?_⟩
  intro lambda hlambda
  exact le_of_lt hlambda.choose

theorem admissibleSet_upwardClosed {lambda₁ lambda₂ : ℝ}
    (hlambda₁ : lambda₁ ∈ admissibleSet) (horder : lambda₁ ≤ lambda₂) :
    lambda₂ ∈ admissibleSet := by
  rcases hlambda₁ with ⟨hpos₁, hzero₁⟩
  have hpos₂ : 0 < lambda₂ := hpos₁.trans_le horder
  have hanti := shootingY_antitone hpos₁ horder 1
    (show (1 : ℝ) ∈ unitInterval by constructor <;> norm_num)
  have hnonneg : 0 ≤ shootingY lambda₂ hpos₂ 1 :=
    shooting_solution_nonneg hpos₂ (shootingY_isSolution lambda₂ hpos₂) 1
      (show (1 : ℝ) ∈ unitInterval by constructor <;> norm_num)
  refine ⟨hpos₂, le_antisymm ?_ hnonneg⟩
  simpa only [hzero₁] using hanti

theorem positiveAdmissibleSet_isClosed : IsClosed positiveAdmissibleSet := by
  let one : unitInterval := ⟨1, by constructor <;> norm_num⟩
  have hevaluation : Continuous (fun parameter : {lambda : ℝ // 0 < lambda} ↦
      shootingYMap parameter one) :=
    (continuous_eval_const one).comp continuous_shootingYMap
  have hclosed : IsClosed {parameter : {lambda : ℝ // 0 < lambda} |
      shootingYMap parameter one = 0} :=
    isClosed_singleton.preimage hevaluation
  change IsClosed {parameter : {lambda : ℝ // 0 < lambda} |
    shootingY parameter.1 parameter.2 1 = 0} at hclosed
  exact hclosed

/-- The explicit barrier `w̄(t)=3t(1-t)/(2λ)` in the proof of
`prop:Cstar-halfline`. -/
noncomputable def upperBarrier (lambda : ℝ) : ℝ → ℝ :=
  ((fun _ : ℝ ↦ 3 / (2 * lambda)) * id) * ((fun _ : ℝ ↦ 1) - id)

theorem upperBarrier_hasDerivAt (lambda t : ℝ) :
    HasDerivAt (upperBarrier lambda)
      ((3 / (2 * lambda)) * (1 - 2 * t)) t := by
  let c : ℝ := 3 / (2 * lambda)
  have h := ((hasDerivAt_const t c).mul (hasDerivAt_id t)).mul
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have hsimple :
      HasDerivAt (((fun _ : ℝ ↦ c) * id) * ((fun _ : ℝ ↦ 1) - id))
        (c * (1 - t) + c * t * (-1)) t := by
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, zero_mul, zero_add, mul_one,
      one_mul, sub_eq_add_neg] using h
  have h' : HasDerivAt (((fun _ : ℝ ↦ c) * id) * ((fun _ : ℝ ↦ 1) - id))
      (c * (1 - 2 * t)) t := by
    have hcoeff : c * (1 - t) + c * t * (-1) = c * (1 - 2 * t) := by ring
    rw [← hcoeff]
    exact hsimple
  unfold upperBarrier
  exact h'

theorem upperBarrier_nonneg {lambda t : ℝ} (hlambda : 0 < lambda)
    (ht : t ∈ unitInterval) : 0 ≤ upperBarrier lambda t := by
  rcases ht with ⟨ht0, ht1⟩
  unfold upperBarrier
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  positivity

/-- Exact residual computation from the source. -/
theorem upperBarrier_residual_identity {lambda t : ℝ} (hlambda : lambda ≠ 0) :
    residualValue lambda (upperBarrier lambda t)
        ((3 / (2 * lambda)) * (1 - 2 * t)) t =
      t * (1 - t) *
        (1 / 2 + (3 / (2 * lambda)) ^ 3 * t * (1 - t) * (1 - 2 * t)) := by
  unfold residualValue upperBarrier
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  field_simp [hlambda]
  ring

/-- The exact cubic-polynomial estimate
`-t(1-t)(1-2t) ≤ 1/(6√3)` on `[0,1]`.  The proof uses the nonnegative
factorization from the expanded formalization reference. -/
theorem cubicPolynomial_max_bound {t : ℝ} (ht : t ∈ unitInterval) :
    -t * (1 - t) * (1 - 2 * t) ≤ 1 / (6 * Real.sqrt 3) := by
  let s : ℝ := Real.sqrt 3
  let x : ℝ := 2 * t - 1
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hssq : s ^ 2 = 3 := by
    dsimp [s]
    norm_num
  have hslt : s < 2 := by nlinarith
  have hxLower : -1 ≤ x := by
    rcases ht with ⟨ht0, _⟩
    dsimp [x]
    linarith
  have hsx : 0 ≤ s * x + 2 := by nlinarith
  have hfactorNonneg : 0 ≤ (s * x - 1) ^ 2 * (s * x + 2) :=
    mul_nonneg (sq_nonneg _) hsx
  have hfactor :
      12 * s * (1 / (6 * s) + t * (1 - t) * (1 - 2 * t)) =
        (s * x - 1) ^ 2 * (s * x + 2) := by
    dsimp [x]
    field_simp [hspos.ne']
    nlinarith
  have hbracket : 0 ≤ 1 / (6 * s) + t * (1 - t) * (1 - 2 * t) := by
    have : 0 ≤ 12 * s *
        (1 / (6 * s) + t * (1 - t) * (1 - 2 * t)) := by
      rw [hfactor]
      exact hfactorNonneg
    nlinarith
  dsimp [s] at hbracket ⊢
  linarith

/-- The point where the cubic polynomial in the barrier argument attains its
maximum on `[0,1]`. -/
noncomputable def cubicPolynomialTMax : ℝ :=
  (1 / 2 : ℝ) * (1 + 1 / Real.sqrt 3)

theorem cubicPolynomialTMax_mem_unitInterval :
    cubicPolynomialTMax ∈ unitInterval := by
  have hspos : 0 < Real.sqrt 3 := by positivity
  have hssq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  unfold cubicPolynomialTMax unitInterval
  constructor <;> field_simp [hspos.ne'] <;> nlinarith

/-- Exact evaluation at the maximizing point from the source. -/
theorem cubicPolynomial_value_at_tMax :
    -cubicPolynomialTMax * (1 - cubicPolynomialTMax) *
        (1 - 2 * cubicPolynomialTMax) =
      1 / (6 * Real.sqrt 3) := by
  have hspos : 0 < Real.sqrt 3 := by positivity
  have hssq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  unfold cubicPolynomialTMax
  field_simp [hspos.ne']
  nlinarith

/-- The source's sharp maximum statement, including both the value and a point
where it is attained. -/
theorem cubicPolynomial_exact_maximum :
    IsGreatest
      ((fun t : ℝ ↦ -t * (1 - t) * (1 - 2 * t)) '' unitInterval)
      (1 / (6 * Real.sqrt 3)) := by
  constructor
  · exact ⟨cubicPolynomialTMax, cubicPolynomialTMax_mem_unitInterval,
      cubicPolynomial_value_at_tMax⟩
  · rintro value ⟨t, ht, rfl⟩
    exact cubicPolynomial_max_bound ht

/-- For `λ ≥ √3/2`, the explicit barrier has nonnegative residual on `[0,1]`. -/
theorem upperBarrier_residual_nonneg {lambda t : ℝ}
    (hlambda : Real.sqrt 3 / 2 ≤ lambda) (ht : t ∈ unitInterval) :
    0 ≤ residualValue lambda (upperBarrier lambda t)
      ((3 / (2 * lambda)) * (1 - 2 * t)) t := by
  have hspos : 0 < Real.sqrt 3 := by positivity
  have hssq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by positivity) hlambda
  let c : ℝ := 3 / (2 * lambda)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hcle : c ≤ Real.sqrt 3 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * lambda)]
    nlinarith [mul_nonneg hlambdaPos.le hspos.le]
  have hcCube : c ^ 3 ≤ (Real.sqrt 3) ^ 3 := by
    exact pow_le_pow_left₀ hcpos.le hcle 3
  have hsCube : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    nlinarith
  have hpoly := cubicPolynomial_max_bound ht
  have hpoly' : -(1 / (6 * Real.sqrt 3)) ≤ t * (1 - t) * (1 - 2 * t) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hpoly' (pow_nonneg hcpos.le 3)
  have hmul' : -c ^ 3 / (6 * Real.sqrt 3) ≤
      c ^ 3 * (t * (1 - t) * (1 - 2 * t)) := by
    calc
      -c ^ 3 / (6 * Real.sqrt 3) =
          c ^ 3 * (-(1 / (6 * Real.sqrt 3))) := by ring
      _ ≤ c ^ 3 * (t * (1 - t) * (1 - 2 * t)) := hmul
  have hfactor : 0 ≤
      1 / 2 + c ^ 3 * t * (1 - t) * (1 - 2 * t) := by
    have hcBound : c ^ 3 / (6 * Real.sqrt 3) ≤ 1 / 2 := by
      rw [hsCube] at hcCube
      have hden : 0 < 6 * Real.sqrt 3 := by positivity
      rw [div_le_iff₀ hden]
      nlinarith
    calc
      0 ≤ 1 / 2 - c ^ 3 / (6 * Real.sqrt 3) := sub_nonneg.mpr hcBound
      _ = 1 / 2 + (-c ^ 3 / (6 * Real.sqrt 3)) := by ring
      _ ≤ 1 / 2 + c ^ 3 * (t * (1 - t) * (1 - 2 * t)) :=
        by simpa [add_comm] using add_le_add_left hmul' (1 / 2)
      _ = 1 / 2 + c ^ 3 * t * (1 - t) * (1 - 2 * t) := by ring
  rw [upperBarrier_residual_identity hlambdaPos.ne']
  change 0 ≤ t * (1 - t) *
    (1 / 2 + c ^ 3 * t * (1 - t) * (1 - 2 * t))
  exact mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) hfactor

/-- The cube of the explicit barrier, used as a supersolution of the shooting ODE. -/
noncomputable def upperBarrierCube (lambda : ℝ) : ℝ → ℝ :=
  upperBarrier lambda ^ (3 : ℕ)

@[simp]
theorem upperBarrierCube_zero (lambda : ℝ) : upperBarrierCube lambda 0 = 0 := by
  simp [upperBarrierCube, upperBarrier]

@[simp]
theorem upperBarrierCube_one (lambda : ℝ) : upperBarrierCube lambda 1 = 0 := by
  simp [upperBarrierCube, upperBarrier]

/-- The source's explicit cube is a supersolution whenever `λ ≥ √3/2`. -/
theorem upperBarrierCube_isSupersolution {lambda : ℝ}
    (hlambda : lambdaUpper ≤ lambda) :
    IsCubeRootSupersolutionOn shootingForcing (3 * lambda)
      (upperBarrierCube lambda) 0 1 := by
  have hlambda' : Real.sqrt 3 / 2 ≤ lambda := by simpa [lambdaUpper] using hlambda
  constructor
  · have hw : Continuous (upperBarrier lambda) :=
      continuous_iff_continuousAt.mpr fun t ↦
        (upperBarrier_hasDerivAt lambda t).continuousAt
    exact (hw.pow 3).continuousOn
  · intro t ht
    let dw : ℝ := (3 / (2 * lambda)) * (1 - 2 * t)
    let derivativeCube : ℝ := 3 * upperBarrier lambda t ^ 2 * dw
    refine ⟨derivativeCube, ?_, ?_⟩
    · exact hasDerivAt_cube (upperBarrier_hasDerivAt lambda t)
    · have hR : 0 ≤ residualValue lambda (upperBarrier lambda t) dw t := by
        exact upperBarrier_residual_nonneg hlambda' ⟨ht.1.le, ht.2.le⟩
      have hsuper := cube_supersolution_of_residual_nonneg hR
      simpa only [shootingForcing, yRhs, upperBarrierCube, Pi.pow_apply,
        derivativeCube, dw, mul_assoc] using hsuper

/-- Every parameter above the source's explicit threshold is admissible. -/
theorem mem_admissibleSet_of_lambdaUpper_le {lambda : ℝ}
    (hlambda : lambdaUpper ≤ lambda) : lambda ∈ admissibleSet := by
  have hlambdaPos : 0 < lambda := lambdaUpper_pos.trans_le hlambda
  let y := shootingY lambda hlambdaPos
  have hy := shootingY_isSolution lambda hlambdaPos
  have hcomparison : ∀ t ∈ unitInterval, y t ≤ upperBarrierCube lambda t :=
    cuberoot_comparison (by norm_num) ShootingAux.forcing_continuous.continuousOn
      (mul_pos (by norm_num) hlambdaPos)
      (ShootingAux.exact_subsolution hy.2.1 hy.2.2.2.2)
      (upperBarrierCube_isSupersolution hlambda)
      (by simp [y, hy.2.2.2.1])
  have hy_le : y 1 ≤ 0 := by
    simpa using hcomparison 1 ⟨by norm_num, le_rfl⟩
  have hy_nonneg : 0 ≤ y 1 :=
    shooting_solution_nonneg hlambdaPos hy 1 ⟨by norm_num, le_rfl⟩
  exact ⟨hlambdaPos, le_antisymm hy_le hy_nonneg⟩

theorem lambdaUpper_mem_admissibleSet : lambdaUpper ∈ admissibleSet :=
  mem_admissibleSet_of_lambdaUpper_le le_rfl

theorem admissibleSet_nonempty : admissibleSet.Nonempty :=
  ⟨lambdaUpper, lambdaUpper_mem_admissibleSet⟩

end SeriesParallel.Appendix
