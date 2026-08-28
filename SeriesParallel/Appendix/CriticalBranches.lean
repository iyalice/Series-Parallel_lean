import SeriesParallel.Appendix.AdmissibleHalfline
import SeriesParallel.Appendix.EndpointAsymptotics
import SeriesParallel.Appendix.LeftEndpointDichotomy

/-!
# Critical and supercritical left branches

This module formalizes Proposition `prop:critical-branches`.  Its first block isolates the
shifted linear supersolution used to rule out a linear branch at the left endpoint.
-/

open Set Filter Topology Asymptotics

namespace SeriesParallel.Appendix

/-- The shifted barrier `w(t)=k(1-t)` from the proof of `prop:critical-branches`. -/
def shiftedLinearBarrier (k t : ℝ) : ℝ := k * (1 - t)

def shiftedLinearBarrierCube (k t : ℝ) : ℝ :=
  shiftedLinearBarrier k t ^ (3 : ℕ)

theorem shiftedLinearBarrier_hasDerivAt (k t : ℝ) :
    HasDerivAt (shiftedLinearBarrier k) (-k) t := by
  unfold shiftedLinearBarrier
  have hlinear : HasDerivAt (fun x : ℝ ↦ k * x) k (1 - t) :=
    hasDerivAt_const_mul k
  exact hlinear.comp_const_sub 1 t

theorem shiftedLinearBarrier_residual (lambda k t : ℝ) :
    residualValue lambda (shiftedLinearBarrier k t) (-k) t =
      (1 - t) * (lambda * k - 1) + (1 - t) ^ 2 * (1 - k ^ 3) := by
  unfold residualValue shiftedLinearBarrier
  ring

/-- The source's small-interval estimate makes the shifted barrier a supersolution. -/
theorem shiftedLinearBarrierCube_isSupersolution {lambda k eta : ℝ}
    (hgap : eta * |1 - k ^ 3| ≤ lambda * k - 1) :
    IsCubeRootSupersolutionOn shootingForcing (3 * lambda)
      (shiftedLinearBarrierCube k) (1 - eta) 1 := by
  constructor
  · have hcontinuous : Continuous (shiftedLinearBarrier k) :=
      continuous_iff_continuousAt.mpr fun t ↦
        (shiftedLinearBarrier_hasDerivAt k t).continuousAt
    exact (hcontinuous.pow 3).continuousOn
  · intro t ht
    have hu0 : 0 < 1 - t := sub_pos.mpr ht.2
    have hueta : 1 - t < eta := by linarith [ht.1]
    let derivativeCube : ℝ := 3 * shiftedLinearBarrier k t ^ 2 * (-k)
    refine ⟨derivativeCube, hasDerivAt_cube (shiftedLinearBarrier_hasDerivAt k t), ?_⟩
    apply cube_supersolution_of_residual_nonneg
    rw [shiftedLinearBarrier_residual]
    have habsLower : -|1 - k ^ 3| ≤ 1 - k ^ 3 := neg_abs_le (1 - k ^ 3)
    have huabs : (1 - t) * |1 - k ^ 3| ≤ eta * |1 - k ^ 3| :=
      mul_le_mul_of_nonneg_right hueta.le (abs_nonneg _)
    have hbracket : 0 ≤ lambda * k - 1 + (1 - t) * (1 - k ^ 3) := by
      nlinarith [mul_le_mul_of_nonneg_left habsLower hu0.le]
    nlinarith

/-- A shifted supersolution touching the shooting solution at `1-eta` forces admissibility. -/
theorem mem_admissibleSet_of_shiftedLinearBarrier {lambda k eta : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hgap : eta * |1 - k ^ 3| ≤ lambda * k - 1)
    (hendpoint : WSolution lambda hlambda eta ≤ k * eta) :
    lambda ∈ admissibleSet := by
  let y := shootingY lambda hlambda
  have hy := shootingY_isSolution lambda hlambda
  have ht0 : 1 - eta < 1 := by linarith
  have ht0mem : 1 - eta ∈ unitInterval := ⟨by linarith, by linarith⟩
  have hWnonneg : 0 ≤ WSolution lambda hlambda eta := by
    unfold WSolution wOfY
    exact Real.cbrt_nonneg.mpr
      (shooting_solution_nonneg hlambda hy (1 - eta) ht0mem)
  have hketa : 0 ≤ k * eta := mul_nonneg hk.le heta.le
  have hcubeOrder : WSolution lambda hlambda eta ^ 3 ≤ (k * eta) ^ 3 :=
    pow_le_pow_left₀ hWnonneg hendpoint 3
  have hWcube : WSolution lambda hlambda eta ^ 3 = y (1 - eta) := by
    simp [WSolution, wOfY, y]
  have hinitial : y (1 - eta) ≤ shiftedLinearBarrierCube k (1 - eta) := by
    unfold shiftedLinearBarrierCube shiftedLinearBarrier
    rw [← hWcube]
    simpa only [sub_sub_cancel] using hcubeOrder
  have hcomparison : ∀ t ∈ Icc (1 - eta) 1,
      y t ≤ shiftedLinearBarrierCube k t :=
    cuberoot_comparison ht0 ShootingAux.forcing_continuous.continuousOn
      (mul_pos (by norm_num) hlambda)
      (ShootingAux.exact_subsolution
        (hy.2.1.mono fun t ht ↦ ⟨ht0mem.1.trans ht.1, ht.2⟩)
        (fun t ht ↦ hy.2.2.2.2 t
          ⟨ht0mem.1.trans_lt ht.1, ht.2⟩))
      (shiftedLinearBarrierCube_isSupersolution hgap) hinitial
  have hyUpper : y 1 ≤ 0 := by
    simpa [shiftedLinearBarrierCube, shiftedLinearBarrier] using
      hcomparison 1 ⟨by linarith, le_rfl⟩
  have hyLower : 0 ≤ y 1 :=
    shooting_solution_nonneg hlambda hy 1 ⟨by norm_num, le_rfl⟩
  exact ⟨hlambda, le_antisymm hyUpper hyLower⟩

/-- A linear branch lies eventually below every strictly larger linear slope. -/
theorem linearBranch_eventually_lt_slope {lambda k : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hk : lambda⁻¹ < k)
    (hlinear : HasLinearBranchAtZero lambda W) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), W u < k * u := by
  have hdenom : ∀ᶠ u in 𝓝[>] (0 : ℝ), u / lambda ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    change 0 < u at hu
    exact div_ne_zero hu.ne' hlambda.ne'
  have hratio : Tendsto (fun u ↦ W u / (u / lambda)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hdenom).mp hlinear
  have hkproduct : 1 < k * lambda := by
    exact (inv_lt_iff_one_lt_mul₀ hlambda).mp hk
  have hratioBound : ∀ᶠ u in 𝓝[>] (0 : ℝ), W u / (u / lambda) < k * lambda :=
    hratio.eventually (Iio_mem_nhds hkproduct)
  filter_upwards [hratioBound, self_mem_nhdsWithin] with u hratioU hu
  change 0 < u at hu
  rw [div_lt_iff₀ (div_pos hu hlambda)] at hratioU
  field_simp [hlambda.ne'] at hratioU ⊢
  nlinarith

/-- The slope and interval length required by the shifted barrier can be chosen from a
linear asymptotic. -/
theorem exists_shiftedBarrier_data_of_linearBranch {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hlinear : HasLinearBranchAtZero lambda W) :
    ∃ k eta : ℝ, 0 < k ∧ lambda⁻¹ < k ∧ 0 < eta ∧ eta ≤ 1 ∧
      eta * |1 - k ^ 3| ≤ (lambda * k - 1) / 2 ∧ W eta < k * eta := by
  let k : ℝ := lambda⁻¹ + 1
  have hk : lambda⁻¹ < k := by simp [k]
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hgap : 0 < lambda * k - 1 := by
    dsimp [k]
    rw [mul_add, mul_inv_cancel₀ hlambda.ne']
    linarith
  let etaBound : ℝ := min 1 ((lambda * k - 1) / (2 * (|1 - k ^ 3| + 1)))
  have hetaBoundPos : 0 < etaBound := by
    dsimp [etaBound]
    positivity
  have hsmall : ∀ᶠ eta in 𝓝[>] (0 : ℝ), eta ∈ Ioc 0 etaBound :=
    Ioc_mem_nhdsGT hetaBoundPos
  obtain ⟨eta, hetaSmall, hetaSlope⟩ :=
    (hsmall.and (linearBranch_eventually_lt_slope hlambda hk hlinear)).exists
  have hetaOne : eta ≤ 1 := hetaSmall.2.trans (min_le_left _ _)
  have hboundCore : eta ≤ (lambda * k - 1) / (2 * (|1 - k ^ 3| + 1)) :=
    hetaSmall.2.trans (min_le_right _ _)
  have habs : 0 ≤ |1 - k ^ 3| := abs_nonneg _
  have hgapBound : eta * |1 - k ^ 3| ≤ (lambda * k - 1) / 2 := by
    have hdenomPos : 0 < 2 * (|1 - k ^ 3| + 1) := by positivity
    rw [le_div_iff₀ hdenomPos] at hboundCore
    nlinarith [mul_nonneg hetaSmall.1.le habs]
  exact ⟨k, eta, hkpos, hk, hetaSmall.1, hetaOne, hgapBound, hetaSlope⟩

/-- Any shooting solution with a linear branch produces a strictly smaller admissible
parameter by the shifted-barrier construction. -/
theorem exists_smaller_admissible_of_linearBranch {lambda : ℝ} (hlambda : 0 < lambda)
    (hlinear : HasLinearBranchAtZero lambda (WSolution lambda hlambda)) :
    ∃ lambda' : ℝ, 0 < lambda' ∧ lambda' < lambda ∧ lambda' ∈ admissibleSet := by
  obtain ⟨k, eta, hkpos, hk, heta, hetaOne, hgap, hendpoint⟩ :=
    exists_shiftedBarrier_data_of_linearBranch hlambda hlinear
  let etaPoint : unitInterval :=
    ⟨1 - eta, ⟨by linarith [hetaOne], by linarith [heta]⟩⟩
  let endpointValue : {mu : ℝ // 0 < mu} → ℝ := fun parameter ↦
    Real.cbrt (shootingYMap parameter etaPoint)
  have hendpointContinuous : Continuous endpointValue := by
    unfold endpointValue
    exact Real.continuous_cbrt.comp
      ((continuous_eval_const etaPoint).comp continuous_shootingYMap)
  let parameter : {mu : ℝ // 0 < mu} := ⟨lambda, hlambda⟩
  have hendpointAt : endpointValue parameter = WSolution lambda hlambda eta := by
    rfl
  have hnear : ∀ᶠ p in 𝓝 parameter, endpointValue p < k * eta := by
    have hopen : Iio (k * eta) ∈ 𝓝 (endpointValue parameter) := by
      rw [hendpointAt]
      exact Iio_mem_nhds hendpoint
    exact hendpointContinuous.continuousAt.tendsto.eventually hopen
  have hkLambda : k⁻¹ < lambda := by
    rw [inv_lt_iff_one_lt_mul₀ hkpos]
    simpa only [mul_comm] using (inv_lt_iff_one_lt_mul₀ hlambda).mp hk
  let lowerValue : ℝ := (k⁻¹ + lambda) / 2
  have hlowerPos : 0 < lowerValue := by
    dsimp [lowerValue]
    positivity
  let lowerParameter : {mu : ℝ // 0 < mu} := ⟨lowerValue, hlowerPos⟩
  have hlower : lowerParameter < parameter := by
    change lowerValue < lambda
    dsimp [lowerValue]
    linarith
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let delta : ℝ := min ((lambda - lowerValue) / 2) (epsilon / 2)
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    have : lowerValue < lambda := hlower
    positivity
  let lambda' : ℝ := lambda - delta
  have hlower' : lowerValue < lambda' := by
    have hdeltaLe : delta ≤ (lambda - lowerValue) / 2 := min_le_left _ _
    dsimp [lambda']
    linarith
  have hlambda' : 0 < lambda' := hlowerPos.trans hlower'
  have hlambda'lt : lambda' < lambda := by
    dsimp [lambda']
    linarith
  let parameter' : {mu : ℝ // 0 < mu} := ⟨lambda', hlambda'⟩
  have hparameterBall : parameter' ∈ Metric.ball parameter epsilon := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    change |lambda' - lambda| < epsilon
    have hdeltaLe : delta ≤ epsilon / 2 := min_le_right _ _
    rw [show lambda' - lambda = -delta by dsimp [lambda']; ring, abs_neg,
      abs_of_nonneg hdeltaPos.le]
    linarith
  have hparameterEndpoint : endpointValue parameter' < k * eta := hball hparameterBall
  have hgap' : eta * |1 - k ^ 3| ≤ lambda' * k - 1 := by
    have hkinv : k * k⁻¹ = 1 := mul_inv_cancel₀ hkpos.ne'
    dsimp [lowerValue] at hlower'
    nlinarith [hgap]
  have hendpoint' : WSolution lambda' hlambda' eta ≤ k * eta := by
    exact hparameterEndpoint.le
  refine ⟨lambda', hlambda', hlambda'lt,
    mem_admissibleSet_of_shiftedLinearBarrier hlambda' hkpos heta hetaOne hgap'
      hendpoint'⟩

/-- Minimality of `lambdaStar` rules out the linear left branch at the critical
parameter. -/
theorem lambdaStar_not_linearBranch :
    ¬ HasLinearBranchAtZero lambdaStar (WSolution lambdaStar lambdaStar_pos) := by
  intro hlinear
  obtain ⟨lambda', hlambda', hlt, hadmissible'⟩ :=
    exists_smaller_admissible_of_linearBranch lambdaStar_pos hlinear
  have hstarLe : lambdaStar ≤ lambda' :=
    mem_admissibleSet_iff_lambdaStar_le.mp hadmissible'
  exact (not_lt_of_ge hstarLe) hlt

/-- Increasing the shooting parameter strictly lowers the transformed solution
at every interior point. -/
theorem WSolution_strictAnti {lambda₁ lambda₂ : ℝ} (hlambda₁ : 0 < lambda₁)
    (horder : lambda₁ < lambda₂) :
    ∀ u ∈ openUnitInterval,
      WSolution lambda₂ (hlambda₁.trans horder) u < WSolution lambda₁ hlambda₁ u := by
  intro u hu
  unfold WSolution wOfY
  apply Real.strictMono_cbrt
  exact shootingY_strictAnti hlambda₁ horder (1 - u)
    ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- A sharp branch, after division by `sqrt u`, converges to its parameter-dependent
coefficient `sqrt (2*lambda)`. -/
theorem sharpBranch_normalized_tendsto {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hsharp : HasSharpBranchAtZero lambda W) :
    Tendsto (fun u : ℝ ↦ W u / Real.sqrt u) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (2 * lambda))) := by
  have hdenom : ∀ᶠ u in 𝓝[>] (0 : ℝ), Real.sqrt (2 * lambda * u) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact Real.sqrt_ne_zero'.mpr (mul_pos (mul_pos (by norm_num) hlambda) hu)
  have hratio : Tendsto
      (fun u : ℝ ↦ W u / Real.sqrt (2 * lambda * u))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hdenom).mp hsharp
  have hscaled := hratio.mul_const (Real.sqrt (2 * lambda))
  have hscaled' : Tendsto
      (fun u : ℝ ↦ (W u / Real.sqrt (2 * lambda * u)) * Real.sqrt (2 * lambda))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (2 * lambda))) := by
    simpa only [one_mul] using hscaled
  apply (tendsto_congr' ?_).2 hscaled'
  filter_upwards [self_mem_nhdsWithin] with u hu
  · have huPos : 0 < u := hu
    have hcoefficientPos : 0 < 2 * lambda := mul_pos (by norm_num) hlambda
    rw [Real.sqrt_mul hcoefficientPos.le]
    field_simp [Real.sqrt_ne_zero'.mpr huPos,
      Real.sqrt_ne_zero'.mpr hcoefficientPos]

/-- Pointwise strict shooting order is incompatible with sharp asymptotics carrying
a strictly larger parameter. -/
theorem parameter_le_of_sharpBranches_of_strictly_below
    {lambda₁ lambda₂ : ℝ} {W₁ W₂ : ℝ → ℝ}
    (hlambda₁ : 0 < lambda₁) (hlambda₂ : 0 < lambda₂)
    (hbelow : ∀ u ∈ openUnitInterval, W₂ u < W₁ u)
    (hsharp₁ : HasSharpBranchAtZero lambda₁ W₁)
    (hsharp₂ : HasSharpBranchAtZero lambda₂ W₂) :
    lambda₂ ≤ lambda₁ := by
  by_contra hnot
  have horder : lambda₁ < lambda₂ := lt_of_not_ge hnot
  have hcoefficientOrder :
      Real.sqrt (2 * lambda₁) < Real.sqrt (2 * lambda₂) := by
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  let midpoint : ℝ :=
    (Real.sqrt (2 * lambda₁) + Real.sqrt (2 * lambda₂)) / 2
  have hleftMidpoint : Real.sqrt (2 * lambda₁) < midpoint := by
    dsimp [midpoint]
    linarith
  have hmidpointRight : midpoint < Real.sqrt (2 * lambda₂) := by
    dsimp [midpoint]
    linarith
  have heventuallyLeft :
      ∀ᶠ u in 𝓝[>] (0 : ℝ), W₁ u / Real.sqrt u < midpoint :=
    (sharpBranch_normalized_tendsto hlambda₁ hsharp₁).eventually
      (Iio_mem_nhds hleftMidpoint)
  have heventuallyRight :
      ∀ᶠ u in 𝓝[>] (0 : ℝ), midpoint < W₂ u / Real.sqrt u :=
    (sharpBranch_normalized_tendsto hlambda₂ hsharp₂).eventually
      (Ioi_mem_nhds hmidpointRight)
  have heventuallySmall :
      ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioc 0 ((1 : ℝ) / 2) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨u, huSmall, huLeft, huRight⟩ :=
    (heventuallySmall.and (heventuallyLeft.and heventuallyRight)).exists
  have huOpen : u ∈ openUnitInterval :=
    ⟨huSmall.1, huSmall.2.trans_lt (by norm_num)⟩
  have hsqrtPos : 0 < Real.sqrt u := Real.sqrt_pos.2 huSmall.1
  have hratioOrder : W₂ u / Real.sqrt u < W₁ u / Real.sqrt u :=
    div_lt_div_of_pos_right (hbelow u huOpen) hsqrtPos
  linarith

/-- The critical alternative in any established A6 dichotomy must be the sharp one. -/
theorem critical_sharp_of_dichotomy
    (hdichotomy : HasExactlyOneLeftBranch lambdaStar
      (WSolution lambdaStar lambdaStar_pos)) :
    HasSharpBranchAtZero lambdaStar (WSolution lambdaStar lambdaStar_pos) := by
  rcases hdichotomy with ⟨hlinear, _⟩ | ⟨hsharp, _⟩
  · exact (lambdaStar_not_linearBranch hlinear).elim
  · exact hsharp

/-- Strict shooting order and the critical sharp branch exclude the sharp branch at
every strictly supercritical parameter. -/
theorem supercritical_not_sharp_of_critical_sharp {lambda : ℝ}
    (horder : lambdaStar < lambda)
    (hcritical : HasSharpBranchAtZero lambdaStar
      (WSolution lambdaStar lambdaStar_pos)) :
    ¬ HasSharpBranchAtZero lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) := by
  intro hsharp
  have hparameterLe := parameter_le_of_sharpBranches_of_strictly_below
    lambdaStar_pos (lambdaStar_pos.trans horder)
    (WSolution_strictAnti lambdaStar_pos horder) hcritical hsharp
  exact (not_le_of_gt horder) hparameterLe

/-- Once A6 supplies the exclusive alternatives, excluding the sharp one selects
the linear branch. -/
theorem supercritical_linear_of_dichotomy {lambda : ℝ}
    (horder : lambdaStar < lambda)
    (hdichotomy : HasExactlyOneLeftBranch lambda
      (WSolution lambda (lambdaStar_pos.trans horder)))
    (hnotSharp : ¬ HasSharpBranchAtZero lambda
      (WSolution lambda (lambdaStar_pos.trans horder))) :
    HasLinearBranchAtZero lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) := by
  rcases hdichotomy with ⟨hlinear, _⟩ | ⟨hsharp, _⟩
  · exact hlinear
  · exact (hnotSharp hsharp).elim

/-- Source-facing package for Proposition `prop:critical-branches`. -/
structure CriticalBranchesConclusion : Prop where
  criticalSharp :
    HasSharpBranchAtZero lambdaStar (WSolution lambdaStar lambdaStar_pos)
  supercriticalLinear : ∀ (lambda : ℝ) (horder : lambdaStar < lambda),
    HasLinearBranchAtZero lambda
      (WSolution lambda (lambdaStar_pos.trans horder))

/-- Logical assembly of A7 from the A6 dichotomy at the critical and all strictly
supercritical parameters.  This keeps the analytic branch selection independent of
the construction used to establish A6. -/
theorem criticalBranches_of_dichotomy
    (hcriticalDichotomy : HasExactlyOneLeftBranch lambdaStar
      (WSolution lambdaStar lambdaStar_pos))
    (hsupercriticalDichotomy : ∀ (lambda : ℝ) (horder : lambdaStar < lambda),
      HasExactlyOneLeftBranch lambda
        (WSolution lambda (lambdaStar_pos.trans horder))) :
    CriticalBranchesConclusion := by
  have hcritical := critical_sharp_of_dichotomy hcriticalDichotomy
  refine ⟨hcritical, ?_⟩
  intro lambda horder
  exact supercritical_linear_of_dichotomy horder
    (hsupercriticalDichotomy lambda horder)
    (supercritical_not_sharp_of_critical_sharp horder hcritical)

/-- Proposition `prop:critical-branches`: the critical solution has the sharp branch,
whereas every strictly supercritical solution has the linear branch. -/
theorem criticalBranches : CriticalBranchesConclusion := by
  apply criticalBranches_of_dichotomy
  · rcases lambdaStar_mem_admissibleSet with ⟨_, hzero⟩
    apply leftEndpointDichotomy lambdaStar_pos
    apply WSolution_isBoundarySolution lambdaStar_pos
    simpa only using hzero
  · intro lambda horder
    have hadmissible : lambda ∈ admissibleSet :=
      mem_admissibleSet_iff_lambdaStar_le.mpr horder.le
    rcases hadmissible with ⟨_, hzero⟩
    have hlambda : 0 < lambda := lambdaStar_pos.trans horder
    apply leftEndpointDichotomy hlambda
    apply WSolution_isBoundarySolution hlambda
    simpa only using hzero

end SeriesParallel.Appendix
