import SeriesParallel.Appendix.HardEdgeConsequences

/-!
# Positive full-line extension of a hard-edge density

The construction follows the final paragraph of B4: extend `log q` by its cubic
right jet, flatten that polynomial with the smooth cutoff, glue at zero, and
exponentiate.
-/

open Filter Set
open scoped ContDiff Topology

namespace SeriesParallel.Appendix

private theorem rightJetPolynomial3_jet {h : ℝ → ℝ} {k : ℕ} (hk : k ≤ 3) :
    iteratedDerivWithin k (rightJetPolynomial3 h) (Iic 0) 0 =
      iteratedDerivWithin k h (Ici 0) 0 := by
  have hpoly : ContDiffAt ℝ k (rightJetPolynomial3 h) 0 := by
    unfold rightJetPolynomial3
    fun_prop
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic (0 : ℝ)) hpoly
    (show (0 : ℝ) ∈ Iic 0 by simp)]
  unfold rightJetPolynomial3
  rw [iteratedDeriv_fun_sum (fun i _ ↦ by fun_prop)]
  interval_cases k
  · simp [Fin.sum_univ_four]
  · simp [Fin.sum_univ_four]
  · simp [Fin.sum_univ_four]
  · simp [Fin.sum_univ_four]
    ring

/-- Gluing two `C³` functions along matching one-sided jets is proved here from
the ordinary derivative and continuity characterizations of `ContDiff`. -/
private theorem contDiff_three_if_le_of_matching_jets
    (left right : ℝ → ℝ) (point : ℝ)
    (hleft : ContDiffOn ℝ 3 left (Iic point))
    (hright : ContDiffOn ℝ 3 right (Ici point))
    (hjets : ∀ k ≤ 3, iteratedDerivWithin k left (Iic point) point =
      iteratedDerivWithin k right (Ici point) point) :
    ContDiff ℝ 3 (fun x ↦ if x ≤ point then left x else right x) := by
  let J : ℕ → ℝ → ℝ := fun k x ↦
    if x ≤ point then iteratedDerivWithin k left (Iic point) x
    else iteratedDerivWithin k right (Ici point) x
  have hJzero : J 0 = fun x ↦ if x ≤ point then left x else right x := by
    funext x
    simp [J, iteratedDerivWithin_zero]
  have hJderiv : ∀ k < 3, ∀ x, HasDerivAt (J k) (J (k + 1) x) x := by
    intro k hk x
    rcases lt_trichotomy x point with hx | hxeq | hx
    · have hxN : Iic point ∈ 𝓝 x := Iic_mem_nhds hx
      have hdWithin := hleft.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Iic point) x hx.le
      have hdAt := hdWithin.differentiableAt hxN
      have hcoef : deriv (iteratedDerivWithin k left (Iic point)) x =
          iteratedDerivWithin (k + 1) left (Iic point) x := by
        rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hxN]
      have hlocal : J k =ᶠ[𝓝 x] iteratedDerivWithin k left (Iic point) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        have hy' : y < point := hy
        simp only [J, if_pos hy'.le]
      have hvalue : J (k + 1) x =
          iteratedDerivWithin (k + 1) left (Iic point) x := by simp [J, hx.le]
      exact (hdAt.hasDerivAt.congr_of_eventuallyEq hlocal).congr_deriv
        (by rw [hcoef, hvalue])
    · subst x
      have hlBase := hleft.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Iic point) point self_mem_Iic
      have hlDeriv : HasDerivWithinAt (iteratedDerivWithin k left (Iic point))
          (iteratedDerivWithin (k + 1) left (Iic point) point) (Iic point) point := by
        rw [iteratedDerivWithin_succ]
        exact hlBase.hasDerivWithinAt
      have hlJ : HasDerivWithinAt (J k)
          (iteratedDerivWithin (k + 1) left (Iic point) point) (Iic point) point := by
        apply hlDeriv.congr
        · intro y hy
          change y ≤ point at hy
          simp only [J, if_pos hy]
        · simp [J]
      have hrBase := hright.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Ici point) point self_mem_Ici
      have hrDeriv : HasDerivWithinAt (iteratedDerivWithin k right (Ici point))
          (iteratedDerivWithin (k + 1) right (Ici point) point) (Ici point) point := by
        rw [iteratedDerivWithin_succ]
        exact hrBase.hasDerivWithinAt
      have hk1 : k + 1 ≤ 3 := by omega
      have hk0 : k ≤ 3 := by omega
      have hrJ : HasDerivWithinAt (J k)
          (iteratedDerivWithin (k + 1) left (Iic point) point) (Ici point) point := by
        have hrDeriv' := hrDeriv.congr_deriv (hjets (k + 1) hk1).symm
        apply hrDeriv'.congr
        · intro y hy
          by_cases hyp : y = point
          · subst y
            simp [J, hjets k hk0]
          · have hy' : point < y := lt_of_le_of_ne hy (Ne.symm hyp)
            simp only [J, if_neg (not_le.mpr hy')]
        · simp [J, hjets k hk0]
      have hunion := hlJ.union hrJ
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
      simpa [J] using hunion
    · have hxN : Ici point ∈ 𝓝 x := Ici_mem_nhds hx
      have hdWithin := hright.differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Ici point) x hx.le
      have hdAt := hdWithin.differentiableAt hxN
      have hcoef : deriv (iteratedDerivWithin k right (Ici point)) x =
          iteratedDerivWithin (k + 1) right (Ici point) x := by
        rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hxN]
      have hlocal : J k =ᶠ[𝓝 x] iteratedDerivWithin k right (Ici point) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        have hy' : point < y := hy
        simp only [J, if_neg (not_le.mpr hy')]
      have hvalue : J (k + 1) x =
          iteratedDerivWithin (k + 1) right (Ici point) x := by
        simp [J, not_le.mpr hx]
      exact (hdAt.hasDerivAt.congr_of_eventuallyEq hlocal).congr_deriv
        (by rw [hcoef, hvalue])
  have hJcont : ∀ k ≤ 3, Continuous (J k) := by
    intro k hk
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_trichotomy x point with hx | hxeq | hx
    · have hxN : Iic point ∈ 𝓝 x := Iic_mem_nhds hx
      have hbranch := hleft.continuousOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Iic point) x hx.le
      apply (hbranch.continuousAt hxN).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hy' : y < point := hy
      simp only [J, if_pos hy'.le]
    · subst x
      have hl := hleft.continuousOn_iteratedDerivWithin
          (by exact_mod_cast hk)
          (uniqueDiffOn_Iic point) point self_mem_Iic
      have hr := hright.continuousOn_iteratedDerivWithin
          (by exact_mod_cast hk)
          (uniqueDiffOn_Ici point) point self_mem_Ici
      have hlJ : ContinuousWithinAt (J k) (Iic point) point :=
        hl.congr (fun y hy ↦ by
          change y ≤ point at hy
          simp only [J, if_pos hy]) (by simp [J])
      have hrJ : ContinuousWithinAt (J k) (Ici point) point := by
        apply hr.congr
        · intro y hy
          by_cases hyp : y = point
          · subst y
            simp [J, hjets k hk]
          · have hy' : point < y := lt_of_le_of_ne hy (Ne.symm hyp)
            simp only [J, if_neg (not_le.mpr hy')]
        · simp [J, hjets k hk]
      have hu := hlJ.union hrJ
      rw [Iic_union_Ici, continuousWithinAt_univ] at hu
      exact hu
    · have hxN : Ici point ∈ 𝓝 x := Ici_mem_nhds hx
      have hbranch := hright.continuousOn_iteratedDerivWithin
        (by exact_mod_cast hk)
        (uniqueDiffOn_Ici point) x hx.le
      apply (hbranch.continuousAt hxN).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have hy' : point < y := hy
      simp only [J, if_neg (not_le.mpr hy')]
  have hC2 : ContDiff ℝ 1 (J 2) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x ↦ (hJderiv 2 (by omega) x).differentiableAt, ?_⟩
    exact (hJcont 3 le_rfl).congr (fun x ↦ (hJderiv 2 (by omega) x).deriv.symm)
  have hC1 : ContDiff ℝ 2 (J 1) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hJderiv 1 (by omega) x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : deriv (J 1) = J 2 := by
        funext x
        exact (hJderiv 1 (by omega) x).deriv
      rw [heq]
      exact hC2
  have hC0 : ContDiff ℝ 3 (J 0) := by
    rw [show (3 : ℕ∞ω) = 2 + 1 by norm_num, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hJderiv 0 (by omega) x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : deriv (J 0) = J 1 := by
        funext x
        exact (hJderiv 0 (by omega) x).deriv
      rw [heq]
      exact hC1
  rw [hJzero] at hC0
  exact hC0

private theorem extendedLogDensity_contDiff_three {q : ℝ → ℝ}
    (hqSmooth : ContDiffOn ℝ 3 q (Ici 0))
    (hqPos : ∀ z ∈ Ici (0 : ℝ), 0 < q z) :
    ∃ cutoff : ℝ → ℝ, ContDiff ℝ 3 (extendedLogDensity q cutoff) ∧
      (∀ z ∈ Ici (0 : ℝ), extendedDensity q cutoff z = q z) ∧
      (∀ z ∈ Iio (-1 : ℝ),
        extendedLogDensity q cutoff z = logDensity q 0) := by
  let h : ℝ → ℝ := logDensity q
  have hhSmooth : ContDiffOn ℝ 3 h (Ici 0) := by
    exact hqSmooth.log (fun z hz ↦ (hqPos z hz).ne')
  rcases ManualInterfaces.MI13_smooth_cutoff with
    ⟨cutoff, hcutoffSmooth, hcutoffOne, hcutoffZero, hcutoffRange⟩
  let P : ℝ → ℝ := rightJetPolynomial3 h
  let left : ℝ → ℝ := fun z ↦
    cutoff z * P z + (1 - cutoff z) * h 0
  have hP : ContDiff ℝ ∞ P := by
    dsimp only [P]
    unfold rightJetPolynomial3
    exact ContDiff.sum fun _ _ ↦ by fun_prop
  have hleftSmooth : ContDiff ℝ 3 left := by
    have hcutoffThree : ContDiff ℝ 3 cutoff :=
      contDiff_infty.mp hcutoffSmooth 3
    have hPThree : ContDiff ℝ 3 P := contDiff_infty.mp hP 3
    dsimp only [left]
    exact (hcutoffThree.mul hPThree).add
      ((contDiff_const.sub hcutoffThree).mul contDiff_const)
  have hleftP : left =ᶠ[nhdsWithin 0 (Iic (0 : ℝ))] P := by
    have hlow : ∀ᶠ z in nhdsWithin 0 (Iic (0 : ℝ)), z ∈ Ioi (-(1 / 2 : ℝ)) :=
      (show ∀ᶠ z in nhds (0 : ℝ), z ∈ Ioi (-(1 / 2 : ℝ)) from
        Ioi_mem_nhds (by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hlow] with z hzIic hzlow
    have hcut : cutoff z = 1 := hcutoffOne z ⟨hzlow.le, hzIic⟩
    simp only [left, hcut, one_mul, sub_self, zero_mul, add_zero]
  have hPzero : P 0 = h 0 := by
    have hjet := rightJetPolynomial3_jet (h := h) (k := 0) (by norm_num)
    simpa only [P, iteratedDerivWithin_zero] using hjet
  have hleftZero : left 0 = h 0 := by
    have hcut : cutoff 0 = 1 := hcutoffOne 0 (by constructor <;> norm_num)
    simp only [left, hcut, one_mul, sub_self, zero_mul, add_zero, hPzero]
  have hjets : ∀ k ≤ 3,
      iteratedDerivWithin k left (Iic 0) 0 =
        iteratedDerivWithin k h (Ici 0) 0 := by
    intro k hk
    calc
      iteratedDerivWithin k left (Iic 0) 0 =
          iteratedDerivWithin k P (Iic 0) 0 :=
        hleftP.iteratedDerivWithin_eq (by exact hleftZero.trans hPzero.symm)
      _ = iteratedDerivWithin k h (Ici 0) 0 :=
        rightJetPolynomial3_jet hk
  have hglued : ContDiff ℝ 3 (fun z ↦ if z ≤ 0 then left z else h z) :=
    contDiff_three_if_le_of_matching_jets left h 0
      hleftSmooth.contDiffOn hhSmooth hjets
  have hbarEq : extendedLogDensity q cutoff =
      fun z ↦ if z ≤ 0 then left z else h z := by
    funext z
    by_cases hz : 0 ≤ z
    · rw [show extendedLogDensity q cutoff z = h z by
        simp only [extendedLogDensity, if_pos hz, h]]
      by_cases hz' : z ≤ 0
      · have : z = 0 := le_antisymm hz' hz
        subst z
        simp only [if_pos le_rfl, hleftZero]
      · simp only [if_neg hz']
    · have hz' : z ≤ 0 := (lt_of_not_ge hz).le
      simp only [extendedLogDensity, if_neg hz, if_pos hz', left, P, h]
  have hbarSmooth : ContDiff ℝ 3 (extendedLogDensity q cutoff) := by
    rw [hbarEq]
    exact hglued
  refine ⟨cutoff, hbarSmooth, ?_, ?_⟩
  · intro z hz
    change 0 ≤ z at hz
    unfold extendedDensity extendedLogDensity logDensity
    rw [if_pos hz, Real.exp_log (hqPos z hz)]
  · intro z hz
    change z < -1 at hz
    have hzneg : ¬ 0 ≤ z := not_le.mpr (hz.trans (by norm_num))
    have hzIic : z ∈ Iic (-1 : ℝ) := by
      change z ≤ -1
      exact hz.le
    have hcut : cutoff z = 0 := hcutoffZero z hzIic
    simp [extendedLogDensity, hzneg, hcut, logDensity]

/-- A positive one-sided `C³` density with the B4 relative derivative bounds has
the positive global `C³` extension constructed in the source. -/
theorem exists_positiveC3DensityExtension {q : ℝ → ℝ}
    (hqSmooth : ContDiffOn ℝ 3 q (Ici 0))
    (hqPos : ∀ z ∈ Ici (0 : ℝ), 0 < q z)
    (hqRelative : HalfLineRelativeDerivativeBounds q) :
    ∃ extension : ℝ → ℝ, IsPositiveC3DensityExtension q extension := by
  rcases extendedLogDensity_contDiff_three hqSmooth hqPos with
    ⟨cutoff, hlogSmooth, heqRight, hlogConstantLeft⟩
  let extension : ℝ → ℝ := extendedDensity q cutoff
  have hextSmooth : ContDiff ℝ 3 extension := by
    change ContDiff ℝ 3 (Real.exp ∘ extendedLogDensity q cutoff)
    exact Real.contDiff_exp.comp hlogSmooth
  have hextPos : ∀ z, 0 < extension z := by
    intro z
    exact extendedDensity_pos q cutoff z
  have heqOn : EqOn extension q (Ici (0 : ℝ)) := by
    intro z hz
    exact heqRight z hz
  rcases hqRelative with ⟨MRight, hMRight, hrightBound⟩
  let ratioSum : ℝ → ℝ := fun z ↦
    |iteratedDeriv 1 extension z| / extension z +
      |iteratedDeriv 2 extension z| / extension z +
      |iteratedDeriv 3 extension z| / extension z
  have hratioContinuous : Continuous ratioSum := by
    have hextContinuous := hextSmooth.continuous
    have h1 := hextSmooth.continuous_iteratedDeriv 1 (by norm_num)
    have h2 := hextSmooth.continuous_iteratedDeriv 2 (by norm_num)
    have h3 := hextSmooth.continuous_iteratedDeriv 3 (by norm_num)
    dsimp only [ratioSum]
    exact ((h1.abs.div hextContinuous fun z ↦ (hextPos z).ne').add
      (h2.abs.div hextContinuous fun z ↦ (hextPos z).ne')).add
      (h3.abs.div hextContinuous fun z ↦ (hextPos z).ne')
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 0).Nonempty from ⟨-1, by constructor <;> norm_num⟩)
    hratioContinuous.continuousOn
  let MCompact : ℝ := ratioSum x
  have hMCompact : 0 ≤ MCompact := by
    dsimp only [MCompact, ratioSum]
    exact add_nonneg
      (add_nonneg (div_nonneg (abs_nonneg _) (hextPos _).le)
        (div_nonneg (abs_nonneg _) (hextPos _).le))
      (div_nonneg (abs_nonneg _) (hextPos _).le)
  have hcompactBound (k : ℕ) (hkOne : 1 ≤ k) (hkThree : k ≤ 3)
      (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 0) :
      |iteratedDeriv k extension z| ≤ MCompact * extension z := by
    have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    have hterm : |iteratedDeriv k extension z| / extension z ≤ ratioSum z := by
      rcases hk with rfl | rfl | rfl <;>
        dsimp only [ratioSum] <;>
        nlinarith [div_nonneg (abs_nonneg (iteratedDeriv 1 extension z))
            (hextPos z).le,
          div_nonneg (abs_nonneg (iteratedDeriv 2 extension z)) (hextPos z).le,
          div_nonneg (abs_nonneg (iteratedDeriv 3 extension z)) (hextPos z).le]
    have hratioMax := hmax hz
    change ratioSum z ≤ ratioSum x at hratioMax
    have hquotient : |iteratedDeriv k extension z| / extension z ≤ MCompact := by
      exact hterm.trans hratioMax
    exact (div_le_iff₀ (hextPos z)).mp hquotient
  have hrightExtensionBound (k : ℕ) (hkOne : 1 ≤ k) (hkThree : k ≤ 3)
      (z : ℝ) (hz : z ∈ Ici (0 : ℝ)) :
      |iteratedDeriv k extension z| ≤ MRight * extension z := by
    have hcontAt : ContDiffAt ℝ k extension z :=
      hextSmooth.contDiffAt.of_le (by exact_mod_cast hkThree)
    have hwithinOrd : iteratedDerivWithin k extension (Ici 0) z =
        iteratedDeriv k extension z :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0 : ℝ))
        hcontAt hz
    have hwithinEq : iteratedDerivWithin k extension (Ici 0) z =
        iteratedDerivWithin k q (Ici 0) z :=
      (iteratedDerivWithin_congr (n := k) heqOn) hz
    calc
      |iteratedDeriv k extension z| =
          |iteratedDerivWithin k extension (Ici 0) z| := by rw [hwithinOrd]
      _ = |iteratedDerivWithin k q (Ici 0) z| := by rw [hwithinEq]
      _ ≤ MRight * q z := hrightBound k hkOne hkThree z hz
      _ = MRight * extension z := by rw [heqOn hz]
  let M : ℝ := max MRight MCompact
  have hM : 0 ≤ M := hMRight.trans (le_max_left _ _)
  refine ⟨extension, hextSmooth, heqOn, hextPos, M, hM, ?_⟩
  intro k hkOne hkThree z
  by_cases hzRight : 0 ≤ z
  · exact (hrightExtensionBound k hkOne hkThree z hzRight).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hextPos z).le)
  · by_cases hzCompact : -1 ≤ z
    · exact (hcompactBound k hkOne hkThree z ⟨hzCompact, le_of_not_ge hzRight⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (hextPos z).le)
    · have hzFar : z ∈ Iio (-1 : ℝ) := lt_of_not_ge hzCompact
      have heventuallyConstant : extension =ᶠ[nhds z] fun _ ↦ extension z := by
        have hstay : ∀ᶠ y in nhds z, y ∈ Iio (-1 : ℝ) :=
          Iio_mem_nhds hzFar
        filter_upwards [hstay] with y hy
        dsimp only [extension, extendedDensity]
        rw [hlogConstantLeft y hy, hlogConstantLeft z hzFar]
      have hkZero : k ≠ 0 := by omega
      have hderivZero : iteratedDeriv k extension z = 0 := by
        have hderivEq := heventuallyConstant.iteratedDeriv_eq k
        simpa only [iteratedDeriv_const, if_neg hkZero] using hderivEq
      rw [hderivZero, abs_zero]
      exact mul_nonneg hM (hextPos z).le

/-- A normalized hard-edge phase inherits the one-sided `C³` and positivity
hypotheses needed by the logarithmic extension construction. -/
theorem hardEdgeDensity_exists_positiveC3DensityExtension {input : MainInput}
    {W Psi : ℝ → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hrelative : HalfLineRelativeDerivativeBounds
      (hardEdgeDensity input W Psi)) :
    ∃ extension : ℝ → ℝ,
      IsPositiveC3DensityExtension (hardEdgeDensity input W Psi) extension := by
  have hcomp : ContDiffOn ℝ ∞ (W ∘ Psi) (Ici (0 : ℝ)) :=
    hW.comp hPsi.1 hPsi.2.2.1
  have hdensityInfinity : ContDiffOn ℝ ∞
      (hardEdgeDensity input W Psi) (Ici (0 : ℝ)) := by
    change ContDiffOn ℝ ∞ (fun z : ℝ ↦ input.beta * W (Psi z)) (Ici 0)
    exact (contDiffOn_const (c := input.beta)).mul hcomp
  have hdensityThree : ContDiffOn ℝ 3
      (hardEdgeDensity input W Psi) (Ici (0 : ℝ)) :=
    contDiffOn_infty.mp hdensityInfinity 3
  have hdensityPos : ∀ z ∈ Ici (0 : ℝ),
      0 < hardEdgeDensity input W Psi z := by
    intro z hz
    exact mul_pos input.beta_pos (hpos (Psi z) (hPsi.2.2.1 hz))
  exact exists_positiveC3DensityExtension hdensityThree hdensityPos hrelative

end SeriesParallel.Appendix
