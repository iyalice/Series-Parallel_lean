import SeriesParallel.Appendix.BasicDefs
import SeriesParallel.ManualInterfaces
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Comparison for the cube-root equation

This file formalizes `lem:cuberoot-comparison`.  The proof follows the source: apply the
positive-part-square function to the difference of the sub- and supersolution and use the
monotonicity of the signed real cube root.
-/

open Filter Set
open scoped Topology

namespace SeriesParallel.Appendix

/-- `lem:cuberoot-comparison`: a subsolution that starts below a supersolution remains below
it on the whole compact interval. -/
theorem cuberoot_comparison {t0 t1 b : ℝ} {a yLower yUpper : ℝ → ℝ}
    (ht : t0 < t1) (_ha : ContinuousOn a (Icc t0 t1)) (hb : 0 < b)
    (hLower : IsCubeRootSubsolutionOn a b yLower t0 t1)
    (hUpper : IsCubeRootSupersolutionOn a b yUpper t0 t1)
    (hInitial : yLower t0 ≤ yUpper t0) :
    ∀ t ∈ Icc t0 t1, yLower t ≤ yUpper t := by
  let d : ℝ → ℝ := fun t ↦ yLower t - yUpper t
  let energy : ℝ → ℝ := fun t ↦ ManualInterfaces.positivePartSquare (d t)
  have hd_cont : ContinuousOn d (Icc t0 t1) := hLower.1.sub hUpper.1
  have henergy_cont : ContinuousOn energy (Icc t0 t1) := by
    have hcontinuous : Continuous ManualInterfaces.positivePartSquare :=
      continuous_iff_continuousAt.mpr fun s ↦
        (ManualInterfaces.MI07_positive_part_square_hasDerivAt s).continuousAt
    exact hcontinuous.continuousOn.comp hd_cont (mapsTo_image d (Icc t0 t1))
  have henergy_deriv : ∀ t ∈ Ioo t0 t1, ∃ e' : ℝ,
      HasDerivAt energy e' t ∧ e' ≤ 0 := by
    intro t ht_mem
    obtain ⟨dyLower, hdyLower, hdyLower_le⟩ := hLower.2 t ht_mem
    obtain ⟨dyUpper, hdyUpper, hdyUpper_le⟩ := hUpper.2 t ht_mem
    refine ⟨max (d t) 0 * (dyLower - dyUpper), ?_, ?_⟩
    · change HasDerivAt (ManualInterfaces.positivePartSquare ∘ d)
        (max (d t) 0 * (dyLower - dyUpper)) t
      exact (ManualInterfaces.MI07_positive_part_square_hasDerivAt (d t)).comp t
        (hdyLower.sub hdyUpper)
    · by_cases hd_nonpos : d t ≤ 0
      · simp [max_eq_right hd_nonpos]
      · have hd_pos : 0 < d t := lt_of_not_ge hd_nonpos
        have hy_lt : yUpper t < yLower t := by simpa [d] using hd_pos
        have hcbrt_lt : Real.cbrt (yUpper t) < Real.cbrt (yLower t) :=
          Real.strictMono_cbrt hy_lt
        have hderiv_lt : dyLower - dyUpper < 0 := by
          calc
            dyLower - dyUpper ≤
                (a t - b * Real.cbrt (yLower t)) -
                  (a t - b * Real.cbrt (yUpper t)) :=
              sub_le_sub hdyLower_le hdyUpper_le
            _ = -b * (Real.cbrt (yLower t) - Real.cbrt (yUpper t)) := by ring
            _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hb) (sub_pos.mpr hcbrt_lt)
        have hmax_pos : 0 < max (d t) 0 := by simp [hd_pos]
        exact mul_nonpos_of_nonneg_of_nonpos hmax_pos.le hderiv_lt.le
  have henergy_anti : AntitoneOn energy (Icc t0 t1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t0 t1) henergy_cont
    · intro t ht_int
      have ht_open : t ∈ Ioo t0 t1 := by
        simpa [interior_Icc, ht.ne] using ht_int
      exact (henergy_deriv t ht_open).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro t ht_int
      have ht_open : t ∈ Ioo t0 t1 := by
        simpa [interior_Icc, ht.ne] using ht_int
      obtain ⟨e', he', he'_nonpos⟩ := henergy_deriv t ht_open
      simpa [he'.deriv] using he'_nonpos
  intro t ht_mem
  have ht0_mem : t0 ∈ Icc t0 t1 := ⟨le_rfl, ht.le⟩
  have henergy_le : energy t ≤ energy t0 :=
    henergy_anti ht0_mem ht_mem ht_mem.1
  have hd0_nonpos : d t0 ≤ 0 := by simpa [d] using hInitial
  have henergy_t0 : energy t0 = 0 := by
    simp [energy, ManualInterfaces.positivePartSquare, max_eq_right hd0_nonpos]
  have henergy_nonneg : 0 ≤ energy t := by
    dsimp [energy, ManualInterfaces.positivePartSquare]
    positivity
  have henergy_zero : energy t = 0 := by linarith
  have hmax_zero : max (d t) 0 = 0 := by
    have : max (d t) 0 ^ 2 = 0 := by
      simpa [energy, ManualInterfaces.positivePartSquare] using
        congrArg (fun x : ℝ ↦ 2 * x) henergy_zero
    nlinarith [sq_nonneg (max (d t) 0)]
  have hd_nonpos : d t ≤ 0 := max_eq_right_iff.mp hmax_zero
  simpa [d] using hd_nonpos

/-- Exact source-facing wrapper for `lem:cuberoot-comparison`.  It records the stated
`C([t₀,t₁]) ∩ C¹((t₀,t₁))` regularity and also covers a degenerate closed interval. -/
theorem cuberoot_comparison_source {t0 t1 b : ℝ} {a yLower yUpper : ℝ → ℝ}
    (ht : t0 ≤ t1) (ha : ContinuousOn a (Icc t0 t1)) (hb : 0 < b)
    (hLower : IsCubeRootC1SubsolutionOn a b yLower t0 t1)
    (hUpper : IsCubeRootC1SupersolutionOn a b yUpper t0 t1)
    (hInitial : yLower t0 ≤ yUpper t0) :
    ∀ t ∈ Icc t0 t1, yLower t ≤ yUpper t := by
  rcases ht.eq_or_lt with hEq | hlt
  · subst t1
    intro t ht
    have ht_eq : t = t0 := le_antisymm ht.2 ht.1
    simpa [ht_eq] using hInitial
  · exact cuberoot_comparison hlt ha hb hLower.toSubsolutionOn
      hUpper.toSupersolutionOn hInitial

end SeriesParallel.Appendix
