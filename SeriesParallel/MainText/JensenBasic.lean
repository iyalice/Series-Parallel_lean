/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.Moments

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The elementary Jensen-gap inequality

This closes the nonnegativity part of `eq:jensen-gap`.  Uniform boundedness of the gap is the
substantive later proposition and is deliberately not asserted here.
-/

@[expose] public section

open MeasureTheory Set

namespace SeriesParallel.MainText

/-- `log E[Z_n] - E[log Z_n]`. -/
noncomputable def jensenGap (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  Real.log (firstMoment p mode n) - meanLog p mode n

/-- Jensen's inequality for the positive, bounded random variable `Z_n`. -/
theorem meanLog_le_log_firstMoment (p : unitInterval) (mode : Mode) (n : ℕ) :
    meanLog p mode n ≤ Real.log (firstMoment p mode n) := by
  let lower : ℝ := ((2 : ℝ) ^ n)⁻¹
  let upper : ℝ := (2 : ℝ) ^ n
  have hlower : 0 < lower := by simp [lower]
  have hconcave : ConcaveOn ℝ (Icc lower upper) Real.log := by
    refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab ↦ ?_⟩
    exact strictConcaveOn_log_Ioi.concaveOn.2
      (hlower.trans_le hx.1) (hlower.trans_le hy.1) ha hb hab
  have hcontinuous : ContinuousOn Real.log (Icc lower upper) :=
    Real.continuousOn_log.mono fun x hx ↦ (hlower.trans_le hx.1).ne'
  have hmem : ∀ᵐ environment ∂environmentMeasure p,
      Z mode n environment ∈ Icc lower upper := by
    filter_upwards with environment
    simpa [lower, upper] using Z_global_bounds mode n environment
  have hlogIntegrable :
      Integrable (Real.log ∘ Z mode n) (environmentMeasure p) := by
    rw [show Real.log ∘ Z mode n = X mode n by rfl]
    exact integrable_X p mode n
  have hjensen := hconcave.le_map_integral hcontinuous isClosed_Icc hmem
    (integrable_Z p mode n) hlogIntegrable
  simpa [firstMoment, meanLog, X, Function.comp_def] using hjensen

theorem jensenGap_nonneg (p : unitInterval) (mode : Mode) (n : ℕ) :
    0 ≤ jensenGap p mode n := by
  unfold jensenGap
  linarith [meanLog_le_log_firstMoment p mode n]

end SeriesParallel.MainText
