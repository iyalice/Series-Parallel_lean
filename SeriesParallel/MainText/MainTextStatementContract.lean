/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.Moments
import SeriesParallel.MainText.DiffusionCoefficient
import SeriesParallel.Appendix.AdmissibleLowerBound
import Mathlib.Data.EReal.Basic

/-!
# Source-facing contracts for the three main-text theorems

This file fixes the complete mathematical content before the proofs are assembled. The first two
contracts use equivalent Lean packaging for the paper's limits: a tail indexed by `n + 1` and a
canonical chosen limit. The third contract directly represents the source BVP and asymptotics.
The real parameter is projected to the canonical unit-interval model; every quantified use also
carries the source hypothesis that the original parameter lies in `[0, 1]`.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace SeriesParallel.MainText

/-- The canonical random-model parameter associated with a real number. -/
noncomputable def modelParameter (p : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one p

@[simp]
theorem modelParameter_eq_of_mem {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    modelParameter p = ⟨p, hp⟩ := by
  exact projIcc_of_mem zero_le_one hp

@[simp]
theorem modelParameter_coe_of_mem {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    (modelParameter p : ℝ) = p := by
  rw [modelParameter_eq_of_mem hp]

/-- A deterministic choice of the limit of a real sequence, with value zero when no limit exists. -/
noncomputable def chosenSequentialLimit (sequence : ℕ → ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ value : ℝ, Tendsto sequence atTop (𝓝 value) then
      Classical.choose h
    else 0

theorem chosenSequentialLimit_spec {sequence : ℕ → ℝ}
    (hexists : ∃ value : ℝ, Tendsto sequence atTop (𝓝 value)) :
    Tendsto sequence atTop (𝓝 (chosenSequentialLimit sequence)) := by
  classical
  rw [chosenSequentialLimit, dif_pos hexists]
  exact Classical.choose_spec hexists

theorem chosenSequentialLimit_eq {sequence : ℕ → ℝ} {value : ℝ}
    (hlimit : Tendsto sequence atTop (𝓝 value)) :
    chosenSequentialLimit sequence = value := by
  apply tendsto_nhds_unique (chosenSequentialLimit_spec ⟨value, hlimit⟩) hlimit

/-- Canonical distance logarithmic speed candidate. -/
noncomputable def vD (p : ℝ) : ℝ :=
  chosenSequentialLimit (normalizedMeanLog (modelParameter p) .distance)

/-- Canonical resistance logarithmic speed candidate. -/
noncomputable def vR (p : ℝ) : ℝ :=
  chosenSequentialLimit (normalizedMeanLog (modelParameter p) .resistance)

/-- Canonical distance first-moment logarithmic-rate candidate. -/
noncomputable def gammaD (p : ℝ) : ℝ :=
  chosenSequentialLimit (normalizedLogFirstMoment (modelParameter p) .distance)

/-- Canonical resistance first-moment logarithmic-rate candidate. -/
noncomputable def gammaR (p : ℝ) : ℝ :=
  chosenSequentialLimit (normalizedLogFirstMoment (modelParameter p) .resistance)

/-- The source convention `log 0 = -∞`, used only for nonnegative first-moment factors. -/
noncomputable def paperLog (x : ℝ) : EReal :=
  if 0 < x then (Real.log x : EReal) else ⊥

@[simp]
theorem paperLog_zero : paperLog 0 = ⊥ := by
  simp [paperLog]

theorem paperLog_of_pos {x : ℝ} (hx : 0 < x) : paperLog x = (Real.log x : EReal) := by
  simp [paperLog, hx]

/-- Almost-sure and `L¹` convergence of the normalized log on the common environment.

The `n + 1` tail is equivalent to the paper's `n ≥ 1` sequence and avoids division by zero. -/
def ConvergesASAndL1AtLinearRate (p : ℝ) (mode : Mode) (value : ℝ) : Prop :=
  (∀ᵐ environment ∂environmentMeasure (modelParameter p),
      Tendsto
        (fun n : ℕ ↦
          X mode (n + 1) environment / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 value)) ∧
    Tendsto
      (fun n : ℕ ↦
        ∫ environment,
          |X mode (n + 1) environment / ((n + 1 : ℕ) : ℝ) - value|
            ∂environmentMeasure (modelParameter p))
      atTop (𝓝 0)

/-- Source-facing statement of `thm:logarithmic-speeds`, with equivalent tail and limit
packaging. -/
def LogarithmicSpeedsStatement : Prop :=
  (∀ (p : ℝ), p ∈ Icc 0 1 →
      ConvergesASAndL1AtLinearRate p .distance (vD p) ∧
        ConvergesASAndL1AtLinearRate p .resistance (vR p)) ∧
    (∀ (p : ℝ), 0 ≤ p → p ≤ 1 / 2 → vD p = 0) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 → vR (1 - p) = -vR p) ∧
    vR (1 / 2) = 0 ∧
    (∀ (p : ℝ), 1 / 2 < p → p ≤ 1 →
      Real.log (2 * p) ≤ vD p ∧ vD p ≤ Real.log 2 ∧
        Real.log (2 * p) ≤ vR p ∧ vR p ≤ Real.log 2)

/-- Source-facing statement of `thm:first-moment-logarithmic-rates`, with equivalent limit
packaging. -/
def FirstMomentLogarithmicRatesStatement : Prop :=
  (∀ (p : ℝ), p ∈ Icc 0 1 →
      Tendsto (normalizedLogFirstMoment (modelParameter p) .distance)
          atTop (𝓝 (gammaD p)) ∧
        Tendsto (normalizedLogFirstMoment (modelParameter p) .resistance)
          atTop (𝓝 (gammaR p))) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 → gammaD p = vD p) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 →
      (gammaR p : EReal) = max (vR p : EReal) (paperLog (2 * p))) ∧
    (∀ (p : ℝ), 1 / 2 ≤ p → p ≤ 1 → gammaR p = vR p)

/-- The literal source BVP on `[0,1]`, with `C¹` regularity on `(0,1)`. -/
def SourceWSolution (lambda : ℝ) (W : ℝ → ℝ) : Prop :=
  ContinuousOn W (Icc 0 1) ∧
    ContDiffOn ℝ 1 W (Ioo 0 1) ∧
    (∀ u ∈ Ioo (0 : ℝ) 1,
      W u ^ 2 * deriv W u - lambda * W u + u * (1 - u) = 0) ∧
    (∀ u ∈ Ioo (0 : ℝ) 1, 0 < W u) ∧
    W 0 = 0 ∧ W 1 = 0

/-- Positive parameters for which the source BVP has a solution. -/
def mainAdmissible : Set ℝ :=
  {lambda : ℝ | 0 < lambda ∧ ∃ W : ℝ → ℝ, SourceWSolution lambda W}

/-- The exact common positive near-critical comparison scale. -/
noncomputable def nearCriticalScale (delta : ℝ) : ℝ :=
  2 * Real.cbrt zetaThree * SeriesParallel.Appendix.lambdaStar *
    Real.rpow delta ((2 : ℝ) / 3)

/-- Exact source-facing statement of `thm:near-critical-speed`. -/
def ResistanceSpeedNearCriticalStatement : Prop :=
  0 < SeriesParallel.Appendix.lambdaStar ∧
    IsLeast mainAdmissible SeriesParallel.Appendix.lambdaStar ∧
    (∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 2 →
      vR (1 / 2 + delta) = -vR (1 / 2 - delta)) ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ vR (1 / 2 + delta)) nearCriticalScale ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ gammaR (1 / 2 + delta)) nearCriticalScale ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ gammaR (1 / 2 - delta)) (fun delta : ℝ ↦ -2 * delta)

#check LogarithmicSpeedsStatement
#check FirstMomentLogarithmicRatesStatement
#check ResistanceSpeedNearCriticalStatement

end SeriesParallel.MainText
