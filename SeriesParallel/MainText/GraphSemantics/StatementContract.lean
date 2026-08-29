/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.GraphSemantics.RandomModel
import SeriesParallel.MainText.MainTextStatementContract

/-!
# Graph-facing contracts for the three principal theorems

These propositions use the traditional graph quantities syntactically.  Pointwise bridge
equalities identify them with the existing scalar contracts, so no probabilistic or asymptotic
argument is duplicated here.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace SeriesParallel.MainText.GraphSemantics

/-- Almost-sure and `L¹` linear-rate convergence stated with `graphX`. -/
def GraphConvergesASAndL1AtLinearRate
    (p : ℝ) (mode : Mode) (value : ℝ) : Prop :=
  (∀ᵐ environment ∂environmentMeasure (modelParameter p),
      Tendsto
        (fun n : ℕ ↦
          graphX mode (n + 1) environment / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 value)) ∧
    Tendsto
      (fun n : ℕ ↦
        ∫ environment,
          |graphX mode (n + 1) environment / ((n + 1 : ℕ) : ℝ) - value|
            ∂environmentMeasure (modelParameter p))
      atTop (𝓝 0)

theorem graphConvergesASAndL1AtLinearRate_iff
    (p : ℝ) (mode : Mode) (value : ℝ) :
    GraphConvergesASAndL1AtLinearRate p mode value ↔
      ConvergesASAndL1AtLinearRate p mode value := by
  simp [GraphConvergesASAndL1AtLinearRate, ConvergesASAndL1AtLinearRate]

/-- Graph-facing version of `thm:logarithmic-speeds`. -/
def GraphLogarithmicSpeedsStatement : Prop :=
  (∀ (p : ℝ), p ∈ Icc 0 1 →
      GraphConvergesASAndL1AtLinearRate p .distance (graphVD p) ∧
        GraphConvergesASAndL1AtLinearRate p .resistance (graphVR p)) ∧
    (∀ (p : ℝ), 0 ≤ p → p ≤ 1 / 2 → graphVD p = 0) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 → graphVR (1 - p) = -graphVR p) ∧
    graphVR (1 / 2) = 0 ∧
    (∀ (p : ℝ), 1 / 2 < p → p ≤ 1 →
      Real.log (2 * p) ≤ graphVD p ∧ graphVD p ≤ Real.log 2 ∧
        Real.log (2 * p) ≤ graphVR p ∧ graphVR p ≤ Real.log 2)

/-- Graph-facing version of `thm:first-moment-logarithmic-rates`. -/
def GraphFirstMomentLogarithmicRatesStatement : Prop :=
  (∀ (p : ℝ), p ∈ Icc 0 1 →
      Tendsto (graphNormalizedLogFirstMoment (modelParameter p) .distance)
          atTop (𝓝 (graphGammaD p)) ∧
        Tendsto (graphNormalizedLogFirstMoment (modelParameter p) .resistance)
          atTop (𝓝 (graphGammaR p))) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 → graphGammaD p = graphVD p) ∧
    (∀ (p : ℝ), p ∈ Icc 0 1 →
      (graphGammaR p : EReal) = max (graphVR p : EReal) (paperLog (2 * p))) ∧
    (∀ (p : ℝ), 1 / 2 ≤ p → p ≤ 1 → graphGammaR p = graphVR p)

/-- Graph-facing version of `thm:near-critical-speed`. -/
def GraphResistanceSpeedNearCriticalStatement : Prop :=
  0 < SeriesParallel.Appendix.lambdaStar ∧
    IsLeast mainAdmissible SeriesParallel.Appendix.lambdaStar ∧
    (∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 2 →
      graphVR (1 / 2 + delta) = -graphVR (1 / 2 - delta)) ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ graphVR (1 / 2 + delta)) nearCriticalScale ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ graphGammaR (1 / 2 + delta)) nearCriticalScale ∧
    IsEquivalent (𝓝[>] (0 : ℝ))
      (fun delta : ℝ ↦ graphGammaR (1 / 2 - delta)) (fun delta : ℝ ↦ -2 * delta)

theorem graphLogarithmicSpeedsStatement_iff :
    GraphLogarithmicSpeedsStatement ↔ LogarithmicSpeedsStatement := by
  unfold GraphLogarithmicSpeedsStatement LogarithmicSpeedsStatement
  simp_rw [graphConvergesASAndL1AtLinearRate_iff, graphVD_eq_vD, graphVR_eq_vR]

theorem graphFirstMomentLogarithmicRatesStatement_iff :
    GraphFirstMomentLogarithmicRatesStatement ↔ FirstMomentLogarithmicRatesStatement := by
  have hsequence (p : unitInterval) (mode : Mode) :
      graphNormalizedLogFirstMoment p mode = normalizedLogFirstMoment p mode := by
    funext n
    exact graphNormalizedLogFirstMoment_eq_normalizedLogFirstMoment p mode n
  constructor
  · intro h
    simpa only [GraphFirstMomentLogarithmicRatesStatement,
      FirstMomentLogarithmicRatesStatement, graphGammaD_eq_gammaD,
      graphGammaR_eq_gammaR, graphVD_eq_vD, graphVR_eq_vR, hsequence] using h
  · intro h
    simpa only [GraphFirstMomentLogarithmicRatesStatement,
      FirstMomentLogarithmicRatesStatement, graphGammaD_eq_gammaD,
      graphGammaR_eq_gammaR, graphVD_eq_vD, graphVR_eq_vR, hsequence] using h

theorem graphResistanceSpeedNearCriticalStatement_iff :
    GraphResistanceSpeedNearCriticalStatement ↔ ResistanceSpeedNearCriticalStatement := by
  unfold GraphResistanceSpeedNearCriticalStatement ResistanceSpeedNearCriticalStatement
  simp_rw [graphVR_eq_vR, graphGammaR_eq_gammaR]

end SeriesParallel.MainText.GraphSemantics
