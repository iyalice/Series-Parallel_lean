/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.GraphSemantics.DistanceBridge
import SeriesParallel.MainText.GraphSemantics.ResistanceBridge
import SeriesParallel.MainText.MainTextStatementContract

/-!
# Traditional graph quantities on the common random environment

The random network is first realized as an edge-indexed multigraph and only then evaluated by
the independent traditional distance and resistance definitions.  The deterministic bridge
theorems identify these quantities samplewise with the recursive scalar model.
-/

open MeasureTheory

namespace SeriesParallel.MainText.GraphSemantics

/-- Graph distance of the realized depth-`n` random network. -/
noncomputable def graphDistanceValue (n : ℕ) (environment : Environment) : ℕ :=
  traditionalDistance (SPNetwork.realize (randomNetwork n environment))

/-- Effective resistance of the realized depth-`n` random network. -/
noncomputable def graphResistanceValue (n : ℕ) (environment : Environment) : ℝ :=
  TwoTerminalMultigraph.traditionalResistance
    (SPNetwork.realize (randomNetwork n environment))

/-- The graph distance agrees samplewise with the recursive distance evaluator. -/
theorem graphDistanceValue_eq_distanceValue (n : ℕ) (environment : Environment) :
    graphDistanceValue n environment = distanceValue n environment := by
  simpa [graphDistanceValue, distanceValue] using
    SPNetwork.traditionalDistance_realize (randomNetwork n environment)

/-- The graph resistance agrees samplewise with the recursive resistance evaluator. -/
theorem graphResistanceValue_eq_resistanceValue (n : ℕ) (environment : Environment) :
    graphResistanceValue n environment = resistanceValue n environment := by
  simpa [graphResistanceValue, resistanceValue] using
    SPNetwork.traditionalResistance_realize (randomNetwork n environment)

/-- The graph-defined unified positive quantity. -/
noncomputable def graphZ (mode : Mode) (n : ℕ) (environment : Environment) : ℝ :=
  match mode with
  | .distance => graphDistanceValue n environment
  | .resistance => graphResistanceValue n environment

/-- The graph-defined logarithmic quantity. -/
noncomputable def graphX (mode : Mode) (n : ℕ) (environment : Environment) : ℝ :=
  Real.log (graphZ mode n environment)

@[simp]
theorem graphZ_eq_Z (mode : Mode) (n : ℕ) (environment : Environment) :
    graphZ mode n environment = Z mode n environment := by
  cases mode <;>
    simp [graphZ, Z, graphDistanceValue_eq_distanceValue,
      graphResistanceValue_eq_resistanceValue]

@[simp]
theorem graphX_eq_X (mode : Mode) (n : ℕ) (environment : Environment) :
    graphX mode n environment = X mode n environment := by
  simp [graphX, X]

/-- First moment formed directly from the graph quantity. -/
noncomputable def graphFirstMoment (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment, graphZ mode n environment ∂environmentMeasure p

/-- Mean logarithm formed directly from the graph quantity. -/
noncomputable def graphMeanLog (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  ∫ environment, graphX mode n environment ∂environmentMeasure p

@[simp]
theorem graphFirstMoment_eq_firstMoment (p : unitInterval) (mode : Mode) (n : ℕ) :
    graphFirstMoment p mode n = firstMoment p mode n := by
  simp [graphFirstMoment, firstMoment]

@[simp]
theorem graphMeanLog_eq_meanLog (p : unitInterval) (mode : Mode) (n : ℕ) :
    graphMeanLog p mode n = meanLog p mode n := by
  simp [graphMeanLog, meanLog]

/-- Graph version of the normalized logarithm of the first moment. -/
noncomputable def graphNormalizedLogFirstMoment
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  Real.log (graphFirstMoment p mode (n + 1)) / (n + 1)

/-- Graph version of the normalized mean logarithm. -/
noncomputable def graphNormalizedMeanLog
    (p : unitInterval) (mode : Mode) (n : ℕ) : ℝ :=
  graphMeanLog p mode (n + 1) / (n + 1)

@[simp]
theorem graphNormalizedLogFirstMoment_eq_normalizedLogFirstMoment
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    graphNormalizedLogFirstMoment p mode n = normalizedLogFirstMoment p mode n := by
  simp [graphNormalizedLogFirstMoment, normalizedLogFirstMoment]

@[simp]
theorem graphNormalizedMeanLog_eq_normalizedMeanLog
    (p : unitInterval) (mode : Mode) (n : ℕ) :
    graphNormalizedMeanLog p mode n = normalizedMeanLog p mode n := by
  simp [graphNormalizedMeanLog, normalizedMeanLog]

/-- Graph-defined distance logarithmic-speed candidate. -/
noncomputable def graphVD (p : ℝ) : ℝ :=
  chosenSequentialLimit (graphNormalizedMeanLog (modelParameter p) .distance)

/-- Graph-defined resistance logarithmic-speed candidate. -/
noncomputable def graphVR (p : ℝ) : ℝ :=
  chosenSequentialLimit (graphNormalizedMeanLog (modelParameter p) .resistance)

/-- Graph-defined distance first-moment-rate candidate. -/
noncomputable def graphGammaD (p : ℝ) : ℝ :=
  chosenSequentialLimit (graphNormalizedLogFirstMoment (modelParameter p) .distance)

/-- Graph-defined resistance first-moment-rate candidate. -/
noncomputable def graphGammaR (p : ℝ) : ℝ :=
  chosenSequentialLimit (graphNormalizedLogFirstMoment (modelParameter p) .resistance)

@[simp]
theorem graphVD_eq_vD (p : ℝ) : graphVD p = vD p := by
  unfold graphVD vD
  apply congrArg chosenSequentialLimit
  funext n
  exact graphNormalizedMeanLog_eq_normalizedMeanLog (modelParameter p) .distance n

@[simp]
theorem graphVR_eq_vR (p : ℝ) : graphVR p = vR p := by
  unfold graphVR vR
  apply congrArg chosenSequentialLimit
  funext n
  exact graphNormalizedMeanLog_eq_normalizedMeanLog (modelParameter p) .resistance n

@[simp]
theorem graphGammaD_eq_gammaD (p : ℝ) : graphGammaD p = gammaD p := by
  unfold graphGammaD gammaD
  apply congrArg chosenSequentialLimit
  funext n
  exact graphNormalizedLogFirstMoment_eq_normalizedLogFirstMoment
    (modelParameter p) .distance n

@[simp]
theorem graphGammaR_eq_gammaR (p : ℝ) : graphGammaR p = gammaR p := by
  unfold graphGammaR gammaR
  apply congrArg chosenSequentialLimit
  funext n
  exact graphNormalizedLogFirstMoment_eq_normalizedLogFirstMoment
    (modelParameter p) .resistance n

end SeriesParallel.MainText.GraphSemantics
