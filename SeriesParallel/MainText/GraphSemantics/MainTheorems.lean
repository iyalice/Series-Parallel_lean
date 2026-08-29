/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.GraphSemantics.StatementContract
import SeriesParallel.MainText.MainTheorems

/-!
# Public graph-facing main theorems

The scalar theorem graph is transported across the proved traditional-graph equalities.  The
formulas exported here genuinely mention graph-defined values and candidate limits.
-/

namespace SeriesParallel.MainText.GraphSemantics

/-- Traditional-graph form of `thm:logarithmic-speeds`. -/
theorem graphLogarithmicSpeeds : GraphLogarithmicSpeedsStatement :=
  graphLogarithmicSpeedsStatement_iff.mpr logarithmicSpeeds

/-- Traditional-graph form of `thm:first-moment-logarithmic-rates`. -/
theorem graphFirstMomentLogarithmicRates : GraphFirstMomentLogarithmicRatesStatement :=
  graphFirstMomentLogarithmicRatesStatement_iff.mpr firstMomentLogarithmicRates

/-- Traditional-graph form of `thm:near-critical-speed`. -/
theorem graphResistanceSpeedNearCritical : GraphResistanceSpeedNearCriticalStatement :=
  graphResistanceSpeedNearCriticalStatement_iff.mpr resistanceSpeedNearCritical

end SeriesParallel.MainText.GraphSemantics
