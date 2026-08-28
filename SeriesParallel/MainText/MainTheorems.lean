/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.LiteratureInterfaces
import SeriesParallel.MainText.RemainingParameters
import SeriesParallel.MainText.ResistanceNearCritical

/-!
# Source-facing main theorems

The first two theorems consume the sole new core literature input only at this final assembly
point.  The imported `resistanceSpeedNearCritical` theorem is proved in its separate
resistance-only module, whose dependency closure excludes that input.
-/

namespace SeriesParallel.MainText

/-- `thm:logarithmic-speeds`. -/
theorem logarithmicSpeeds : LogarithmicSpeedsStatement :=
  logarithmicSpeeds_of_critical_input distanceGamma_half_eq_zero

/-- `thm:first-moment-logarithmic-rates`. -/
theorem firstMomentLogarithmicRates : FirstMomentLogarithmicRatesStatement :=
  firstMomentLogarithmicRates_of_critical_input distanceGamma_half_eq_zero

end SeriesParallel.MainText
