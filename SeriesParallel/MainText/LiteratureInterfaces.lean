/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.MainTextStatementContract

/-!
# Minimal literature interface consumed by the main theorems

The critical annealed distance exponent is the sole new core literature input.  Parameter
monotonicity propagates this one value to the complete subcritical distance range.
-/

namespace SeriesParallel.MainText

/-- External input E-Dcrit: the critical distance first-moment exponent vanishes. -/
axiom distanceGamma_half_eq_zero : gammaD (1 / 2) = 0

end SeriesParallel.MainText
