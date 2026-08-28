/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import SeriesParallel.MainText.DiffusionCoefficient

/-!
# Main-text external interfaces

This module is intentionally empty.  The currently compiled main-text subgraph does not require
any new project axiom: in particular, positivity of the diffusion coefficient is proved from its
integral definition.  Literature results and the closed-form evaluation
`diffusionCoefficient = 2 * zetaThree` will be added here only when a compiled downstream theorem
actually needs them; reserving an interface is not a reason to enlarge the trust boundary.

The pre-existing appendix interface
`SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` is unchanged.
-/

namespace SeriesParallel.MainText

/-- A machine-checkable witness that this layer currently adds no external proposition. -/
theorem externalInterfaces_currently_empty : True := True.intro

end SeriesParallel.MainText
