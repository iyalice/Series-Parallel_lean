import SeriesParallel.MainText.DiffusionCoefficient
import SeriesParallel.MainText.ProfileFacade

/-!
# Instantiating the appendix profiles with the main-text coefficient

The appendix stays parameterized by `SeriesParallel.MainInput`.  These wrappers pass it the
concrete coefficient whose positivity was proved from the main-text integral, without adding the
stronger closed-form evaluation as a structure field or an axiom.
-/

namespace SeriesParallel.MainText

open SeriesParallel.Appendix

/-- The full-line distribution specialized to the internally constructed diffusion input. -/
theorem diffusion_full_line_distribution {lambda : ℝ} (horder : lambdaStar < lambda) :
    ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion diffusionMainInput lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi :=
  full_line_distribution horder

/-- The hard-edge distribution specialized to the internally constructed diffusion input. -/
theorem diffusion_hard_edge_distribution {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ∃ Psi : ℝ → ℝ,
      IsHardEdgeProfileConclusion diffusionMainInput lambda (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsHardEdgeProfileConclusion diffusionMainInput lambda (WSolution lambda hlambda) Phi →
            Set.EqOn Phi Psi (Set.Ici (0 : ℝ)) :=
  hard_edge_distribution hlambda hsubcritical

end SeriesParallel.MainText
