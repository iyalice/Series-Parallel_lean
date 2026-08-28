import SeriesParallel.Appendix.HardEdgeAssembly
import SeriesParallel.Appendix.HardEdgeProfileEstimates
import SeriesParallel.Appendix.HardEdgeExtension

/-!
# The subcritical hard-edge profile from right-endpoint regularity

This is the source-facing B4 assembly point.  It deliberately takes the
right-endpoint regularity conclusion as an input, so it does not depend on the
remaining proof of B2.
-/

open Set
open scoped ContDiff

namespace SeriesParallel.Appendix

/-- Exact source-facing B4 phase theorem.  Candidate phases carry only the monotone
half-line data stated in the source; uniqueness is `EqOn` on `[0,∞)` because values on
the negative half-line are irrelevant. -/
theorem subcriticalProfile_exactSource {input : MainInput} {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ∃ Psi : ℝ → ℝ,
      IsExactHardEdgeProfile input (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsExactHardEdgeProfile input (WSolution lambda hlambda) Phi →
            EqOn Phi Psi (Ici (0 : ℝ)) := by
  let W : ℝ → ℝ := WSolution lambda hlambda
  have hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1) := by
    exact WSolution_contDiffOn_infty_Ico_of_lt_lambdaStar hlambda hsubcritical
  have hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u := by
    exact WSolution_pos_Ico_of_lt_lambdaStar hlambda hsubcritical
  have hlinear : HasLinearBranchAtOne lambda W := by
    exact WSolution_linearAtOne lambda hlambda
  change ∃ Psi : ℝ → ℝ, IsExactHardEdgeProfile input W Psi ∧
    ∀ Phi : ℝ → ℝ, IsExactHardEdgeProfile input W Phi →
      EqOn Phi Psi (Ici (0 : ℝ))
  exact exists_exactHardEdgeProfile_uniqueOn hlambda hW hpos hlinear

/-- The subcritical hard-edge conclusion follows from the right-endpoint
regularity of the canonical transform.  Uniqueness is asserted only on the
natural half-line domain of the phase. -/
theorem subcriticalProfile_of_rightEndpointRegularity {input : MainInput}
    {lambda : ℝ} (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar)
    (hright : RightLinearBranchRegularity lambda (WSolution lambda hlambda)) :
    ∃ Psi : ℝ → ℝ,
      IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Phi →
            EqOn Phi Psi (Ici (0 : ℝ)) := by
  let W : ℝ → ℝ := WSolution lambda hlambda
  have hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1) := by
    dsimp only [W]
    exact WSolution_contDiffOn_infty_Ico_of_lt_lambdaStar hlambda hsubcritical
  have hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u := by
    dsimp only [W]
    exact WSolution_pos_Ico_of_lt_lambdaStar hlambda hsubcritical
  have hlinear : HasLinearBranchAtOne lambda W := by
    dsimp only [W]
    exact WSolution_linearAtOne lambda hlambda
  change ∃ Psi : ℝ → ℝ, IsHardEdgeProfileConclusion input lambda W Psi ∧
    ∀ Phi : ℝ → ℝ, IsHardEdgeProfileConclusion input lambda W Phi →
      EqOn Phi Psi (Ici (0 : ℝ))
  apply exists_hardEdgeProfileConclusion_uniqueOn_of_estimates hlambda hW hpos hlinear
  · intro Psi hPsi
    dsimp only [W] at hPsi ⊢
    exact WSolution_hardEdgeProfileEquation hlambda hsubcritical hPsi
  · intro Psi hPsi
    exact hardEdgeDensity_halfLineRelativeDerivativeBounds_of_rightEndpointRegularity
      hW hpos hright hPsi
  · intro Psi hPsi
    exact hardEdgeProfile_hasRightExponentialTail hlambda hPsi hlinear
  · intro Psi hPsi
    have hrelative :=
      hardEdgeDensity_halfLineRelativeDerivativeBounds_of_rightEndpointRegularity
        hW hpos hright hPsi
    exact hardEdgeDensity_exists_positiveC3DensityExtension hW hpos hPsi hrelative

/-- `cor:subcritical-profile`: the canonical subcritical shooting solution
produces the normalized hard-edge profile, unique on its natural half-line,
with the profile equation, relative bounds, right tail, finite-mean law, and a
positive `C³` density extension to the whole real line. -/
theorem subcriticalProfile {input : MainInput} {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ∃ Psi : ℝ → ℝ,
      IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Phi →
            EqOn Phi Psi (Ici (0 : ℝ)) := by
  apply subcriticalProfile_of_rightEndpointRegularity hlambda hsubcritical
  exact WSolution_rightLinearBranchRegularity lambda hlambda
    (WSolution_linearAtOne lambda hlambda)

end SeriesParallel.Appendix
