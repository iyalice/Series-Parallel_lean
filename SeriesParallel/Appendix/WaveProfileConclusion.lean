import SeriesParallel.Appendix.CriticalBranches
import SeriesParallel.Appendix.LinearBranchRegularity
import SeriesParallel.Appendix.WaveProfileAssembly
import SeriesParallel.Appendix.WaveProfileEstimates

/-!
# The supercritical full-line profile from endpoint regularity
-/

open Set
open scoped ContDiff

namespace SeriesParallel.Appendix

/-- Exact source-facing B3 phase theorem.  The uniqueness candidates assume
`Monotone`, not `StrictMono`; strictness follows internally from the positive phase
right-hand side. -/
theorem waveProfile_exactSource {input : MainInput} {lambda : ℝ}
    (horder : lambdaStar < lambda) :
    ∃! Phi : ℝ → ℝ, IsExactWaveProfile input
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi := by
  let hlambda : 0 < lambda := lambdaStar_pos.trans horder
  let W : ℝ → ℝ := WSolution lambda hlambda
  have hW : ContDiffOn ℝ ∞ W openUnitInterval := by
    exact WSolution_contDiffOn_infty_interior lambda hlambda
  have hpos : ∀ u ∈ openUnitInterval, 0 < W u := by
    exact WSolution_pos lambda hlambda
  have hzero : HasLinearBranchAtZero lambda W := by
    dsimp only [W, hlambda]
    exact criticalBranches.supercriticalLinear lambda horder
  have hone : HasLinearBranchAtOne lambda W := by
    exact WSolution_linearAtOne lambda hlambda
  change ∃! Phi : ℝ → ℝ, IsExactWaveProfile input W Phi
  exact existsUnique_exactWaveProfile_of_linear_branches hlambda hW hpos hzero hone

/-- B3 assembled from the two endpoint-regularity conclusions.  The public source
theorem below obtains this hypothesis from B2. -/
theorem waveRelativeDerivatives_of_regularities {input : MainInput} {lambda : ℝ}
    (horder : lambdaStar < lambda)
    (hregularity : LinearBranchRegularityConclusion lambda
      (WSolution lambda (lambdaStar_pos.trans horder))) :
    ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion input lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi := by
  let hlambda : 0 < lambda := lambdaStar_pos.trans horder
  let W : ℝ → ℝ := WSolution lambda hlambda
  have hzero : HasLinearBranchAtZero lambda W := by
    dsimp only [W, hlambda]
    exact criticalBranches.supercriticalLinear lambda horder
  have hone : HasLinearBranchAtOne lambda W := by
    dsimp only [W, hlambda]
    exact WSolution_linearAtOne lambda (lambdaStar_pos.trans horder)
  have hleft : LeftLinearBranchRegularity lambda W := by
    exact hregularity.atZero hzero
  have hright : RightLinearBranchRegularity lambda W := by
    exact hregularity.atOne hone
  have hW : ContDiffOn ℝ ∞ W openUnitInterval := by
    exact WSolution_contDiffOn_infty_interior lambda hlambda
  have hpos : ∀ u ∈ openUnitInterval, 0 < W u := by
    exact WSolution_pos lambda hlambda
  have hode : ∀ u ∈ openUnitInterval, SatisfiesWODEAt lambda W u := by
    exact WSolution_satisfiesWODEAt lambda hlambda
  change ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion input lambda W Phi
  apply existsUnique_waveProfileConclusion_of_estimates hlambda hW hpos hode
    hzero hone
  · intro Phi hPhi
    exact waveDensity_fullLineRelativeDerivativeBounds_of_endpoint_regularities
      hW hpos hleft hright hPhi
  · intro Phi hPhi
    exact waveProfile_hasTwoSidedExponentialTails hlambda hPhi hzero hone

/-- `cor:wave-relative-derivatives`: the canonical supercritical boundary
solution produces the unique normalized full-line profile together with the
wave equation, relative derivative bounds, both tails, and its finite-moment
probability law. -/
theorem waveRelativeDerivatives {input : MainInput} {lambda : ℝ}
    (horder : lambdaStar < lambda) :
    ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion input lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi := by
  let hlambda : 0 < lambda := lambdaStar_pos.trans horder
  have hadmissible : lambda ∈ admissibleSet :=
    mem_admissibleSet_iff_lambdaStar_le.mpr horder.le
  rcases hadmissible with ⟨_hlambda, hzero⟩
  have hsolution : IsWBoundarySolution lambda (WSolution lambda hlambda) := by
    apply WSolution_isBoundarySolution hlambda
    simpa only using hzero
  exact waveRelativeDerivatives_of_regularities horder
    (linearBranchRegularity hlambda hsolution)

end SeriesParallel.Appendix
