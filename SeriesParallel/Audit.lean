import SeriesParallel.Appendix
import SeriesParallel.AppendixPublicAPI

/-!
# Appendix trust-boundary and semantic regression audit

Every source-facing A1--A7/B1--B4 wrapper, the fixed density-defined probability laws,
and the two main-text density glue theorems are audited below.
-/

open Set
open scoped ENNReal

/-! A1--A7. -/
#print axioms SeriesParallel.Appendix.cuberoot_comparison_source
#print axioms SeriesParallel.Appendix.shootingProperties
#print axioms SeriesParallel.Appendix.cstarHalfline
#print axioms SeriesParallel.Appendix.existsUnique_boundarySolution_iff_lambdaStar_le
#print axioms SeriesParallel.Appendix.subcriticalW
#print axioms SeriesParallel.Appendix.linearAtOne
#print axioms SeriesParallel.Appendix.WSolution_linearAtOne
#print axioms SeriesParallel.Appendix.leftEndpoint_sourceLocalInverse
#print axioms SeriesParallel.Appendix.leftEndpointDichotomy_source
#print axioms SeriesParallel.Appendix.criticalBranches

/-! B1--B4 exact source-facing wrappers. -/
#print axioms SeriesParallel.Appendix.finiteAsymptoticODE_source
#print axioms SeriesParallel.Appendix.leftLinearBranchRegularity_source
#print axioms SeriesParallel.Appendix.rightLinearBranchRegularity_source
#print axioms SeriesParallel.Appendix.linearBranchRegularity_source
#print axioms SeriesParallel.Appendix.existsUnique_exactWaveProfile_of_linear_branches
#print axioms SeriesParallel.Appendix.waveProfile_exactSource
#print axioms SeriesParallel.Appendix.waveRelativeDerivatives
#print axioms SeriesParallel.Appendix.exists_exactHardEdgeProfile_uniqueOn
#print axioms SeriesParallel.Appendix.subcriticalProfile_exactSource
#print axioms SeriesParallel.Appendix.subcriticalProfile
#print axioms SeriesParallel.Appendix.IsExactWaveProfile.strictMono
#print axioms SeriesParallel.Appendix.IsExactHardEdgeProfile.strictMonoOn

/-! Fixed density-defined measures and main-text-derived density glue. -/
#print axioms SeriesParallel.Appendix.waveProfileLaw_probability_with_finiteAbsoluteFirstMoment
#print axioms SeriesParallel.Appendix.hardEdgeLaw_probability_with_finiteMean
#print axioms SeriesParallel.Appendix.hardEdgeLaw_singleton_zero
#print axioms SeriesParallel.Appendix.hardEdge_probabilityLaw_singleton_zero
#print axioms SeriesParallel.AppendixPublicAPI.wave_density_probability
#print axioms SeriesParallel.AppendixPublicAPI.hardEdge_density_probability
#print axioms SeriesParallel.Appendix.IsNormalizedHardEdgeProfile.hardEdgeDensity_zero
#print axioms SeriesParallel.Appendix.IsNormalizedHardEdgeProfile.hardEdgeDensity_zero_pos
#print axioms SeriesParallel.Appendix.IsNormalizedHardEdgeProfile.hardEdgeDensity_eq_deriv
#print axioms SeriesParallel.Appendix.IsNormalizedHardEdgeProfile.hardEdgeDensity_zero_eq_derivWithin
#print axioms SeriesParallel.Appendix.hardEdgeCDF_monotone
#print axioms SeriesParallel.Appendix.hardEdgeCDF_strictMonoOn
#print axioms SeriesParallel.AppendixPublicAPI.zeroExtendedHardEdgeDensity_zero
#print axioms SeriesParallel.AppendixPublicAPI.zeroExtendedHardEdgeDensity_eq_probabilityDensity
#print axioms SeriesParallel.AppendixPublicAPI.hardEdgeLaw_eq_withDensity_zeroExtended

/-! Supporting generic conclusions that must not acquire project admissions. -/
#print axioms SeriesParallel.Appendix.finiteAsymptoticODE
#print axioms SeriesParallel.Appendix.linearBranchRegularity
#print axioms SeriesParallel.Appendix.exists_waveProfile_probabilityLaw_with_finiteAbsoluteFirstMoment
#print axioms SeriesParallel.Appendix.exists_hardEdge_probabilityLaw_with_finiteMean
#print axioms SeriesParallel.Appendix.hardEdgeCDF_not_differentiableAt_zero

namespace SeriesParallel.AppendixAudit

open SeriesParallel
open SeriesParallel.Appendix
open SeriesParallel.AppendixPublicAPI

example (input : MainInput) (W Psi : ℝ → ℝ) :
    zeroExtendedHardEdgeDensity input W Psi 0 = 0 :=
  zeroExtendedHardEdgeDensity_zero input W Psi

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    hardEdgeDensity input W Psi 0 = input.beta * W 0 :=
  hPsi.hardEdgeDensity_zero

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    0 < hardEdgeDensity input W Psi 0 :=
  hPsi.hardEdgeDensity_zero_pos hpos

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u) :
    ¬ DifferentiableAt ℝ (hardEdgeCDF Psi) 0 :=
  hardEdgeCDF_not_differentiableAt_zero hPsi
    (hPsi.hardEdgeDensity_zero_pos hpos)

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi)
    (htail : HasRightExponentialTail Psi) :
    hardEdgeLaw input W Psi ({0} : Set ℝ) = 0 :=
  hardEdgeLaw_singleton_zero hPsi htail

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    Monotone (hardEdgeCDF Psi) :=
  hardEdgeCDF_monotone hPsi

example {input : MainInput} {W Psi : ℝ → ℝ}
    (hPsi : IsNormalizedHardEdgeProfile input W Psi) :
    StrictMonoOn (hardEdgeCDF Psi) (Ici 0) :=
  hardEdgeCDF_strictMonoOn hPsi

example (input : MainInput) (W Psi : ℝ → ℝ) :
    hardEdgeLaw input W Psi =
      MeasureTheory.volume.withDensity (fun z ↦
        ENNReal.ofReal (zeroExtendedHardEdgeDensity input W Psi z)) :=
  hardEdgeLaw_eq_withDensity_zeroExtended input W Psi

end SeriesParallel.AppendixAudit
