import SeriesParallel.Appendix.HardEdgeMeasures

/-!
# Assembly of the hard-edge profile conclusion

The source asserts uniqueness of the phase on `[0,∞)`.  Values of the chosen
representative on the negative half-line are intentionally not constrained, so the
uniqueness conclusion below is `EqOn` rather than global function equality.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-- Exact source conclusion attached to a candidate normalized hard-edge profile.
The density, probability law, and positive extension are existential data; only the
phase itself is unique on its mathematical domain. -/
def IsHardEdgeProfileConclusion (input : MainInput) (lambda : ℝ)
    (W Psi : ℝ → ℝ) : Prop :=
  IsNormalizedHardEdgeProfile input W Psi ∧
    (∀ z ∈ Ici (0 : ℝ),
      hardEdgeDensity input W Psi z = derivWithin Psi (Ici 0) z) ∧
    0 < hardEdgeDensity input W Psi 0 ∧
    (∀ z ∈ Ici (0 : ℝ), 0 < hardEdgeDensity input W Psi z) ∧
    (∀ z ∈ Ici (0 : ℝ),
      input.a * hardEdgeDensity input W Psi z *
          derivWithin (hardEdgeDensity input W Psi) (Ici 0) z +
          2 * Psi z * (1 - Psi z) =
        input.kappa lambda * hardEdgeDensity input W Psi z) ∧
    HalfLineRelativeDerivativeBounds (hardEdgeDensity input W Psi) ∧
    Tendsto (fun z ↦ hardEdgeDensity input W Psi z / (1 - Psi z)) atTop
      (𝓝 (input.beta / lambda)) ∧
    HasRightExponentialTail Psi ∧
    (∃ mu : Measure ℝ, IsProbabilityLawOfCDF (hardEdgeCDF Psi) mu ∧
      mu (Iio (0 : ℝ)) = 0 ∧ Integrable id mu) ∧
    ∃ extension : ℝ → ℝ,
      IsPositiveC3DensityExtension (hardEdgeDensity input W Psi) extension

/-- Generic B4 assembly once the source's relative derivative estimates and
cutoff-extension calculation have been established. -/
theorem exists_hardEdgeProfileConclusion_uniqueOn_of_estimates {input : MainInput}
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) 1))
    (hpos : ∀ u ∈ Ico (0 : ℝ) 1, 0 < W u)
    (hlinear : HasLinearBranchAtOne lambda W)
    (hequation : ∀ Psi, IsNormalizedHardEdgeProfile input W Psi →
      ∀ z ∈ Ici (0 : ℝ),
        input.a * hardEdgeDensity input W Psi z *
            derivWithin (hardEdgeDensity input W Psi) (Ici 0) z +
            2 * Psi z * (1 - Psi z) =
          input.kappa lambda * hardEdgeDensity input W Psi z)
    (hrelative : ∀ Psi, IsNormalizedHardEdgeProfile input W Psi →
      HalfLineRelativeDerivativeBounds (hardEdgeDensity input W Psi))
    (htails : ∀ Psi, IsNormalizedHardEdgeProfile input W Psi →
      HasRightExponentialTail Psi)
    (hextension : ∀ Psi, IsNormalizedHardEdgeProfile input W Psi →
      ∃ extension : ℝ → ℝ,
        IsPositiveC3DensityExtension (hardEdgeDensity input W Psi) extension) :
    ∃ Psi : ℝ → ℝ, IsHardEdgeProfileConclusion input lambda W Psi ∧
      ∀ Phi : ℝ → ℝ, IsHardEdgeProfileConclusion input lambda W Phi →
        EqOn Phi Psi (Ici (0 : ℝ)) := by
  rcases exists_normalizedHardEdgeProfile_uniqueOn hlambda hW hpos hlinear with
    ⟨Psi, hPsi, hPsiUnique⟩
  have htail := htails Psi hPsi
  rcases exists_hardEdge_probabilityLaw_with_finiteMean hPsi htail with
    ⟨mu, hmu, hsupport, hmean⟩
  have hqzero : 0 < hardEdgeDensity input W Psi 0 := by
    unfold hardEdgeDensity
    rw [hPsi.2.2.2.1]
    exact mul_pos input.beta_pos (hpos 0 ⟨le_rfl, zero_lt_one⟩)
  have hqpos : ∀ z ∈ Ici (0 : ℝ),
      0 < hardEdgeDensity input W Psi z := by
    intro z hz
    unfold hardEdgeDensity
    exact mul_pos input.beta_pos (hpos (Psi z) (hPsi.2.2.1 hz))
  refine ⟨Psi, ?_, ?_⟩
  · refine ⟨hPsi, ?_, hqzero, hqpos, hequation Psi hPsi,
      hrelative Psi hPsi, ?_, htail, ?_, hextension Psi hPsi⟩
    · intro z hz
      exact (hPsi.derivWithin_eq_hardEdgeDensity hz).symm
    · exact hardEdgeDensity_div_one_sub_profile_tendsto_atTop hlambda hPsi hlinear
    · exact ⟨mu, hmu, hsupport, hmean⟩
  · intro Phi hPhi
    exact hPsiUnique Phi hPhi.1.toExact

end SeriesParallel.Appendix
