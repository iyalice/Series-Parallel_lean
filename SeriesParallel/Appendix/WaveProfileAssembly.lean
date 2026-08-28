import SeriesParallel.Appendix.ProfileMeasures

/-!
# Assembly of the full-line profile conclusion

The proposition below is the proof-relevant-free public shape of B3.  In particular,
the density is the explicit phase expression and is proved equal to `deriv Phi`.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace SeriesParallel.Appendix

/-- Exact source conclusion attached to a candidate normalized full-line profile. -/
def IsWaveProfileConclusion (input : MainInput) (lambda : ℝ)
    (W Phi : ℝ → ℝ) : Prop :=
  IsNormalizedWaveProfile input W Phi ∧
    (∀ z, deriv Phi z = waveDensity input W Phi z) ∧
    (∀ z, 0 < waveDensity input W Phi z) ∧
    (∀ z,
      input.a * waveDensity input W Phi z * deriv (waveDensity input W Phi) z -
          2 * Phi z * (1 - Phi z) =
        -input.kappa lambda * waveDensity input W Phi z) ∧
    FullLineRelativeDerivativeBounds (waveDensity input W Phi) ∧
    Tendsto (fun z ↦ waveDensity input W Phi z / Phi z) atBot
      (𝓝 (input.beta / lambda)) ∧
    Tendsto (fun z ↦ waveDensity input W Phi z / (1 - Phi z)) atTop
      (𝓝 (input.beta / lambda)) ∧
    HasTwoSidedExponentialTails Phi ∧
    ∃ mu : Measure ℝ, IsProbabilityLawOfCDF Phi mu ∧
      Integrable (fun x : ℝ ↦ |x|) mu

/-- Generic B3 assembly after the ODE-relative-bound and exponential-tail estimates
have been established.  All hypotheses are direct source proof obligations, not new
manual interfaces. -/
theorem existsUnique_waveProfileConclusion_of_estimates {input : MainInput}
    {lambda : ℝ} {W : ℝ → ℝ} (hlambda : 0 < lambda)
    (hW : ContDiffOn ℝ ∞ W openUnitInterval)
    (hpos : ∀ u ∈ openUnitInterval, 0 < W u)
    (hode : ∀ u ∈ openUnitInterval, SatisfiesWODEAt lambda W u)
    (hzero : HasLinearBranchAtZero lambda W)
    (hone : HasLinearBranchAtOne lambda W)
    (hrelative : ∀ Phi, IsNormalizedWaveProfile input W Phi →
      FullLineRelativeDerivativeBounds (waveDensity input W Phi))
    (htails : ∀ Phi, IsNormalizedWaveProfile input W Phi →
      HasTwoSidedExponentialTails Phi) :
    ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion input lambda W Phi := by
  rcases existsUnique_normalizedWaveProfile_of_linear_branches hlambda hW hpos hzero hone with
    ⟨Phi, hPhi, hPhiUnique⟩
  have htail := htails Phi hPhi
  rcases exists_waveProfile_probabilityLaw_with_finiteAbsoluteFirstMoment hPhi htail with
    ⟨mu, hmu, hmoment⟩
  refine ⟨Phi, ?_, ?_⟩
  · refine ⟨hPhi, ?_, ?_, ?_, hrelative Phi hPhi, ?_, ?_, htail,
      mu, hmu, hmoment⟩
    · intro z
      exact hPhi.deriv_eq_waveDensity z
    · intro z
      unfold waveDensity
      exact mul_pos input.beta_pos (hpos (1 - Phi z)
        ⟨by linarith [(hPhi.2.2.1 z).2], by linarith [(hPhi.2.2.1 z).1]⟩)
    · intro z
      exact waveEquationAt_of_phase_of_wODE (hPhi.2.2.2.2.1 z)
        (hode (1 - Phi z) ⟨by linarith [(hPhi.2.2.1 z).2],
          by linarith [(hPhi.2.2.1 z).1]⟩)
    · exact waveDensity_div_profile_tendsto_atBot hlambda hPhi hone
    · exact waveDensity_div_one_sub_profile_tendsto_atTop hlambda hPhi hzero
  · intro Psi hPsi
    exact hPhiUnique Psi hPsi.1

end SeriesParallel.Appendix
