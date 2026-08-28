import SeriesParallel.MainTextInterface
import SeriesParallel.Appendix.WaveProfileConclusion
import SeriesParallel.Appendix.HardEdgeProfileConclusion
import SeriesParallel.AppendixPublicAPI

/-!
# Main-text profile façade

This module gives the eleven profile labels moved from the appendix to the main text a narrow,
source-facing API.  All mathematical content is supplied by the already proved appendix profile
packages.  In particular, hard-edge uniqueness remains equality only on `[0, ∞)`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SeriesParallel.MainText

open SeriesParallel.Appendix

/-- `prop:full-line-distribution`: the canonical supercritical shooting solution gives the
unique normalized full-line distribution, its equation and relative bounds, both tail ratios,
and a finite-absolute-first-moment probability law. -/
theorem full_line_distribution {input : MainInput} {lambda : ℝ}
    (horder : lambdaStar < lambda) :
    ∃! Phi : ℝ → ℝ, IsWaveProfileConclusion input lambda
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi :=
  waveRelativeDerivatives horder

/-- `eq:Phi-phase-definition`: exact full-line phase existence and uniqueness, with merely
monotone candidates as in the source. -/
theorem full_line_phase_definition {input : MainInput} {lambda : ℝ}
    (horder : lambdaStar < lambda) :
    ∃! Phi : ℝ → ℝ, IsExactWaveProfile input
      (WSolution lambda (lambdaStar_pos.trans horder)) Phi :=
  waveProfile_exactSource horder

/-- `eq:upper-profile-equation`: the differential equation projected from the full-line
distribution package. -/
theorem upper_profile_equation {input : MainInput} {lambda : ℝ} {W Phi : ℝ → ℝ}
    (h : IsWaveProfileConclusion input lambda W Phi) :
    ∀ z,
      input.a * waveDensity input W Phi z * deriv (waveDensity input W Phi) z -
          2 * Phi z * (1 - Phi z) =
        -input.kappa lambda * waveDensity input W Phi z :=
  h.2.2.2.1

/-- `eq:full-line-relative-bounds`: relative derivative bounds through order three for the
full-line density. -/
theorem full_line_relative_bounds {input : MainInput} {lambda : ℝ} {W Phi : ℝ → ℝ}
    (h : IsWaveProfileConclusion input lambda W Phi) :
    FullLineRelativeDerivativeBounds (waveDensity input W Phi) :=
  h.2.2.2.2.1

/-- `eq:full-line-tail-ratios`: both source tail ratios for the full-line density. -/
theorem full_line_tail_ratios {input : MainInput} {lambda : ℝ} {W Phi : ℝ → ℝ}
    (h : IsWaveProfileConclusion input lambda W Phi) :
    Tendsto (fun z ↦ waveDensity input W Phi z / Phi z) atBot
        (nhds (input.beta / lambda)) ∧
      Tendsto (fun z ↦ waveDensity input W Phi z / (1 - Phi z)) atTop
        (nhds (input.beta / lambda)) :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- `prop:hard-edge-distribution`: the canonical subcritical shooting solution gives a
normalized hard-edge distribution with the equation, relative bounds, right tail, finite-mean
law, and positive global density extension.  Uniqueness is only `EqOn` `[0, ∞)`. -/
theorem hard_edge_distribution {input : MainInput} {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ∃ Psi : ℝ → ℝ,
      IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsHardEdgeProfileConclusion input lambda (WSolution lambda hlambda) Phi →
            EqOn Phi Psi (Ici (0 : ℝ)) :=
  subcriticalProfile hlambda hsubcritical

/-- `eq:Psi-subcritical-definition`: exact hard-edge phase existence and uniqueness on its
natural half-line.  Candidate values on the negative half-line remain unconstrained. -/
theorem hard_edge_phase_definition {input : MainInput} {lambda : ℝ}
    (hlambda : 0 < lambda) (hsubcritical : lambda < lambdaStar) :
    ∃ Psi : ℝ → ℝ,
      IsExactHardEdgeProfile input (WSolution lambda hlambda) Psi ∧
        ∀ Phi : ℝ → ℝ,
          IsExactHardEdgeProfile input (WSolution lambda hlambda) Phi →
            EqOn Phi Psi (Ici (0 : ℝ)) :=
  subcriticalProfile_exactSource hlambda hsubcritical

/-- `eq:lower-profile-equation`: the one-sided differential equation, including `z = 0`,
projected from the hard-edge distribution package. -/
theorem lower_profile_equation {input : MainInput} {lambda : ℝ} {W Psi : ℝ → ℝ}
    (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    ∀ z ∈ Ici (0 : ℝ),
      input.a * hardEdgeDensity input W Psi z *
          derivWithin (hardEdgeDensity input W Psi) (Ici 0) z +
          2 * Psi z * (1 - Psi z) =
        input.kappa lambda * hardEdgeDensity input W Psi z :=
  h.2.2.2.2.1

/-- `eq:subcritical-relative-bounds`: one-sided relative derivative bounds through order three
for the hard-edge density. -/
theorem subcritical_relative_bounds {input : MainInput} {lambda : ℝ}
    {W Psi : ℝ → ℝ} (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    HalfLineRelativeDerivativeBounds (hardEdgeDensity input W Psi) :=
  h.2.2.2.2.2.1

/-- `eq:q-extension-bounds`: existence of the positive global `C³` extension, equal to the
physical density on `[0, ∞)` and satisfying the source's relative bounds. -/
theorem hard_edge_density_extension_bounds {input : MainInput} {lambda : ℝ}
    {W Psi : ℝ → ℝ} (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    ∃ extension : ℝ → ℝ,
      IsPositiveC3DensityExtension (hardEdgeDensity input W Psi) extension :=
  h.2.2.2.2.2.2.2.2.2

/-- `eq:subcritical-right-tail`: the source right-tail density ratio. -/
theorem subcritical_right_tail {input : MainInput} {lambda : ℝ} {W Psi : ℝ → ℝ}
    (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    Tendsto (fun z ↦ hardEdgeDensity input W Psi z / (1 - Psi z)) atTop
      (nhds (input.beta / lambda)) :=
  h.2.2.2.2.2.2.1

/-- Probability-density conclusion of `prop:full-line-distribution`, delegated to the existing
narrow appendix public API. -/
theorem full_line_density_probability {input : MainInput} {lambda : ℝ}
    {W Phi : ℝ → ℝ} (h : IsWaveProfileConclusion input lambda W Phi) :
    let q : ℝ → ℝ := waveDensity input W Phi
    (∀ z, 0 ≤ q z) ∧ Integrable q ∧ (∫ z, q z) = 1 ∧
      ∀ mu : Measure ℝ, IsProbabilityLawOfCDF Phi mu →
        mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)) :=
  SeriesParallel.AppendixPublicAPI.wave_density_probability h

/-- Probability-density conclusion of `prop:hard-edge-distribution`, using the physical zero
extension rather than the positive analytic extension. -/
theorem hard_edge_density_probability {input : MainInput} {lambda : ℝ}
    {W Psi : ℝ → ℝ} (h : IsHardEdgeProfileConclusion input lambda W Psi) :
    let q : ℝ → ℝ := hardEdgeDensity input W Psi
    let q0 : ℝ → ℝ :=
      SeriesParallel.AppendixPublicAPI.zeroExtendedHardEdgeDensity input W Psi
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ q z) ∧ IntegrableOn q (Ici 0) ∧
      (∫ z in Ici (0 : ℝ), q z) = 1 ∧ Integrable q0 ∧
      ∀ mu : Measure ℝ, IsProbabilityLawOfCDF (hardEdgeCDF Psi) mu →
        mu = volume.withDensity (fun z ↦ ENNReal.ofReal (q0 z)) :=
  SeriesParallel.AppendixPublicAPI.hardEdge_density_probability h

end SeriesParallel.MainText
