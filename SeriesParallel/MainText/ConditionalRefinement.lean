/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.StructuralProperties

/-!
# Conditional refinement on the common tree environment

This module packages the exact leaf-substitution identity with the probabilistic facts needed
after revealing the first `n` levels.  In particular, the full family of depth-`n` descendant
environments is independent of the sigma algebra generated strictly above depth `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SeriesParallel.MainText

@[reducible]
private def coordinateSigma (w : Word) : MeasurableSpace Environment :=
  MeasurableSpace.comap (coordinate w) inferInstance

@[reducible]
private def coordinatesBelow (n : ℕ) : MeasurableSpace Environment :=
  ⨆ w ∈ {w : Word | w.length < n}, coordinateSigma w

@[reducible]
private def coordinatesAtOrBelow (n : ℕ) : MeasurableSpace Environment :=
  ⨆ w ∈ {w : Word | n ≤ w.length}, coordinateSigma w

private theorem finiteLevelSigma_le_coordinatesBelow (n : ℕ) :
    finiteLevelSigma n ≤ coordinatesBelow n := by
  unfold finiteLevelSigma coordinatesBelow
  refine iSup_le fun w ↦ ?_
  exact le_iSup_of_le w.1 (le_iSup_of_le w.2 le_rfl)

private theorem descendantFamily_comap_le_atOrBelow (n : ℕ) :
    MeasurableSpace.comap (descendantFamily n)
      (inferInstance : MeasurableSpace (Level n → Environment)) ≤
        coordinatesAtOrBelow n := by
  rw [show (inferInstance : MeasurableSpace (Level n → Environment)) =
    ⨆ u : Level n,
      MeasurableSpace.comap (fun family : Level n → Environment ↦ family u)
        (inferInstance : MeasurableSpace Environment) from rfl]
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun u ↦ ?_
  rw [MeasurableSpace.comap_comp]
  rw [show (inferInstance : MeasurableSpace Environment) =
    ⨆ tail : Word,
      MeasurableSpace.comap (fun environment : Environment ↦ environment tail)
        (inferInstance : MeasurableSpace Bool) from rfl]
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun tail ↦ ?_
  rw [MeasurableSpace.comap_comp]
  change coordinateSigma (u.1 ++ tail) ≤ coordinatesAtOrBelow n
  have hlength : n ≤ (u.1 ++ tail).length := by simp [u.2]
  exact le_iSup_of_le (u.1 ++ tail) (le_iSup_of_le hlength le_rfl)

private theorem levelCoordinates_disjoint (n : ℕ) :
    Disjoint {w : Word | w.length < n} {w : Word | n ≤ w.length} := by
  rw [Set.disjoint_left]
  change ∀ w : Word, w.length < n → n ≤ w.length → False
  exact fun _ hlt hle ↦ (not_lt_of_ge hle) hlt

/-- The first `n` levels and all descendant environments rooted at level `n` are independent. -/
theorem finiteLevelSigma_indep_descendantFamily (p : unitInterval) (n : ℕ) :
    Indep (finiteLevelSigma n)
      (MeasurableSpace.comap (descendantFamily n) inferInstance) (environmentMeasure p) := by
  have hcoordinateLe : ∀ w, coordinateSigma w ≤
      (inferInstance : MeasurableSpace Environment) := fun w ↦
    (measurable_coordinate w).comap_le
  have hcoordinates : iIndep coordinateSigma (environmentMeasure p) :=
    (coordinates_iIndep p).iIndep
  have hblocks : Indep (coordinatesBelow n) (coordinatesAtOrBelow n)
      (environmentMeasure p) :=
    indep_iSup_of_disjoint hcoordinateLe hcoordinates (levelCoordinates_disjoint n)
  refine indep_of_indep_of_le hblocks (finiteLevelSigma_le_coordinatesBelow n) ?_
  exact descendantFamily_comap_le_atOrBelow n

/-- Exact deterministic refinement together with the complete iid descendant-law package. -/
theorem conditional_refinement_core (p : unitInterval) (n r : ℕ) :
    (∀ environment,
      randomNetwork (n + r) environment =
        (randomNetwork n environment).substitute
          (fun word ↦ randomNetwork r (Environment.subtree word environment))) ∧
      (environmentMeasure p).map (descendantFamily n) =
        Measure.infinitePi (fun _ : Level n ↦ environmentMeasure p) ∧
      iIndepFun (fun w : Level n ↦ subtreeShift w.1) (environmentMeasure p) ∧
      Indep (finiteLevelSigma n)
        (MeasurableSpace.comap (descendantFamily n) inferInstance) (environmentMeasure p) := by
  exact ⟨randomNetwork_refinement n r, descendantFamily_map p n,
    descendantFamilies_iIndep p n, finiteLevelSigma_indep_descendantFamily p n⟩

end SeriesParallel.MainText
