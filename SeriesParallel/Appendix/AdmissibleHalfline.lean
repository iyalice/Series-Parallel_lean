import SeriesParallel.Appendix.AdmissibleLowerBound

/-!
# The admissible half-line

This module closes the proof of `prop:Cstar-halfline`: the infimum of the admissible
parameters is itself admissible, so upward closure identifies the admissible set exactly.
-/

open Set Filter Topology

namespace SeriesParallel.Appendix

/-- Closedness in the positive-parameter subtype places the infimum in the admissible set. -/
theorem lambdaStar_mem_admissibleSet : lambdaStar ∈ admissibleSet := by
  rcases exists_seq_tendsto_sInf admissibleSet_nonempty admissibleSet_bddBelow with
    ⟨parameters, _, hparameters, hmem⟩
  let positiveParameters : ℕ → {lambda : ℝ // 0 < lambda} :=
    fun n ↦ ⟨parameters n, (hmem n).choose⟩
  let starParameter : {lambda : ℝ // 0 < lambda} := ⟨lambdaStar, lambdaStar_pos⟩
  have hpositiveTendsto : Tendsto positiveParameters atTop (𝓝 starParameter) := by
    apply tendsto_subtype_rng.mpr
    exact hparameters
  have hpositiveMem : ∀ n, positiveParameters n ∈ positiveAdmissibleSet := by
    intro n
    change shootingY (parameters n) (hmem n).choose 1 = 0
    exact (hmem n).choose_spec
  have hstarPositive : starParameter ∈ positiveAdmissibleSet :=
    positiveAdmissibleSet_isClosed.mem_of_tendsto hpositiveTendsto
      (Eventually.of_forall hpositiveMem)
  exact ⟨lambdaStar_pos, hstarPositive⟩

/-- The source's exact identity `A = [lambdaStar, infinity)`. -/
theorem admissibleSet_eq_Ici_lambdaStar : admissibleSet = Ici lambdaStar := by
  ext lambda
  constructor
  · intro hlambda
    exact csInf_le admissibleSet_bddBelow hlambda
  · intro hlambda
    exact admissibleSet_upwardClosed lambdaStar_mem_admissibleSet hlambda

theorem mem_admissibleSet_iff_lambdaStar_le {lambda : ℝ} :
    lambda ∈ admissibleSet ↔ lambdaStar ≤ lambda := by
  rw [admissibleSet_eq_Ici_lambdaStar]
  rfl

/-- Direct source-facing existence-and-uniqueness characterization of the
admissible half-line.  The positivity hypothesis is exactly the parameter
domain used in the paper. -/
theorem existsUnique_boundarySolution_iff_lambdaStar_le {lambda : ℝ}
    (hlambda : 0 < lambda) :
    (∃! W : ℝ → ℝ, IsWBoundarySolution lambda W) ↔ lambdaStar ≤ lambda := by
  rw [← mem_admissibleSet_iff_lambdaStar_le]
  exact (mem_admissibleSet_iff_existsUnique_boundarySolution hlambda).symm

/-- Source-facing package for Proposition `prop:Cstar-halfline`. -/
structure CstarHalflineConclusion : Prop where
  criticalPositive : 0 < lambdaStar
  admissibleHalfline : admissibleSet = Ici lambdaStar
  criticalLowerBound : lambdaLower ≤ lambdaStar
  criticalUpperBound : lambdaStar ≤ lambdaUpper

/-- Proposition `prop:Cstar-halfline`, including both explicit rough bounds. -/
theorem cstarHalfline : CstarHalflineConclusion :=
  { criticalPositive := lambdaStar_pos
    admissibleHalfline := admissibleSet_eq_Ici_lambdaStar
    criticalLowerBound := lambdaLower_le_lambdaStar
    criticalUpperBound := lambdaStar_le_upper }

end SeriesParallel.Appendix
