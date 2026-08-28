/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.FinitePaths

/-!
# Finite unit flows on two-terminal series--parallel networks

A flow is represented recursively. At a series gate both children carry the same through-current;
at a parallel gate the real parameter is the fraction sent through the left child, while the right
child carries the complementary fraction. This representation permits arbitrary signed branch
currents and makes the parallel square-completion argument literal.
-/

@[expose] public section

namespace SeriesParallel.MainText.SPNetwork

/-- Recursive normalized through-flows on a two-terminal network. -/
def Flow : (network : SPNetwork) → Type
  | .edge => PUnit
  | .series left right => Flow left × Flow right
  | .parallel left right => ℝ × Flow left × Flow right

/-- Addresses of all leaves, independent of whether an internal gate is series or parallel. -/
def leafAddresses : SPNetwork → List (List Bool)
  | .edge => [[]]
  | .series left right =>
      left.leafAddresses.map (false :: ·) ++ right.leafAddresses.map (true :: ·)
  | .parallel left right =>
      left.leafAddresses.map (false :: ·) ++ right.leafAddresses.map (true :: ·)

/-- Through-current at a leaf address, extended by zero away from the network leaves. -/
noncomputable def Flow.currentAt : {network : SPNetwork} → Flow network → List Bool → ℝ
  | .edge, _, [] => 1
  | .edge, _, _ :: _ => 0
  | .series _ _, flow, false :: word => flow.1.currentAt word
  | .series _ _, flow, true :: word => flow.2.currentAt word
  | .series _ _, _, [] => 0
  | .parallel _ _, flow, false :: word => flow.1 * flow.2.1.currentAt word
  | .parallel _ _, flow, true :: word => (1 - flow.1) * flow.2.2.currentAt word
  | .parallel _ _, _, [] => 0

/-- Energy of a flow when each leaf address is assigned a resistance. -/
noncomputable def Flow.energy : {network : SPNetwork} →
    Flow network → (List Bool → ℝ) → ℝ
  | .edge, _, resistanceAt => resistanceAt []
  | .series _ _, flow, resistanceAt =>
      flow.1.energy (fun word ↦ resistanceAt (false :: word)) +
        flow.2.energy (fun word ↦ resistanceAt (true :: word))
  | .parallel _ _, flow, resistanceAt =>
      flow.1 ^ 2 * flow.2.1.energy (fun word ↦ resistanceAt (false :: word)) +
        (1 - flow.1) ^ 2 *
          flow.2.2.energy (fun word ↦ resistanceAt (true :: word))

private theorem sq_mul_list_sum {alpha : Type} (constant : ℝ) (words : List alpha)
    (current resistanceAt : alpha → ℝ) :
    constant ^ 2 *
        (words.map fun word ↦ current word ^ 2 * resistanceAt word).sum =
      (words.map fun word ↦
        (constant * current word) ^ 2 * resistanceAt word).sum := by
  induction words with
  | nil => simp
  | cons word words ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]
      congr 1
      ring

/-- Recursive energy is the finite sum of squared leaf currents times leaf resistances. -/
theorem Flow.energy_eq_sum {network : SPNetwork} (flow : Flow network)
    (resistanceAt : List Bool → ℝ) :
    flow.energy resistanceAt =
      (network.leafAddresses.map fun word ↦
        flow.currentAt word ^ 2 * resistanceAt word).sum := by
  induction network generalizing resistanceAt with
  | edge =>
      cases flow
      simp [Flow.energy, leafAddresses, Flow.currentAt]
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      simp only [Flow.energy, leafAddresses, List.map_append, List.sum_append,
        List.map_map]
      rw [ihLeft, ihRight]
      rfl
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨current, leftFlow, rightFlow⟩
      simp only [Flow.energy, leafAddresses, List.map_append, List.sum_append,
        List.map_map]
      rw [ihLeft, ihRight]
      change
        current ^ 2 *
              (left.leafAddresses.map fun word ↦
                leftFlow.currentAt word ^ 2 * resistanceAt (false :: word)).sum +
            (1 - current) ^ 2 *
              (right.leafAddresses.map fun word ↦
                rightFlow.currentAt word ^ 2 * resistanceAt (true :: word)).sum =
          (left.leafAddresses.map fun word ↦
                (current * leftFlow.currentAt word) ^ 2 *
                  resistanceAt (false :: word)).sum +
            (right.leafAddresses.map fun word ↦
                ((1 - current) * rightFlow.currentAt word) ^ 2 *
                  resistanceAt (true :: word)).sum
      rw [sq_mul_list_sum, sq_mul_list_sum]

/-- Energy when every leaf has unit resistance. -/
noncomputable def Flow.unitEnergy {network : SPNetwork} (flow : Flow network) : ℝ :=
  flow.energy fun _ ↦ 1

/-- Energy is homogeneous when all leaf resistances are the same constant. -/
theorem Flow.energy_const {network : SPNetwork} (flow : Flow network) (constant : ℝ) :
    flow.energy (fun _ ↦ constant) = flow.unitEnergy * constant := by
  induction network with
  | edge =>
      cases flow
      simp [Flow.energy, Flow.unitEnergy]
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      change
        leftFlow.energy (fun _ ↦ constant) + rightFlow.energy (fun _ ↦ constant) =
          (leftFlow.unitEnergy + rightFlow.unitEnergy) * constant
      rw [ihLeft, ihRight]
      ring
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨current, leftFlow, rightFlow⟩
      change
        current ^ 2 * leftFlow.energy (fun _ ↦ constant) +
            (1 - current) ^ 2 * rightFlow.energy (fun _ ↦ constant) =
          (current ^ 2 * leftFlow.unitEnergy +
              (1 - current) ^ 2 * rightFlow.unitEnergy) * constant
      rw [ihLeft, ihRight]
      ring

/-- Nonnegative leaf resistances give nonnegative flow energy. -/
theorem Flow.energy_nonneg {network : SPNetwork} (flow : Flow network)
    (resistanceAt : List Bool → ℝ) (hresistance : ∀ word, 0 ≤ resistanceAt word) :
    0 ≤ flow.energy resistanceAt := by
  induction network generalizing resistanceAt with
  | edge => exact hresistance []
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      exact add_nonneg
        (ihLeft leftFlow (fun word ↦ resistanceAt (false :: word))
          (fun word ↦ hresistance (false :: word)))
        (ihRight rightFlow (fun word ↦ resistanceAt (true :: word))
          (fun word ↦ hresistance (true :: word)))
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨current, leftFlow, rightFlow⟩
      exact add_nonneg
        (mul_nonneg (sq_nonneg current)
          (ihLeft leftFlow (fun word ↦ resistanceAt (false :: word))
            (fun word ↦ hresistance (false :: word))))
        (mul_nonneg (sq_nonneg (1 - current))
          (ihRight rightFlow (fun word ↦ resistanceAt (true :: word))
            (fun word ↦ hresistance (true :: word))))

/-- The energy-minimizing normalized flow, defined by recursive current division. -/
noncomputable def optimalFlow : (network : SPNetwork) → Flow network
  | .edge => PUnit.unit
  | .series left right => (optimalFlow left, optimalFlow right)
  | .parallel left right =>
      (right.resistance / (left.resistance + right.resistance),
        optimalFlow left, optimalFlow right)

/-- Send one unit of current along a chosen path and zero through the unused parallel branch. -/
noncomputable def Flow.ofPath : {network : SPNetwork} → Path network → Flow network
  | .edge, _ => PUnit.unit
  | .series _ _, path => (Flow.ofPath path.1, Flow.ofPath path.2)
  | .parallel _ right, Sum.inl path => (1, Flow.ofPath path, optimalFlow right)
  | .parallel left _, Sum.inr path => (0, optimalFlow left, Flow.ofPath path)

/-- A path flow has energy equal to the number of unit edges traversed by the path. -/
theorem Flow.unitEnergy_ofPath {network : SPNetwork} (path : Path network) :
    (Flow.ofPath path).unitEnergy = path.length := by
  induction network with
  | edge =>
      cases path
      simp [Flow.unitEnergy, Flow.energy, Path.length, Path.weightedLength]
  | series left right ihLeft ihRight =>
      rcases path with ⟨leftPath, rightPath⟩
      change (Flow.ofPath leftPath).unitEnergy + (Flow.ofPath rightPath).unitEnergy =
        ((leftPath.length + rightPath.length : ℕ) : ℝ)
      rw [ihLeft, ihRight]
      norm_num
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · change
          1 ^ 2 * (Flow.ofPath leftPath).unitEnergy +
              (1 - 1) ^ 2 * (optimalFlow right).unitEnergy = leftPath.length
        rw [ihLeft]
        ring
      · change
          0 ^ 2 * (optimalFlow left).unitEnergy +
              (1 - 0) ^ 2 * (Flow.ofPath rightPath).unitEnergy = rightPath.length
        rw [ihRight]
        ring

private theorem parallel_energy_sub_resistance_eq_square
    {leftResistance rightResistance current : ℝ}
    (hleft : 0 < leftResistance) (hright : 0 < rightResistance) :
    current ^ 2 * leftResistance + (1 - current) ^ 2 * rightResistance -
        leftResistance * rightResistance / (leftResistance + rightResistance) =
      ((leftResistance + rightResistance) * current - rightResistance) ^ 2 /
        (leftResistance + rightResistance) := by
  field_simp [ne_of_gt (add_pos hleft hright)]
  ring

/-- Parallel square completion: every split has at least harmonic-combination energy. -/
theorem harmonic_le_split_energy {leftResistance rightResistance current : ℝ}
    (hleft : 0 < leftResistance) (hright : 0 < rightResistance) :
    leftResistance * rightResistance / (leftResistance + rightResistance) ≤
      current ^ 2 * leftResistance + (1 - current) ^ 2 * rightResistance := by
  rw [← sub_nonneg]
  rw [parallel_energy_sub_resistance_eq_square hleft hright]
  positivity

/-- The recursively chosen flow has energy equal to effective resistance. -/
@[simp]
theorem optimalFlow_unitEnergy (network : SPNetwork) :
    (optimalFlow network).unitEnergy = network.resistance := by
  induction network with
  | edge => rfl
  | series left right ihLeft ihRight =>
      change (optimalFlow left).unitEnergy + (optimalFlow right).unitEnergy =
        left.resistance + right.resistance
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      change
        (right.resistance / (left.resistance + right.resistance)) ^ 2 *
              (optimalFlow left).unitEnergy +
            (1 - right.resistance / (left.resistance + right.resistance)) ^ 2 *
              (optimalFlow right).unitEnergy =
          left.resistance * right.resistance /
            (left.resistance + right.resistance)
      rw [ihLeft, ihRight]
      have hleft := left.resistance_pos
      have hright := right.resistance_pos
      field_simp [left.resistance_ne_zero, right.resistance_ne_zero,
        ne_of_gt (add_pos hleft hright)]
      ring

/-- Thomson's principle for the recursive series--parallel flow semantics. -/
theorem resistance_le_unitEnergy {network : SPNetwork} (flow : Flow network) :
    network.resistance ≤ flow.unitEnergy := by
  induction network with
  | edge =>
      cases flow
      simp [Flow.unitEnergy, Flow.energy, resistance]
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      change left.resistance + right.resistance ≤
        leftFlow.unitEnergy + rightFlow.unitEnergy
      exact add_le_add (ihLeft leftFlow) (ihRight rightFlow)
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨current, leftFlow, rightFlow⟩
      have hcurrent : 0 ≤ current ^ 2 := sq_nonneg current
      have hcomplement : 0 ≤ (1 - current) ^ 2 := sq_nonneg (1 - current)
      change
        left.resistance * right.resistance / (left.resistance + right.resistance) ≤
          current ^ 2 * leftFlow.unitEnergy +
            (1 - current) ^ 2 * rightFlow.unitEnergy
      calc
        left.resistance * right.resistance / (left.resistance + right.resistance) ≤
            current ^ 2 * left.resistance +
              (1 - current) ^ 2 * right.resistance :=
          harmonic_le_split_energy left.resistance_pos right.resistance_pos
        _ ≤ current ^ 2 * leftFlow.unitEnergy +
              (1 - current) ^ 2 * rightFlow.unitEnergy := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ihLeft leftFlow) hcurrent)
            (mul_le_mul_of_nonneg_left (ihRight rightFlow) hcomplement)

/-- Insert independently chosen normalized flows into every substituted leaf. -/
noncomputable def Flow.substitute : {network : SPNetwork} →
    (replacement : List Bool → SPNetwork) → Flow network →
      ((word : List Bool) → Flow (replacement word)) →
        Flow (network.substitute replacement)
  | .edge, _, _, innerFlow => innerFlow []
  | .series _ _, replacement, outerFlow, innerFlow =>
      (Flow.substitute (fun word ↦ replacement (false :: word)) outerFlow.1
          (fun word ↦ innerFlow (false :: word)),
        Flow.substitute (fun word ↦ replacement (true :: word)) outerFlow.2
          (fun word ↦ innerFlow (true :: word)))
  | .parallel _ _, replacement, outerFlow, innerFlow =>
      (outerFlow.1,
        Flow.substitute (fun word ↦ replacement (false :: word)) outerFlow.2.1
          (fun word ↦ innerFlow (false :: word)),
        Flow.substitute (fun word ↦ replacement (true :: word)) outerFlow.2.2
          (fun word ↦ innerFlow (true :: word)))

/-- Substituting optimal inner flows turns their effective resistances into leaf weights. -/
theorem substitute_optimalFlow_unitEnergy {network : SPNetwork}
    (replacement : List Bool → SPNetwork) (outerFlow : Flow network) :
    (outerFlow.substitute replacement fun word ↦ optimalFlow (replacement word)).unitEnergy =
      outerFlow.energy fun word ↦ (replacement word).resistance := by
  induction network generalizing replacement with
  | edge =>
      change (optimalFlow (replacement [])).unitEnergy = (replacement []).resistance
      exact optimalFlow_unitEnergy (replacement [])
  | series left right ihLeft ihRight =>
      rcases outerFlow with ⟨leftFlow, rightFlow⟩
      change
        (Flow.substitute (fun word ↦ replacement (false :: word)) leftFlow
              (fun word ↦ optimalFlow (replacement (false :: word)))).unitEnergy +
            (Flow.substitute (fun word ↦ replacement (true :: word)) rightFlow
              (fun word ↦ optimalFlow (replacement (true :: word)))).unitEnergy =
          leftFlow.energy (fun word ↦ (replacement (false :: word)).resistance) +
            rightFlow.energy (fun word ↦ (replacement (true :: word)).resistance)
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      rcases outerFlow with ⟨current, leftFlow, rightFlow⟩
      change
        current ^ 2 *
              (Flow.substitute (fun word ↦ replacement (false :: word)) leftFlow
                (fun word ↦ optimalFlow (replacement (false :: word)))).unitEnergy +
            (1 - current) ^ 2 *
              (Flow.substitute (fun word ↦ replacement (true :: word)) rightFlow
                (fun word ↦ optimalFlow (replacement (true :: word)))).unitEnergy =
          current ^ 2 *
              leftFlow.energy (fun word ↦ (replacement (false :: word)).resistance) +
            (1 - current) ^ 2 *
              rightFlow.energy (fun word ↦ (replacement (true :: word)).resistance)
      rw [ihLeft, ihRight]

/-- General resistance substitution bound obtained by composing minimizing inner flows. -/
theorem resistance_substitute_le_energy {network : SPNetwork}
    (replacement : List Bool → SPNetwork) (outerFlow : Flow network) :
    (network.substitute replacement).resistance ≤
      outerFlow.energy fun word ↦ (replacement word).resistance := by
  calc
    (network.substitute replacement).resistance ≤
        (outerFlow.substitute replacement
          fun word ↦ optimalFlow (replacement word)).unitEnergy :=
      resistance_le_unitEnergy _
    _ = outerFlow.energy fun word ↦ (replacement word).resistance :=
      substitute_optimalFlow_unitEnergy replacement outerFlow

/-- The canonical outer flow gives the substitution bound used after conditioning. -/
theorem resistance_substitute_le_optimal_energy (network : SPNetwork)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).resistance ≤
      (optimalFlow network).energy fun word ↦ (replacement word).resistance :=
  resistance_substitute_le_energy replacement (optimalFlow network)

/-- Effective resistance is bounded by the boundary-to-boundary graph distance. -/
theorem resistance_le_distance (network : SPNetwork) :
    network.resistance ≤ network.distance := by
  calc
    network.resistance ≤ (Flow.ofPath network.shortestPath).unitEnergy :=
      resistance_le_unitEnergy (Flow.ofPath network.shortestPath)
    _ = network.shortestPath.length := Flow.unitEnergy_ofPath network.shortestPath
    _ = network.distance := by rw [length_shortestPath]

end SeriesParallel.MainText.SPNetwork
