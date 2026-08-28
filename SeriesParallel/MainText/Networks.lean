/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Finite two-terminal series--parallel networks

This module gives the recursive network syntax used by the main-text model.  Every leaf is a
unit-resistance edge.  The two numerical semantics are boundary-to-boundary graph distance and
effective resistance.

## Main results

- `SPNetwork.distance`: graph distance of a finite series--parallel network.
- `SPNetwork.resistance`: effective resistance with unit-resistance leaves.
- `SPNetwork.resistance_dual`: exchanging series and parallel inverts resistance.
- `SPNetwork.distance_bounds` and `SPNetwork.resistance_bounds`: deterministic finite bounds.
-/

@[expose] public section

namespace SeriesParallel.MainText

/-- A finite two-terminal network generated from one edge by series and parallel composition. -/
inductive SPNetwork where
  | edge : SPNetwork
  | series : SPNetwork → SPNetwork → SPNetwork
  | parallel : SPNetwork → SPNetwork → SPNetwork
  deriving DecidableEq, Repr

namespace SPNetwork

/-- The number of unit edges in a finite series--parallel network. -/
def edgeCount : SPNetwork → ℕ
  | edge => 1
  | series left right => left.edgeCount + right.edgeCount
  | parallel left right => left.edgeCount + right.edgeCount

/-- Boundary-to-boundary graph distance. -/
def distance : SPNetwork → ℕ
  | edge => 1
  | series left right => left.distance + right.distance
  | parallel left right => min left.distance right.distance

/-- Effective resistance when every leaf has resistance one. -/
noncomputable def resistance : SPNetwork → ℝ
  | edge => 1
  | series left right => left.resistance + right.resistance
  | parallel left right =>
      left.resistance * right.resistance / (left.resistance + right.resistance)

/-- The planar two-terminal dual, which exchanges series and parallel gates. -/
def dual : SPNetwork → SPNetwork
  | edge => edge
  | series left right => parallel left.dual right.dual
  | parallel left right => series left.dual right.dual

/-- Replace each leaf by a network selected by its left/right address. -/
def substitute : SPNetwork → (List Bool → SPNetwork) → SPNetwork
  | edge, replacement => replacement []
  | series left right, replacement =>
      series (left.substitute fun word ↦ replacement (false :: word))
        (right.substitute fun word ↦ replacement (true :: word))
  | parallel left right, replacement =>
      parallel (left.substitute fun word ↦ replacement (false :: word))
        (right.substitute fun word ↦ replacement (true :: word))

/-- Replace every leaf of `network` by the same two-terminal network. -/
def substituteConst (network replacement : SPNetwork) : SPNetwork :=
  network.substitute fun _ ↦ replacement

@[simp]
theorem edgeCount_edge : edge.edgeCount = 1 := rfl

@[simp]
theorem edgeCount_series (left right : SPNetwork) :
    (series left right).edgeCount = left.edgeCount + right.edgeCount := rfl

@[simp]
theorem edgeCount_parallel (left right : SPNetwork) :
    (parallel left right).edgeCount = left.edgeCount + right.edgeCount := rfl

@[simp]
theorem distance_edge : edge.distance = 1 := rfl

@[simp]
theorem distance_series (left right : SPNetwork) :
    (series left right).distance = left.distance + right.distance := rfl

@[simp]
theorem distance_parallel (left right : SPNetwork) :
    (parallel left right).distance = min left.distance right.distance := rfl

@[simp]
theorem resistance_edge : edge.resistance = 1 := rfl

@[simp]
theorem resistance_series (left right : SPNetwork) :
    (series left right).resistance = left.resistance + right.resistance := rfl

@[simp]
theorem resistance_parallel (left right : SPNetwork) :
    (parallel left right).resistance =
      left.resistance * right.resistance / (left.resistance + right.resistance) := rfl

@[simp]
theorem dual_edge : edge.dual = edge := rfl

@[simp]
theorem dual_series (left right : SPNetwork) :
    (series left right).dual = parallel left.dual right.dual := rfl

@[simp]
theorem dual_parallel (left right : SPNetwork) :
    (parallel left right).dual = series left.dual right.dual := rfl

@[simp]
theorem substitute_edge (replacement : List Bool → SPNetwork) :
    edge.substitute replacement = replacement [] := rfl

@[simp]
theorem substitute_series (left right : SPNetwork) (replacement : List Bool → SPNetwork) :
    (series left right).substitute replacement =
      series (left.substitute fun word ↦ replacement (false :: word))
        (right.substitute fun word ↦ replacement (true :: word)) := rfl

@[simp]
theorem substitute_parallel (left right : SPNetwork) (replacement : List Bool → SPNetwork) :
    (parallel left right).substitute replacement =
      parallel (left.substitute fun word ↦ replacement (false :: word))
        (right.substitute fun word ↦ replacement (true :: word)) := rfl

@[simp]
theorem dual_dual (network : SPNetwork) : network.dual.dual = network := by
  induction network with
  | edge => rfl
  | series left right ihLeft ihRight => simp [ihLeft, ihRight]
  | parallel left right ihLeft ihRight => simp [ihLeft, ihRight]

/-- Duality commutes with arbitrary leaf substitution. -/
theorem dual_substitute (network : SPNetwork) (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).dual =
      network.dual.substitute (fun word ↦ (replacement word).dual) := by
  induction network generalizing replacement with
  | edge => rfl
  | series left right ihLeft ihRight =>
      simp only [substitute_series, dual_series, substitute_parallel]
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      simp only [substitute_parallel, dual_parallel, substitute_series]
      rw [ihLeft, ihRight]

@[simp]
theorem distance_substituteConst (network replacement : SPNetwork) :
    (network.substituteConst replacement).distance =
      network.distance * replacement.distance := by
  induction network with
  | edge => simp [substituteConst]
  | series left right ihLeft ihRight =>
      change (left.substituteConst replacement).distance +
        (right.substituteConst replacement).distance = _
      rw [ihLeft, ihRight]
      simp [distance, Nat.add_mul]
  | parallel left right ihLeft ihRight =>
      change min (left.substituteConst replacement).distance
        (right.substituteConst replacement).distance = _
      rw [ihLeft, ihRight, Nat.mul_min_mul_right]
      rfl

theorem edgeCount_pos (network : SPNetwork) : 0 < network.edgeCount := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight => simp [edgeCount, ihLeft, ihRight]
  | parallel left right ihLeft ihRight => simp [edgeCount, ihLeft, ihRight]

theorem distance_pos (network : SPNetwork) : 0 < network.distance := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight => simp [distance, ihLeft, ihRight]
  | parallel left right ihLeft ihRight => simpa [distance] using lt_min ihLeft ihRight

theorem resistance_pos (network : SPNetwork) : 0 < network.resistance := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight => simpa [resistance] using add_pos ihLeft ihRight
  | parallel left right ihLeft ihRight =>
      exact div_pos (mul_pos ihLeft ihRight) (add_pos ihLeft ihRight)

theorem resistance_ne_zero (network : SPNetwork) : network.resistance ≠ 0 :=
  network.resistance_pos.ne'

@[simp]
theorem resistance_substituteConst (network replacement : SPNetwork) :
    (network.substituteConst replacement).resistance =
      network.resistance * replacement.resistance := by
  induction network with
  | edge => simp [substituteConst]
  | series left right ihLeft ihRight =>
      change (left.substituteConst replacement).resistance +
        (right.substituteConst replacement).resistance = _
      rw [ihLeft, ihRight]
      simp [resistance, add_mul]
  | parallel left right ihLeft ihRight =>
      change (left.substituteConst replacement).resistance *
          (right.substituteConst replacement).resistance /
          ((left.substituteConst replacement).resistance +
            (right.substituteConst replacement).resistance) =
        left.resistance * right.resistance /
            (left.resistance + right.resistance) * replacement.resistance
      rw [ihLeft, ihRight]
      have hleft := left.resistance_pos
      have hright := right.resistance_pos
      have hreplacement := replacement.resistance_pos
      field_simp [left.resistance_ne_zero, right.resistance_ne_zero,
        replacement.resistance_ne_zero, ne_of_gt (add_pos hleft hright),
        ne_of_gt (add_pos (mul_pos hleft hreplacement) (mul_pos hright hreplacement))]

/-- Graph distance lies between one and the number of edges. -/
theorem distance_bounds (network : SPNetwork) :
    1 ≤ network.distance ∧ network.distance ≤ network.edgeCount := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight =>
      constructor
      · exact le_trans ihLeft.1 (Nat.le_add_right _ _)
      · simpa [distance, edgeCount] using Nat.add_le_add ihLeft.2 ihRight.2
  | parallel left right ihLeft ihRight =>
      constructor
      · simpa [distance] using le_min ihLeft.1 ihRight.1
      · exact le_trans (min_le_left _ _) <| le_trans ihLeft.2 (Nat.le_add_right _ _)

/-- Effective resistance is at most the number of unit edges. -/
theorem resistance_le_edgeCount (network : SPNetwork) :
    network.resistance ≤ network.edgeCount := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight =>
      exact_mod_cast add_le_add ihLeft ihRight
  | parallel left right ihLeft ihRight =>
      have hleft := left.resistance_pos
      have hright := right.resistance_pos
      calc
        left.resistance * right.resistance / (left.resistance + right.resistance)
            ≤ left.resistance := by
              rw [div_le_iff₀ (add_pos hleft hright)]
              nlinarith
        _ ≤ left.edgeCount := ihLeft
        _ ≤ left.edgeCount + right.edgeCount := by
          exact_mod_cast Nat.le_add_right left.edgeCount right.edgeCount
        _ = (parallel left right).edgeCount := by simp

/-- Exchanging every series and parallel gate takes effective resistance to its reciprocal. -/
theorem resistance_dual (network : SPNetwork) :
    network.dual.resistance = network.resistance⁻¹ := by
  induction network with
  | edge => simp
  | series left right ihLeft ihRight =>
      rw [dual_series, resistance_parallel, ihLeft, ihRight]
      field_simp [left.resistance_ne_zero, right.resistance_ne_zero,
        ne_of_gt (add_pos left.resistance_pos right.resistance_pos),
        ne_of_gt (add_pos right.resistance_pos left.resistance_pos)];
        simp [resistance, add_comm]
  | parallel left right ihLeft ihRight =>
      rw [dual_parallel, resistance_series, ihLeft, ihRight, resistance_parallel]
      field_simp [left.resistance_ne_zero, right.resistance_ne_zero,
        ne_of_gt (add_pos left.resistance_pos right.resistance_pos)]; ring

/-- Combined deterministic bounds for finite unit-resistance networks. -/
theorem resistance_bounds (network : SPNetwork) :
    0 < network.resistance ∧ network.resistance ≤ network.edgeCount :=
  ⟨network.resistance_pos, network.resistance_le_edgeCount⟩

end SPNetwork

end SeriesParallel.MainText
