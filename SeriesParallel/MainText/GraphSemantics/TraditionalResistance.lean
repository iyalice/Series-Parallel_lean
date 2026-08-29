/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.GraphSemantics.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Traditional Kirchhoff--Thomson resistance

This module defines signed currents, vertex divergence, through-flows, unit-resistance energy,
and effective resistance for an arbitrary finite edge-indexed two-terminal multigraph.  The
definitions are independent of the recursive series--parallel syntax and its scalar evaluators.
-/

@[expose] public section

open scoped BigOperators

namespace SeriesParallel.MainText.GraphSemantics

namespace TwoTerminalMultigraph

/-- A signed current on the independently identified physical edges of `G`. -/
abbrev Current (G : TwoTerminalMultigraph) := G.Edge → ℝ

/-- Net outward current at a vertex, relative to the fixed orientation of every edge. -/
noncomputable def divergence (G : TwoTerminalMultigraph) (current : G.Current)
    (vertex : G.Vertex) : ℝ :=
  (∑ edge : G.Edge, if G.tail edge = vertex then current edge else 0) -
    ∑ edge : G.Edge, if G.head edge = vertex then current edge else 0

/-- The prescribed divergence of a value-`I` flow at a vertex. -/
def throughFlowDemand (G : TwoTerminalMultigraph) (I : ℝ) (vertex : G.Vertex) : ℝ :=
  if vertex = G.source then I else if vertex = G.sink then -I else 0

/-- Kirchhoff feasibility for a signed current carrying value `I` from source to sink. -/
def IsThroughFlow (G : TwoTerminalMultigraph) (I : ℝ) (current : G.Current) : Prop :=
  ∀ vertex, G.divergence current vertex = G.throughFlowDemand I vertex

/-- Thomson energy when every physical edge has unit resistance. -/
noncomputable def unitEnergy (G : TwoTerminalMultigraph) (current : G.Current) : ℝ :=
  ∑ edge : G.Edge, current edge ^ 2

/-- Energies attained by conventional unit through-flows. -/
def energySet (G : TwoTerminalMultigraph) : Set ℝ :=
  {energy | ∃ current : G.Current,
    G.IsThroughFlow 1 current ∧ G.unitEnergy current = energy}

/-- A raw graph has a physical resistance interpretation exactly when a unit flow exists. -/
def HasUnitFlow (G : TwoTerminalMultigraph) : Prop :=
  G.energySet.Nonempty

/-- Traditional effective resistance as the infimum of all unit-flow energies. -/
noncomputable def traditionalResistance (G : TwoTerminalMultigraph) : ℝ :=
  sInf G.energySet

/-- Divergence at the source of a through-flow is its value. -/
theorem IsThroughFlow.divergence_source {G : TwoTerminalMultigraph} {I : ℝ}
    {current : G.Current} (hcurrent : G.IsThroughFlow I current) :
    G.divergence current G.source = I := by
  simpa [throughFlowDemand, G.source_ne_sink] using hcurrent G.source

/-- Divergence at the sink of a through-flow is minus its value. -/
theorem IsThroughFlow.divergence_sink {G : TwoTerminalMultigraph} {I : ℝ}
    {current : G.Current} (hcurrent : G.IsThroughFlow I current) :
    G.divergence current G.sink = -I := by
  simpa [throughFlowDemand, G.source_ne_sink.symm] using hcurrent G.sink

/-- Through-flows satisfy Kirchhoff conservation at every nonterminal vertex. -/
theorem IsThroughFlow.divergence_eq_zero {G : TwoTerminalMultigraph} {I : ℝ}
    {current : G.Current} (hcurrent : G.IsThroughFlow I current) {vertex : G.Vertex}
    (hsource : vertex ≠ G.source) (hsink : vertex ≠ G.sink) :
    G.divergence current vertex = 0 := by
  simpa [throughFlowDemand, hsource, hsink] using hcurrent vertex

/-- The divergence of every signed current sums to zero over all vertices. -/
theorem sum_divergence (G : TwoTerminalMultigraph) (current : G.Current) :
    ∑ vertex : G.Vertex, G.divergence current vertex = 0 := by
  simp only [divergence, Finset.sum_sub_distrib]
  have htail :
      (∑ vertex : G.Vertex, ∑ edge : G.Edge,
        if G.tail edge = vertex then current edge else 0) = ∑ edge, current edge := by
    rw [Finset.sum_comm]
    simp
  have hhead :
      (∑ vertex : G.Vertex, ∑ edge : G.Edge,
        if G.head edge = vertex then current edge else 0) = ∑ edge, current edge := by
    rw [Finset.sum_comm]
    simp
  rw [htail, hhead, sub_self]

/-- Source divergence and interior conservation determine the missing sink equation. -/
theorem isThroughFlow_of_source_of_interior {G : TwoTerminalMultigraph} {I : ℝ}
    {current : G.Current} (hsource : G.divergence current G.source = I)
    (hinterior : ∀ vertex, vertex ≠ G.source → vertex ≠ G.sink →
      G.divergence current vertex = 0) :
    G.IsThroughFlow I current := by
  have herase :
      (∑ vertex ∈ (Finset.univ.erase G.sink), G.divergence current vertex) = I := by
    calc
      (∑ vertex ∈ (Finset.univ.erase G.sink), G.divergence current vertex) =
          ∑ vertex ∈ (Finset.univ.erase G.sink),
            if vertex = G.source then I else 0 := by
        apply Finset.sum_congr rfl
        intro vertex hvertex
        by_cases hsourceVertex : vertex = G.source
        · subst vertex
          simp [hsource]
        · have hsinkVertex : vertex ≠ G.sink := by
            simpa using (Finset.mem_erase.mp hvertex).1
          simp [hsourceVertex, hinterior vertex hsourceVertex hsinkVertex]
      _ = I := by simp [G.source_ne_sink]
  have htotal := G.sum_divergence current
  have hdecompose := Finset.sum_erase_add (Finset.univ : Finset G.Vertex)
    (G.divergence current) (Finset.mem_univ G.sink)
  rw [herase, htotal] at hdecompose
  have hsink : G.divergence current G.sink = -I :=
    eq_neg_of_add_eq_zero_right hdecompose
  intro vertex
  by_cases hsourceVertex : vertex = G.source
  · subst vertex
    simpa [throughFlowDemand, G.source_ne_sink] using hsource
  by_cases hsinkVertex : vertex = G.sink
  · subst vertex
    simpa [throughFlowDemand, G.source_ne_sink.symm] using hsink
  · simpa [throughFlowDemand, hsourceVertex, hsinkVertex] using
      hinterior vertex hsourceVertex hsinkVertex

/-- Sink divergence and interior conservation determine the missing source equation. -/
theorem isThroughFlow_of_sink_of_interior {G : TwoTerminalMultigraph} {I : ℝ}
    {current : G.Current} (hsink : G.divergence current G.sink = -I)
    (hinterior : ∀ vertex, vertex ≠ G.source → vertex ≠ G.sink →
      G.divergence current vertex = 0) :
    G.IsThroughFlow I current := by
  have herase :
      (∑ vertex ∈ (Finset.univ.erase G.source), G.divergence current vertex) = -I := by
    calc
      (∑ vertex ∈ (Finset.univ.erase G.source), G.divergence current vertex) =
          ∑ vertex ∈ (Finset.univ.erase G.source),
            if vertex = G.sink then -I else 0 := by
        apply Finset.sum_congr rfl
        intro vertex hvertex
        by_cases hsinkVertex : vertex = G.sink
        · subst vertex
          simp [hsink]
        · have hsourceVertex : vertex ≠ G.source := by
            simpa using (Finset.mem_erase.mp hvertex).1
          simp [hsinkVertex, hinterior vertex hsourceVertex hsinkVertex]
      _ = -I := by simp [G.source_ne_sink.symm]
  have htotal := G.sum_divergence current
  have hdecompose := Finset.sum_erase_add (Finset.univ : Finset G.Vertex)
    (G.divergence current) (Finset.mem_univ G.source)
  rw [herase, htotal] at hdecompose
  have hsource : G.divergence current G.source = I := by
    have := eq_neg_of_add_eq_zero_right hdecompose
    simpa using this
  intro vertex
  by_cases hsourceVertex : vertex = G.source
  · subst vertex
    simpa [throughFlowDemand, G.source_ne_sink] using hsource
  by_cases hsinkVertex : vertex = G.sink
  · subst vertex
    simpa [throughFlowDemand, G.source_ne_sink.symm] using hsink
  · simpa [throughFlowDemand, hsourceVertex, hsinkVertex] using
      hinterior vertex hsourceVertex hsinkVertex

/-- The identically zero current is a conventional zero through-flow. -/
theorem zero_isThroughFlow (G : TwoTerminalMultigraph) :
    G.IsThroughFlow 0 (fun _ ↦ 0) := by
  intro vertex
  simp [divergence, throughFlowDemand]

/-- Unit energy is nonnegative for every signed current, including circulations. -/
theorem unitEnergy_nonneg (G : TwoTerminalMultigraph) (current : G.Current) :
    0 ≤ G.unitEnergy current := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The set of feasible unit-flow energies is bounded below by zero. -/
theorem energySet_bddBelow (G : TwoTerminalMultigraph) : BddBelow G.energySet := by
  refine ⟨0, ?_⟩
  rintro energy ⟨current, _, rfl⟩
  exact G.unitEnergy_nonneg current

/-- The energy of any conventional unit flow belongs to the Thomson feasible set. -/
theorem unitEnergy_mem_energySet {G : TwoTerminalMultigraph} {current : G.Current}
    (hcurrent : G.IsThroughFlow 1 current) :
    G.unitEnergy current ∈ G.energySet :=
  ⟨current, hcurrent, rfl⟩

end TwoTerminalMultigraph

end SeriesParallel.MainText.GraphSemantics
