/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Finite edge-indexed two-terminal multigraphs

This module defines the evaluator-independent graph object used by the traditional graph
semantics.  Physical edges are elements of a bundled finite type, so parallel-edge multiplicity
is retained even though the simple shadow used for distance forgets it.
-/

@[expose] public section

namespace SeriesParallel.MainText.GraphSemantics

/-- A finite oriented presentation of an undirected edge-indexed two-terminal multigraph. -/
structure TwoTerminalMultigraph where
  Vertex : Type
  Edge : Type
  vertexFintype' : Fintype Vertex
  vertexDecidableEq' : DecidableEq Vertex
  edgeFintype' : Fintype Edge
  edgeDecidableEq' : DecidableEq Edge
  tail : Edge → Vertex
  head : Edge → Vertex
  source : Vertex
  sink : Vertex
  source_ne_sink : source ≠ sink

namespace TwoTerminalMultigraph

instance instFintypeVertex (G : TwoTerminalMultigraph) : Fintype G.Vertex :=
  G.vertexFintype'

instance instDecidableEqVertex (G : TwoTerminalMultigraph) : DecidableEq G.Vertex :=
  G.vertexDecidableEq'

instance instFintypeEdge (G : TwoTerminalMultigraph) : Fintype G.Edge :=
  G.edgeFintype'

instance instDecidableEqEdge (G : TwoTerminalMultigraph) : DecidableEq G.Edge :=
  G.edgeDecidableEq'

/-- The number of physical edges, including parallel edges with the same endpoints. -/
def edgeCard (G : TwoTerminalMultigraph) : ℕ :=
  Fintype.card G.Edge

/-- The raw multigraph has no physical edge whose two endpoints coincide. -/
def NoLoops (G : TwoTerminalMultigraph) : Prop :=
  ∀ e : G.Edge, G.tail e ≠ G.head e

/-- Undirected adjacency induced by at least one physical edge. -/
def ShadowAdj (G : TwoTerminalMultigraph) (u v : G.Vertex) : Prop :=
  u ≠ v ∧ ∃ e : G.Edge,
    (G.tail e = u ∧ G.head e = v) ∨ (G.tail e = v ∧ G.head e = u)

theorem shadowAdj_symm (G : TwoTerminalMultigraph) :
    Std.Symm G.ShadowAdj := by
  constructor
  rintro u v ⟨hne, e, h⟩
  exact ⟨hne.symm, e, h.symm⟩

theorem shadowAdj_irrefl (G : TwoTerminalMultigraph) :
    Std.Irrefl G.ShadowAdj := by
  constructor
  intro u h
  exact h.1 rfl

/-- The simple undirected shadow used for general walks and graph distance. -/
def simpleShadow (G : TwoTerminalMultigraph) : SimpleGraph G.Vertex where
  Adj := G.ShadowAdj
  symm := G.shadowAdj_symm
  loopless := G.shadowAdj_irrefl

@[simp]
theorem simpleShadow_adj (G : TwoTerminalMultigraph) (u v : G.Vertex) :
    G.simpleShadow.Adj u v ↔ G.ShadowAdj u v :=
  Iff.rfl

/-- Every physical non-loop edge produces an edge of the simple shadow. -/
theorem tail_adj_head (G : TwoTerminalMultigraph) (hno : G.NoLoops) (e : G.Edge) :
    G.simpleShadow.Adj (G.tail e) (G.head e) := by
  exact ⟨hno e, e, Or.inl ⟨rfl, rfl⟩⟩

end TwoTerminalMultigraph

end SeriesParallel.MainText.GraphSemantics
