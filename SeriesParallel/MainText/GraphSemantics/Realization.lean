/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.GraphSemantics.Basic
public import SeriesParallel.MainText.Networks

/-!
# Structural realization of series--parallel syntax

The realization below only inspects the constructors of `SPNetwork`.  Its tagged internal vertices
avoid quotients, while sum-typed physical edges retain parallel multiplicity.
-/

@[expose] public section

namespace SeriesParallel.MainText

namespace SPNetwork

/-- The two external terminal tags. -/
inductive Boundary where
  | source
  | sink
  deriving DecidableEq, Fintype, Repr

/-- Physical leaf-edge identities.  Sums preserve identity in both composite constructors. -/
def PhysicalEdge : SPNetwork → Type
  | .edge => PUnit
  | .series left right => left.PhysicalEdge ⊕ right.PhysicalEdge
  | .parallel left right => left.PhysicalEdge ⊕ right.PhysicalEdge

/-- Internal vertices, with one fresh joining vertex at every series gate. -/
def InternalVertex : SPNetwork → Type
  | .edge => Empty
  | .series left right => PUnit ⊕ (left.InternalVertex ⊕ right.InternalVertex)
  | .parallel left right => left.InternalVertex ⊕ right.InternalVertex

/-- Vertices of the realized graph: two external tags plus all recursively tagged internals. -/
abbrev RealizedVertex (network : SPNetwork) : Type :=
  Boundary ⊕ network.InternalVertex

instance instFintypePhysicalEdge : (network : SPNetwork) → Fintype network.PhysicalEdge
  | .edge => inferInstanceAs (Fintype PUnit)
  | .series left right | .parallel left right =>
      letI := instFintypePhysicalEdge left
      letI := instFintypePhysicalEdge right
      inferInstanceAs (Fintype (left.PhysicalEdge ⊕ right.PhysicalEdge))

instance instDecidableEqPhysicalEdge :
    (network : SPNetwork) → DecidableEq network.PhysicalEdge
  | .edge => inferInstanceAs (DecidableEq PUnit)
  | .series left right | .parallel left right =>
      letI := instDecidableEqPhysicalEdge left
      letI := instDecidableEqPhysicalEdge right
      inferInstanceAs (DecidableEq (left.PhysicalEdge ⊕ right.PhysicalEdge))

instance instFintypeInternalVertex : (network : SPNetwork) → Fintype network.InternalVertex
  | .edge => inferInstanceAs (Fintype Empty)
  | .series left right =>
      letI := instFintypeInternalVertex left
      letI := instFintypeInternalVertex right
      inferInstanceAs
        (Fintype (PUnit ⊕ (left.InternalVertex ⊕ right.InternalVertex)))
  | .parallel left right =>
      letI := instFintypeInternalVertex left
      letI := instFintypeInternalVertex right
      inferInstanceAs (Fintype (left.InternalVertex ⊕ right.InternalVertex))

instance instDecidableEqInternalVertex :
    (network : SPNetwork) → DecidableEq network.InternalVertex
  | .edge => inferInstanceAs (DecidableEq Empty)
  | .series left right =>
      letI := instDecidableEqInternalVertex left
      letI := instDecidableEqInternalVertex right
      inferInstanceAs
        (DecidableEq (PUnit ⊕ (left.InternalVertex ⊕ right.InternalVertex)))
  | .parallel left right =>
      letI := instDecidableEqInternalVertex left
      letI := instDecidableEqInternalVertex right
      inferInstanceAs (DecidableEq (left.InternalVertex ⊕ right.InternalVertex))

instance instFintypeRealizedVertex (network : SPNetwork) : Fintype network.RealizedVertex := by
  letI := instFintypeInternalVertex network
  exact inferInstanceAs (Fintype (Boundary ⊕ network.InternalVertex))

instance instDecidableEqRealizedVertex (network : SPNetwork) :
    DecidableEq network.RealizedVertex := by
  letI := instDecidableEqInternalVertex network
  exact inferInstanceAs (DecidableEq (Boundary ⊕ network.InternalVertex))

/-- The external source in every realization. -/
def realizedSource (network : SPNetwork) : network.RealizedVertex :=
  Sum.inl .source

/-- The external sink in every realization. -/
def realizedSink (network : SPNetwork) : network.RealizedVertex :=
  Sum.inl .sink

/-- The fresh joining vertex of a series composition. -/
def seriesJoin (left right : SPNetwork) : (series left right).RealizedVertex :=
  Sum.inr (Sum.inl PUnit.unit)

/-- Embed the left child's vertices into a series composition. -/
def seriesLeftVertex {left right : SPNetwork} :
    left.RealizedVertex → (series left right).RealizedVertex
  | Sum.inl .source => (series left right).realizedSource
  | Sum.inl .sink => seriesJoin left right
  | Sum.inr v => Sum.inr (Sum.inr (Sum.inl v))

/-- Embed the right child's vertices into a series composition. -/
def seriesRightVertex {left right : SPNetwork} :
    right.RealizedVertex → (series left right).RealizedVertex
  | Sum.inl .source => seriesJoin left right
  | Sum.inl .sink => (series left right).realizedSink
  | Sum.inr v => Sum.inr (Sum.inr (Sum.inr v))

/-- Embed the left child's vertices into a parallel composition. -/
def parallelLeftVertex {left right : SPNetwork} :
    left.RealizedVertex → (parallel left right).RealizedVertex
  | Sum.inl .source => (parallel left right).realizedSource
  | Sum.inl .sink => (parallel left right).realizedSink
  | Sum.inr v => Sum.inr (Sum.inl v)

/-- Embed the right child's vertices into a parallel composition. -/
def parallelRightVertex {left right : SPNetwork} :
    right.RealizedVertex → (parallel left right).RealizedVertex
  | Sum.inl .source => (parallel left right).realizedSource
  | Sum.inl .sink => (parallel left right).realizedSink
  | Sum.inr v => Sum.inr (Sum.inr v)

/-- A left inverse to the left-child embedding at a series gate. -/
def seriesLeftRetract {left right : SPNetwork} :
    (series left right).RealizedVertex → left.RealizedVertex
  | Sum.inl .source => left.realizedSource
  | Sum.inl .sink => left.realizedSource
  | Sum.inr (Sum.inl _) => left.realizedSink
  | Sum.inr (Sum.inr (Sum.inl v)) => Sum.inr v
  | Sum.inr (Sum.inr (Sum.inr _)) => left.realizedSource

/-- A left inverse to the right-child embedding at a series gate. -/
def seriesRightRetract {left right : SPNetwork} :
    (series left right).RealizedVertex → right.RealizedVertex
  | Sum.inl .source => right.realizedSource
  | Sum.inl .sink => right.realizedSink
  | Sum.inr (Sum.inl _) => right.realizedSource
  | Sum.inr (Sum.inr (Sum.inl _)) => right.realizedSource
  | Sum.inr (Sum.inr (Sum.inr v)) => Sum.inr v

/-- A left inverse to the left-child embedding at a parallel gate. -/
def parallelLeftRetract {left right : SPNetwork} :
    (parallel left right).RealizedVertex → left.RealizedVertex
  | Sum.inl boundary => Sum.inl boundary
  | Sum.inr (Sum.inl v) => Sum.inr v
  | Sum.inr (Sum.inr _) => left.realizedSource

/-- A left inverse to the right-child embedding at a parallel gate. -/
def parallelRightRetract {left right : SPNetwork} :
    (parallel left right).RealizedVertex → right.RealizedVertex
  | Sum.inl boundary => Sum.inl boundary
  | Sum.inr (Sum.inl _) => right.realizedSource
  | Sum.inr (Sum.inr v) => Sum.inr v

theorem seriesLeftVertex_injective (left right : SPNetwork) :
    Function.Injective (@seriesLeftVertex left right) := by
  apply Function.LeftInverse.injective (g := @seriesLeftRetract left right)
  rintro (boundary | internal)
  · cases boundary <;> rfl
  · rfl

theorem seriesRightVertex_injective (left right : SPNetwork) :
    Function.Injective (@seriesRightVertex left right) := by
  apply Function.LeftInverse.injective (g := @seriesRightRetract left right)
  rintro (boundary | internal)
  · cases boundary <;> rfl
  · rfl

theorem parallelLeftVertex_injective (left right : SPNetwork) :
    Function.Injective (@parallelLeftVertex left right) := by
  apply Function.LeftInverse.injective (g := @parallelLeftRetract left right)
  rintro (boundary | internal)
  · cases boundary <;> rfl
  · rfl

theorem parallelRightVertex_injective (left right : SPNetwork) :
    Function.Injective (@parallelRightVertex left right) := by
  apply Function.LeftInverse.injective (g := @parallelRightRetract left right)
  rintro (boundary | internal)
  · cases boundary <;> rfl
  · rfl

@[simp]
theorem seriesLeftVertex_eq_source (left right : SPNetwork) (v : left.RealizedVertex) :
    @seriesLeftVertex left right v = (series left right).realizedSource ↔
      v = left.realizedSource := by
  constructor
  · intro h
    apply seriesLeftVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem seriesLeftVertex_eq_join (left right : SPNetwork) (v : left.RealizedVertex) :
    @seriesLeftVertex left right v = seriesJoin left right ↔ v = left.realizedSink := by
  constructor
  · intro h
    apply seriesLeftVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem seriesRightVertex_eq_join (left right : SPNetwork) (v : right.RealizedVertex) :
    @seriesRightVertex left right v = seriesJoin left right ↔ v = right.realizedSource := by
  constructor
  · intro h
    apply seriesRightVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem seriesRightVertex_eq_sink (left right : SPNetwork) (v : right.RealizedVertex) :
    @seriesRightVertex left right v = (series left right).realizedSink ↔
      v = right.realizedSink := by
  constructor
  · intro h
    apply seriesRightVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem parallelLeftVertex_eq_source (left right : SPNetwork) (v : left.RealizedVertex) :
    @parallelLeftVertex left right v = (parallel left right).realizedSource ↔
      v = left.realizedSource := by
  constructor
  · intro h
    apply parallelLeftVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem parallelLeftVertex_eq_sink (left right : SPNetwork) (v : left.RealizedVertex) :
    @parallelLeftVertex left right v = (parallel left right).realizedSink ↔
      v = left.realizedSink := by
  constructor
  · intro h
    apply parallelLeftVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem parallelRightVertex_eq_source (left right : SPNetwork) (v : right.RealizedVertex) :
    @parallelRightVertex left right v = (parallel left right).realizedSource ↔
      v = right.realizedSource := by
  constructor
  · intro h
    apply parallelRightVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem parallelRightVertex_eq_sink (left right : SPNetwork) (v : right.RealizedVertex) :
    @parallelRightVertex left right v = (parallel left right).realizedSink ↔
      v = right.realizedSink := by
  constructor
  · intro h
    apply parallelRightVertex_injective left right
    exact h.trans rfl
  · rintro rfl
    rfl

@[simp]
theorem seriesLeftVertex_ne_sink (left right : SPNetwork) (v : left.RealizedVertex) :
    @seriesLeftVertex left right v ≠ (series left right).realizedSink := by
  intro h
  rcases v with boundary | internal
  · cases boundary with
    | source =>
        change Sum.inl Boundary.source = Sum.inl Boundary.sink at h
        exact Boundary.noConfusion (Sum.inl.inj h)
    | sink =>
        change Sum.inr (Sum.inl PUnit.unit) = Sum.inl Boundary.sink at h
        cases h
  · change Sum.inr (Sum.inr (Sum.inl internal)) = Sum.inl Boundary.sink at h
    cases h

@[simp]
theorem seriesRightVertex_ne_source (left right : SPNetwork) (v : right.RealizedVertex) :
    @seriesRightVertex left right v ≠ (series left right).realizedSource := by
  intro h
  rcases v with boundary | internal
  · cases boundary with
    | source =>
        change Sum.inr (Sum.inl PUnit.unit) = Sum.inl Boundary.source at h
        cases h
    | sink =>
        change Sum.inl Boundary.sink = Sum.inl Boundary.source at h
        exact Boundary.noConfusion (Sum.inl.inj h)
  · change Sum.inr (Sum.inr (Sum.inr internal)) = Sum.inl Boundary.source at h
    cases h

/-- Fixed recursive orientation: every physical edge points from source toward sink. -/
def realizedTail : (network : SPNetwork) → network.PhysicalEdge → network.RealizedVertex
  | .edge, _ => edge.realizedSource
  | .series left _, Sum.inl e => seriesLeftVertex (left.realizedTail e)
  | .series _ right, Sum.inr e => seriesRightVertex (right.realizedTail e)
  | .parallel left _, Sum.inl e => parallelLeftVertex (left.realizedTail e)
  | .parallel _ right, Sum.inr e => parallelRightVertex (right.realizedTail e)

/-- Head endpoint for the fixed recursive orientation. -/
def realizedHead : (network : SPNetwork) → network.PhysicalEdge → network.RealizedVertex
  | .edge, _ => edge.realizedSink
  | .series left _, Sum.inl e => seriesLeftVertex (left.realizedHead e)
  | .series _ right, Sum.inr e => seriesRightVertex (right.realizedHead e)
  | .parallel left _, Sum.inl e => parallelLeftVertex (left.realizedHead e)
  | .parallel _ right, Sum.inr e => parallelRightVertex (right.realizedHead e)

@[simp]
theorem seriesLeftVertex_source (left right : SPNetwork) :
    @seriesLeftVertex left right left.realizedSource = (series left right).realizedSource :=
  rfl

@[simp]
theorem seriesLeftVertex_sink (left right : SPNetwork) :
    @seriesLeftVertex left right left.realizedSink = seriesJoin left right :=
  rfl

@[simp]
theorem seriesRightVertex_source (left right : SPNetwork) :
    @seriesRightVertex left right right.realizedSource = seriesJoin left right :=
  rfl

@[simp]
theorem seriesRightVertex_sink (left right : SPNetwork) :
    @seriesRightVertex left right right.realizedSink = (series left right).realizedSink :=
  rfl

@[simp]
theorem parallelLeftVertex_source (left right : SPNetwork) :
    @parallelLeftVertex left right left.realizedSource = (parallel left right).realizedSource :=
  rfl

@[simp]
theorem parallelLeftVertex_sink (left right : SPNetwork) :
    @parallelLeftVertex left right left.realizedSink = (parallel left right).realizedSink :=
  rfl

@[simp]
theorem parallelRightVertex_source (left right : SPNetwork) :
    @parallelRightVertex left right right.realizedSource = (parallel left right).realizedSource :=
  rfl

@[simp]
theorem parallelRightVertex_sink (left right : SPNetwork) :
    @parallelRightVertex left right right.realizedSink = (parallel left right).realizedSink :=
  rfl

@[simp]
theorem realizedTail_series_left (left right : SPNetwork) (e : left.PhysicalEdge) :
    (series left right).realizedTail (Sum.inl e) =
      seriesLeftVertex (left.realizedTail e) :=
  rfl

@[simp]
theorem realizedTail_series_right (left right : SPNetwork) (e : right.PhysicalEdge) :
    (series left right).realizedTail (Sum.inr e) =
      seriesRightVertex (right.realizedTail e) :=
  rfl

@[simp]
theorem realizedHead_series_left (left right : SPNetwork) (e : left.PhysicalEdge) :
    (series left right).realizedHead (Sum.inl e) =
      seriesLeftVertex (left.realizedHead e) :=
  rfl

@[simp]
theorem realizedHead_series_right (left right : SPNetwork) (e : right.PhysicalEdge) :
    (series left right).realizedHead (Sum.inr e) =
      seriesRightVertex (right.realizedHead e) :=
  rfl

@[simp]
theorem realizedTail_parallel_left (left right : SPNetwork) (e : left.PhysicalEdge) :
    (parallel left right).realizedTail (Sum.inl e) =
      parallelLeftVertex (left.realizedTail e) :=
  rfl

@[simp]
theorem realizedTail_parallel_right (left right : SPNetwork) (e : right.PhysicalEdge) :
    (parallel left right).realizedTail (Sum.inr e) =
      parallelRightVertex (right.realizedTail e) :=
  rfl

@[simp]
theorem realizedHead_parallel_left (left right : SPNetwork) (e : left.PhysicalEdge) :
    (parallel left right).realizedHead (Sum.inl e) =
      parallelLeftVertex (left.realizedHead e) :=
  rfl

@[simp]
theorem realizedHead_parallel_right (left right : SPNetwork) (e : right.PhysicalEdge) :
    (parallel left right).realizedHead (Sum.inr e) =
      parallelRightVertex (right.realizedHead e) :=
  rfl

/-- Structural finite multigraph realization of a series--parallel network. -/
abbrev realize (network : SPNetwork) : GraphSemantics.TwoTerminalMultigraph where
  Vertex := network.RealizedVertex
  Edge := network.PhysicalEdge
  vertexFintype' := instFintypeRealizedVertex network
  vertexDecidableEq' := instDecidableEqRealizedVertex network
  edgeFintype' := instFintypePhysicalEdge network
  edgeDecidableEq' := instDecidableEqPhysicalEdge network
  tail := network.realizedTail
  head := network.realizedHead
  source := network.realizedSource
  sink := network.realizedSink
  source_ne_sink := by
    intro h
    exact Boundary.noConfusion (Sum.inl.inj h)

@[simp]
theorem realize_Vertex (network : SPNetwork) : network.realize.Vertex = network.RealizedVertex :=
  rfl

@[simp]
theorem realize_Edge (network : SPNetwork) : network.realize.Edge = network.PhysicalEdge :=
  rfl

@[simp]
theorem realize_source (network : SPNetwork) : network.realize.source = network.realizedSource :=
  rfl

@[simp]
theorem realize_sink (network : SPNetwork) : network.realize.sink = network.realizedSink :=
  rfl

@[simp]
theorem realize_tail (network : SPNetwork) (e : network.PhysicalEdge) :
    network.realize.tail e = network.realizedTail e :=
  rfl

@[simp]
theorem realize_head (network : SPNetwork) (e : network.PhysicalEdge) :
    network.realize.head e = network.realizedHead e :=
  rfl

/-- Every structurally realized physical edge has distinct endpoints. -/
theorem realize_noLoops (network : SPNetwork) : network.realize.NoLoops := by
  induction network with
  | edge =>
      intro e
      cases e
      intro h
      exact Boundary.noConfusion (Sum.inl.inj h)
  | series left right ihLeft ihRight =>
      intro e
      rcases e with e | e
      · intro h
        exact ihLeft e (seriesLeftVertex_injective left right h)
      · intro h
        exact ihRight e (seriesRightVertex_injective left right h)
  | parallel left right ihLeft ihRight =>
      intro e
      rcases e with e | e
      · intro h
        exact ihLeft e (parallelLeftVertex_injective left right h)
      · intro h
        exact ihRight e (parallelRightVertex_injective left right h)

/-- Physical-edge cardinality agrees with the syntax-tree leaf count. -/
theorem realize_edgeCard (network : SPNetwork) :
    network.realize.edgeCard = network.edgeCount := by
  induction network with
  | edge => simp [GraphSemantics.TwoTerminalMultigraph.edgeCard, realize, PhysicalEdge]
  | series left right ihLeft ihRight =>
      change Fintype.card left.PhysicalEdge = left.edgeCount at ihLeft
      change Fintype.card right.PhysicalEdge = right.edgeCount at ihRight
      change Fintype.card (left.PhysicalEdge ⊕ right.PhysicalEdge) =
        left.edgeCount + right.edgeCount
      rw [Fintype.card_sum, ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      change Fintype.card left.PhysicalEdge = left.edgeCount at ihLeft
      change Fintype.card right.PhysicalEdge = right.edgeCount at ihRight
      change Fintype.card (left.PhysicalEdge ⊕ right.PhysicalEdge) =
        left.edgeCount + right.edgeCount
      rw [Fintype.card_sum, ihLeft, ihRight]

/-- A unit network has one physical edge. -/
theorem realize_one_edgeCard : edge.realize.edgeCard = 1 := by
  rw [realize_edgeCard]
  rfl

/-- Two unit edges in series have two distinct physical identities. -/
theorem realize_twoSeries_edgeCard : (series edge edge).realize.edgeCard = 2 := by
  rw [realize_edgeCard]
  rfl

/-- Two unit branches in parallel remain two distinct physical edges. -/
theorem realize_twoParallel_edgeCard : (parallel edge edge).realize.edgeCard = 2 := by
  rw [realize_edgeCard]
  rfl

/-- The two unit branches in the parallel regression are distinct physical edge values. -/
theorem twoParallel_physicalEdges_distinct :
    (Sum.inl PUnit.unit : (parallel edge edge).PhysicalEdge) ≠ Sum.inr PUnit.unit := by
  decide

end SPNetwork

end SeriesParallel.MainText
