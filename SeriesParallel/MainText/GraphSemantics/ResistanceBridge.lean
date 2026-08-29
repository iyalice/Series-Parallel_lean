/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.FiniteFlows
public import SeriesParallel.MainText.GraphSemantics.Realization
public import SeriesParallel.MainText.GraphSemantics.TraditionalResistance

/-!
# Resistance bridge for structural series--parallel realizations

This bridge maps recursive normalized flows to conventional signed edge currents and proves the
generalized Thomson lower bound for every conventional through-current, including currents with
circulation.  The traditional definitions remain in the evaluator-independent module below.
-/

@[expose] public section

open scoped BigOperators

namespace SeriesParallel.MainText

namespace SPNetwork

open GraphSemantics

private theorem sum_sum_type {α β : Type} [Fintype α] [Fintype β]
    (summand : α ⊕ β → ℝ) :
    (∑ index : α ⊕ β, summand index) =
      (∑ index : α, summand (Sum.inl index)) +
        ∑ index : β, summand (Sum.inr index) := by
  classical
  change (Finset.univ.sum summand) = _
  rw [← Finset.univ_disjSum_univ, Finset.sum_disjSum]

@[simp]
private theorem seriesRightVertex_ne_leftInternal (left right : SPNetwork)
    (rightVertex : right.RealizedVertex) (leftInternal : left.InternalVertex) :
    @seriesRightVertex left right rightVertex ≠
      seriesLeftVertex (Sum.inr leftInternal) := by
  rcases rightVertex with boundary | internal
  · cases boundary <;> simp [seriesRightVertex, seriesLeftVertex, seriesJoin,
      realizedSink]
  · intro h
    change Sum.inr (Sum.inr (Sum.inr internal)) =
      Sum.inr (Sum.inr (Sum.inl leftInternal)) at h
    simp at h

@[simp]
private theorem seriesLeftVertex_ne_rightInternal (left right : SPNetwork)
    (leftVertex : left.RealizedVertex) (rightInternal : right.InternalVertex) :
    @seriesLeftVertex left right leftVertex ≠
      seriesRightVertex (Sum.inr rightInternal) := by
  rcases leftVertex with boundary | internal
  · cases boundary <;> simp [seriesRightVertex, seriesLeftVertex, seriesJoin,
      realizedSource]
  · intro h
    change Sum.inr (Sum.inr (Sum.inl internal)) =
      Sum.inr (Sum.inr (Sum.inr rightInternal)) at h
    simp at h

@[simp]
private theorem parallelRightVertex_ne_leftInternal (left right : SPNetwork)
    (rightVertex : right.RealizedVertex) (leftInternal : left.InternalVertex) :
    @parallelRightVertex left right rightVertex ≠
      parallelLeftVertex (Sum.inr leftInternal) := by
  rcases rightVertex with boundary | internal
  · cases boundary <;> simp [parallelRightVertex, parallelLeftVertex,
      realizedSource, realizedSink]
  · simp [parallelRightVertex, parallelLeftVertex]

@[simp]
private theorem parallelLeftVertex_ne_rightInternal (left right : SPNetwork)
    (leftVertex : left.RealizedVertex) (rightInternal : right.InternalVertex) :
    @parallelLeftVertex left right leftVertex ≠
      parallelRightVertex (Sum.inr rightInternal) := by
  rcases leftVertex with boundary | internal
  · cases boundary <;> simp [parallelRightVertex, parallelLeftVertex,
      realizedSource, realizedSink]
  · simp [parallelRightVertex, parallelLeftVertex]

/-- Restrict a current on a series composition to its left physical-edge summand. -/
def seriesLeftCurrent {left right : SPNetwork}
    (current : (series left right).realize.Current) : left.realize.Current :=
  fun edge ↦ current (Sum.inl edge)

/-- Restrict a current on a series composition to its right physical-edge summand. -/
def seriesRightCurrent {left right : SPNetwork}
    (current : (series left right).realize.Current) : right.realize.Current :=
  fun edge ↦ current (Sum.inr edge)

/-- Restrict a current on a parallel composition to its left physical-edge summand. -/
def parallelLeftCurrent {left right : SPNetwork}
    (current : (parallel left right).realize.Current) : left.realize.Current :=
  fun edge ↦ current (Sum.inl edge)

/-- Restrict a current on a parallel composition to its right physical-edge summand. -/
def parallelRightCurrent {left right : SPNetwork}
    (current : (parallel left right).realize.Current) : right.realize.Current :=
  fun edge ↦ current (Sum.inr edge)

private theorem divergence_series_split {left right : SPNetwork}
    (current : (series left right).realize.Current)
    (vertex : (series left right).RealizedVertex) :
    (series left right).realize.divergence current vertex =
      ((∑ edge : left.PhysicalEdge,
          if seriesLeftVertex (left.realizedTail edge) = vertex then
            current (Sum.inl edge) else 0) -
        ∑ edge : left.PhysicalEdge,
          if seriesLeftVertex (left.realizedHead edge) = vertex then
            current (Sum.inl edge) else 0) +
      ((∑ edge : right.PhysicalEdge,
          if seriesRightVertex (right.realizedTail edge) = vertex then
            current (Sum.inr edge) else 0) -
        ∑ edge : right.PhysicalEdge,
          if seriesRightVertex (right.realizedHead edge) = vertex then
            current (Sum.inr edge) else 0) := by
  change
    ((∑ edge : left.PhysicalEdge ⊕ right.PhysicalEdge,
        if (series left right).realizedTail edge = vertex then current edge else 0) -
      ∑ edge : left.PhysicalEdge ⊕ right.PhysicalEdge,
        if (series left right).realizedHead edge = vertex then current edge else 0) = _
  rw [sum_sum_type, sum_sum_type]
  simp only [realizedTail_series_left, realizedTail_series_right,
    realizedHead_series_left, realizedHead_series_right]
  ring_nf

private theorem divergence_parallel_split {left right : SPNetwork}
    (current : (parallel left right).realize.Current)
    (vertex : (parallel left right).RealizedVertex) :
    (parallel left right).realize.divergence current vertex =
      ((∑ edge : left.PhysicalEdge,
          if parallelLeftVertex (left.realizedTail edge) = vertex then
            current (Sum.inl edge) else 0) -
        ∑ edge : left.PhysicalEdge,
          if parallelLeftVertex (left.realizedHead edge) = vertex then
            current (Sum.inl edge) else 0) +
      ((∑ edge : right.PhysicalEdge,
          if parallelRightVertex (right.realizedTail edge) = vertex then
            current (Sum.inr edge) else 0) -
        ∑ edge : right.PhysicalEdge,
          if parallelRightVertex (right.realizedHead edge) = vertex then
            current (Sum.inr edge) else 0) := by
  change
    ((∑ edge : left.PhysicalEdge ⊕ right.PhysicalEdge,
        if (parallel left right).realizedTail edge = vertex then current edge else 0) -
      ∑ edge : left.PhysicalEdge ⊕ right.PhysicalEdge,
        if (parallel left right).realizedHead edge = vertex then current edge else 0) = _
  rw [sum_sum_type, sum_sum_type]
  simp only [realizedTail_parallel_left, realizedTail_parallel_right,
    realizedHead_parallel_left, realizedHead_parallel_right]
  ring_nf

/-- Scale a recursive normalized flow to a signed current of arbitrary value. -/
noncomputable def Flow.toCurrent : {network : SPNetwork} →
    Flow network → ℝ → network.realize.Current
  | .edge, _, I, _ => I
  | .series _ _, flow, I, Sum.inl physicalEdge => flow.1.toCurrent I physicalEdge
  | .series _ _, flow, I, Sum.inr physicalEdge => flow.2.toCurrent I physicalEdge
  | .parallel _ _, flow, I, Sum.inl physicalEdge =>
      flow.2.1.toCurrent (I * flow.1) physicalEdge
  | .parallel _ _, flow, I, Sum.inr physicalEdge =>
      flow.2.2.toCurrent (I * (1 - flow.1)) physicalEdge

/-- Unit-resistance energy splits over the two edge summands of a series gate. -/
theorem unitEnergy_series_split {left right : SPNetwork}
    (current : (series left right).realize.Current) :
    (series left right).realize.unitEnergy current =
      left.realize.unitEnergy (seriesLeftCurrent current) +
        right.realize.unitEnergy (seriesRightCurrent current) := by
  exact sum_sum_type fun edge ↦ current edge ^ 2

/-- Unit-resistance energy splits over the two edge summands of a parallel gate. -/
theorem unitEnergy_parallel_split {left right : SPNetwork}
    (current : (parallel left right).realize.Current) :
    (parallel left right).realize.unitEnergy current =
      left.realize.unitEnergy (parallelLeftCurrent current) +
        right.realize.unitEnergy (parallelRightCurrent current) := by
  exact sum_sum_type fun edge ↦ current edge ^ 2

/-- At a series source, only the left child contributes to divergence. -/
theorem divergence_series_source {left right : SPNetwork}
    (current : (series left right).realize.Current) :
    (series left right).realize.divergence current (series left right).realizedSource =
      left.realize.divergence (seriesLeftCurrent current) left.realizedSource := by
  rw [divergence_series_split]
  simp [TwoTerminalMultigraph.divergence, seriesLeftCurrent]

/-- At a series sink, only the right child contributes to divergence. -/
theorem divergence_series_sink {left right : SPNetwork}
    (current : (series left right).realize.Current) :
    (series left right).realize.divergence current (series left right).realizedSink =
      right.realize.divergence (seriesRightCurrent current) right.realizedSink := by
  rw [divergence_series_split]
  simp [TwoTerminalMultigraph.divergence, seriesRightCurrent]

/-- At a series join, the two incident child divergences add. -/
theorem divergence_series_join {left right : SPNetwork}
    (current : (series left right).realize.Current) :
    (series left right).realize.divergence current (seriesJoin left right) =
      left.realize.divergence (seriesLeftCurrent current) left.realizedSink +
        right.realize.divergence (seriesRightCurrent current) right.realizedSource := by
  rw [divergence_series_split]
  simp [TwoTerminalMultigraph.divergence, seriesLeftCurrent, seriesRightCurrent]

/-- A tagged left internal vertex has exactly its left-child divergence. -/
theorem divergence_series_left_internal {left right : SPNetwork}
    (current : (series left right).realize.Current) (vertex : left.InternalVertex) :
    (series left right).realize.divergence current
        (seriesLeftVertex (Sum.inr vertex)) =
      left.realize.divergence (seriesLeftCurrent current) (Sum.inr vertex) := by
  rw [divergence_series_split]
  simp [TwoTerminalMultigraph.divergence, seriesLeftCurrent,
    (seriesLeftVertex_injective left right).eq_iff]

/-- A tagged right internal vertex has exactly its right-child divergence. -/
theorem divergence_series_right_internal {left right : SPNetwork}
    (current : (series left right).realize.Current) (vertex : right.InternalVertex) :
    (series left right).realize.divergence current
        (seriesRightVertex (Sum.inr vertex)) =
      right.realize.divergence (seriesRightCurrent current) (Sum.inr vertex) := by
  rw [divergence_series_split]
  simp [TwoTerminalMultigraph.divergence, seriesRightCurrent,
    (seriesRightVertex_injective left right).eq_iff]

/-- At a parallel source, the two branch divergences add. -/
theorem divergence_parallel_source {left right : SPNetwork}
    (current : (parallel left right).realize.Current) :
    (parallel left right).realize.divergence current (parallel left right).realizedSource =
      left.realize.divergence (parallelLeftCurrent current) left.realizedSource +
        right.realize.divergence (parallelRightCurrent current) right.realizedSource := by
  rw [divergence_parallel_split]
  simp [TwoTerminalMultigraph.divergence, parallelLeftCurrent, parallelRightCurrent]

/-- At a parallel sink, the two branch divergences add. -/
theorem divergence_parallel_sink {left right : SPNetwork}
    (current : (parallel left right).realize.Current) :
    (parallel left right).realize.divergence current (parallel left right).realizedSink =
      left.realize.divergence (parallelLeftCurrent current) left.realizedSink +
        right.realize.divergence (parallelRightCurrent current) right.realizedSink := by
  rw [divergence_parallel_split]
  simp [TwoTerminalMultigraph.divergence, parallelLeftCurrent, parallelRightCurrent]

/-- A tagged left parallel interior has exactly its left-branch divergence. -/
theorem divergence_parallel_left_internal {left right : SPNetwork}
    (current : (parallel left right).realize.Current) (vertex : left.InternalVertex) :
    (parallel left right).realize.divergence current
        (parallelLeftVertex (Sum.inr vertex)) =
      left.realize.divergence (parallelLeftCurrent current) (Sum.inr vertex) := by
  rw [divergence_parallel_split]
  simp [TwoTerminalMultigraph.divergence, parallelLeftCurrent,
    (parallelLeftVertex_injective left right).eq_iff]

/-- A tagged right parallel interior has exactly its right-branch divergence. -/
theorem divergence_parallel_right_internal {left right : SPNetwork}
    (current : (parallel left right).realize.Current) (vertex : right.InternalVertex) :
    (parallel left right).realize.divergence current
        (parallelRightVertex (Sum.inr vertex)) =
      right.realize.divergence (parallelRightCurrent current) (Sum.inr vertex) := by
  rw [divergence_parallel_split]
  simp [TwoTerminalMultigraph.divergence, parallelRightCurrent,
    (parallelRightVertex_injective left right).eq_iff]

/-- Equal-value child flows assemble to a conventional flow through a series gate. -/
theorem isThroughFlow_series_of_children {left right : SPNetwork} {I : ℝ}
    {current : (series left right).realize.Current}
    (hleft : left.realize.IsThroughFlow I (seriesLeftCurrent current))
    (hright : right.realize.IsThroughFlow I (seriesRightCurrent current)) :
    (series left right).realize.IsThroughFlow I current := by
  intro vertex
  rcases vertex with boundary | internal
  · cases boundary with
    | source =>
        change
          (series left right).realize.divergence current
              (series left right).realizedSource =
            (series left right).realize.throughFlowDemand I
              (series left right).realizedSource
        rw [divergence_series_source, hleft.divergence_source]
        simp [TwoTerminalMultigraph.throughFlowDemand, realizedSource]
    | sink =>
        change
          (series left right).realize.divergence current
              (series left right).realizedSink =
            (series left right).realize.throughFlowDemand I
              (series left right).realizedSink
        rw [divergence_series_sink, hright.divergence_sink]
        simp [TwoTerminalMultigraph.throughFlowDemand, realizedSource, realizedSink]
  · rcases internal with join | internal
    · cases join
      change
        (series left right).realize.divergence current (seriesJoin left right) =
          (series left right).realize.throughFlowDemand I (seriesJoin left right)
      rw [divergence_series_join, hleft.divergence_sink, hright.divergence_source]
      simp [TwoTerminalMultigraph.throughFlowDemand, seriesJoin, realizedSource, realizedSink]
    · rcases internal with leftInternal | rightInternal
      · change
          (series left right).realize.divergence current
              (seriesLeftVertex (Sum.inr leftInternal)) =
            (series left right).realize.throughFlowDemand I
              (seriesLeftVertex (Sum.inr leftInternal))
        rw [divergence_series_left_internal]
        rw [hleft.divergence_eq_zero (by simp [realizedSource]) (by simp [realizedSink])]
        simp [TwoTerminalMultigraph.throughFlowDemand, seriesLeftVertex,
          realizedSource, realizedSink]
      · change
          (series left right).realize.divergence current
              (seriesRightVertex (Sum.inr rightInternal)) =
            (series left right).realize.throughFlowDemand I
              (seriesRightVertex (Sum.inr rightInternal))
        rw [divergence_series_right_internal]
        rw [hright.divergence_eq_zero (by simp [realizedSource]) (by simp [realizedSink])]
        simp [TwoTerminalMultigraph.throughFlowDemand, seriesRightVertex,
          realizedSource, realizedSink]

/-- Branch flows whose values add to `I` assemble to a parallel `I`-flow. -/
theorem isThroughFlow_parallel_of_children {left right : SPNetwork} {I J K : ℝ}
    {current : (parallel left right).realize.Current}
    (hleft : left.realize.IsThroughFlow J (parallelLeftCurrent current))
    (hright : right.realize.IsThroughFlow K (parallelRightCurrent current))
    (hvalue : J + K = I) :
    (parallel left right).realize.IsThroughFlow I current := by
  intro vertex
  rcases vertex with boundary | internal
  · cases boundary with
    | source =>
        change
          (parallel left right).realize.divergence current
              (parallel left right).realizedSource =
            (parallel left right).realize.throughFlowDemand I
              (parallel left right).realizedSource
        rw [divergence_parallel_source, hleft.divergence_source,
          hright.divergence_source, hvalue]
        simp [TwoTerminalMultigraph.throughFlowDemand, realizedSource]
    | sink =>
        change
          (parallel left right).realize.divergence current
              (parallel left right).realizedSink =
            (parallel left right).realize.throughFlowDemand I
              (parallel left right).realizedSink
        rw [divergence_parallel_sink, hleft.divergence_sink, hright.divergence_sink]
        simp [TwoTerminalMultigraph.throughFlowDemand, realizedSource, realizedSink, ← hvalue]
        ring
  · rcases internal with leftInternal | rightInternal
    · change
        (parallel left right).realize.divergence current
            (parallelLeftVertex (Sum.inr leftInternal)) =
          (parallel left right).realize.throughFlowDemand I
            (parallelLeftVertex (Sum.inr leftInternal))
      rw [divergence_parallel_left_internal]
      rw [hleft.divergence_eq_zero (by simp [realizedSource]) (by simp [realizedSink])]
      simp [TwoTerminalMultigraph.throughFlowDemand, parallelLeftVertex,
        realizedSource, realizedSink]
    · change
        (parallel left right).realize.divergence current
            (parallelRightVertex (Sum.inr rightInternal)) =
          (parallel left right).realize.throughFlowDemand I
            (parallelRightVertex (Sum.inr rightInternal))
      rw [divergence_parallel_right_internal]
      rw [hright.divergence_eq_zero (by simp [realizedSource]) (by simp [realizedSink])]
      simp [TwoTerminalMultigraph.throughFlowDemand, parallelRightVertex,
        realizedSource, realizedSink]

/-- Scaling a recursive normalized flow gives a conventional through-flow of that value. -/
theorem flow_toCurrent_isThroughFlow {network : SPNetwork} (flow : Flow network) (I : ℝ) :
    network.realize.IsThroughFlow I (flow.toCurrent I) := by
  induction network generalizing I with
  | edge =>
      cases flow
      intro vertex
      rcases vertex with boundary | internal
      · cases boundary <;>
          simp [TwoTerminalMultigraph.divergence, TwoTerminalMultigraph.throughFlowDemand,
            Flow.toCurrent, PhysicalEdge, realizedTail, realizedHead, realizedSource, realizedSink]
      · exact internal.elim
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      apply isThroughFlow_series_of_children
      · change left.realize.IsThroughFlow I (leftFlow.toCurrent I)
        exact ihLeft leftFlow I
      · change right.realize.IsThroughFlow I (rightFlow.toCurrent I)
        exact ihRight rightFlow I
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨split, leftFlow, rightFlow⟩
      apply isThroughFlow_parallel_of_children
      · change left.realize.IsThroughFlow (I * split) (leftFlow.toCurrent (I * split))
        exact ihLeft leftFlow (I * split)
      · change right.realize.IsThroughFlow (I * (1 - split))
          (rightFlow.toCurrent (I * (1 - split)))
        exact ihRight rightFlow (I * (1 - split))
      · ring

/-- The conventional current has the expected homogeneous recursive-flow energy. -/
theorem flow_toCurrent_unitEnergy {network : SPNetwork} (flow : Flow network) (I : ℝ) :
    network.realize.unitEnergy (flow.toCurrent I) = I ^ 2 * flow.unitEnergy := by
  induction network generalizing I with
  | edge =>
      cases flow
      simp [TwoTerminalMultigraph.unitEnergy, Flow.toCurrent, Flow.unitEnergy,
        Flow.energy, PhysicalEdge]
  | series left right ihLeft ihRight =>
      rcases flow with ⟨leftFlow, rightFlow⟩
      rw [unitEnergy_series_split]
      change
        left.realize.unitEnergy (leftFlow.toCurrent I) +
            right.realize.unitEnergy (rightFlow.toCurrent I) =
          I ^ 2 * (leftFlow.unitEnergy + rightFlow.unitEnergy)
      rw [ihLeft, ihRight]
      ring
  | parallel left right ihLeft ihRight =>
      rcases flow with ⟨split, leftFlow, rightFlow⟩
      rw [unitEnergy_parallel_split]
      change
        left.realize.unitEnergy (leftFlow.toCurrent (I * split)) +
            right.realize.unitEnergy (rightFlow.toCurrent (I * (1 - split))) =
          I ^ 2 *
            (split ^ 2 * leftFlow.unitEnergy +
              (1 - split) ^ 2 * rightFlow.unitEnergy)
      rw [ihLeft, ihRight]
      ring

/-- Restriction to the left child of a series flow preserves the full flow value. -/
theorem seriesLeftCurrent_isThroughFlow {left right : SPNetwork} {I : ℝ}
    {current : (series left right).realize.Current}
    (hcurrent : (series left right).realize.IsThroughFlow I current) :
    left.realize.IsThroughFlow I (seriesLeftCurrent current) := by
  apply TwoTerminalMultigraph.isThroughFlow_of_source_of_interior
  · rw [← divergence_series_source]
    exact hcurrent.divergence_source
  · rintro (boundary | internal) hsource hsink
    · cases boundary <;> simp [realizedSource, realizedSink] at hsource hsink
    · rw [← divergence_series_left_internal]
      apply hcurrent.divergence_eq_zero
      · simp [seriesLeftVertex, realizedSource]
      · simp [seriesLeftVertex, realizedSink]

/-- Restriction to the right child of a series flow preserves the full flow value. -/
theorem seriesRightCurrent_isThroughFlow {left right : SPNetwork} {I : ℝ}
    {current : (series left right).realize.Current}
    (hcurrent : (series left right).realize.IsThroughFlow I current) :
    right.realize.IsThroughFlow I (seriesRightCurrent current) := by
  apply TwoTerminalMultigraph.isThroughFlow_of_sink_of_interior
  · rw [← divergence_series_sink]
    exact hcurrent.divergence_sink
  · rintro (boundary | internal) hsource hsink
    · cases boundary <;> simp [realizedSource, realizedSink] at hsource hsink
    · rw [← divergence_series_right_internal]
      apply hcurrent.divergence_eq_zero
      · simp [seriesRightVertex, realizedSource]
      · simp [seriesRightVertex, realizedSink]

/-- A parallel left restriction is a flow whose value is its own source divergence. -/
theorem parallelLeftCurrent_isThroughFlow {left right : SPNetwork} {I : ℝ}
    {current : (parallel left right).realize.Current}
    (hcurrent : (parallel left right).realize.IsThroughFlow I current) :
    left.realize.IsThroughFlow
      (left.realize.divergence (parallelLeftCurrent current) left.realizedSource)
      (parallelLeftCurrent current) := by
  apply TwoTerminalMultigraph.isThroughFlow_of_source_of_interior rfl
  rintro (boundary | internal) hsource hsink
  · cases boundary <;> simp [realizedSource, realizedSink] at hsource hsink
  · rw [← divergence_parallel_left_internal]
    apply hcurrent.divergence_eq_zero
    · simp [parallelLeftVertex, realizedSource]
    · simp [parallelLeftVertex, realizedSink]

/-- A parallel right restriction is a flow whose value is its own source divergence. -/
theorem parallelRightCurrent_isThroughFlow {left right : SPNetwork} {I : ℝ}
    {current : (parallel left right).realize.Current}
    (hcurrent : (parallel left right).realize.IsThroughFlow I current) :
    right.realize.IsThroughFlow
      (right.realize.divergence (parallelRightCurrent current) right.realizedSource)
      (parallelRightCurrent current) := by
  apply TwoTerminalMultigraph.isThroughFlow_of_source_of_interior rfl
  rintro (boundary | internal) hsource hsink
  · cases boundary <;> simp [realizedSource, realizedSink] at hsource hsink
  · rw [← divergence_parallel_right_internal]
    apply hcurrent.divergence_eq_zero
    · simp [parallelRightVertex, realizedSource]
    · simp [parallelRightVertex, realizedSink]

/-- Arbitrary-value parallel square completion. -/
theorem generalized_harmonic_le_split_energy {leftResistance rightResistance : ℝ}
    (hleft : 0 < leftResistance) (hright : 0 < rightResistance) (I J : ℝ) :
    I ^ 2 * (leftResistance * rightResistance / (leftResistance + rightResistance)) ≤
      J ^ 2 * leftResistance + (I - J) ^ 2 * rightResistance := by
  have hsum : 0 < leftResistance + rightResistance := add_pos hleft hright
  rw [← sub_nonneg]
  have hid :
      J ^ 2 * leftResistance + (I - J) ^ 2 * rightResistance -
          I ^ 2 * (leftResistance * rightResistance /
            (leftResistance + rightResistance)) =
        ((leftResistance + rightResistance) * J - I * rightResistance) ^ 2 /
          (leftResistance + rightResistance) := by
    field_simp [ne_of_gt hsum]
    ring
  rw [hid]
  positivity

/-- Generalized Thomson bound for every real flow value and every signed conventional current. -/
theorem generalized_thomson (network : SPNetwork) (I : ℝ)
    (current : network.realize.Current) (hcurrent : network.realize.IsThroughFlow I current) :
    I ^ 2 * network.resistance ≤ network.realize.unitEnergy current := by
  induction network generalizing I with
  | edge =>
      have hsource := hcurrent.divergence_source
      have hedge : current PUnit.unit = I := by
        simpa [TwoTerminalMultigraph.divergence, PhysicalEdge, realizedTail, realizedHead,
          realizedSource, realizedSink] using hsource
      simp [TwoTerminalMultigraph.unitEnergy, resistance, PhysicalEdge, hedge]
  | series left right ihLeft ihRight =>
      have hleft := seriesLeftCurrent_isThroughFlow hcurrent
      have hright := seriesRightCurrent_isThroughFlow hcurrent
      have hleftBound := ihLeft I (seriesLeftCurrent current) hleft
      have hrightBound := ihRight I (seriesRightCurrent current) hright
      rw [unitEnergy_series_split]
      change I ^ 2 * (left.resistance + right.resistance) ≤ _
      nlinarith
  | parallel left right ihLeft ihRight =>
      let J := left.realize.divergence (parallelLeftCurrent current) left.realizedSource
      let K := right.realize.divergence (parallelRightCurrent current) right.realizedSource
      have hleft : left.realize.IsThroughFlow J (parallelLeftCurrent current) :=
        parallelLeftCurrent_isThroughFlow hcurrent
      have hright : right.realize.IsThroughFlow K (parallelRightCurrent current) :=
        parallelRightCurrent_isThroughFlow hcurrent
      have hvalue : J + K = I := by
        have hsplit := divergence_parallel_source current
        rw [hcurrent.divergence_source] at hsplit
        simpa [J, K] using hsplit.symm
      have hleftBound := ihLeft J (parallelLeftCurrent current) hleft
      have hrightBound := ihRight K (parallelRightCurrent current) hright
      rw [unitEnergy_parallel_split]
      change
        I ^ 2 *
            (left.resistance * right.resistance /
              (left.resistance + right.resistance)) ≤
          left.realize.unitEnergy (parallelLeftCurrent current) +
            right.realize.unitEnergy (parallelRightCurrent current)
      calc
        I ^ 2 *
              (left.resistance * right.resistance /
                (left.resistance + right.resistance)) ≤
            J ^ 2 * left.resistance + (I - J) ^ 2 * right.resistance :=
          generalized_harmonic_le_split_energy left.resistance_pos
            right.resistance_pos I J
        _ = J ^ 2 * left.resistance + K ^ 2 * right.resistance := by
          rw [← hvalue]
          ring
        _ ≤ left.realize.unitEnergy (parallelLeftCurrent current) +
              right.realize.unitEnergy (parallelRightCurrent current) :=
          add_le_add hleftBound hrightBound

/-- The conventional current obtained from the recursive minimizer. -/
noncomputable def attainingCurrent (network : SPNetwork) : network.realize.Current :=
  (optimalFlow network).toCurrent 1

/-- The attaining current is a conventional unit through-flow. -/
theorem attainingCurrent_isThroughFlow (network : SPNetwork) :
    network.realize.IsThroughFlow 1 network.attainingCurrent :=
  flow_toCurrent_isThroughFlow (optimalFlow network) 1

/-- The attaining current has exactly the recursive effective-resistance energy. -/
theorem attainingCurrent_unitEnergy (network : SPNetwork) :
    network.realize.unitEnergy network.attainingCurrent = network.resistance := by
  rw [attainingCurrent, flow_toCurrent_unitEnergy, optimalFlow_unitEnergy]
  ring

/-- Every structural realization has a conventional unit flow. -/
theorem realize_hasUnitFlow (network : SPNetwork) : network.realize.HasUnitFlow := by
  exact ⟨network.realize.unitEnergy network.attainingCurrent,
    network.attainingCurrent,
    network.attainingCurrent_isThroughFlow,
    rfl⟩

/-- The recursive resistance is the least conventional unit-flow energy. -/
theorem resistance_isLeast_energySet (network : SPNetwork) :
    IsLeast network.realize.energySet network.resistance := by
  constructor
  · exact ⟨network.attainingCurrent, network.attainingCurrent_isThroughFlow,
      network.attainingCurrent_unitEnergy⟩
  · rintro energy ⟨current, hcurrent, rfl⟩
    simpa using generalized_thomson network 1 current hcurrent

/-- Traditional Kirchhoff--Thomson resistance agrees with the recursive evaluator. -/
theorem traditionalResistance_realize (network : SPNetwork) :
    network.realize.traditionalResistance = network.resistance := by
  unfold TwoTerminalMultigraph.traditionalResistance
  exact (resistance_isLeast_energySet network).isGLB.csInf_eq
    (realize_hasUnitFlow network)

/-- Regression: two unit edges in series have traditional resistance `2`. -/
theorem traditionalResistance_twoSeries :
    (series edge edge).realize.traditionalResistance = 2 := by
  rw [traditionalResistance_realize]
  norm_num [resistance]

/-- Regression: two distinct unit parallel edges have traditional resistance `1 / 2`. -/
theorem traditionalResistance_twoParallel :
    (parallel edge edge).realize.traditionalResistance = (1 / 2 : ℝ) := by
  rw [traditionalResistance_realize]
  norm_num [resistance]

end SPNetwork

end SeriesParallel.MainText
