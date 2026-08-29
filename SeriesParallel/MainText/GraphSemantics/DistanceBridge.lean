/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.FinitePaths
public import SeriesParallel.MainText.GraphSemantics.Realization
public import SeriesParallel.MainText.GraphSemantics.TraditionalDistance

/-!
# Bridge from general graph distance to the recursive distance evaluator

Recursive paths give source-to-sink walks for the upper bound.  A vertex-level certificate that is
1-Lipschitz across every physical edge controls arbitrary walks and gives the reverse bound.
-/

@[expose] public section

namespace SeriesParallel.MainText

namespace SPNetwork

open GraphSemantics

/-- The realized left child of a series gate maps homomorphically into the parent shadow. -/
abbrev seriesLeftShadowHom (left right : SPNetwork) :
    left.realize.simpleShadow →g (series left right).realize.simpleShadow where
  toFun := seriesLeftVertex
  map_rel' := by
    rintro u v ⟨hne, e, hends⟩
    refine ⟨?_, Sum.inl e, ?_⟩
    · intro h
      exact hne (seriesLeftVertex_injective left right h)
    rcases hends with hends | hends
    · exact Or.inl ⟨congrArg seriesLeftVertex hends.1, congrArg seriesLeftVertex hends.2⟩
    · exact Or.inr ⟨congrArg seriesLeftVertex hends.1, congrArg seriesLeftVertex hends.2⟩

/-- The realized right child of a series gate maps homomorphically into the parent shadow. -/
abbrev seriesRightShadowHom (left right : SPNetwork) :
    right.realize.simpleShadow →g (series left right).realize.simpleShadow where
  toFun := seriesRightVertex
  map_rel' := by
    rintro u v ⟨hne, e, hends⟩
    refine ⟨?_, Sum.inr e, ?_⟩
    · intro h
      exact hne (seriesRightVertex_injective left right h)
    rcases hends with hends | hends
    · exact Or.inl ⟨congrArg seriesRightVertex hends.1, congrArg seriesRightVertex hends.2⟩
    · exact Or.inr ⟨congrArg seriesRightVertex hends.1, congrArg seriesRightVertex hends.2⟩

/-- The realized left child of a parallel gate maps homomorphically into the parent shadow. -/
abbrev parallelLeftShadowHom (left right : SPNetwork) :
    left.realize.simpleShadow →g (parallel left right).realize.simpleShadow where
  toFun := parallelLeftVertex
  map_rel' := by
    rintro u v ⟨hne, e, hends⟩
    refine ⟨?_, Sum.inl e, ?_⟩
    · intro h
      exact hne (parallelLeftVertex_injective left right h)
    rcases hends with hends | hends
    · exact Or.inl ⟨congrArg parallelLeftVertex hends.1,
        congrArg parallelLeftVertex hends.2⟩
    · exact Or.inr ⟨congrArg parallelLeftVertex hends.1,
        congrArg parallelLeftVertex hends.2⟩

/-- The realized right child of a parallel gate maps homomorphically into the parent shadow. -/
abbrev parallelRightShadowHom (left right : SPNetwork) :
    right.realize.simpleShadow →g (parallel left right).realize.simpleShadow where
  toFun := parallelRightVertex
  map_rel' := by
    rintro u v ⟨hne, e, hends⟩
    refine ⟨?_, Sum.inr e, ?_⟩
    · intro h
      exact hne (parallelRightVertex_injective left right h)
    rcases hends with hends | hends
    · exact Or.inl ⟨congrArg parallelRightVertex hends.1,
        congrArg parallelRightVertex hends.2⟩
    · exact Or.inr ⟨congrArg parallelRightVertex hends.1,
        congrArg parallelRightVertex hends.2⟩

/-- Map a recursive boundary path to an unrestricted walk in the realized simple shadow. -/
def Path.toRealizeWalk : {network : SPNetwork} → (path : Path network) →
    network.realize.simpleShadow.Walk network.realize.source network.realize.sink
  | .edge, _ =>
      (SPNetwork.edge.realize.tail_adj_head SPNetwork.edge.realize_noLoops PUnit.unit).toWalk
  | .series left right, (leftPath, rightPath) =>
      (leftPath.toRealizeWalk.map (seriesLeftShadowHom left right)).append
        (rightPath.toRealizeWalk.map (seriesRightShadowHom left right))
  | .parallel left right, Sum.inl leftPath =>
      leftPath.toRealizeWalk.map (parallelLeftShadowHom left right)
  | .parallel left right, Sum.inr rightPath =>
      rightPath.toRealizeWalk.map (parallelRightShadowHom left right)

/-- Mapping a recursive path to the realization preserves its number of traversed edges. -/
@[simp]
theorem Path.length_toRealizeWalk {network : SPNetwork} (path : Path network) :
    path.toRealizeWalk.length = path.length := by
  induction network with
  | edge =>
      cases path
      change 1 = 1
      rfl
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      calc
        (@Path.toRealizeWalk (SPNetwork.series left right) (leftPath, rightPath)).length =
            ((leftPath.toRealizeWalk.map (seriesLeftShadowHom left right)).append
              (rightPath.toRealizeWalk.map (seriesRightShadowHom left right))).length := rfl
        _ = (leftPath.toRealizeWalk.map (seriesLeftShadowHom left right)).length +
            (rightPath.toRealizeWalk.map (seriesRightShadowHom left right)).length :=
          SimpleGraph.Walk.length_append _ _
        _ = leftPath.toRealizeWalk.length + rightPath.toRealizeWalk.length := by
          rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
        _ = leftPath.length + rightPath.length := by rw [ihLeft, ihRight]
        _ = @Path.length (SPNetwork.series left right) (leftPath, rightPath) := rfl
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · calc
          (@Path.toRealizeWalk (SPNetwork.parallel left right) (Sum.inl leftPath)).length =
              (leftPath.toRealizeWalk.map (parallelLeftShadowHom left right)).length := rfl
          _ = leftPath.toRealizeWalk.length :=
            SimpleGraph.Walk.length_map (parallelLeftShadowHom left right)
              leftPath.toRealizeWalk
          _ = leftPath.length := ihLeft leftPath
          _ = @Path.length (SPNetwork.parallel left right) (Sum.inl leftPath) := rfl
      · calc
          (@Path.toRealizeWalk (SPNetwork.parallel left right) (Sum.inr rightPath)).length =
              (rightPath.toRealizeWalk.map (parallelRightShadowHom left right)).length := rfl
          _ = rightPath.toRealizeWalk.length :=
            SimpleGraph.Walk.length_map (parallelRightShadowHom left right)
              rightPath.toRealizeWalk
          _ = rightPath.length := ihRight rightPath
          _ = @Path.length (SPNetwork.parallel left right) (Sum.inr rightPath) := rfl

/-- The source and sink of every realization are connected by a graph walk. -/
theorem realize_reachable (network : SPNetwork) :
    network.realize.simpleShadow.Reachable network.realize.source network.realize.sink :=
  ⟨network.anyPath.toRealizeWalk⟩

/-- The recursive shortest path supplies the graph-distance upper bound. -/
theorem traditionalDistance_realize_le (network : SPNetwork) :
    traditionalDistance network.realize ≤ network.distance := by
  calc
    traditionalDistance network.realize ≤ network.shortestPath.toRealizeWalk.length :=
      traditionalDistance_le_walk_length _ _
    _ = network.shortestPath.length := Path.length_toRealizeWalk _
    _ = network.distance := network.length_shortestPath

/-- Inductive level certificate used to control every walk, including walks with backtracking. -/
def vertexLevel : (network : SPNetwork) → network.RealizedVertex → ℕ
  | .edge, Sum.inl .source => 0
  | .edge, Sum.inl .sink => 1
  | .edge, Sum.inr internal => nomatch internal
  | .series _ _, Sum.inl .source => 0
  | .series left right, Sum.inl .sink => left.distance + right.distance
  | .series left _, Sum.inr (Sum.inl _) => left.distance
  | .series left _, Sum.inr (Sum.inr (Sum.inl v)) => left.vertexLevel (Sum.inr v)
  | .series left right, Sum.inr (Sum.inr (Sum.inr v)) =>
      left.distance + right.vertexLevel (Sum.inr v)
  | .parallel _ _, Sum.inl .source => 0
  | .parallel left right, Sum.inl .sink => min left.distance right.distance
  | .parallel left right, Sum.inr (Sum.inl v) =>
      min (left.vertexLevel (Sum.inr v)) (min left.distance right.distance)
  | .parallel left right, Sum.inr (Sum.inr v) =>
      min (right.vertexLevel (Sum.inr v)) (min left.distance right.distance)

@[simp]
theorem vertexLevel_source (network : SPNetwork) :
    network.vertexLevel network.realizedSource = 0 := by
  cases network <;> rfl

@[simp]
theorem vertexLevel_sink (network : SPNetwork) :
    network.vertexLevel network.realizedSink = network.distance := by
  cases network <;> rfl

@[simp]
theorem vertexLevel_seriesLeftVertex (left right : SPNetwork) (v : left.RealizedVertex) :
    (series left right).vertexLevel (seriesLeftVertex v) = left.vertexLevel v := by
  rcases v with boundary | internal
  · cases boundary
    · calc
        (series left right).vertexLevel (seriesLeftVertex left.realizedSource) = 0 := rfl
        _ = left.vertexLevel left.realizedSource := (vertexLevel_source left).symm
    · calc
        (series left right).vertexLevel (seriesLeftVertex left.realizedSink) =
            left.distance := rfl
        _ = left.vertexLevel left.realizedSink := (vertexLevel_sink left).symm
  · rfl

@[simp]
theorem vertexLevel_seriesRightVertex (left right : SPNetwork) (v : right.RealizedVertex) :
    (series left right).vertexLevel (seriesRightVertex v) =
      left.distance + right.vertexLevel v := by
  rcases v with boundary | internal
  · cases boundary
    · calc
        (series left right).vertexLevel (seriesRightVertex right.realizedSource) =
            left.distance := rfl
        _ = left.distance + right.vertexLevel right.realizedSource := by simp
    · calc
        (series left right).vertexLevel (seriesRightVertex right.realizedSink) =
            left.distance + right.distance := rfl
        _ = left.distance + right.vertexLevel right.realizedSink := by simp
  · rfl

@[simp]
theorem vertexLevel_parallelLeftVertex (left right : SPNetwork) (v : left.RealizedVertex) :
    (parallel left right).vertexLevel (parallelLeftVertex v) =
      min (left.vertexLevel v) (min left.distance right.distance) := by
  rcases v with boundary | internal
  · cases boundary
    · calc
        (parallel left right).vertexLevel (parallelLeftVertex left.realizedSource) = 0 := rfl
        _ = min (left.vertexLevel left.realizedSource)
            (min left.distance right.distance) := by simp
    · calc
        (parallel left right).vertexLevel (parallelLeftVertex left.realizedSink) =
            min left.distance right.distance := rfl
        _ = min (left.vertexLevel left.realizedSink) (min left.distance right.distance) := by
          rw [vertexLevel_sink]
          omega
  · rfl

@[simp]
theorem vertexLevel_parallelRightVertex (left right : SPNetwork) (v : right.RealizedVertex) :
    (parallel left right).vertexLevel (parallelRightVertex v) =
      min (right.vertexLevel v) (min left.distance right.distance) := by
  rcases v with boundary | internal
  · cases boundary
    · calc
        (parallel left right).vertexLevel (parallelRightVertex right.realizedSource) = 0 := rfl
        _ = min (right.vertexLevel right.realizedSource)
            (min left.distance right.distance) := by simp
    · calc
        (parallel left right).vertexLevel (parallelRightVertex right.realizedSink) =
            min left.distance right.distance := rfl
        _ = min (right.vertexLevel right.realizedSink) (min left.distance right.distance) := by
          rw [vertexLevel_sink]
          omega
  · rfl

private theorem min_le_min_add_one {a b c : ℕ} (h : a ≤ b + 1) :
    min a c ≤ min b c + 1 := by
  omega

/-- The certificate changes by at most one across every physical edge. -/
theorem vertexLevel_edge_lipschitz (network : SPNetwork) (e : network.PhysicalEdge) :
    network.vertexLevel (network.realizedHead e) ≤
        network.vertexLevel (network.realizedTail e) + 1 ∧
      network.vertexLevel (network.realizedTail e) ≤
        network.vertexLevel (network.realizedHead e) + 1 := by
  induction network with
  | edge =>
      cases e
      simp [realizedTail, realizedHead]
  | series left right ihLeft ihRight =>
      rcases e with e | e
      · simpa using ihLeft e
      · have h := ihRight e
        simp only [realizedTail_series_right, realizedHead_series_right,
          vertexLevel_seriesRightVertex]
        omega
  | parallel left right ihLeft ihRight =>
      rcases e with e | e
      · have h := ihLeft e
        simp only [realizedTail_parallel_left, realizedHead_parallel_left,
          vertexLevel_parallelLeftVertex]
        exact ⟨min_le_min_add_one h.1, min_le_min_add_one h.2⟩
      · have h := ihRight e
        simp only [realizedTail_parallel_right, realizedHead_parallel_right,
          vertexLevel_parallelRightVertex]
        exact ⟨min_le_min_add_one h.1, min_le_min_add_one h.2⟩

/-- Adjacent realized vertices have levels differing by at most one in either direction. -/
theorem vertexLevel_adjacent_le {network : SPNetwork} {u v : network.RealizedVertex}
    (hadj : network.realize.simpleShadow.Adj u v) :
    network.vertexLevel v ≤ network.vertexLevel u + 1 := by
  rcases hadj with ⟨_, e, hends⟩
  rcases hends with hends | hends
  · rw [← hends.1, ← hends.2]
    exact (network.vertexLevel_edge_lipschitz e).1
  · rw [← hends.1, ← hends.2]
    exact (network.vertexLevel_edge_lipschitz e).2

/-- Telescoping the certificate along an arbitrary general walk. -/
theorem vertexLevel_end_le_start_add_length {network : SPNetwork}
    {u v : network.RealizedVertex} (walk : network.realize.simpleShadow.Walk u v) :
    network.vertexLevel v ≤ network.vertexLevel u + walk.length := by
  induction walk with
  | nil => simp
  | @cons u v w hadj walk ih =>
      have hstep := @vertexLevel_adjacent_le network u v hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Every graph walk from the realized source to sink has length at least recursive distance. -/
theorem distance_le_realize_walk_length (network : SPNetwork)
    (walk : network.realize.simpleShadow.Walk network.realize.source network.realize.sink) :
    network.distance ≤ walk.length := by
  simpa using network.vertexLevel_end_le_start_add_length walk

/-- The certificate and a shortest reachable walk give the graph-distance lower bound. -/
theorem distance_le_traditionalDistance_realize (network : SPNetwork) :
    network.distance ≤ traditionalDistance network.realize := by
  obtain ⟨walk, hwalk⟩ := network.realize_reachable.exists_walk_length_eq_dist
  change network.distance ≤
    network.realize.simpleShadow.dist network.realize.source network.realize.sink
  rw [← hwalk]
  exact network.distance_le_realize_walk_length walk

/-- Traditional walk distance of every structural realization equals its recursive evaluator. -/
theorem traditionalDistance_realize (network : SPNetwork) :
    traditionalDistance network.realize = network.distance :=
  Nat.le_antisymm network.traditionalDistance_realize_le
    network.distance_le_traditionalDistance_realize

/-- A unit edge has traditional graph distance one. -/
theorem traditionalDistance_one : traditionalDistance edge.realize = 1 := by
  rw [traditionalDistance_realize]
  rfl

/-- Two unit edges in series have traditional graph distance two. -/
theorem traditionalDistance_twoSeries :
    traditionalDistance (series edge edge).realize = 2 := by
  rw [traditionalDistance_realize]
  rfl

/-- Two unit edges in parallel have distance one, while retaining both physical edges. -/
theorem traditionalDistance_twoParallel :
    traditionalDistance (parallel edge edge).realize = 1 := by
  rw [traditionalDistance_realize]
  rfl

end SPNetwork

end SeriesParallel.MainText
