/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.GraphSemantics.Basic

/-!
# Traditional distance on a finite edge-indexed multigraph

Distance is defined using unrestricted walks in the simple undirected shadow.  This module has no
dependency on the recursive series--parallel syntax or any recursive evaluator.
-/

@[expose] public section

namespace SeriesParallel.MainText.GraphSemantics

/-- Traditional unweighted source-to-sink graph distance. -/
noncomputable def traditionalDistance (G : TwoTerminalMultigraph) : ℕ :=
  G.simpleShadow.dist G.source G.sink

/-- Any source-to-sink walk gives an upper bound on traditional distance. -/
theorem traditionalDistance_le_walk_length (G : TwoTerminalMultigraph)
    (walk : G.simpleShadow.Walk G.source G.sink) :
    traditionalDistance G ≤ walk.length :=
  SimpleGraph.dist_le walk

/-- A realized graph with a source-to-sink walk has genuinely reachable terminals. -/
theorem reachable_of_source_sink_walk (G : TwoTerminalMultigraph)
    (walk : G.simpleShadow.Walk G.source G.sink) :
    G.simpleShadow.Reachable G.source G.sink :=
  ⟨walk⟩

end SeriesParallel.MainText.GraphSemantics
