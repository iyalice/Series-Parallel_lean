/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.Networks

/-!
# Finite path semantics for two-terminal series--parallel networks

This module equips `SPNetwork` with its finite family of boundary-to-boundary paths.  Series
composition pairs paths, whereas parallel composition chooses one branch.  The weighted path
minimum identifies the recursive distance evaluator and gives the deterministic substitution
bound used by the first-moment argument.
-/

@[expose] public section

namespace SeriesParallel.MainText

namespace SPNetwork

/-- Boundary-to-boundary paths, defined recursively from the two-terminal syntax. -/
def Path : SPNetwork → Type
  | .edge => PUnit
  | .series left right => Path left × Path right
  | .parallel left right => Path left ⊕ Path right

namespace Path

/-- The unique path through one edge. -/
def edge : Path .edge := PUnit.unit

/-- Concatenate paths through two networks in series. -/
def series {left right : SPNetwork} (leftPath : Path left) (rightPath : Path right) :
    Path (.series left right) :=
  (leftPath, rightPath)

/-- Use a path through the left branch of a parallel network. -/
def parallelLeft {left right : SPNetwork} (path : Path left) : Path (.parallel left right) :=
  Sum.inl path

/-- Use a path through the right branch of a parallel network. -/
def parallelRight {left right : SPNetwork} (path : Path right) : Path (.parallel left right) :=
  Sum.inr path

end Path

instance instDecidableEqPath : (network : SPNetwork) → DecidableEq (Path network)
  | .edge => inferInstanceAs (DecidableEq PUnit)
  | .series left right =>
      letI := instDecidableEqPath left
      letI := instDecidableEqPath right
      inferInstanceAs (DecidableEq (Path left × Path right))
  | .parallel left right =>
      letI := instDecidableEqPath left
      letI := instDecidableEqPath right
      inferInstanceAs (DecidableEq (Path left ⊕ Path right))

instance instFintypePath : (network : SPNetwork) → Fintype (Path network)
  | .edge => inferInstanceAs (Fintype PUnit)
  | .series left right =>
      letI := instFintypePath left
      letI := instFintypePath right
      inferInstanceAs (Fintype (Path left × Path right))
  | .parallel left right =>
      letI := instFintypePath left
      letI := instFintypePath right
      inferInstanceAs (Fintype (Path left ⊕ Path right))

/-- A deterministic path, used only to witness that every path family is nonempty. -/
def anyPath : (network : SPNetwork) → Path network
  | .edge => Path.edge
  | .series left right => Path.series left.anyPath right.anyPath
  | .parallel left _ => Path.parallelLeft left.anyPath

instance instNonemptyPath (network : SPNetwork) : Nonempty (Path network) :=
  ⟨network.anyPath⟩

/-- Every finite two-terminal series--parallel network has a finite path family. -/
theorem finite_path_family (network : SPNetwork) : Finite (Path network) := inferInstance

/-- Every finite two-terminal series--parallel network has a boundary-to-boundary path. -/
theorem nonempty_path_family (network : SPNetwork) : Nonempty (Path network) := inferInstance

/-- Addresses of the leaf edges traversed by a path. -/
def Path.addresses : {network : SPNetwork} → Path network → List (List Bool)
  | .edge, _ => [[]]
  | .series _ _, (leftPath, rightPath) =>
      leftPath.addresses.map (false :: ·) ++ rightPath.addresses.map (true :: ·)
  | .parallel _ _, Sum.inl leftPath => leftPath.addresses.map (false :: ·)
  | .parallel _ _, Sum.inr rightPath => rightPath.addresses.map (true :: ·)

/-- Length of a path when an address `word` has the prescribed natural-number weight. -/
def Path.weightedLength : {network : SPNetwork} →
    Path network → (List Bool → ℕ) → ℕ
  | .edge, _, weight => weight []
  | .series _ _, (leftPath, rightPath), weight =>
      leftPath.weightedLength (fun word ↦ weight (false :: word)) +
        rightPath.weightedLength (fun word ↦ weight (true :: word))
  | .parallel _ _, Sum.inl leftPath, weight =>
      leftPath.weightedLength fun word ↦ weight (false :: word)
  | .parallel _ _, Sum.inr rightPath, weight =>
      rightPath.weightedLength fun word ↦ weight (true :: word)

/-- The ordinary number of unit edges traversed by a path. -/
def Path.length {network : SPNetwork} (path : Path network) : ℕ :=
  path.weightedLength fun _ ↦ 1

/-- Weighted length is the sum of the weights at the traversed leaf addresses. -/
theorem Path.weightedLength_eq_sum_addresses {network : SPNetwork} (path : Path network)
    (weight : List Bool → ℕ) :
    path.weightedLength weight = (path.addresses.map weight).sum := by
  induction network generalizing weight with
  | edge =>
      cases path
      rfl
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      simp only [weightedLength, addresses, List.map_append, List.sum_append]
      rw [ihLeft, ihRight]
      simp only [List.map_map, Function.comp_def]
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · simp only [weightedLength, addresses, ihLeft, List.map_map, Function.comp_def]
      · simp only [weightedLength, addresses, ihRight, List.map_map, Function.comp_def]

/-- Ordinary length is the number of leaf addresses traversed by the path. -/
theorem Path.length_eq_length_addresses {network : SPNetwork} (path : Path network) :
    path.length = path.addresses.length := by
  rw [Path.length, path.weightedLength_eq_sum_addresses]
  simp

/-- Recursive boundary distance for arbitrary natural-number leaf weights. -/
def weightedDistance : (network : SPNetwork) → (List Bool → ℕ) → ℕ
  | .edge, weight => weight []
  | .series left right, weight =>
      left.weightedDistance (fun word ↦ weight (false :: word)) +
        right.weightedDistance (fun word ↦ weight (true :: word))
  | .parallel left right, weight =>
      min (left.weightedDistance fun word ↦ weight (false :: word))
        (right.weightedDistance fun word ↦ weight (true :: word))

/-- Canonical weighted shortest path, with a deterministic preference for the left branch. -/
def shortestPathWith : (network : SPNetwork) → (List Bool → ℕ) → Path network
  | .edge, _ => Path.edge
  | .series left right, weight =>
      Path.series
        (left.shortestPathWith fun word ↦ weight (false :: word))
        (right.shortestPathWith fun word ↦ weight (true :: word))
  | .parallel left right, weight =>
      if left.weightedDistance (fun word ↦ weight (false :: word)) ≤
          right.weightedDistance (fun word ↦ weight (true :: word)) then
        Path.parallelLeft (left.shortestPathWith fun word ↦ weight (false :: word))
      else
        Path.parallelRight (right.shortestPathWith fun word ↦ weight (true :: word))

/-- The canonical weighted shortest path attains the recursive weighted distance. -/
theorem weightedLength_shortestPathWith (network : SPNetwork) (weight : List Bool → ℕ) :
    (network.shortestPathWith weight).weightedLength weight =
      network.weightedDistance weight := by
  induction network generalizing weight with
  | edge => rfl
  | series left right ihLeft ihRight =>
      simp only [shortestPathWith, Path.series, Path.weightedLength, weightedDistance]
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      by_cases hleft :
          left.weightedDistance (fun word ↦ weight (false :: word)) ≤
            right.weightedDistance (fun word ↦ weight (true :: word))
      · simp only [shortestPathWith, hleft, if_pos, Path.parallelLeft,
          Path.weightedLength, weightedDistance]
        rw [ihLeft, min_eq_left hleft]
      · have hright :
            right.weightedDistance (fun word ↦ weight (true :: word)) ≤
              left.weightedDistance (fun word ↦ weight (false :: word)) :=
          Nat.le_of_lt (Nat.lt_of_not_ge hleft)
        simp only [shortestPathWith, hleft, if_false, Path.parallelRight,
          Path.weightedLength, weightedDistance]
        rw [ihRight, min_eq_right hright]

/-- Every path has weighted length at least the recursive weighted distance. -/
theorem weightedDistance_le_weightedLength {network : SPNetwork} (path : Path network)
    (weight : List Bool → ℕ) : network.weightedDistance weight ≤ path.weightedLength weight := by
  induction network generalizing weight with
  | edge =>
      cases path
      exact le_rfl
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      exact Nat.add_le_add (ihLeft leftPath _) (ihRight rightPath _)
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · exact (min_le_left _ _).trans (ihLeft leftPath _)
      · exact (min_le_right _ _).trans (ihRight rightPath _)

/-- The canonical weighted path is a minimum among the finite path family. -/
theorem shortestPathWith_minimal (network : SPNetwork) (weight : List Bool → ℕ)
    (path : Path network) :
    (network.shortestPathWith weight).weightedLength weight ≤ path.weightedLength weight := by
  rw [weightedLength_shortestPathWith]
  exact weightedDistance_le_weightedLength path weight

/-- The unweighted recursive distance is weighted distance with every leaf weight equal to one. -/
theorem weightedDistance_one_eq_distance (network : SPNetwork) :
    network.weightedDistance (fun _ ↦ 1) = network.distance := by
  induction network with
  | edge => rfl
  | series left right ihLeft ihRight =>
      simp only [weightedDistance, distance]
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      simp only [weightedDistance, distance]
      rw [ihLeft, ihRight]

/-- The canonical shortest path for unit leaf weights. -/
def shortestPath (network : SPNetwork) : Path network :=
  network.shortestPathWith fun _ ↦ 1

/-- The canonical shortest path has length equal to `SPNetwork.distance`. -/
@[simp]
theorem length_shortestPath (network : SPNetwork) :
    network.shortestPath.length = network.distance := by
  rw [shortestPath, Path.length, weightedLength_shortestPathWith,
    weightedDistance_one_eq_distance]

/-- The canonical shortest path traverses exactly `distance` template leaves. -/
@[simp]
theorem length_addresses_shortestPath (network : SPNetwork) :
    network.shortestPath.addresses.length = network.distance := by
  rw [← Path.length_eq_length_addresses, length_shortestPath]

/-- `SPNetwork.distance` is a lower bound for the length of every path. -/
theorem distance_le_path_length {network : SPNetwork} (path : Path network) :
    network.distance ≤ path.length := by
  rw [← weightedDistance_one_eq_distance, Path.length]
  exact weightedDistance_le_weightedLength path (fun _ ↦ 1)

/-- The canonical path realizes the minimum of all boundary-to-boundary path lengths. -/
theorem shortestPath_minimal (network : SPNetwork) (path : Path network) :
    network.shortestPath.length ≤ path.length := by
  rw [length_shortestPath]
  exact distance_le_path_length path

/-- The finite universal path family is nonempty as a `Finset`. -/
theorem univ_paths_nonempty (network : SPNetwork) :
    (Finset.univ : Finset (Path network)).Nonempty :=
  ⟨network.anyPath, Finset.mem_univ _⟩

/-- Minimum weighted length over the complete finite path family. -/
def minimumWeightedPathLength (network : SPNetwork) (weight : List Bool → ℕ) : ℕ :=
  (Finset.univ : Finset (Path network)).inf' network.univ_paths_nonempty
    (fun path ↦ path.weightedLength weight)

/-- The recursive weighted evaluator is exactly the finite path minimum. -/
theorem weightedDistance_eq_minimumWeightedPathLength (network : SPNetwork)
    (weight : List Bool → ℕ) :
    network.weightedDistance weight = network.minimumWeightedPathLength weight := by
  apply le_antisymm
  · apply Finset.le_inf' network.univ_paths_nonempty
    intro path _
    exact weightedDistance_le_weightedLength path weight
  · calc
      network.minimumWeightedPathLength weight ≤
          (network.shortestPathWith weight).weightedLength weight := by
        exact Finset.inf'_le _ (Finset.mem_univ _)
      _ = network.weightedDistance weight :=
        weightedLength_shortestPathWith network weight

/-- `SPNetwork.distance` is exactly the minimum of the finite path-length family. -/
theorem distance_eq_minimumPathLength (network : SPNetwork) :
    network.distance = network.minimumWeightedPathLength (fun _ ↦ 1) := by
  rw [← weightedDistance_eq_minimumWeightedPathLength,
    weightedDistance_one_eq_distance]

/-- Replace every leaf traversed by a template path by a chosen path in its replacement. -/
def Path.substitute : {network : SPNetwork} → (path : Path network) →
    (replacement : List Bool → SPNetwork) →
    ((word : List Bool) → Path (replacement word)) → Path (network.substitute replacement)
  | .edge, _, _, replacementPath => replacementPath []
  | .series _ _, (leftPath, rightPath), replacement, replacementPath =>
      (leftPath.substitute (fun word ↦ replacement (false :: word))
          (fun word ↦ replacementPath (false :: word)),
        rightPath.substitute (fun word ↦ replacement (true :: word))
          (fun word ↦ replacementPath (true :: word)))
  | .parallel _ _, Sum.inl leftPath, replacement, replacementPath =>
      Sum.inl <| leftPath.substitute (fun word ↦ replacement (false :: word))
        (fun word ↦ replacementPath (false :: word))
  | .parallel _ _, Sum.inr rightPath, replacement, replacementPath =>
      Sum.inr <| rightPath.substitute (fun word ↦ replacement (true :: word))
        (fun word ↦ replacementPath (true :: word))

/-- Substituting chosen path witnesses turns template weighted length into ordinary length. -/
theorem Path.length_substitute {network : SPNetwork} (path : Path network)
    (replacement : List Bool → SPNetwork)
    (replacementPath : (word : List Bool) → Path (replacement word)) :
    (path.substitute replacement replacementPath).length =
      path.weightedLength (fun word ↦ (replacementPath word).length) := by
  induction network generalizing replacement with
  | edge =>
      cases path
      rfl
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      change
        (leftPath.substitute (fun word ↦ replacement (false :: word))
              (fun word ↦ replacementPath (false :: word))).length +
            (rightPath.substitute (fun word ↦ replacement (true :: word))
              (fun word ↦ replacementPath (true :: word))).length =
          leftPath.weightedLength
              (fun word ↦ (replacementPath (false :: word)).length) +
            rightPath.weightedLength
              (fun word ↦ (replacementPath (true :: word)).length)
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · change
          (leftPath.substitute (fun word ↦ replacement (false :: word))
              (fun word ↦ replacementPath (false :: word))).length =
            leftPath.weightedLength
              (fun word ↦ (replacementPath (false :: word)).length)
        rw [ihLeft]
      · change
          (rightPath.substitute (fun word ↦ replacement (true :: word))
              (fun word ↦ replacementPath (true :: word))).length =
            rightPath.weightedLength
              (fun word ↦ (replacementPath (true :: word)).length)
        rw [ihRight]

/-- Canonical concatenation of shortest paths in all replacements traversed by a template path. -/
def Path.substituteShortest {network : SPNetwork} (path : Path network)
    (replacement : List Bool → SPNetwork) : Path (network.substitute replacement) :=
  path.substitute replacement fun word ↦ (replacement word).shortestPath

/-- The canonical substituted witness has the expected replacement-weighted length. -/
theorem Path.length_substituteShortest {network : SPNetwork} (path : Path network)
    (replacement : List Bool → SPNetwork) :
    (path.substituteShortest replacement).length =
      path.weightedLength (fun word ↦ (replacement word).distance) := by
  rw [substituteShortest, length_substitute]
  congr 1
  funext word
  exact length_shortestPath (replacement word)

/-- Substitution evaluates distance by assigning each template leaf its replacement distance. -/
theorem distance_substitute_eq_weightedDistance (network : SPNetwork)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance =
      network.weightedDistance (fun word ↦ (replacement word).distance) := by
  induction network generalizing replacement with
  | edge => rfl
  | series left right ihLeft ihRight =>
      simp only [substitute_series, distance_series, weightedDistance]
      rw [ihLeft, ihRight]
  | parallel left right ihLeft ihRight =>
      simp only [substitute_parallel, distance_parallel, weightedDistance]
      rw [ihLeft, ihRight]

/-- Any template path bounds the distance after arbitrary leaf substitution. -/
theorem distance_substitute_le_weightedLength {network : SPNetwork} (path : Path network)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance ≤
      path.weightedLength (fun word ↦ (replacement word).distance) := by
  rw [distance_substitute_eq_weightedDistance]
  exact weightedDistance_le_weightedLength path _

/-- Address-sum form of the arbitrary-path substitution inequality. -/
theorem distance_substitute_le_path_sum {network : SPNetwork} (path : Path network)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance ≤
      (path.addresses.map fun word ↦ (replacement word).distance).sum := by
  rw [← Path.weightedLength_eq_sum_addresses]
  exact distance_substitute_le_weightedLength path replacement

/-- The canonical template shortest path gives the substitution bound used in refinement. -/
theorem distance_substitute_le_shortestPathWeightedLength (network : SPNetwork)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance ≤
      network.shortestPath.weightedLength (fun word ↦ (replacement word).distance) :=
  distance_substitute_le_weightedLength network.shortestPath replacement

/-- The path obtained by concatenating replacement shortest paths witnesses the upper bound. -/
theorem distance_substitute_le_substituteShortest_length {network : SPNetwork}
    (path : Path network) (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance ≤
      (path.substituteShortest replacement).length := by
  rw [Path.length_substituteShortest]
  exact distance_substitute_le_weightedLength path replacement

/-- Address-sum form of the deterministic shortest-path substitution inequality. -/
theorem distance_substitute_le_shortestPath_sum (network : SPNetwork)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance ≤
      (network.shortestPath.addresses.map fun word ↦ (replacement word).distance).sum := by
  exact distance_substitute_le_path_sum network.shortestPath replacement

/-- Exact finite-minimum form of the arbitrary substitution distance identity. -/
theorem distance_substitute_eq_minimumWeightedPathLength (network : SPNetwork)
    (replacement : List Bool → SPNetwork) :
    (network.substitute replacement).distance =
      network.minimumWeightedPathLength (fun word ↦ (replacement word).distance) := by
  rw [distance_substitute_eq_weightedDistance,
    weightedDistance_eq_minimumWeightedPathLength]

end SPNetwork

end SeriesParallel.MainText
