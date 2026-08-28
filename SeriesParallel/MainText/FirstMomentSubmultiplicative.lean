/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import SeriesParallel.MainText.FiniteFlows
import SeriesParallel.MainText.FirstMomentBounds
import SeriesParallel.MainText.MainTextStatementContract
import Mathlib.Analysis.Subadditive
import Mathlib.Probability.Independence.Integration

/-!
# First-moment submultiplicativity and its logarithmic rate

The deterministic input is leaf substitution.  A shortest path supplies the distance
coefficients, while the energy-minimizing unit flow supplies the resistance coefficients.
Both coefficient families depend only on the first `n` levels and hence are independent of the
depth-`n` descendant environments.  Integrating the substitution bounds gives the source
first-moment submultiplicativity inequality, from which Fekete's lemma supplies the canonical
logarithmic first-moment rate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology unitInterval

namespace SeriesParallel.MainText

/-- The lexicographically recursive list of all binary words of a fixed length. -/
private def levelWords : ℕ → List Word
  | 0 => [[]]
  | n + 1 =>
      (levelWords n).map (false :: ·) ++ (levelWords n).map (true :: ·)

private theorem mem_levelWords {n : ℕ} {word : Word} :
    word ∈ levelWords n ↔ word.length = n := by
  induction n generalizing word with
  | zero => simp [levelWords]
  | succ n ih =>
      cases word with
      | nil => simp [levelWords]
      | cons bit tail =>
          cases bit <;> simp [levelWords, ih]

private theorem levelWords_nodup (n : ℕ) : (levelWords n).Nodup := by
  induction n with
  | zero => simp [levelWords]
  | succ n ih =>
      rw [levelWords, List.nodup_append]
      have hfalseInjective : Function.Injective (false :: ·) := fun _ _ h ↦ by
        simpa using h
      have htrueInjective : Function.Injective (true :: ·) := fun _ _ h ↦ by
        simpa using h
      refine ⟨ih.map hfalseInjective, ih.map htrueInjective, ?_⟩
      intro leftWord hfalse rightWord htrue heq
      obtain ⟨left, -, hleft⟩ := List.mem_map.mp hfalse
      obtain ⟨right, -, hright⟩ := List.mem_map.mp htrue
      rw [← hleft, ← hright] at heq
      simp at heq

private theorem randomNetwork_leafAddresses (n : ℕ) (environment : Environment) :
    (randomNetwork n environment).leafAddresses = levelWords n := by
  induction n generalizing environment with
  | zero => rfl
  | succ n ih =>
      by_cases hroot : environment root
      · simp [randomNetwork, hroot, SPNetwork.leafAddresses, levelWords, ih]
      · simp [randomNetwork, hroot, SPNetwork.leafAddresses, levelWords, ih]

private theorem SPNetwork.Path.addresses_subset_leafAddresses
    {network : SPNetwork} (path : network.Path) :
    ∀ word ∈ path.addresses, word ∈ network.leafAddresses := by
  induction network with
  | edge =>
      cases path
      simp [SPNetwork.Path.addresses, SPNetwork.leafAddresses]
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      intro word hword
      simp only [SPNetwork.Path.addresses, SPNetwork.leafAddresses, List.mem_append,
        List.mem_map] at hword ⊢
      rcases hword with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩
      · exact Or.inl ⟨tail, ihLeft leftPath tail htail, rfl⟩
      · exact Or.inr ⟨tail, ihRight rightPath tail htail, rfl⟩
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · intro word hword
        simp only [SPNetwork.Path.addresses, List.mem_map] at hword
        obtain ⟨tail, htail, rfl⟩ := hword
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨tail, ihLeft leftPath tail htail, rfl⟩)
      · intro word hword
        simp only [SPNetwork.Path.addresses, List.mem_map] at hword
        obtain ⟨tail, htail, rfl⟩ := hword
        exact List.mem_append_right _
          (List.mem_map.mpr ⟨tail, ihRight rightPath tail htail, rfl⟩)

private theorem SPNetwork.Path.addresses_nodup
    {network : SPNetwork} (path : network.Path) : path.addresses.Nodup := by
  induction network with
  | edge =>
      cases path
      simp [SPNetwork.Path.addresses]
  | series left right ihLeft ihRight =>
      obtain ⟨leftPath, rightPath⟩ := path
      rw [SPNetwork.Path.addresses, List.nodup_append]
      have hfalseInjective : Function.Injective (false :: ·) := fun _ _ h ↦ by
        simpa using h
      have htrueInjective : Function.Injective (true :: ·) := fun _ _ h ↦ by
        simpa using h
      refine ⟨(ihLeft leftPath).map hfalseInjective,
        (ihRight rightPath).map htrueInjective, ?_⟩
      intro leftWord hfalse rightWord htrue heq
      obtain ⟨left, -, hleft⟩ := List.mem_map.mp hfalse
      obtain ⟨right, -, hright⟩ := List.mem_map.mp htrue
      rw [← hleft, ← hright] at heq
      simp at heq
  | parallel left right ihLeft ihRight =>
      rcases path with leftPath | rightPath
      · apply (ihLeft leftPath).map
        intro _ _ h
        simpa using h
      · apply (ihRight rightPath).map
        intro _ _ h
        simpa using h

/-- Prefix removal sends information above depth `n + 1` to information above depth `n`. -/
private theorem measurable_subtreeShift_finiteLevel (n : ℕ) (bit : Bool) :
    Measurable[finiteLevelSigma (n + 1), finiteLevelSigma n] (subtreeShift [bit]) := by
  apply Measurable.of_comap_le
  unfold finiteLevelSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun word ↦ ?_
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (coordinate (bit :: word.1)) inferInstance ≤ _
  let prefixed : {word : Word // word.length < n + 1} :=
    ⟨bit :: word.1, by simpa using Nat.succ_lt_succ word.2⟩
  exact le_iSup_of_le prefixed le_rfl

/-- `Z_n` is measurable using only the coordinates strictly above depth `n`. -/
theorem measurable_Z_finiteLevel (mode : Mode) (n : ℕ) :
    Measurable[finiteLevelSigma n] (Z mode n) := by
  induction n with
  | zero =>
      rw [show Z mode 0 = fun _ : Environment ↦ (1 : ℝ) by
        funext environment
        exact Z_zero mode environment]
      fun_prop
  | succ n ih =>
      have hleft : Measurable[finiteLevelSigma (n + 1)]
          (fun environment ↦ Z mode n (Environment.subtree [false] environment)) := by
        simpa only [Environment.subtree, Function.comp_def] using
          ih.comp (measurable_subtreeShift_finiteLevel n false)
      have hright : Measurable[finiteLevelSigma (n + 1)]
          (fun environment ↦ Z mode n (Environment.subtree [true] environment)) := by
        simpa only [Environment.subtree, Function.comp_def] using
          ih.comp (measurable_subtreeShift_finiteLevel n true)
      have hroot : Measurable[finiteLevelSigma (n + 1)] (coordinate root) :=
        measurable_coordinate_finiteLevel (by simp [root])
      have hrootSet : MeasurableSet[finiteLevelSigma (n + 1)]
          {environment : Environment | environment root = true} := by
        change MeasurableSet[finiteLevelSigma (n + 1)] (coordinate root ⁻¹' {true})
        exact hroot (measurableSet_singleton true)
      cases mode with
      | distance =>
          rw [show Z .distance (n + 1) = fun environment ↦
              if environment root then
                Z .distance n (Environment.subtree [false] environment) +
                  Z .distance n (Environment.subtree [true] environment)
              else
                min (Z .distance n (Environment.subtree [false] environment))
                  (Z .distance n (Environment.subtree [true] environment)) by
            funext environment
            simp only [Z, distanceValue_succ, Nat.cast_ite, Nat.cast_add,
              Nat.cast_min]]
          exact Measurable.ite hrootSet (hleft.add hright) (hleft.min hright)
      | resistance =>
          rw [show Z .resistance (n + 1) = fun environment ↦
              if environment root then
                Z .resistance n (Environment.subtree [false] environment) +
                  Z .resistance n (Environment.subtree [true] environment)
              else
                Z .resistance n (Environment.subtree [false] environment) *
                    Z .resistance n (Environment.subtree [true] environment) /
                  (Z .resistance n (Environment.subtree [false] environment) +
                    Z .resistance n (Environment.subtree [true] environment)) by
            funext environment
            exact resistanceValue_succ n environment]
          exact Measurable.ite hrootSet (hleft.add hright)
            ((hleft.mul hright).div (hleft.add hright))

/-- Indicator coefficients of the canonical shortest path through the depth-`n` template. -/
private noncomputable def distanceCoefficient : ℕ → Environment → Word → ℝ
  | 0, _, [] => 1
  | 0, _, _ :: _ => 0
  | _ + 1, _, [] => 0
  | n + 1, environment, false :: tail =>
      let left := Environment.subtree [false] environment
      let right := Environment.subtree [true] environment
      if environment root then distanceCoefficient n left tail
      else if Z .distance n left ≤ Z .distance n right then
        distanceCoefficient n left tail
      else 0
  | n + 1, environment, true :: tail =>
      let left := Environment.subtree [false] environment
      let right := Environment.subtree [true] environment
      if environment root then distanceCoefficient n right tail
      else if Z .distance n left ≤ Z .distance n right then 0
      else distanceCoefficient n right tail

/-- Squared leaf-current coefficients of the canonical minimizing unit flow. -/
private noncomputable def resistanceCoefficient : ℕ → Environment → Word → ℝ
  | 0, _, [] => 1
  | 0, _, _ :: _ => 0
  | _ + 1, _, [] => 0
  | n + 1, environment, false :: tail =>
      let left := Environment.subtree [false] environment
      let right := Environment.subtree [true] environment
      if environment root then resistanceCoefficient n left tail
      else
        (Z .resistance n right / (Z .resistance n left + Z .resistance n right)) ^ 2 *
          resistanceCoefficient n left tail
  | n + 1, environment, true :: tail =>
      let left := Environment.subtree [false] environment
      let right := Environment.subtree [true] environment
      if environment root then resistanceCoefficient n right tail
      else
        (1 - Z .resistance n right /
          (Z .resistance n left + Z .resistance n right)) ^ 2 *
            resistanceCoefficient n right tail

private theorem measurable_rootSet_finiteLevel (n : ℕ) :
    MeasurableSet[finiteLevelSigma (n + 1)]
      {environment : Environment | environment root = true} := by
  change MeasurableSet[finiteLevelSigma (n + 1)] (coordinate root ⁻¹' {true})
  exact measurable_coordinate_finiteLevel (by simp [root]) (measurableSet_singleton true)

private theorem measurable_distanceCoefficient (n : ℕ) (word : Word) :
    Measurable[finiteLevelSigma n] (fun environment ↦
      distanceCoefficient n environment word) := by
  induction n generalizing word with
  | zero =>
      cases word <;> simp only [distanceCoefficient] <;> fun_prop
  | succ n ih =>
      cases word with
      | nil => simp only [distanceCoefficient]; fun_prop
      | cons bit tail =>
          have hleftCoeff : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              distanceCoefficient n (Environment.subtree [false] environment) tail) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (ih tail).comp (measurable_subtreeShift_finiteLevel n false)
          have hrightCoeff : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              distanceCoefficient n (Environment.subtree [true] environment) tail) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (ih tail).comp (measurable_subtreeShift_finiteLevel n true)
          have hleftZ : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              Z .distance n (Environment.subtree [false] environment)) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (measurable_Z_finiteLevel .distance n).comp
                (measurable_subtreeShift_finiteLevel n false)
          have hrightZ : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              Z .distance n (Environment.subtree [true] environment)) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (measurable_Z_finiteLevel .distance n).comp
                (measurable_subtreeShift_finiteLevel n true)
          have hchoice : MeasurableSet[finiteLevelSigma (n + 1)] {environment |
              Z .distance n (Environment.subtree [false] environment) ≤
                Z .distance n (Environment.subtree [true] environment)} :=
            measurableSet_le hleftZ hrightZ
          cases bit with
          | false =>
              exact Measurable.ite (measurable_rootSet_finiteLevel n) hleftCoeff
                (Measurable.ite hchoice hleftCoeff measurable_const)
          | true =>
              exact Measurable.ite (measurable_rootSet_finiteLevel n) hrightCoeff
                (Measurable.ite hchoice measurable_const hrightCoeff)

private theorem measurable_resistanceCoefficient (n : ℕ) (word : Word) :
    Measurable[finiteLevelSigma n] (fun environment ↦
      resistanceCoefficient n environment word) := by
  induction n generalizing word with
  | zero =>
      cases word <;> simp only [resistanceCoefficient] <;> fun_prop
  | succ n ih =>
      cases word with
      | nil => simp only [resistanceCoefficient]; fun_prop
      | cons bit tail =>
          have hleftCoeff : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              resistanceCoefficient n (Environment.subtree [false] environment) tail) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (ih tail).comp (measurable_subtreeShift_finiteLevel n false)
          have hrightCoeff : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              resistanceCoefficient n (Environment.subtree [true] environment) tail) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (ih tail).comp (measurable_subtreeShift_finiteLevel n true)
          have hleftZ : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              Z .resistance n (Environment.subtree [false] environment)) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (measurable_Z_finiteLevel .resistance n).comp
                (measurable_subtreeShift_finiteLevel n false)
          have hrightZ : Measurable[finiteLevelSigma (n + 1)] (fun environment ↦
              Z .resistance n (Environment.subtree [true] environment)) := by
            simpa only [Environment.subtree, Function.comp_def] using
              (measurable_Z_finiteLevel .resistance n).comp
                (measurable_subtreeShift_finiteLevel n true)
          have hcurrent := hrightZ.div (hleftZ.add hrightZ)
          cases bit with
          | false =>
              exact Measurable.ite (measurable_rootSet_finiteLevel n) hleftCoeff
                ((hcurrent.pow_const 2).mul hleftCoeff)
          | true =>
              exact Measurable.ite (measurable_rootSet_finiteLevel n) hrightCoeff
                ((measurable_const.sub hcurrent).pow_const 2 |>.mul hrightCoeff)

private theorem distanceCoefficient_eq_shortestPath (n : ℕ) (environment : Environment)
    (word : Word) :
    distanceCoefficient n environment word =
      if word ∈ (randomNetwork n environment).shortestPath.addresses then 1 else 0 := by
  induction n generalizing environment word with
  | zero =>
      cases word <;>
        simp [distanceCoefficient, SPNetwork.shortestPath,
          SPNetwork.shortestPathWith, SPNetwork.Path.addresses]
  | succ n ih =>
      cases word with
      | nil =>
          simp only [distanceCoefficient]
          rw [if_neg]
          intro hnil
          have hleaf := SPNetwork.Path.addresses_subset_leafAddresses
            (randomNetwork (n + 1) environment).shortestPath [] hnil
          rw [randomNetwork_leafAddresses] at hleaf
          have hlength := mem_levelWords.mp hleaf
          simp at hlength
      | cons bit tail =>
          cases hroot : environment root with
          | true =>
              rw [randomNetwork_succ_series hroot]
              cases bit <;>
                simp [distanceCoefficient, hroot, SPNetwork.shortestPath,
                  SPNetwork.shortestPathWith, SPNetwork.Path.addresses,
                  SPNetwork.Path.series, ih]
          | false =>
            have hcast :
                (Z .distance n (Environment.subtree [false] environment) ≤
                    Z .distance n (Environment.subtree [true] environment)) ↔
                  (randomNetwork n (Environment.subtree [false] environment)).distance ≤
                    (randomNetwork n
                      (Environment.subtree [true] environment)).distance := by
                simp only [Z, distanceValue]
                exact_mod_cast Iff.rfl
            by_cases hchoice :
                Z .distance n (Environment.subtree [false] environment) ≤
                  Z .distance n (Environment.subtree [true] environment)
            · have hnetworkChoice := hcast.mp hchoice
              rw [randomNetwork_succ_parallel hroot]
              cases bit <;>
                simp [distanceCoefficient, hroot, SPNetwork.shortestPath,
                  SPNetwork.shortestPathWith, SPNetwork.Path.addresses,
                  SPNetwork.Path.parallelLeft,
                  SPNetwork.weightedDistance_one_eq_distance, hchoice, hnetworkChoice, ih]
            · have hnetworkChoice : ¬
                  (randomNetwork n
                        (Environment.subtree [false] environment)).distance ≤
                    (randomNetwork n
                      (Environment.subtree [true] environment)).distance :=
                fun h ↦ hchoice (hcast.mpr h)
              rw [randomNetwork_succ_parallel hroot]
              cases bit <;>
                simp [distanceCoefficient, hroot, SPNetwork.shortestPath,
                  SPNetwork.shortestPathWith, SPNetwork.Path.addresses,
                  SPNetwork.Path.parallelRight,
                  SPNetwork.weightedDistance_one_eq_distance, hchoice, hnetworkChoice, ih]

private theorem resistanceCoefficient_eq_current_sq (n : ℕ) (environment : Environment)
    (word : Word) :
    resistanceCoefficient n environment word =
      ((SPNetwork.optimalFlow (randomNetwork n environment)).currentAt word) ^ 2 := by
  induction n generalizing environment word with
  | zero =>
      cases word <;>
        simp [resistanceCoefficient, SPNetwork.optimalFlow,
          SPNetwork.Flow.currentAt]
  | succ n ih =>
      cases word with
      | nil =>
          cases hroot : environment root with
          | false =>
              rw [randomNetwork_succ_parallel hroot]
              simp [resistanceCoefficient, SPNetwork.Flow.currentAt]
          | true =>
              rw [randomNetwork_succ_series hroot]
              simp [resistanceCoefficient, SPNetwork.Flow.currentAt]
      | cons bit tail =>
          cases hroot : environment root with
          | true =>
              rw [randomNetwork_succ_series hroot]
              cases bit <;>
                simp [resistanceCoefficient, hroot, SPNetwork.optimalFlow,
                  SPNetwork.Flow.currentAt, ih]
          | false =>
              rw [randomNetwork_succ_parallel hroot]
              cases bit <;>
                simp only [resistanceCoefficient, hroot,
                  SPNetwork.optimalFlow, SPNetwork.Flow.currentAt, Z, resistanceValue]
              · rw [ih]
                simp
                ring
              · rw [ih]
                simp
                ring

private theorem shortestPath_toFinset_subset_levelWords
    (n : ℕ) (environment : Environment) :
    (randomNetwork n environment).shortestPath.addresses.toFinset ⊆
      (levelWords n).toFinset := by
  intro word hword
  simp only [List.mem_toFinset] at hword ⊢
  rw [← randomNetwork_leafAddresses n environment]
  exact SPNetwork.Path.addresses_subset_leafAddresses _ word hword

private theorem levelWords_filter_shortestPath (n : ℕ) (environment : Environment) :
    (levelWords n).toFinset.filter
        (fun word ↦ word ∈ (randomNetwork n environment).shortestPath.addresses) =
      (randomNetwork n environment).shortestPath.addresses.toFinset := by
  ext word
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · exact fun h ↦ h.2
  · intro h
    have huniverse : word ∈ (levelWords n).toFinset :=
      shortestPath_toFinset_subset_levelWords n environment
        (by simpa only [List.mem_toFinset] using h)
    exact ⟨by simpa only [List.mem_toFinset] using huniverse, h⟩

private theorem distanceCoefficient_sum_mul (n : ℕ) (environment : Environment)
    (weight : Word → ℝ) :
    ∑ word ∈ (levelWords n).toFinset,
        distanceCoefficient n environment word * weight word =
      ((randomNetwork n environment).shortestPath.addresses.map weight).sum := by
  let path := (randomNetwork n environment).shortestPath
  calc
    ∑ word ∈ (levelWords n).toFinset,
        distanceCoefficient n environment word * weight word =
        ∑ word ∈ (levelWords n).toFinset,
          if word ∈ path.addresses then weight word else 0 := by
      apply Finset.sum_congr rfl
      intro word _
      rw [distanceCoefficient_eq_shortestPath]
      split <;> simp_all only [one_mul, zero_mul]
    _ = ∑ word ∈ (levelWords n).toFinset.filter
          (fun word ↦ word ∈ path.addresses), weight word := by
      rw [Finset.sum_filter]
    _ = ∑ word ∈ path.addresses.toFinset, weight word := by
      rw [show (levelWords n).toFinset.filter (fun word ↦ word ∈ path.addresses) =
        path.addresses.toFinset by
          exact levelWords_filter_shortestPath n environment]
    _ = (path.addresses.map weight).sum :=
      List.sum_toFinset weight (SPNetwork.Path.addresses_nodup path)

private theorem resistanceCoefficient_sum_mul (n : ℕ) (environment : Environment)
    (weight : Word → ℝ) :
    ∑ word ∈ (levelWords n).toFinset,
        resistanceCoefficient n environment word * weight word =
      (SPNetwork.optimalFlow (randomNetwork n environment)).energy weight := by
  rw [SPNetwork.Flow.energy_eq_sum, randomNetwork_leafAddresses]
  rw [← List.sum_toFinset
    (fun word ↦
      (SPNetwork.optimalFlow (randomNetwork n environment)).currentAt word ^ 2 *
        weight word)
    (levelWords_nodup n)]
  apply Finset.sum_congr rfl
  intro word _
  rw [resistanceCoefficient_eq_current_sq]

/-- The fixed-level coefficient family, shortest-path or squared-current according to the mode. -/
private noncomputable def refinementCoefficient
    (mode : Mode) (n : ℕ) (environment : Environment) (word : Word) : ℝ :=
  match mode with
  | .distance => distanceCoefficient n environment word
  | .resistance => resistanceCoefficient n environment word

private theorem measurable_refinementCoefficient (mode : Mode) (n : ℕ) (word : Word) :
    Measurable[finiteLevelSigma n] (fun environment ↦
      refinementCoefficient mode n environment word) := by
  cases mode with
  | distance => exact measurable_distanceCoefficient n word
  | resistance => exact measurable_resistanceCoefficient n word

private theorem refinementCoefficient_nonneg
    (mode : Mode) (n : ℕ) (environment : Environment) (word : Word) :
    0 ≤ refinementCoefficient mode n environment word := by
  cases mode with
  | distance =>
      rw [refinementCoefficient, distanceCoefficient_eq_shortestPath]
      split <;> norm_num
  | resistance =>
      rw [refinementCoefficient, resistanceCoefficient_eq_current_sq]
      exact sq_nonneg _

private theorem refinementCoefficient_sum (mode : Mode) (n : ℕ)
    (environment : Environment) :
    ∑ word ∈ (levelWords n).toFinset,
        refinementCoefficient mode n environment word = Z mode n environment := by
  cases mode with
  | distance =>
      have hcost := distanceCoefficient_sum_mul n environment (fun _ ↦ 1)
      simp only [refinementCoefficient, mul_one] at hcost ⊢
      calc
        ∑ word ∈ (levelWords n).toFinset, distanceCoefficient n environment word =
            ((randomNetwork n environment).shortestPath.addresses.map
              (fun _ ↦ (1 : ℝ))).sum := hcost
        _ = ((randomNetwork n environment).shortestPath.addresses.length : ℝ) := by
          simp
        _ = ((randomNetwork n environment).distance : ℝ) := by
          rw [SPNetwork.length_addresses_shortestPath]
        _ = Z .distance n environment := rfl
  | resistance =>
      have hcost := resistanceCoefficient_sum_mul n environment (fun _ ↦ 1)
      simp only [refinementCoefficient, mul_one] at hcost ⊢
      calc
        ∑ word ∈ (levelWords n).toFinset, resistanceCoefficient n environment word =
            (SPNetwork.optimalFlow (randomNetwork n environment)).energy
              (fun _ ↦ 1) := hcost
        _ = (SPNetwork.optimalFlow (randomNetwork n environment)).unitEnergy := rfl
        _ = (randomNetwork n environment).resistance :=
          SPNetwork.optimalFlow_unitEnergy _
        _ = Z .resistance n environment := rfl

private theorem distance_refinement_le_coefficient_sum
    (n r : ℕ) (environment : Environment) :
    Z .distance (n + r) environment ≤
      ∑ word ∈ (levelWords n).toFinset,
        distanceCoefficient n environment word *
          Z .distance r (Environment.subtree word environment) := by
  let replacement : Word → SPNetwork := fun word ↦
    randomNetwork r (Environment.subtree word environment)
  have hbound := SPNetwork.distance_substitute_le_shortestPath_sum
    (randomNetwork n environment) replacement
  have hboundReal :
      (((randomNetwork n environment).substitute replacement).distance : ℝ) ≤
        (((randomNetwork n environment).shortestPath.addresses.map
          (fun word ↦ (replacement word).distance)).sum : ℕ) := by
    exact_mod_cast hbound
  calc
    Z .distance (n + r) environment =
        (((randomNetwork n environment).substitute replacement).distance : ℝ) := by
      rw [Z, distanceValue, randomNetwork_refinement]
    _ ≤ (((randomNetwork n environment).shortestPath.addresses.map
          (fun word ↦ (replacement word).distance)).sum : ℕ) := hboundReal
    _ = ((randomNetwork n environment).shortestPath.addresses.map
          (fun word ↦ ((replacement word).distance : ℝ))).sum := by
      induction (randomNetwork n environment).shortestPath.addresses with
      | nil => simp
      | cons word words ih => simp [ih]
    _ = ∑ word ∈ (levelWords n).toFinset,
          distanceCoefficient n environment word *
            ((replacement word).distance : ℝ) :=
      (distanceCoefficient_sum_mul n environment
        (fun word ↦ ((replacement word).distance : ℝ))).symm
    _ = ∑ word ∈ (levelWords n).toFinset,
          distanceCoefficient n environment word *
            Z .distance r (Environment.subtree word environment) := by
      rfl

private theorem resistance_refinement_le_coefficient_sum
    (n r : ℕ) (environment : Environment) :
    Z .resistance (n + r) environment ≤
      ∑ word ∈ (levelWords n).toFinset,
        resistanceCoefficient n environment word *
          Z .resistance r (Environment.subtree word environment) := by
  let replacement : Word → SPNetwork := fun word ↦
    randomNetwork r (Environment.subtree word environment)
  have hbound := SPNetwork.resistance_substitute_le_optimal_energy
    (randomNetwork n environment) replacement
  calc
    Z .resistance (n + r) environment =
        ((randomNetwork n environment).substitute replacement).resistance := by
      rw [Z, resistanceValue, randomNetwork_refinement]
    _ ≤ (SPNetwork.optimalFlow (randomNetwork n environment)).energy
          (fun word ↦ (replacement word).resistance) := hbound
    _ = ∑ word ∈ (levelWords n).toFinset,
          resistanceCoefficient n environment word *
            (replacement word).resistance :=
      (resistanceCoefficient_sum_mul n environment
        (fun word ↦ (replacement word).resistance)).symm
    _ = ∑ word ∈ (levelWords n).toFinset,
          resistanceCoefficient n environment word *
            Z .resistance r (Environment.subtree word environment) := by
      rfl

private theorem Z_refinement_le_coefficient_sum
    (mode : Mode) (n r : ℕ) (environment : Environment) :
    Z mode (n + r) environment ≤
      ∑ word ∈ (levelWords n).toFinset,
        refinementCoefficient mode n environment word *
          Z mode r (Environment.subtree word environment) := by
  cases mode with
  | distance => exact distance_refinement_le_coefficient_sum n r environment
  | resistance => exact resistance_refinement_le_coefficient_sum n r environment

private theorem refinementCoefficient_le_two_pow
    (mode : Mode) (n : ℕ) (environment : Environment) {word : Word}
    (hword : word ∈ (levelWords n).toFinset) :
    refinementCoefficient mode n environment word ≤ (2 : ℝ) ^ n := by
  calc
    refinementCoefficient mode n environment word ≤
        ∑ other ∈ (levelWords n).toFinset,
          refinementCoefficient mode n environment other :=
      Finset.single_le_sum
        (fun other _ ↦ refinementCoefficient_nonneg mode n environment other) hword
    _ = Z mode n environment := refinementCoefficient_sum mode n environment
    _ ≤ (2 : ℝ) ^ n := Z_le_two_pow mode n environment

private theorem integrable_refinementCoefficient
    (p : unitInterval) (mode : Mode) (n : ℕ) {word : Word}
    (hword : word ∈ (levelWords n).toFinset) :
    Integrable (fun environment ↦ refinementCoefficient mode n environment word)
      (environmentMeasure p) := by
  have hmeas : Measurable
      (fun environment ↦ refinementCoefficient mode n environment word) :=
    (measurable_refinementCoefficient mode n word).mono (finiteLevelSigma_le n) le_rfl
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((2 : ℝ) ^ n)
  filter_upwards with environment
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact refinementCoefficient_le_two_pow mode n environment hword
  · exact refinementCoefficient_nonneg mode n environment word

private theorem integrable_Z_subtree
    (p : unitInterval) (mode : Mode) (r : ℕ) (word : Word) :
    Integrable (fun environment ↦ Z mode r (Environment.subtree word environment))
      (environmentMeasure p) := by
  simpa only [Environment.subtree, Function.comp_def] using
    (subtreeShift_measurePreserving p word).integrable_comp_of_integrable
      (integrable_Z p mode r)

private theorem integral_Z_subtree
    (p : unitInterval) (mode : Mode) (r : ℕ) (word : Word) :
    (∫ environment, Z mode r (Environment.subtree word environment)
        ∂environmentMeasure p) = firstMoment p mode r := by
  simpa only [firstMoment, Environment.subtree, Function.comp_def] using
    (subtreeShift_hasLaw p word).integral_comp
      (measurable_Z mode r).aestronglyMeasurable

private theorem past_descendant_comp_indep
    (p : unitInterval) (n : ℕ) (past : Environment → ℝ)
    (future : (Level n → Environment) → ℝ)
    (hpast : Measurable[finiteLevelSigma n] past) (hfuture : Measurable future) :
    past ⟂ᵢ[environmentMeasure p] (future ∘ descendantFamily n) := by
  rw [IndepFun_iff_Indep]
  apply indep_of_indep_of_le
    (finiteLevelSigma_indep_descendantFamily p n) hpast.comap_le
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hfuture.comap_le

private theorem refinementCoefficient_subtree_indep
    (p : unitInterval) (mode : Mode) (n r : ℕ) {word : Word}
    (hword : word ∈ (levelWords n).toFinset) :
    (fun environment ↦ refinementCoefficient mode n environment word)
      ⟂ᵢ[environmentMeasure p]
    (fun environment ↦ Z mode r (Environment.subtree word environment)) := by
  have hlength : word.length = n :=
    mem_levelWords.mp (by simpa only [List.mem_toFinset] using hword)
  let vertex : Level n := ⟨word, hlength⟩
  let future : (Level n → Environment) → ℝ := fun family ↦ Z mode r (family vertex)
  have hfuture : Measurable future :=
    (measurable_Z mode r).comp (measurable_pi_apply vertex)
  have hindep := past_descendant_comp_indep p n
    (fun environment ↦ refinementCoefficient mode n environment word) future
    (measurable_refinementCoefficient mode n word) hfuture
  simpa only [future, Function.comp_def, descendantFamily, Environment.subtree, vertex] using
    hindep

private theorem integrable_refinement_product
    (p : unitInterval) (mode : Mode) (n r : ℕ) {word : Word}
    (hword : word ∈ (levelWords n).toFinset) :
    Integrable
      (fun environment ↦ refinementCoefficient mode n environment word *
        Z mode r (Environment.subtree word environment))
      (environmentMeasure p) := by
  have hindep := refinementCoefficient_subtree_indep p mode n r hword
  change Integrable
    ((fun environment ↦ refinementCoefficient mode n environment word) *
      fun environment ↦ Z mode r (Environment.subtree word environment))
    (environmentMeasure p)
  exact hindep.integrable_mul
    (integrable_refinementCoefficient p mode n hword)
    (integrable_Z_subtree p mode r word)

private theorem integral_refinement_product
    (p : unitInterval) (mode : Mode) (n r : ℕ) {word : Word}
    (hword : word ∈ (levelWords n).toFinset) :
    (∫ environment, refinementCoefficient mode n environment word *
        Z mode r (Environment.subtree word environment) ∂environmentMeasure p) =
      (∫ environment, refinementCoefficient mode n environment word
        ∂environmentMeasure p) * firstMoment p mode r := by
  have hindep := refinementCoefficient_subtree_indep p mode n r hword
  calc
    (∫ environment, refinementCoefficient mode n environment word *
        Z mode r (Environment.subtree word environment) ∂environmentMeasure p) =
        (∫ environment, refinementCoefficient mode n environment word
          ∂environmentMeasure p) *
          ∫ environment, Z mode r (Environment.subtree word environment)
            ∂environmentMeasure p :=
      hindep.integral_fun_mul_eq_mul_integral
        (integrable_refinementCoefficient p mode n hword).aestronglyMeasurable
        (integrable_Z_subtree p mode r word).aestronglyMeasurable
    _ = (∫ environment, refinementCoefficient mode n environment word
          ∂environmentMeasure p) * firstMoment p mode r := by
      rw [integral_Z_subtree p mode r word]

/-- First moments are submultiplicative under deterministic leaf refinement. -/
theorem firstMoment_submultiplicative
    (p : unitInterval) (mode : Mode) (n r : ℕ) :
    firstMoment p mode (n + r) ≤
      firstMoment p mode n * firstMoment p mode r := by
  let words := (levelWords n).toFinset
  have hsumIntegrable : Integrable
      (fun environment ↦
        ∑ word ∈ words,
          refinementCoefficient mode n environment word *
            Z mode r (Environment.subtree word environment))
      (environmentMeasure p) := by
    apply integrable_finsetSum
    intro word hword
    exact integrable_refinement_product p mode n r hword
  calc
    firstMoment p mode (n + r) =
        ∫ environment, Z mode (n + r) environment ∂environmentMeasure p := rfl
    _ ≤ ∫ environment,
          ∑ word ∈ words,
            refinementCoefficient mode n environment word *
              Z mode r (Environment.subtree word environment)
          ∂environmentMeasure p := by
      apply integral_mono (integrable_Z p mode (n + r)) hsumIntegrable
      intro environment
      simpa only [words] using
        Z_refinement_le_coefficient_sum mode n r environment
    _ = ∑ word ∈ words,
          ∫ environment, refinementCoefficient mode n environment word *
            Z mode r (Environment.subtree word environment)
            ∂environmentMeasure p := by
      exact integral_finsetSum words
        (fun word hword ↦ integrable_refinement_product p mode n r hword)
    _ = ∑ word ∈ words,
          (∫ environment, refinementCoefficient mode n environment word
            ∂environmentMeasure p) * firstMoment p mode r := by
      apply Finset.sum_congr rfl
      intro word hword
      exact integral_refinement_product p mode n r hword
    _ = (∑ word ∈ words,
          ∫ environment, refinementCoefficient mode n environment word
            ∂environmentMeasure p) * firstMoment p mode r := by
      rw [Finset.sum_mul]
    _ = (∫ environment,
          ∑ word ∈ words, refinementCoefficient mode n environment word
          ∂environmentMeasure p) * firstMoment p mode r := by
      congr 1
      symm
      exact integral_finsetSum words
        (fun word hword ↦ integrable_refinementCoefficient p mode n hword)
    _ = firstMoment p mode n * firstMoment p mode r := by
      congr 1
      apply integral_congr_ae
      filter_upwards with environment
      simpa only [words] using refinementCoefficient_sum mode n environment

/-- The logarithm of the first moment is a subadditive real sequence. -/
theorem logFirstMoment_subadditive (p : unitInterval) (mode : Mode) :
    Subadditive (fun n ↦ Real.log (firstMoment p mode n)) := by
  intro n r
  calc
    Real.log (firstMoment p mode (n + r)) ≤
        Real.log (firstMoment p mode n * firstMoment p mode r) :=
      Real.log_le_log (firstMoment_pos p mode (n + r))
        (firstMoment_submultiplicative p mode n r)
    _ = Real.log (firstMoment p mode n) +
          Real.log (firstMoment p mode r) :=
      Real.log_mul (firstMoment_ne_zero p mode n)
        (firstMoment_ne_zero p mode r)

private theorem bddBelow_normalized_logFirstMoment
    (p : unitInterval) (mode : Mode) :
    BddBelow (Set.range fun n : ℕ ↦
      Real.log (firstMoment p mode n) / (n : ℝ)) := by
  refine ⟨-Real.log 2, ?_⟩
  rintro value ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, div_zero]
    exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  · have hlower := (firstMoment_bounds p mode n).1
    have hlog := Real.log_le_log
      (by positivity : 0 < ((2 : ℝ) ^ n)⁻¹) hlower
    rw [Real.log_inv, Real.log_pow] at hlog
    rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    calc
      -Real.log 2 * (n : ℝ) = -((n : ℝ) * Real.log 2) := by ring
      _ ≤ Real.log (firstMoment p mode n) := hlog

/-- Fekete convergence for the normalized log first moment, with the zero index omitted. -/
theorem normalizedLogFirstMoment_tendsto_feketeLimit
    (p : unitInterval) (mode : Mode) :
    Tendsto (normalizedLogFirstMoment p mode) atTop
      (𝓝 (logFirstMoment_subadditive p mode).lim) := by
  have hbase := (logFirstMoment_subadditive p mode).tendsto_lim
    (bddBelow_normalized_logFirstMoment p mode)
  have hshift := (tendsto_add_atTop_iff_nat 1).2 hbase
  have hsequence : normalizedLogFirstMoment p mode =
      (fun n : ℕ ↦ Real.log (firstMoment p mode (n + 1)) / ((n : ℝ) + 1)) := by
    funext n
    exact normalizedLogFirstMoment.eq_def p mode n
  rw [hsequence]
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

/-- The canonical normalized log-first-moment sequence has a finite real limit. -/
theorem normalizedLogFirstMoment_converges
    (p : unitInterval) (mode : Mode) :
    ∃ value : ℝ,
      Tendsto (normalizedLogFirstMoment p mode) atTop (𝓝 value) :=
  ⟨(logFirstMoment_subadditive p mode).lim,
    normalizedLogFirstMoment_tendsto_feketeLimit p mode⟩

/-- The deterministic limit selector in the statement contract chooses the Fekete limit. -/
theorem normalizedLogFirstMoment_tendsto_chosenSequentialLimit
    (p : unitInterval) (mode : Mode) :
    Tendsto (normalizedLogFirstMoment p mode) atTop
      (𝓝 (chosenSequentialLimit (normalizedLogFirstMoment p mode))) :=
  chosenSequentialLimit_spec (normalizedLogFirstMoment_converges p mode)

/-- The distance first-moment sequence converges to the contract's canonical `gammaD`. -/
theorem normalizedLogFirstMoment_tendsto_gammaD (p : ℝ) :
    Tendsto (normalizedLogFirstMoment (modelParameter p) .distance) atTop
      (𝓝 (gammaD p)) := by
  rw [gammaD]
  exact normalizedLogFirstMoment_tendsto_chosenSequentialLimit
    (modelParameter p) .distance

/-- The resistance first-moment sequence converges to the contract's canonical `gammaR`. -/
theorem normalizedLogFirstMoment_tendsto_gammaR (p : ℝ) :
    Tendsto (normalizedLogFirstMoment (modelParameter p) .resistance) atTop
      (𝓝 (gammaR p)) := by
  rw [gammaR]
  exact normalizedLogFirstMoment_tendsto_chosenSequentialLimit
    (modelParameter p) .resistance

/-- The convergence conjunct of `FirstMomentLogarithmicRatesStatement`. -/
theorem firstMomentLogarithmicRates_convergence :
    ∀ p : ℝ, p ∈ Set.Icc 0 1 →
      Tendsto (normalizedLogFirstMoment (modelParameter p) .distance) atTop
          (𝓝 (gammaD p)) ∧
        Tendsto (normalizedLogFirstMoment (modelParameter p) .resistance) atTop
          (𝓝 (gammaR p)) := by
  intro p _
  exact ⟨normalizedLogFirstMoment_tendsto_gammaD p,
    normalizedLogFirstMoment_tendsto_gammaR p⟩

end SeriesParallel.MainText
