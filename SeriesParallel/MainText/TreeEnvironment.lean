/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeriesParallel formalization contributors
-/
module

public import Mathlib.Data.Set.Finite.List
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Process.Filtration

/-!
# The canonical Bernoulli environment on the binary tree

This module realizes every generation of the random series--parallel model on one probability
space.  Tree vertices are finite Boolean words and the environment is the countable product of
Bernoulli laws, with `true` having mass `p`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace SeriesParallel.MainText

/-- A vertex of the rooted binary tree, encoded by the edge labels from the root. -/
abbrev Word := List Bool

/-- A complete assignment of Boolean choices to all vertices of the binary tree. -/
abbrev Environment := Word → Bool

/-- The root of the binary tree. -/
@[expose]
def root : Word := []

/-- Append one labelled edge to a tree vertex. -/
@[expose]
def child (w : Word) (b : Bool) : Word := w ++ [b]

/-- The child reached by a `false` edge. -/
@[expose]
def leftChild (w : Word) : Word := child w false

/-- The child reached by a `true` edge. -/
@[expose]
def rightChild (w : Word) : Word := child w true

/-- Prefix order on tree vertices. -/
@[expose]
def IsPrefix (u v : Word) : Prop := ∃ t, v = u ++ t

/-- The vertices at depth `n`. -/
abbrev Level (n : ℕ) := {w : Word // w.length = n}

instance levelFinite (n : ℕ) : Finite (Level n) := List.finite_length_eq Bool n

@[simp]
theorem length_child (w : Word) (b : Bool) : (child w b).length = w.length + 1 := by
  simp [child]

@[simp]
theorem root_prefix (w : Word) : IsPrefix root w := by
  exact ⟨w, by simp [root]⟩

theorem prefix_child (w : Word) (b : Bool) : IsPrefix w (child w b) := by
  exact ⟨[b], rfl⟩

theorem IsPrefix.refl (w : Word) : IsPrefix w w := by
  exact ⟨[], by simp⟩

theorem IsPrefix.trans {u v w : Word} (huv : IsPrefix u v) (hvw : IsPrefix v w) :
    IsPrefix u w := by
  obtain ⟨a, rfl⟩ := huv
  obtain ⟨b, rfl⟩ := hvw
  exact ⟨a ++ b, by simp⟩

/-- Re-root an environment at the subtree with root `w`. -/
@[expose]
def subtreeShift (w : Word) (environment : Environment) : Environment :=
  fun u ↦ environment (w ++ u)

@[simp]
theorem subtreeShift_apply (w u : Word) (environment : Environment) :
    subtreeShift w environment u = environment (w ++ u) := rfl

@[simp]
theorem subtreeShift_root (environment : Environment) :
    subtreeShift root environment = environment := by
  ext u
  simp [subtreeShift, root]

@[simp]
theorem subtreeShift_comp (u w : Word) (environment : Environment) :
    subtreeShift u (subtreeShift w environment) = subtreeShift (w ++ u) environment := by
  ext v
  simp [subtreeShift, List.append_assoc]

namespace Environment

/-- Re-root an environment at `stem`; the stem is the first argument. -/
@[expose]
def subtree (stem : Word) (environment : Environment) : Environment :=
  subtreeShift stem environment

@[simp]
theorem subtree_apply (stem tail : Word) (environment : Environment) :
    subtree stem environment tail = environment (stem ++ tail) := by
  rfl

@[simp]
theorem subtree_root (environment : Environment) : subtree root environment = environment := by
  simp [subtree]

@[simp]
theorem subtree_append (u w : Word) (environment : Environment) :
    subtree u (subtree w environment) = subtree (w ++ u) environment := by
  simp [subtree]

end Environment

/-- Flip every Boolean choice in an environment. -/
@[expose]
def complementEnvironment (environment : Environment) : Environment :=
  fun w ↦ !environment w

@[simp]
theorem complementEnvironment_apply (environment : Environment) (w : Word) :
    complementEnvironment environment w = !environment w := rfl

@[simp]
theorem complementEnvironment_involutive (environment : Environment) :
    complementEnvironment (complementEnvironment environment) = environment := by
  ext w
  simp [complementEnvironment]

@[simp]
theorem complementEnvironment_subtreeShift (w : Word) (environment : Environment) :
    complementEnvironment (subtreeShift w environment) =
      subtreeShift w (complementEnvironment environment) := by
  rfl

/-- The coordinate random variable at the tree vertex `w`. -/
@[expose]
def coordinate (w : Word) : Environment → Bool := fun environment ↦ environment w

theorem measurable_coordinate (w : Word) : Measurable (coordinate w) := by
  exact measurable_pi_apply w

theorem measurable_subtreeShift (w : Word) : Measurable (subtreeShift w) := by
  exact measurable_pi_iff.mpr fun u ↦ measurable_coordinate (w ++ u)

theorem measurable_complementEnvironment : Measurable complementEnvironment := by
  refine measurable_pi_iff.mpr fun w ↦ ?_
  exact (measurable_of_finite Bool.not).comp (measurable_coordinate w)

/-- The Bernoulli Boolean law in which `true` has probability `p`. -/
@[expose]
noncomputable def bernoulliBool (p : unitInterval) : Measure Bool :=
  bernoulliMeasure true false p

instance (p : unitInterval) : IsProbabilityMeasure (bernoulliBool p) := by
  unfold bernoulliBool
  infer_instance

@[simp]
theorem bernoulliBool_real_true (p : unitInterval) : (bernoulliBool p).real {true} = p := by
  simp [bernoulliBool]

@[simp]
theorem bernoulliBool_real_false (p : unitInterval) :
    (bernoulliBool p).real {false} = 1 - p := by
  simp [bernoulliBool]

/-- The canonical common environment law: the product of identical Bernoulli Boolean laws. -/
@[expose]
noncomputable def environmentMeasure (p : unitInterval) : Measure Environment :=
  Measure.infinitePi fun _ : Word ↦ bernoulliBool p

instance (p : unitInterval) : IsProbabilityMeasure (environmentMeasure p) := by
  unfold environmentMeasure
  infer_instance

theorem coordinate_hasLaw (p : unitInterval) (w : Word) :
    HasLaw (coordinate w) (bernoulliBool p) (environmentMeasure p) := by
  change HasLaw (fun environment : Word → Bool ↦ environment w) (bernoulliBool p)
    (Measure.infinitePi fun _ : Word ↦ bernoulliBool p)
  exact (measurePreserving_eval_infinitePi (fun _ : Word ↦ bernoulliBool p) w).hasLaw

/-- All coordinate variables on the canonical environment are mutually independent. -/
theorem coordinates_iIndep (p : unitInterval) :
    iIndepFun (fun w : Word ↦ coordinate w) (environmentMeasure p) := by
  change iIndepFun (fun w : Word ↦ fun environment : Word → Bool ↦ environment w)
    (Measure.infinitePi fun _ : Word ↦ bernoulliBool p)
  exact iIndepFun_infinitePi (P := fun _ : Word ↦ bernoulliBool p)
    (X := fun _ (b : Bool) ↦ b) fun _ ↦ measurable_id

/-- The information revealed by the vertices strictly above depth `n`. -/
@[expose, reducible]
def finiteLevelSigma (n : ℕ) : MeasurableSpace Environment :=
  ⨆ w : {w : Word // w.length < n},
    MeasurableSpace.comap (coordinate w.1) inferInstance

theorem finiteLevelSigma_le (n : ℕ) :
    finiteLevelSigma n ≤ (inferInstance : MeasurableSpace Environment) := by
  refine iSup_le fun w ↦ ?_
  exact (measurable_coordinate w.1).comap_le

theorem finiteLevelSigma_mono {m n : ℕ} (hmn : m ≤ n) :
    finiteLevelSigma m ≤ finiteLevelSigma n := by
  refine iSup_le fun w ↦ ?_
  let w' : {w : Word // w.length < n} := ⟨w.1, lt_of_lt_of_le w.2 hmn⟩
  exact le_iSup_of_le w' le_rfl

theorem measurable_coordinate_finiteLevel {n : ℕ} {w : Word} (hw : w.length < n) :
    Measurable[finiteLevelSigma n] (coordinate w) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨w, hw⟩ : {u : Word // u.length < n}) le_rfl

/-- Subtree shifts preserve the homogeneous Bernoulli environment law. -/
theorem subtreeShift_map (p : unitInterval) (w : Word) :
    (environmentMeasure p).map (subtreeShift w) = environmentMeasure p := by
  change (Measure.infinitePi fun _ : Word ↦ bernoulliBool p).map
      (fun environment u ↦ environment (w ++ u)) =
    Measure.infinitePi fun _ : Word ↦ bernoulliBool p
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Word ↦ bernoulliBool p) (List.append_right_injective w)

theorem subtreeShift_measurePreserving (p : unitInterval) (w : Word) :
    MeasurePreserving (subtreeShift w) (environmentMeasure p) (environmentMeasure p) where
  measurable := measurable_subtreeShift w
  map_eq := subtreeShift_map p w

theorem subtreeShift_hasLaw (p : unitInterval) (w : Word) :
    HasLaw (subtreeShift w) (environmentMeasure p) (environmentMeasure p) :=
  (subtreeShift_measurePreserving p w).hasLaw

private theorem levelAppend_injective (n : ℕ) :
    Function.Injective (fun q : Level n × Word ↦ q.1.1 ++ q.2) := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  have huv : u.1 = v.1 := by
    have := congrArg (List.take n) h
    simpa [u.2, v.2] using this
  have huv' : u = v := Subtype.ext huv
  subst v
  have hab : a = b := List.append_right_injective u.1 h
  subst b
  rfl

/-- The coordinate sets below two distinct vertices at one level are disjoint. -/
theorem descendantRanges_disjoint {n : ℕ} {u v : Level n} (huv : u ≠ v) :
    Disjoint (Set.range fun tail : Word ↦ u.1 ++ tail)
      (Set.range fun tail : Word ↦ v.1 ++ tail) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hab⟩
  have huvValue : u.1 = v.1 := by
    have := congrArg (List.take n) hab.symm
    simpa [u.2, v.2] using this
  exact huv (Subtype.ext huvValue)

/-- Package all depth-`n` descendant environments as one random variable. -/
@[expose]
def descendantFamily (n : ℕ) : Environment → Level n → Environment :=
  fun environment w ↦ subtreeShift w.1 environment

theorem measurable_descendantFamily (n : ℕ) : Measurable (descendantFamily n) := by
  exact measurable_pi_iff.mpr fun w ↦ measurable_subtreeShift w.1

/-- The joint law of the subtrees rooted at one level is the product environment law. -/
theorem descendantFamily_map (p : unitInterval) (n : ℕ) :
    (environmentMeasure p).map (descendantFamily n) =
      Measure.infinitePi fun _ : Level n ↦ environmentMeasure p := by
  let flat : Environment → Level n × Word → Bool :=
    fun environment q ↦ environment (q.1.1 ++ q.2)
  have mflat : Measurable flat := by
    exact measurable_pi_iff.mpr fun q ↦ measurable_coordinate (q.1.1 ++ q.2)
  have hflat :
      (environmentMeasure p).map flat =
        Measure.infinitePi fun _ : Level n × Word ↦ bernoulliBool p := by
    simpa [flat, environmentMeasure] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : Word ↦ bernoulliBool p) (levelAppend_injective n))
  calc
    (environmentMeasure p).map (descendantFamily n) =
        (environmentMeasure p).map
          ((MeasurableEquiv.curry (Level n) Word Bool) ∘ flat) := by
            congr 1
    _ = ((environmentMeasure p).map flat).map
          (MeasurableEquiv.curry (Level n) Word Bool) := by
            rw [Measure.map_map
              (MeasurableEquiv.curry (Level n) Word Bool).measurable mflat]
    _ = (Measure.infinitePi fun _ : Level n × Word ↦ bernoulliBool p).map
          (MeasurableEquiv.curry (Level n) Word Bool) := by rw [hflat]
    _ = Measure.infinitePi fun _ : Level n ↦ environmentMeasure p := by
      simpa [environmentMeasure] using
        (Measure.infinitePi_map_curry
          (fun _ : Level n ↦ fun _ : Word ↦ bernoulliBool p))

/-- Descendant environments rooted at the same level are mutually independent. -/
theorem descendantFamilies_iIndep (p : unitInterval) (n : ℕ) :
    iIndepFun (fun w : Level n ↦ subtreeShift w.1) (environmentMeasure p) := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map
    (P := environmentMeasure p) (X := fun w : Level n ↦ subtreeShift w.1)
    (fun w ↦ measurable_subtreeShift w.1)).2 ?_
  change (environmentMeasure p).map (descendantFamily n) =
    Measure.infinitePi fun w : Level n ↦ (environmentMeasure p).map (subtreeShift w.1)
  rw [descendantFamily_map]
  congr 1
  funext w
  exact (subtreeShift_map p w.1).symm

/-- In particular, two distinct depth-`n` descendant environments are independent. -/
theorem descendantEnvironments_indep (p : unitInterval) {n : ℕ} {u v : Level n}
    (huv : u ≠ v) :
    subtreeShift u.1 ⟂ᵢ[environmentMeasure p] subtreeShift v.1 :=
  (descendantFamilies_iIndep p n).indepFun huv

private theorem bernoulliBool_map_not (p : unitInterval) :
    (bernoulliBool p).map Bool.not = bernoulliBool (unitInterval.symm p) := by
  change (bernoulliMeasure true false p).map Bool.not =
    bernoulliMeasure true false (unitInterval.symm p)
  rw [map_bernoulliMeasure]
  simp [bernoulliMeasure_def, add_comm]

/-- Complementation sends parameter `p` to `1-p` on the canonical environment. -/
theorem complementEnvironment_map (p : unitInterval) :
    (environmentMeasure p).map complementEnvironment =
      environmentMeasure (unitInterval.symm p) := by
  change (Measure.infinitePi fun _ : Word ↦ bernoulliBool p).map
      (fun environment w ↦ Bool.not (environment w)) =
    Measure.infinitePi fun _ : Word ↦ bernoulliBool (unitInterval.symm p)
  rw [Measure.infinitePi_map_pi (fun _ : Word ↦ bernoulliBool p)
    (fun _ : Word ↦ measurable_of_finite Bool.not)]
  simp_rw [bernoulliBool_map_not]

theorem complementEnvironment_measurePreserving (p : unitInterval) :
    MeasurePreserving complementEnvironment (environmentMeasure p)
      (environmentMeasure (unitInterval.symm p)) where
  measurable := measurable_complementEnvironment
  map_eq := complementEnvironment_map p

end SeriesParallel.MainText
