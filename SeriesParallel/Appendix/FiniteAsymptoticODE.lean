import SeriesParallel.Appendix.BasicDefs
import SeriesParallel.ManualInterfaces
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A finite expansion for an asymptotically autonomous ODE

This file formalizes the objects and the public conclusion of
`lem:finite-asymptotic-ode`.  In particular, the remainder estimates use mathlib's
`iteratedDeriv` and `IsBigO` at `atTop`, so all derivatives through order four are
part of the statement rather than hidden in prose.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace SeriesParallel.Appendix

open SeriesParallel.ManualInterfaces

/-- Right-hand side of `eq:asymptotically-autonomous-ode`. -/
noncomputable def asymptoticallyAutonomousRhs (F G : ℝ → ℝ) (t y : ℝ) : ℝ :=
  F y + t⁻¹ * G y

/-- The exact hypotheses on the solution in `eq:asymptotically-autonomous-ode`. -/
def IsAsymptoticallyAutonomousSolution (I : Set ℝ) (F G : ℝ → ℝ)
    (yStar T0 : ℝ) (Y : ℝ → ℝ) : Prop :=
  IsOpen I ∧
    yStar ∈ I ∧
    0 < T0 ∧
    MapsTo Y (Ici T0) I ∧
    ContDiffOn ℝ 1 Y (Ici T0) ∧
    (∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t) ∧
    Tendsto Y atTop (𝓝 yStar)

/-- Exact source-facing B1 solution predicate on the closed half-line.  The ODE is stated
with a within derivative at every `t ∈ Ici T0`, including the left endpoint. -/
def IsAsymptoticallyAutonomousSolutionSource (I : Set ℝ) (F G : ℝ → ℝ)
    (yStar T0 : ℝ) (Y : ℝ → ℝ) : Prop :=
  IsOpen I ∧
    yStar ∈ I ∧
    0 < T0 ∧
    MapsTo Y (Ici T0) I ∧
    ContDiffOn ℝ 1 Y (Ici T0) ∧
    (∀ t ∈ Ici T0,
      HasDerivWithinAt Y (asymptoticallyAutonomousRhs F G t (Y t)) (Ici T0) t) ∧
    Tendsto Y atTop (𝓝 yStar)

/-- The exact closed-half-line B1 predicate implies the interior helper used by the proof. -/
theorem IsAsymptoticallyAutonomousSolutionSource.toInterior
    {I : Set ℝ} {F G : ℝ → ℝ} {yStar T0 : ℝ} {Y : ℝ → ℝ}
    (h : IsAsymptoticallyAutonomousSolutionSource I F G yStar T0 Y) :
    IsAsymptoticallyAutonomousSolution I F G yStar T0 Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, h.2.2.2.2.2.2⟩
  intro t ht
  exact (h.2.2.2.2.2.1 t (mem_Ici.mpr ht.le)).hasDerivAt (Ici_mem_nhds ht)

/-- A polynomial with no constant term and eight coefficients, denoted `p₈` in the
source.  `b 0` is the coefficient of `x`, and `b 7` that of `x⁸`. -/
def polynomial8 (b : Fin 8 → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin 8, b j * x ^ (j.1 + 1)

/-- The eight-term comparison function `P₈(t)=y_*+p₈(t⁻¹)`. -/
noncomputable def approximation8 (yStar : ℝ) (b : Fin 8 → ℝ) (t : ℝ) : ℝ :=
  yStar + polynomial8 b t⁻¹

/-- The defect `D₈=P₈'-F(P₈)-t⁻¹G(P₈)` from `eq:D8-bound`. -/
noncomputable def defect8 (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (t : ℝ) : ℝ :=
  deriv (approximation8 yStar b) t - F (approximation8 yStar b t) -
    t⁻¹ * G (approximation8 yStar b t)

/-- The reciprocal-coordinate defect `H₈(x)` displayed in the proof. -/
noncomputable def reciprocalDefect8 (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) (x : ℝ) : ℝ :=
  -x ^ 2 * deriv (polynomial8 b) x - F (yStar + polynomial8 b x) -
    x * G (yStar + polynomial8 b x)

/-- The exact remainder `R=Y-P₈` used in `eq:R-linear-equation`. -/
noncomputable def remainder8 (Y : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ) (t : ℝ) : ℝ :=
  Y t - approximation8 yStar b t

/-- The nonlinear difference term in the remainder equation, before the
mean-value coefficient is introduced. -/
noncomputable def nonlinearRemainderTerm (F G Y P : ℝ → ℝ) (t : ℝ) : ℝ :=
  F (Y t) - F (P t) + t⁻¹ * (G (Y t) - G (P t))

/-- The mean-value coefficient `A(t)` in the exact linear remainder equation. -/
noncomputable def remainderLinearCoefficient (F G : ℝ → ℝ) (Y : ℝ → ℝ)
    (yStar : ℝ) (b : Fin 8 → ℝ) (t : ℝ) : ℝ :=
  ∫ theta in (0 : ℝ)..1,
    (deriv F (approximation8 yStar b t + theta * remainder8 Y yStar b t) +
      t⁻¹ * deriv G (approximation8 yStar b t + theta * remainder8 Y yStar b t))

/-- The four-term approximation appearing in `eq:finite-asymptotic-expansion`. -/
noncomputable def approximation4 (yStar : ℝ) (b : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  yStar + ∑ j : Fin 4, b j * (t ^ (j.1 + 1))⁻¹

/-- Restrict eight recursively constructed coefficients to the four displayed
in the public expansion. -/
def truncateCoefficients4 (b : Fin 8 → ℝ) : Fin 4 → ℝ :=
  fun j ↦ b ⟨j.1, j.2.trans (by norm_num)⟩

/-- The four omitted terms of the auxiliary eight-term comparison function. -/
noncomputable def approximationTail8 (b : Fin 8 → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin 4, b ⟨j.1 + 4, by omega⟩ * (t ^ (j.1 + 5))⁻¹

/-- The remainder after the four source-visible terms. -/
noncomputable def finiteAsymptoticRemainder (Y : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  Y t - approximation4 yStar b t

/-- The complete conclusion of `eq:finite-asymptotic-expansion`, including the
coefficient `b₁` and all derivative estimates `0 ≤ ℓ ≤ 4`. -/
structure FiniteAsymptoticExpansion (F G Y : ℝ → ℝ) (yStar : ℝ) where
  /-- Coefficients `b₁,…,b₄`, indexed from zero in Lean. -/
  coefficients : Fin 4 → ℝ
  /-- The source's explicit first coefficient. -/
  firstCoefficient : coefficients 0 = -G yStar / deriv F yStar
  /-- Simultaneous estimates for the remainder and its first four derivatives. -/
  derivativeRemainderBigO : ∀ ell : ℕ, ell ≤ 4 →
    (fun t : ℝ ↦ iteratedDeriv ell
      (finiteAsymptoticRemainder Y yStar coefficients) t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹)

/-! ## Source-labelled intermediate formulas -/

/-- The eight reciprocal-coordinate jets which are killed in the source's recursive
construction of `b₁,…,b₈`. -/
def HasVanishingReciprocalJet (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ) : Prop :=
  ∀ j ≤ 8, iteratedDeriv j (reciprocalDefect8 F G yStar b) 0 = 0

/-- The finite triangular-jet calculation underlying the recursive construction of
`b₁,…,b₈`: below order `j`, a factor `x^j` kills every jet, while the `j`-th jet
only sees the value of the remaining smooth factor at zero.  This avoids expanding a
general Faà di Bruno sum. -/
theorem iteratedDeriv_pow_mul_zero {n j : ℕ} (hnj : n ≤ j) (Q : ℝ → ℝ)
    (hQ : ContDiffAt ℝ n Q 0) :
    iteratedDeriv n (fun x : ℝ ↦ x ^ j * Q x) 0 =
      if n = j then j.factorial * Q 0 else 0 := by
  have hpow : ContDiffAt ℝ n (fun x : ℝ ↦ x ^ j) 0 := by fun_prop
  rw [show (fun x : ℝ ↦ x ^ j * Q x) = (fun x : ℝ ↦ x ^ j) * Q by rfl,
    iteratedDeriv_mul hpow hQ]
  by_cases hnj' : n = j
  · subst n
    rw [Finset.sum_eq_single j]
    · simp [Nat.descFactorial_self]
    · intro i hi hij
      have hi_le : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hi' : i < j := lt_of_le_of_ne hi_le hij
      have hsub : j - i ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hi'
      simp [hsub]
    · simp
  · have hne : ∀ i ∈ Finset.range (n + 1), i ≠ j := by
      intro i hi hij
      have hi' := Finset.mem_range.mp hi
      subst i
      omega
    simp only [if_neg hnj']
    apply Finset.sum_eq_zero
    intro i hi
    have hi_le_n : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hi_le_j : i ≤ j := hi_le_n.trans hnj
    have hi_lt_j : i < j := lt_of_le_of_ne hi_le_j (hne i hi)
    have hsub : j - i ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hi_lt_j
    simp [hsub]

/-- Replace one of the eight coefficients. -/
def updateCoefficient8 (b : Fin 8 → ℝ) (j : Fin 8) (c : ℝ) : Fin 8 → ℝ :=
  Function.update b j c

/-- Successively choose the eight coefficients so that the next reciprocal-defect jet
vanishes.  Stages beyond eight are inert; the construction is only used at stage eight. -/
noncomputable def recursiveCoefficients8 (F G : ℝ → ℝ) (yStar : ℝ) :
    ℕ → Fin 8 → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 =>
      let previous := recursiveCoefficients8 F G yStar n
      if hn : n < 8 then
        let j : Fin 8 := ⟨n, hn⟩
        updateCoefficient8 previous j
          (previous j + iteratedDeriv (n + 1)
            (reciprocalDefect8 F G yStar previous) 0 /
              (deriv F yStar * (n + 1).factorial))
      else previous

/-- Updating coefficient `j` perturbs `p₈` by exactly one monomial. -/
theorem polynomial8_update_sub (b : Fin 8 → ℝ) (j : Fin 8) (c x : ℝ) :
    polynomial8 (updateCoefficient8 b j c) x - polynomial8 b x =
      (c - b j) * x ^ (j.1 + 1) := by
  classical
  unfold polynomial8 updateCoefficient8
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i : Fin 8, (Function.update b j c i * x ^ (i.1 + 1) - b i * x ^ (i.1 + 1)) =
        ∑ i : Fin 8, (Function.update b j c i - b i) * x ^ (i.1 + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (c - b j) * x ^ (j.1 + 1) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp

/-- A local factorization by `x^j` is enough to prove the triangular jet law.  In
particular, the proof only invokes the finite Leibniz rule; it does not expand the
composition jets of `F` or `G`. -/
theorem triangular_jet_of_factorization {Hnew Hold Q E : ℝ → ℝ} {n j : ℕ}
    (hnj : n ≤ j) (c : ℝ) (hHnew : ContDiffAt ℝ n Hnew 0)
    (hHold : ContDiffAt ℝ n Hold 0) (hQ : ContDiffAt ℝ n Q 0)
    (hE : ContDiffAt ℝ n E 0)
    (hfactor : (Hnew - Hold) =ᶠ[𝓝 0]
      (fun x : ℝ ↦ -c * (x ^ j * Q x) + x ^ (j + 1) * E x)) :
    iteratedDeriv n Hnew 0 - iteratedDeriv n Hold 0 =
      if n = j then -c * j.factorial * Q 0 else 0 := by
  have hpowQ : ContDiffAt ℝ n (fun x : ℝ ↦ x ^ j * Q x) 0 := by fun_prop
  have hpowE : ContDiffAt ℝ n (fun x : ℝ ↦ x ^ (j + 1) * E x) 0 := by fun_prop
  rw [← iteratedDeriv_sub hHnew hHold]
  rw [hfactor.iteratedDeriv_eq n]
  change iteratedDeriv n
    ((fun x : ℝ ↦ -c * (x ^ j * Q x)) + (fun x : ℝ ↦ x ^ (j + 1) * E x)) 0 = _
  rw [iteratedDeriv_add (by fun_prop : ContDiffAt ℝ n
    (fun x : ℝ ↦ -c * (x ^ j * Q x)) 0) hpowE]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_pow_mul_zero hnj Q hQ]
  rw [iteratedDeriv_pow_mul_zero (hnj.trans (Nat.le_succ j)) E hE]
  have hn_succ : n ≠ j + 1 := by omega
  simp only [hn_succ, if_false, add_zero]
  by_cases hn : n = j
  · subst n
    simp
    ring
  · simp [hn]

/-- Composition preserves equality of finite scalar jets.  This is the only use of the
general Faà di Bruno formula needed for the lower-order part of the coefficient recursion;
the proof compares its summands without enumerating ordered partitions. -/
theorem iteratedDeriv_comp_eq_of_jets_eq {outer inner₁ inner₂ : ℝ → ℝ} {n : ℕ}
    (hinnerValue : inner₁ 0 = inner₂ 0)
    (hjets : ∀ k ≤ n, iteratedDeriv k inner₁ 0 = iteratedDeriv k inner₂ 0)
    (houter : ContDiffAt ℝ n outer (inner₁ 0))
    (hinner₁ : ContDiffAt ℝ n inner₁ 0) (hinner₂ : ContDiffAt ℝ n inner₂ 0) :
    iteratedDeriv n (outer ∘ inner₁) 0 = iteratedDeriv n (outer ∘ inner₂) 0 := by
  have houter₂ : ContDiffAt ℝ n outer (inner₂ 0) := hinnerValue ▸ houter
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition houter hinner₁ le_rfl,
    iteratedDeriv_comp_eq_sum_orderedFinpartition houter₂ hinner₂ le_rfl]
  apply Finset.sum_congr rfl
  intro partition _
  rw [hinnerValue]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact hjets _ (OrderedFinpartition.partSize_le partition k)

/-- A successor-order composition formula obtained by applying Leibniz to the ordinary
chain rule.  It is more convenient than enumerating ordered partitions when isolating the
single term containing the highest inner jet. -/
theorem iteratedDeriv_comp_succ_eq_sum {outer inner : ℝ → ℝ} {n : ℕ}
    (houter : ContDiffAt ℝ (n + 1) outer (inner 0))
    (hinner : ContDiffAt ℝ (n + 1) inner 0) :
    iteratedDeriv (n + 1) (outer ∘ inner) 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        iteratedDeriv i (deriv outer ∘ inner) 0 *
          iteratedDeriv (n - i) (deriv inner) 0 := by
  have houterDeriv : ContDiffAt ℝ n (deriv outer) (inner 0) := by
    exact houter.derivWithin (m := n) (by norm_num)
  have hinnerN : ContDiffAt ℝ n inner 0 := hinner.of_le (by norm_num)
  have hcomp : ContDiffAt ℝ n (deriv outer ∘ inner) 0 :=
    houterDeriv.comp 0 hinnerN
  have hderivInner : ContDiffAt ℝ n (deriv inner) 0 := by
    exact hinner.derivWithin (m := n) (by norm_num)
  have hchain : deriv (outer ∘ inner) =ᶠ[𝓝 0]
      (fun x : ℝ ↦ deriv outer (inner x) * deriv inner x) := by
    have hinnerEventually := hinner.eventually (by simp)
    have houterEventually := (hinner.continuousAt.tendsto.eventually
      (houter.eventually (by simp)))
    filter_upwards [hinnerEventually, houterEventually] with x hix hox
    have hdInner : DifferentiableAt ℝ inner x := hix.differentiableAt (by norm_num)
    have hdOuter : DifferentiableAt ℝ outer (inner x) := hox.differentiableAt (by norm_num)
    exact (hdOuter.hasDerivAt.comp x hdInner.hasDerivAt).deriv
  rw [iteratedDeriv_succ', hchain.iteratedDeriv_eq n]
  change iteratedDeriv n ((deriv outer ∘ inner) * deriv inner) 0 = _
  exact iteratedDeriv_mul hcomp hderivInner

/-- The highest inner jet enters a composition linearly, with coefficient the first
derivative of the outer function.  All other Leibniz summands depend only on lower
inner jets and cancel. -/
theorem iteratedDeriv_comp_succ_sub_of_lower_jets_eq
    {outer inner₁ inner₂ : ℝ → ℝ} {n : ℕ}
    (hvalue : inner₁ 0 = inner₂ 0)
    (hjets : ∀ k ≤ n, iteratedDeriv k inner₁ 0 = iteratedDeriv k inner₂ 0)
    (houter : ContDiffAt ℝ (n + 1) outer (inner₁ 0))
    (hinner₁ : ContDiffAt ℝ (n + 1) inner₁ 0)
    (hinner₂ : ContDiffAt ℝ (n + 1) inner₂ 0) :
    iteratedDeriv (n + 1) (outer ∘ inner₁) 0 -
      iteratedDeriv (n + 1) (outer ∘ inner₂) 0 =
        deriv outer (inner₁ 0) *
          (iteratedDeriv (n + 1) inner₁ 0 - iteratedDeriv (n + 1) inner₂ 0) := by
  have houter₂ : ContDiffAt ℝ (n + 1) outer (inner₂ 0) := hvalue ▸ houter
  rw [iteratedDeriv_comp_succ_eq_sum houter hinner₁,
    iteratedDeriv_comp_succ_eq_sum houter₂ hinner₂, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
      Function.comp_apply]
    have hsucc₁ : iteratedDeriv n (deriv inner₁) 0 = iteratedDeriv (n + 1) inner₁ 0 := by
      rw [iteratedDeriv_succ']
    have hsucc₂ : iteratedDeriv n (deriv inner₂) 0 = iteratedDeriv (n + 1) inner₂ 0 := by
      rw [iteratedDeriv_succ']
    simp only [Nat.sub_zero]
    rw [hsucc₁, hsucc₂, ← hvalue]
    ring
  · intro i hi hi0
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ n := Nat.le_of_lt_succ hi_lt
    have houterDeriv : ContDiffAt ℝ i (deriv outer) (inner₁ 0) := by
      exact (houter.derivWithin (m := n) (by norm_num)).of_le (by exact_mod_cast hi_le)
    have hcomp : iteratedDeriv i (deriv outer ∘ inner₁) 0 =
        iteratedDeriv i (deriv outer ∘ inner₂) 0 := by
      apply iteratedDeriv_comp_eq_of_jets_eq hvalue
      · intro k hk
        exact hjets k (hk.trans hi_le)
      · exact houterDeriv
      · exact hinner₁.of_le (by exact_mod_cast hi_le.trans (Nat.le_succ n))
      · exact hinner₂.of_le (by exact_mod_cast hi_le.trans (Nat.le_succ n))
    have hindex : n - i + 1 ≤ n := by omega
    have hderivInner : iteratedDeriv (n - i) (deriv inner₁) 0 =
        iteratedDeriv (n - i) (deriv inner₂) 0 := by
      rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
      exact hjets _ hindex
    rw [hcomp, hderivInner]
    ring
  · simp

/-- The concrete jet change caused by updating one coefficient of `p₈`. -/
theorem polynomial8_update_jet (b : Fin 8 → ℝ) (j : Fin 8) (c : ℝ) {n : ℕ}
    (hn : n ≤ j.1 + 1) :
    iteratedDeriv n (polynomial8 (updateCoefficient8 b j c)) 0 -
      iteratedDeriv n (polynomial8 b) 0 =
        if n = j.1 + 1 then (c - b j) * (j.1 + 1).factorial else 0 := by
  have hnew : ContDiffAt ℝ n (polynomial8 (updateCoefficient8 b j c)) 0 := by
    unfold polynomial8
    fun_prop
  have hold : ContDiffAt ℝ n (polynomial8 b) 0 := by
    unfold polynomial8
    fun_prop
  have hfactor : (polynomial8 (updateCoefficient8 b j c) - polynomial8 b) =ᶠ[𝓝 0]
      (fun x : ℝ ↦ -(-(c - b j)) * (x ^ (j.1 + 1) * 1) +
        x ^ (j.1 + 1 + 1) * 0) := by
    filter_upwards with x
    change polynomial8 (updateCoefficient8 b j c) x - polynomial8 b x = _
    rw [polynomial8_update_sub]
    ring
  have htri := triangular_jet_of_factorization hn (-(c - b j)) hnew hold
    (Q := fun _ ↦ 1) (E := fun _ ↦ 0) (by fun_prop) (by fun_prop) hfactor
  by_cases hnj : n = j.1 + 1
  · simp only [hnj, if_true] at htri ⊢
    ring_nf at htri ⊢
    exact htri
  · simpa only [hnj, if_false] using htri

/-- Adding the fixed center `y_*` does not change any positive-order update jet. -/
theorem translatedPolynomial8_update_jet (yStar : ℝ) (b : Fin 8 → ℝ)
    (j : Fin 8) (c : ℝ) {n : ℕ} (hn : n ≤ j.1 + 1) :
    iteratedDeriv n (fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x) 0 -
      iteratedDeriv n (fun x ↦ yStar + polynomial8 b x) 0 =
        if n = j.1 + 1 then (c - b j) * (j.1 + 1).factorial else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [polynomial8]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [iteratedDeriv_const_add hnpos, iteratedDeriv_const_add hnpos]
    exact polynomial8_update_jet b j c hn

/-- Multiplication by the identity shifts scalar jets by one order. -/
theorem iteratedDeriv_id_mul_zero (n : ℕ) (Q : ℝ → ℝ) (hQ : ContDiffAt ℝ n Q 0) :
    iteratedDeriv n (fun x : ℝ ↦ x * Q x) 0 =
      (n : ℝ) * iteratedDeriv (n - 1) Q 0 := by
  cases n with
  | zero => simp
  | succ n =>
      have hid : ContDiffAt ℝ (n + 1) (fun x : ℝ ↦ x) 0 := by fun_prop
      rw [show (fun x : ℝ ↦ x * Q x) = (fun x : ℝ ↦ x) * Q by rfl,
        iteratedDeriv_mul hid hQ]
      rw [Finset.sum_eq_single 1]
      · simp [Nat.choose_one_right]
      · intro i hi hi1
        simp [iteratedDeriv_fun_id_zero, hi1]
      · intro hnot
        exfalso
        apply hnot
        simp

/-- The derivative of the updated polynomial differs by the derivative of its single
new monomial. -/
theorem deriv_polynomial8_update_sub (b : Fin 8 → ℝ) (j : Fin 8) (c x : ℝ) :
    deriv (polynomial8 (updateCoefficient8 b j c)) x - deriv (polynomial8 b) x =
      (c - b j) * (j.1 + 1) * x ^ j.1 := by
  have hfun : polynomial8 (updateCoefficient8 b j c) =
      fun y ↦ polynomial8 b y + (c - b j) * y ^ (j.1 + 1) := by
    funext y
    linarith [polynomial8_update_sub b j c y]
  have hold : DifferentiableAt ℝ (polynomial8 b) x := by
    unfold polynomial8
    fun_prop
  have hmonomial : HasDerivAt (fun y : ℝ ↦ (c - b j) * y ^ (j.1 + 1))
      ((c - b j) * (j.1 + 1) * x ^ j.1) x := by
    simpa [Nat.cast_add, mul_assoc] using
      ((hasDerivAt_pow (j.1 + 1) x).const_mul (c - b j))
  have hderiv : deriv (fun y ↦ polynomial8 b y + (c - b j) * y ^ (j.1 + 1)) x =
      deriv (polynomial8 b) x + (c - b j) * (j.1 + 1) * x ^ j.1 :=
    (hold.hasDerivAt.add hmonomial).deriv
  rw [hfun, hderiv]
  ring

/-- The explicit `-x²p₈'` part of `H₈` changes only at order `j+2`, hence it
does not affect any jet through the updated order `j+1`. -/
theorem reciprocalDerivativeTerm_update_jet_zero (b : Fin 8 → ℝ) (j : Fin 8)
    (c : ℝ) {n : ℕ} (hn : n ≤ j.1 + 1) :
    iteratedDeriv n
        (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 (updateCoefficient8 b j c)) x) 0 -
      iteratedDeriv n (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 b) x) 0 = 0 := by
  have hnew : ContDiffAt ℝ n
      (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 (updateCoefficient8 b j c)) x) 0 := by
    unfold polynomial8
    fun_prop
  have hold : ContDiffAt ℝ n (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 b) x) 0 := by
    unfold polynomial8
    fun_prop
  have hfactor :
      ((fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 (updateCoefficient8 b j c)) x) -
          (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 b) x)) =ᶠ[𝓝 0]
        (fun x : ℝ ↦ -(0 : ℝ) * (x ^ (j.1 + 1) * 0) +
          x ^ (j.1 + 1 + 1) * (-(c - b j) * (j.1 + 1))) := by
    filter_upwards with x
    change -x ^ 2 * deriv (polynomial8 (updateCoefficient8 b j c)) x -
      (-x ^ 2 * deriv (polynomial8 b) x) = _
    rw [show deriv (polynomial8 (updateCoefficient8 b j c)) x =
      deriv (polynomial8 b) x + (c - b j) * (j.1 + 1) * x ^ j.1 by
        linarith [deriv_polynomial8_update_sub b j c x]]
    ring
  have htri := triangular_jet_of_factorization hn 0 hnew hold
    (Q := fun _ ↦ 0) (E := fun _ ↦ -(c - b j) * (j.1 + 1))
    (by fun_prop) (by fun_prop) hfactor
  simpa using htri

/-- Updating `b_j` changes the corresponding jet of a smooth composition only through
the ordinary derivative of the outer function.  This is the triangular chain-rule step
used for the `F(y_*+p₈)` term. -/
theorem translatedPolynomial8_comp_update_jet (outer : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) (j : Fin 8) (c : ℝ) {n : ℕ} (hn : n ≤ j.1 + 1)
    (houter : ContDiffAt ℝ (j.1 + 1) outer yStar) :
    iteratedDeriv n
        (outer ∘ fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x) 0 -
      iteratedDeriv n (outer ∘ fun x ↦ yStar + polynomial8 b x) 0 =
        if n = j.1 + 1 then
          deriv outer yStar * ((c - b j) * (j.1 + 1).factorial)
        else 0 := by
  let innerNew := fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x
  let innerOld := fun x ↦ yStar + polynomial8 b x
  have hvalue : innerNew 0 = innerOld 0 := by simp [innerNew, innerOld, polynomial8]
  have hcenter : innerNew 0 = yStar := by simp [innerNew, polynomial8]
  have hinnerNew : ContDiffAt ℝ (j.1 + 1) innerNew 0 := by
    dsimp only [innerNew]
    unfold polynomial8
    fun_prop
  have hinnerOld : ContDiffAt ℝ (j.1 + 1) innerOld 0 := by
    dsimp only [innerOld]
    unfold polynomial8
    fun_prop
  have hlower : ∀ k ≤ j.1, iteratedDeriv k innerNew 0 = iteratedDeriv k innerOld 0 := by
    intro k hk
    have hupdate := translatedPolynomial8_update_jet yStar b j c
      (n := k) (hk.trans (Nat.le_succ j.1))
    have hkne : k ≠ j.1 + 1 := by omega
    simp only [hkne, if_false] at hupdate
    linarith
  by_cases htop : n = j.1 + 1
  · subst n
    have hlead := iteratedDeriv_comp_succ_sub_of_lower_jets_eq hvalue hlower
      (hcenter ▸ houter) hinnerNew hinnerOld
    have hupdate := translatedPolynomial8_update_jet yStar b j c
      (n := j.1 + 1) (le_refl _)
    simp only [innerNew, innerOld] at hlead hupdate ⊢
    simp only [if_true] at hupdate ⊢
    rw [hlead, hupdate]
    simp [polynomial8]
  · have hnlt : n ≤ j.1 := by omega
    have hcomp := iteratedDeriv_comp_eq_of_jets_eq hvalue
      (fun k hk ↦ hlower k (hk.trans hnlt))
      ((hcenter ▸ houter).of_le (by exact_mod_cast hn))
      (hinnerNew.of_le (by exact_mod_cast hn)) (hinnerOld.of_le (by exact_mod_cast hn))
    simp only [innerNew, innerOld] at hcomp ⊢
    rw [hcomp]
    simp [htop]

/-- The extra factor `x` delays the effect of an updated coefficient by one order.
This is the triangular step for the `x G(y_*+p₈)` term. -/
theorem translatedPolynomial8_id_mul_comp_update_jet_zero (outer : ℝ → ℝ)
    (yStar : ℝ) (b : Fin 8 → ℝ) (j : Fin 8) (c : ℝ) {n : ℕ}
    (hn : n ≤ j.1 + 1) (houter : ContDiffAt ℝ (j.1 + 1) outer yStar) :
    iteratedDeriv n
        (fun x ↦ x * outer (yStar + polynomial8 (updateCoefficient8 b j c) x)) 0 -
      iteratedDeriv n (fun x ↦ x * outer (yStar + polynomial8 b x)) 0 = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      have hnlt : n < j.1 + 1 := by omega
      have hnle : n ≤ j.1 + 1 := hnlt.le
      have hnew : ContDiffAt ℝ (n + 1)
          (fun x ↦ outer (yStar + polynomial8 (updateCoefficient8 b j c) x)) 0 := by
        have hinner : ContDiffAt ℝ (n + 1)
            (fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x) 0 := by
          unfold polynomial8
          fun_prop
        have hcenter : yStar + polynomial8 (updateCoefficient8 b j c) 0 = yStar := by
          simp [polynomial8]
        exact (hcenter ▸ houter.of_le (by exact_mod_cast hn)).comp 0 hinner
      have hold : ContDiffAt ℝ (n + 1)
          (fun x ↦ outer (yStar + polynomial8 b x)) 0 := by
        have hinner : ContDiffAt ℝ (n + 1)
            (fun x ↦ yStar + polynomial8 b x) 0 := by
          unfold polynomial8
          fun_prop
        have hcenter : yStar + polynomial8 b 0 = yStar := by simp [polynomial8]
        exact (hcenter ▸ houter.of_le (by exact_mod_cast hn)).comp 0 hinner
      rw [iteratedDeriv_id_mul_zero (n + 1) _ hnew,
        iteratedDeriv_id_mul_zero (n + 1) _ hold]
      simp only [Nat.add_sub_cancel]
      have hcomp := translatedPolynomial8_comp_update_jet outer yStar b j c
        (n := n) hnle houter
      have hnne : n ≠ j.1 + 1 := by omega
      simp only [hnne, if_false] at hcomp
      change iteratedDeriv n
        (fun x ↦ outer (yStar + polynomial8 (updateCoefficient8 b j c) x)) 0 -
        iteratedDeriv n (fun x ↦ outer (yStar + polynomial8 b x)) 0 = 0 at hcomp
      rw [show iteratedDeriv n
          (fun x ↦ outer (yStar + polynomial8 (updateCoefficient8 b j c) x)) 0 =
          iteratedDeriv n (fun x ↦ outer (yStar + polynomial8 b x)) 0 by
        exact sub_eq_zero.mp hcomp]
      ring

/-- The complete local triangular jet law for `H₈`.  Updating coefficient `j`
leaves all jets below order `j+1` unchanged and changes that jet only by
`-F'(y_*) (c-b_j) (j+1)!`. -/
theorem reciprocalDefect8_update_jet (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) (j : Fin 8) (c : ℝ) {n : ℕ} (hn : n ≤ j.1 + 1)
    (hF : ContDiffAt ℝ (j.1 + 1) F yStar)
    (hG : ContDiffAt ℝ (j.1 + 1) G yStar) :
    iteratedDeriv n (reciprocalDefect8 F G yStar (updateCoefficient8 b j c)) 0 -
      iteratedDeriv n (reciprocalDefect8 F G yStar b) 0 =
        if n = j.1 + 1 then
          -(deriv F yStar * ((c - b j) * (j.1 + 1).factorial))
        else 0 := by
  let Tnew := fun x : ℝ ↦
    -x ^ 2 * deriv (polynomial8 (updateCoefficient8 b j c)) x
  let Told := fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 b) x
  let Fnew := fun x : ℝ ↦
    F (yStar + polynomial8 (updateCoefficient8 b j c) x)
  let Fold := fun x : ℝ ↦ F (yStar + polynomial8 b x)
  let Gnew := fun x : ℝ ↦
    x * G (yStar + polynomial8 (updateCoefficient8 b j c) x)
  let Gold := fun x : ℝ ↦ x * G (yStar + polynomial8 b x)
  have hTnew : ContDiffAt ℝ n Tnew 0 := by
    dsimp only [Tnew]
    unfold polynomial8
    fun_prop
  have hTold : ContDiffAt ℝ n Told 0 := by
    dsimp only [Told]
    unfold polynomial8
    fun_prop
  have hFnew : ContDiffAt ℝ n Fnew 0 := by
    have hinner : ContDiffAt ℝ n
        (fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x) 0 := by
      unfold polynomial8
      fun_prop
    have hcenter : yStar + polynomial8 (updateCoefficient8 b j c) 0 = yStar := by
      simp [polynomial8]
    exact (hcenter ▸ hF.of_le (by exact_mod_cast hn)).comp 0 hinner
  have hFold : ContDiffAt ℝ n Fold 0 := by
    have hinner : ContDiffAt ℝ n (fun x ↦ yStar + polynomial8 b x) 0 := by
      unfold polynomial8
      fun_prop
    have hcenter : yStar + polynomial8 b 0 = yStar := by simp [polynomial8]
    exact (hcenter ▸ hF.of_le (by exact_mod_cast hn)).comp 0 hinner
  have hGnew : ContDiffAt ℝ n Gnew 0 := by
    dsimp only [Gnew]
    have hinner : ContDiffAt ℝ n
        (fun x ↦ yStar + polynomial8 (updateCoefficient8 b j c) x) 0 := by
      unfold polynomial8
      fun_prop
    have hcenter : yStar + polynomial8 (updateCoefficient8 b j c) 0 = yStar := by
      simp [polynomial8]
    have hcomp := (hcenter ▸ hG.of_le (by exact_mod_cast hn)).comp 0 hinner
    exact contDiffAt_id.mul hcomp
  have hGold : ContDiffAt ℝ n Gold 0 := by
    dsimp only [Gold]
    have hinner : ContDiffAt ℝ n (fun x ↦ yStar + polynomial8 b x) 0 := by
      unfold polynomial8
      fun_prop
    have hcenter : yStar + polynomial8 b 0 = yStar := by simp [polynomial8]
    have hcomp := (hcenter ▸ hG.of_le (by exact_mod_cast hn)).comp 0 hinner
    exact contDiffAt_id.mul hcomp
  have hT := reciprocalDerivativeTerm_update_jet_zero b j c hn
  have hFc := translatedPolynomial8_comp_update_jet F yStar b j c hn hF
  have hGc := translatedPolynomial8_id_mul_comp_update_jet_zero G yStar b j c hn hG
  have hdecompNew : iteratedDeriv n (fun x ↦ Tnew x - Fnew x - Gnew x) 0 =
      (iteratedDeriv n Tnew 0 - iteratedDeriv n Fnew 0) - iteratedDeriv n Gnew 0 := by
    rw [iteratedDeriv_fun_sub (hTnew.sub hFnew) hGnew,
      iteratedDeriv_fun_sub hTnew hFnew]
  have hdecompOld : iteratedDeriv n (fun x ↦ Told x - Fold x - Gold x) 0 =
      (iteratedDeriv n Told 0 - iteratedDeriv n Fold 0) - iteratedDeriv n Gold 0 := by
    rw [iteratedDeriv_fun_sub (hTold.sub hFold) hGold,
      iteratedDeriv_fun_sub hTold hFold]
  change iteratedDeriv n (fun x ↦ Tnew x - Fnew x - Gnew x) 0 -
    iteratedDeriv n (fun x ↦ Told x - Fold x - Gold x) 0 = _
  rw [hdecompNew, hdecompOld]
  change iteratedDeriv n Tnew 0 - iteratedDeriv n Told 0 = 0 at hT
  change iteratedDeriv n Fnew 0 - iteratedDeriv n Fold 0 = _ at hFc
  change iteratedDeriv n Gnew 0 - iteratedDeriv n Gold 0 = 0 at hGc
  by_cases htop : n = j.1 + 1
  · subst n
    simp only [if_true] at hFc ⊢
    linarith
  · simp only [htop, if_false] at hFc ⊢
    linarith

/-- The recursive coefficients kill every reciprocal-defect jet through the current
stage.  At stage eight this is precisely the source's recursive `b₁,…,b₈`
construction. -/
theorem recursiveCoefficients8_vanish (F G : ℝ → ℝ) (yStar : ℝ)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0)
    (hF : ContDiffAt ℝ 8 F yStar) (hG : ContDiffAt ℝ 8 G yStar) :
    ∀ stage ≤ 8, ∀ k ≤ stage,
      iteratedDeriv k
        (reciprocalDefect8 F G yStar (recursiveCoefficients8 F G yStar stage)) 0 = 0 := by
  intro stage hstage
  induction stage with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simp [recursiveCoefficients8, reciprocalDefect8, polynomial8, hFzero]
  | succ stage ih =>
      have hstageLt : stage < 8 := by omega
      let previous := recursiveCoefficients8 F G yStar stage
      let j : Fin 8 := ⟨stage, hstageLt⟩
      let oldJet := iteratedDeriv (stage + 1)
        (reciprocalDefect8 F G yStar previous) 0
      let chosen := previous j + oldJet / (deriv F yStar * (stage + 1).factorial)
      have hrec : recursiveCoefficients8 F G yStar (stage + 1) =
          updateCoefficient8 previous j chosen := by
        simp only [recursiveCoefficients8, hstageLt, ↓reduceDIte, previous, j, oldJet, chosen]
      intro k hk
      rw [hrec]
      have hkOrder : k ≤ j.1 + 1 := by simpa only [j] using hk
      have hFstage : ContDiffAt ℝ (j.1 + 1) F yStar :=
        hF.of_le (by exact_mod_cast hstage)
      have hGstage : ContDiffAt ℝ (j.1 + 1) G yStar :=
        hG.of_le (by exact_mod_cast hstage)
      have hupdate := reciprocalDefect8_update_jet F G yStar previous j chosen
        hkOrder hFstage hGstage
      by_cases htop : k = stage + 1
      · subst k
        have htopj : stage + 1 = j.1 + 1 := by rfl
        simp only [htopj, if_true] at hupdate
        change iteratedDeriv (stage + 1)
            (reciprocalDefect8 F G yStar (updateCoefficient8 previous j chosen)) 0 -
          oldJet = _ at hupdate
        have hdenom : deriv F yStar * (stage + 1).factorial ≠ 0 := by
          exact mul_ne_zero hmu (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        have hchosen : chosen - previous j =
            oldJet / (deriv F yStar * (stage + 1).factorial) := by
          simp only [chosen]
          ring
        rw [hchosen] at hupdate
        simp only [j] at hupdate
        have hcancel : deriv F yStar *
            (oldJet / (deriv F yStar * (stage + 1).factorial) *
              (stage + 1).factorial) = oldJet := by
          field_simp [hdenom]
        rw [hcancel] at hupdate
        linarith
      · have hkPrev : k ≤ stage := by omega
        have hold := ih (by omega : stage ≤ 8) k hkPrev
        have hkne : k ≠ j.1 + 1 := by simpa only [j] using htop
        simp only [hkne, if_false] at hupdate
        change iteratedDeriv k
            (reciprocalDefect8 F G yStar (updateCoefficient8 previous j chosen)) 0 -
          iteratedDeriv k (reciprocalDefect8 F G yStar previous) 0 = 0 at hupdate
        change iteratedDeriv k (reciprocalDefect8 F G yStar previous) 0 = 0 at hold
        linarith

/-- The stage-eight recursive coefficients have all the required vanishing jets. -/
theorem recursiveCoefficients8_hasVanishingReciprocalJet (F G : ℝ → ℝ) (yStar : ℝ)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0)
    (hF : ContDiffAt ℝ 8 F yStar) (hG : ContDiffAt ℝ 8 G yStar) :
    HasVanishingReciprocalJet F G yStar (recursiveCoefficients8 F G yStar 8) := by
  intro k hk
  exact recursiveCoefficients8_vanish F G yStar hFzero hmu hF hG 8 le_rfl k hk

/-- With every polynomial coefficient initially zero, the first defect jet is
`-G(y_*)`. -/
theorem reciprocalDefect8_zeroCoefficients_firstJet (F G : ℝ → ℝ) (yStar : ℝ) :
    iteratedDeriv 1 (reciprocalDefect8 F G yStar (fun _ ↦ 0)) 0 = -G yStar := by
  have hpoly : polynomial8 (fun _ : Fin 8 ↦ (0 : ℝ)) = fun _ ↦ 0 := by
    funext x
    simp [polynomial8]
  have hfun : reciprocalDefect8 F G yStar (fun _ ↦ 0) =
      fun x : ℝ ↦ -F yStar - x * G yStar := by
    funext x
    simp [reciprocalDefect8, hpoly]
  rw [hfun, iteratedDeriv_succ']
  simp

/-- The first recursively chosen coefficient is the source-visible value
`-G(y_*)/F'(y_*)`; subsequent updates affect only higher coordinates. -/
theorem recursiveCoefficients8_firstCoefficient (F G : ℝ → ℝ) (yStar : ℝ) :
    recursiveCoefficients8 F G yStar 8 (0 : Fin 8) =
      -G yStar / deriv F yStar := by
  have hstage : ∀ stage : ℕ, 1 ≤ stage → stage ≤ 8 →
      recursiveCoefficients8 F G yStar stage (0 : Fin 8) =
        -G yStar / deriv F yStar := by
    intro stage hpos hle
    induction stage with
    | zero => omega
    | succ n ih =>
        rw [recursiveCoefficients8]
        split_ifs with hn
        · simp only
          by_cases hnzero : n = 0
          · subst n
            have hjet : deriv
                (reciprocalDefect8 F G yStar (fun _ ↦ 0)) 0 = -G yStar := by
              simpa [iteratedDeriv_succ'] using
                reciprocalDefect8_zeroCoefficients_firstJet F G yStar
            simp [recursiveCoefficients8, updateCoefficient8, hjet]
          · have hne : (⟨n, hn⟩ : Fin 8) ≠ (0 : Fin 8) := by
              intro h
              have : n = 0 := by simpa using congrArg Fin.val h
              exact hnzero this
            rw [show updateCoefficient8
                (recursiveCoefficients8 F G yStar n) ⟨n, hn⟩
                  (recursiveCoefficients8 F G yStar n ⟨n, hn⟩ +
                    iteratedDeriv (n + 1)
                      (reciprocalDefect8 F G yStar
                        (recursiveCoefficients8 F G yStar n)) 0 /
                      (deriv F yStar * (n + 1).factorial)) 0 =
                recursiveCoefficients8 F G yStar n 0 by
                  simp [updateCoefficient8, Function.update, Ne.symm hne]]
            exact ih (by omega) (by omega)
        · omega
  exact hstage 8 (by omega) (by omega)

/-- Restrict the recursively chosen eight coefficients to the four coefficients
visible in the public expansion. -/
noncomputable def finiteCoefficients4 (F G : ℝ → ℝ) (yStar : ℝ) : Fin 4 → ℝ :=
  fun j ↦ recursiveCoefficients8 F G yStar 8 ⟨j.1, j.2.trans (by omega)⟩

/-- The restricted coefficient vector retains the source-visible first value. -/
theorem finiteCoefficients4_firstCoefficient (F G : ℝ → ℝ) (yStar : ℝ) :
    finiteCoefficients4 F G yStar 0 = -G yStar / deriv F yStar := by
  exact recursiveCoefficients8_firstCoefficient F G yStar

/-- Source regularity localizes to the reciprocal defect on a symmetric interval about
the origin.  This is the precise `C⁹` input required by MI10. -/
theorem exists_reciprocalDefect8_contDiffOn {I : Set ℝ} (F G : ℝ → ℝ)
    (yStar : ℝ) (b : Fin 8 → ℝ) (hIopen : IsOpen I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I) :
    ∃ η : ℝ, 0 < η ∧
      ContDiffOn ℝ 9 (reciprocalDefect8 F G yStar b) (Ioo (-η) η) := by
  let inner : ℝ → ℝ := fun x ↦ yStar + polynomial8 b x
  have hinner : ContDiff ℝ 9 inner := by
    dsimp [inner]
    unfold polynomial8
    fun_prop
  have hinner_zero : inner 0 = yStar := by
    simp [inner, polynomial8]
  have hevent : ∀ᶠ x in 𝓝 (0 : ℝ), inner x ∈ I := by
    apply hinner.continuous.continuousAt
    simpa only [hinner_zero] using hIopen.mem_nhds hyStar
  rcases Metric.mem_nhds_iff.mp hevent with ⟨η, hη, hball⟩
  have hmaps : MapsTo inner (Ioo (-η) η) I := by
    intro x hx
    apply hball
    simpa only [Real.ball_zero_eq_Ioo] using hx
  have hFcomp : ContDiffOn ℝ 9 (fun x ↦ F (inner x)) (Ioo (-η) η) := by
    change ContDiffOn ℝ 9 (F ∘ inner) (Ioo (-η) η)
    exact hF.comp hinner.contDiffOn hmaps
  have hGcomp : ContDiffOn ℝ 9 (fun x ↦ G (inner x)) (Ioo (-η) η) := by
    change ContDiffOn ℝ 9 (G ∘ inner) (Ioo (-η) η)
    exact hG.comp hinner.contDiffOn hmaps
  refine ⟨η, hη, ?_⟩
  change ContDiffOn ℝ 9
    (fun x ↦ -x ^ 2 * deriv (polynomial8 b) x - F (inner x) - x * G (inner x))
      (Ioo (-η) η)
  have hpolyTerm : ContDiff ℝ 9
      (fun x : ℝ ↦ -x ^ 2 * deriv (polynomial8 b) x) := by
    unfold polynomial8
    fun_prop
  exact (hpolyTerm.contDiffOn.sub hFcomp).sub
    (contDiffOn_id.mul hGcomp)

/-- The recursively normalized reciprocal defect satisfies all four Taylor-remainder
estimates supplied by MI10. -/
theorem recursive_reciprocalDefect8_jet_isBigO {I : Set ℝ} (F G : ℝ → ℝ)
    (yStar : ℝ) (hIopen : IsOpen I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) :
    ∀ m ≤ 4,
      (fun x ↦ iteratedDeriv m
        (reciprocalDefect8 F G yStar (recursiveCoefficients8 F G yStar 8)) x) =O[𝓝 0]
        fun x ↦ x ^ (9 - m) := by
  let b := recursiveCoefficients8 F G yStar 8
  obtain ⟨η, hη, hsmooth⟩ :=
    exists_reciprocalDefect8_contDiffOn F G yStar b hIopen hyStar hF hG
  have hF8 : ContDiffAt ℝ 8 F yStar :=
    ((hF yStar hyStar).contDiffAt (hIopen.mem_nhds hyStar)).of_le (by norm_num)
  have hG8 : ContDiffAt ℝ 8 G yStar :=
    ((hG yStar hyStar).contDiffAt (hIopen.mem_nhds hyStar)).of_le (by norm_num)
  have hvanish : ∀ j ≤ 8,
      iteratedDeriv j (reciprocalDefect8 F G yStar b) 0 = 0 :=
    recursiveCoefficients8_hasVanishingReciprocalJet F G yStar hFzero hmu hF8 hG8
  exact MI10_taylor_with_derivative_remainders
    (reciprocalDefect8 F G yStar b) η hη hsmooth hvanish

/-- `P₈` tends to `y_*` under the reciprocal change of variables. -/
theorem approximation8_tendsto (yStar : ℝ) (b : Fin 8 → ℝ) :
    Tendsto (approximation8 yStar b) atTop (𝓝 yStar) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hpoly : Continuous (polynomial8 b) := by
    unfold polynomial8
    fun_prop
  have hzero : polynomial8 b 0 = 0 := by
    simp [polynomial8]
  change Tendsto (fun t : ℝ ↦ yStar + polynomial8 b t⁻¹) atTop (𝓝 yStar)
  simpa only [Function.comp_apply, hzero, add_zero] using
    (hpoly.continuousAt.tendsto.comp hinv).const_add yStar

/-- The displayed identity `D₈(t)=H₈(t⁻¹)`. -/
theorem defect8_eq_reciprocalDefect8 (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0) :
    defect8 F G yStar b t = reciprocalDefect8 F G yStar b t⁻¹ := by
  have hpoly : Differentiable ℝ (polynomial8 b) := by
    unfold polynomial8
    fun_prop
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(t ^ 2)⁻¹) t := by
    simpa only [one_div] using hasDerivAt_inv ht
  have happ : HasDerivAt (approximation8 yStar b)
      (deriv (polynomial8 b) t⁻¹ * -(t ^ 2)⁻¹) t := by
    change HasDerivAt (fun s ↦ yStar + polynomial8 b s⁻¹)
      (deriv (polynomial8 b) t⁻¹ * -(t ^ 2)⁻¹) t
    exact (hpoly.differentiableAt.hasDerivAt.comp t hinv).const_add yStar
  rw [defect8, reciprocalDefect8, happ.deriv]
  simp only [approximation8]
  field_simp

/-- The zeroth-order case of `eq:D8-bound`, obtained by composing the Taylor estimate
with `t ↦ t⁻¹`.  Orders one through four additionally require the explicit repeated
reciprocal-chain calculation from the source. -/
theorem defect8_isBigO_zero (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hH : reciprocalDefect8 F G yStar b =O[𝓝 0] (fun x : ℝ ↦ x ^ 9)) :
    defect8 F G yStar b =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  have hcomp := hH.comp_tendsto (tendsto_inv_atTop_zero :
    Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  apply hcomp.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (defect8_eq_reciprocalDefect8 F G yStar b ht.ne').symm
  · filter_upwards with t
    simp only [Function.comp_apply, inv_pow]

/-- The first reciprocal-chain identity used in `eq:D8-bound`. -/
theorem defect8_first_derivative_eq (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hH : DifferentiableAt ℝ (reciprocalDefect8 F G yStar b) t⁻¹) :
    iteratedDeriv 1 (defect8 F G yStar b) t =
      deriv (reciprocalDefect8 F G yStar b) t⁻¹ * (-(t ^ 2)⁻¹) := by
  let H := reciprocalDefect8 F G yStar b
  have heq : defect8 F G yStar b =ᶠ[𝓝 t] fun s ↦ H s⁻¹ := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    exact defect8_eq_reciprocalDefect8 F G yStar b hs
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-(t ^ 2)⁻¹) t := by
    simpa only [one_div] using hasDerivAt_inv ht
  have hcomp : HasDerivAt (fun s ↦ H s⁻¹)
      (deriv H t⁻¹ * (-(t ^ 2)⁻¹)) t :=
    hH.hasDerivAt.comp t hinv
  rw [iteratedDeriv_succ']
  exact (hcomp.congr_of_eventuallyEq heq).deriv

/-- The second derivative of reciprocal inversion away from the origin. -/
theorem iteratedDeriv_two_inv {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) t = 2 * (t ^ 3)⁻¹ := by
  rw [show iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) =
      deriv (deriv fun s : ℝ ↦ s⁻¹) by rw [iteratedDeriv_succ, iteratedDeriv_one]]
  have heq : deriv (fun s : ℝ ↦ s⁻¹) = fun s ↦ -(s ^ 2)⁻¹ := by
    funext s
    exact deriv_inv
  rw [heq]
  have hp := hasDerivAt_pow 2 t
  have hi := hp.inv (pow_ne_zero 2 ht)
  have hn := hi.neg
  change deriv (-(fun s : ℝ ↦ s ^ 2)⁻¹) t = _
  rw [hn.deriv]
  field_simp
  ring

/-- The second reciprocal-chain identity used in `eq:D8-bound`. -/
theorem defect8_second_derivative_eq (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hH : ContDiffAt ℝ 2 (reciprocalDefect8 F G yStar b) t⁻¹) :
    iteratedDeriv 2 (defect8 F G yStar b) t =
      iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ * (-(t ^ 2)⁻¹) ^ 2 +
        deriv (reciprocalDefect8 F G yStar b) t⁻¹ * (2 * (t ^ 3)⁻¹) := by
  let H := reciprocalDefect8 F G yStar b
  let inv : ℝ → ℝ := fun s ↦ s⁻¹
  have heq : defect8 F G yStar b =ᶠ[𝓝 t] H ∘ inv := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    exact defect8_eq_reciprocalDefect8 F G yStar b hs
  have hinv : ContDiffAt ℝ 2 inv t := by
    dsimp [inv]
    fun_prop
  rw [heq.iteratedDeriv_eq 2,
    iteratedDeriv_comp_two hH hinv, deriv_inv, iteratedDeriv_two_inv ht]

/-- The third derivative of reciprocal inversion away from the origin. -/
theorem iteratedDeriv_three_inv {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv 3 (fun s : ℝ ↦ s⁻¹) t = -6 * (t ^ 4)⁻¹ := by
  rw [iteratedDeriv_succ]
  have heq : iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) =ᶠ[𝓝 t]
      fun s ↦ 2 * (s ^ 3)⁻¹ := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    exact iteratedDeriv_two_inv hs
  have hp := hasDerivAt_pow 3 t
  have hd := (hp.inv (pow_ne_zero 3 ht)).const_mul (2 : ℝ)
  rw [heq.deriv_eq]
  change deriv (fun y ↦ 2 * (fun x : ℝ ↦ x ^ 3)⁻¹ y) t = _
  rw [hd.deriv]
  field_simp
  ring

/-- A `C^(m+1)` scalar function has the expected derivative of its `m`th iterated
derivative. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffAt {H : ℝ → ℝ} {x : ℝ} (m : ℕ)
    (hH : ContDiffAt ℝ (m + 1) H x) :
    HasDerivAt (iteratedDeriv m H) (iteratedDeriv (m + 1) H x) x := by
  induction m generalizing H with
  | zero =>
      simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.zero_add] using
        (hH.differentiableAt (by norm_num)).hasDerivAt
  | succ m ih =>
      rw [iteratedDeriv_succ', show m + 1 + 1 = (m + 1) + 1 by omega,
        iteratedDeriv_succ']
      apply ih
      exact hH.derivWithin (m := m + 1) (by norm_num)

/-- The fourth derivative of reciprocal inversion away from the origin. -/
theorem iteratedDeriv_four_inv {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv 4 (fun s : ℝ ↦ s⁻¹) t = 24 * (t ^ 5)⁻¹ := by
  rw [iteratedDeriv_succ]
  have heq : iteratedDeriv 3 (fun s : ℝ ↦ s⁻¹) =ᶠ[𝓝 t]
      fun s ↦ -6 * (s ^ 4)⁻¹ := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    exact iteratedDeriv_three_inv hs
  have hp := hasDerivAt_pow 4 t
  have hd := (hp.inv (pow_ne_zero 4 ht)).const_mul (-6 : ℝ)
  rw [heq.deriv_eq]
  change deriv (fun y ↦ -6 * (fun x : ℝ ↦ x ^ 4)⁻¹ y) t = _
  rw [hd.deriv]
  field_simp
  ring

/-- The third reciprocal-chain identity used in `eq:D8-bound`. -/
theorem defect8_third_derivative_eq (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hH : ContDiffAt ℝ 3 (reciprocalDefect8 F G yStar b) t⁻¹) :
    iteratedDeriv 3 (defect8 F G yStar b) t =
      iteratedDeriv 3 (reciprocalDefect8 F G yStar b) t⁻¹ * (-(t ^ 2)⁻¹) ^ 3 +
      3 * iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (2 * (t ^ 3)⁻¹) * (-(t ^ 2)⁻¹) +
      deriv (reciprocalDefect8 F G yStar b) t⁻¹ * (-6 * (t ^ 4)⁻¹) := by
  let H := reciprocalDefect8 F G yStar b
  let inv : ℝ → ℝ := fun s ↦ s⁻¹
  have heq : defect8 F G yStar b =ᶠ[𝓝 t] H ∘ inv := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    exact defect8_eq_reciprocalDefect8 F G yStar b hs
  have hinv : ContDiffAt ℝ 3 inv t := by
    dsimp [inv]
    fun_prop
  rw [heq.iteratedDeriv_eq 3, iteratedDeriv_comp_three hH hinv,
    deriv_inv, iteratedDeriv_two_inv ht, iteratedDeriv_three_inv ht]

/-- A simplified form of the third reciprocal-chain identity, convenient for one
final differentiation. -/
theorem defect8_third_derivative_eq_simplified (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hH : ContDiffAt ℝ 3 (reciprocalDefect8 F G yStar b) t⁻¹) :
    iteratedDeriv 3 (defect8 F G yStar b) t =
      -iteratedDeriv 3 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 6)⁻¹ -
      6 * iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 5)⁻¹ -
      6 * iteratedDeriv 1 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 4)⁻¹ := by
  rw [defect8_third_derivative_eq F G yStar b ht hH]
  simp only [iteratedDeriv_one]
  field_simp
  ring

/-- The fourth reciprocal-chain identity used in `eq:D8-bound`. -/
theorem defect8_fourth_derivative_eq (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hH : ContDiffAt ℝ 4 (reciprocalDefect8 F G yStar b) t⁻¹) :
    iteratedDeriv 4 (defect8 F G yStar b) t =
      iteratedDeriv 4 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 8)⁻¹ +
      12 * iteratedDeriv 3 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 7)⁻¹ +
      36 * iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 6)⁻¹ +
      24 * iteratedDeriv 1 (reciprocalDefect8 F G yStar b) t⁻¹ * (t ^ 5)⁻¹ := by
  let H := reciprocalDefect8 F G yStar b
  let inv : ℝ → ℝ := fun s ↦ s⁻¹
  have hinv : HasDerivAt inv (-(t ^ 2)⁻¹) t := by
    dsimp [inv]
    simpa only [one_div] using hasDerivAt_inv ht
  have hH1 := hasDerivAt_iteratedDeriv_of_contDiffAt 1
    (hH.of_le (by norm_num) : ContDiffAt ℝ 2 H t⁻¹)
  have hH2 := hasDerivAt_iteratedDeriv_of_contDiffAt 2
    (hH.of_le (by norm_num) : ContDiffAt ℝ 3 H t⁻¹)
  have hH3 := hasDerivAt_iteratedDeriv_of_contDiffAt 3 hH
  have hc1 := hH1.comp t hinv
  have hc2 := hH2.comp t hinv
  have hc3 := hH3.comp t hinv
  have hq4 := (hasDerivAt_pow 4 t).inv (pow_ne_zero 4 ht)
  have hq5 := (hasDerivAt_pow 5 t).inv (pow_ne_zero 5 ht)
  have hq6 := (hasDerivAt_pow 6 t).inv (pow_ne_zero 6 ht)
  have hterm1 := (hc3.mul hq6).neg
  have hterm2 := (hc2.mul hq5).const_mul (-6 : ℝ)
  have hterm3 := (hc1.mul hq4).const_mul (-6 : ℝ)
  have hrhs : HasDerivAt
      (fun s ↦
        -iteratedDeriv 3 H s⁻¹ * (s ^ 6)⁻¹ -
        6 * iteratedDeriv 2 H s⁻¹ * (s ^ 5)⁻¹ -
        6 * iteratedDeriv 1 H s⁻¹ * (s ^ 4)⁻¹)
      (iteratedDeriv 4 H t⁻¹ * (t ^ 8)⁻¹ +
        12 * iteratedDeriv 3 H t⁻¹ * (t ^ 7)⁻¹ +
        36 * iteratedDeriv 2 H t⁻¹ * (t ^ 6)⁻¹ +
        24 * iteratedDeriv 1 H t⁻¹ * (t ^ 5)⁻¹) t := by
    have hraw := (hterm1.add hterm2).add hterm3
    apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
    · dsimp [H, inv] at hraw ⊢
      field_simp [ht]
      ring
    · filter_upwards with s
      dsimp [H, inv]
      ring
  have hHnear : ∀ᶠ z in 𝓝 t⁻¹, ContDiffAt ℝ 4 H z :=
    hH.eventually (by simp)
  have heq : (fun s ↦ iteratedDeriv 3 (defect8 F G yStar b) s) =ᶠ[𝓝 t]
      (fun s ↦
        -iteratedDeriv 3 H s⁻¹ * (s ^ 6)⁻¹ -
        6 * iteratedDeriv 2 H s⁻¹ * (s ^ 5)⁻¹ -
        6 * iteratedDeriv 1 H s⁻¹ * (s ^ 4)⁻¹) := by
    filter_upwards [eventually_ne_nhds ht,
      hinv.continuousAt.eventually hHnear] with s hs hsmooth
    exact defect8_third_derivative_eq_simplified F G yStar b hs
      (hsmooth.of_le (by norm_num))
  rw [iteratedDeriv_succ, heq.deriv_eq, hrhs.deriv]

/-- The order-one case of `eq:D8-bound`. -/
theorem defect8_isBigO_one (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hHsmooth : ∀ᶠ x in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (reciprocalDefect8 F G yStar b) x)
    (hH1 : (fun x ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 8)) :
    (fun t ↦ iteratedDeriv 1 (defect8 F G yStar b) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 10)⁻¹) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hcomp := hH1.comp_tendsto hinv
  have hfactor : (fun t : ℝ ↦ -(t ^ 2)⁻¹) =O[atTop]
      (fun t : ℝ ↦ (t ^ 2)⁻¹) :=
    (isBigO_refl (fun t : ℝ ↦ (t ^ 2)⁻¹) atTop).neg_left
  have hmul := hcomp.mul hfactor
  apply hmul.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hinv.eventually hHsmooth]
      with t ht hdiff
    rw [defect8_first_derivative_eq F G yStar b ht.ne' hdiff]
    simp only [iteratedDeriv_one, Function.comp_apply]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply, inv_pow]
    field_simp

/-- The order-two case of `eq:D8-bound`. -/
theorem defect8_isBigO_two (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hHsmooth : ∀ᶠ x in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 2 (reciprocalDefect8 F G yStar b) x)
    (hH1 : (fun x ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 8))
    (hH2 : (fun x ↦ iteratedDeriv 2 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 7)) :
    (fun t ↦ iteratedDeriv 2 (defect8 F G yStar b) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 11)⁻¹) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1comp := hH1.comp_tendsto hinv
  have h2comp := hH2.comp_tendsto hinv
  have hfactor1 : (fun t : ℝ ↦ (-(t ^ 2)⁻¹) ^ 2) =O[atTop]
      (fun t : ℝ ↦ (t ^ 4)⁻¹) := by
    apply (isBigO_refl (fun t : ℝ ↦ (t ^ 4)⁻¹) atTop).congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp
    · filter_upwards with t
      rfl
  have hfactor2 : (fun t : ℝ ↦ 2 * (t ^ 3)⁻¹) =O[atTop]
      (fun t : ℝ ↦ (t ^ 3)⁻¹) :=
    (isBigO_refl (fun t : ℝ ↦ (t ^ 3)⁻¹) atTop).const_mul_left 2
  have hterm1 := h2comp.mul hfactor1
  have hterm2 := h1comp.mul hfactor2
  have hterm1' :
      (fun t ↦ iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (-(t ^ 2)⁻¹) ^ 2) =O[atTop] (fun t : ℝ ↦ (t ^ 11)⁻¹) := by
    apply hterm1.congr'
    · filter_upwards with t
      rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [Function.comp_apply, inv_pow]
      field_simp
  have hterm2' :
      (fun t ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (2 * (t ^ 3)⁻¹)) =O[atTop] (fun t : ℝ ↦ (t ^ 11)⁻¹) := by
    apply hterm2.congr'
    · filter_upwards with t
      simp only [iteratedDeriv_one, Function.comp_apply]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [Function.comp_apply, inv_pow]
      field_simp
  apply (hterm1'.add hterm2').congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hinv.eventually hHsmooth]
      with t ht hsmooth
    simpa only [iteratedDeriv_one] using
      (defect8_second_derivative_eq F G yStar b ht.ne' hsmooth).symm
  · filter_upwards with t
    rfl

/-- The order-three case of `eq:D8-bound`. -/
theorem defect8_isBigO_three (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hHsmooth : ∀ᶠ x in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 3 (reciprocalDefect8 F G yStar b) x)
    (hH1 : (fun x ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 8))
    (hH2 : (fun x ↦ iteratedDeriv 2 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 7))
    (hH3 : (fun x ↦ iteratedDeriv 3 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 6)) :
    (fun t ↦ iteratedDeriv 3 (defect8 F G yStar b) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 12)⁻¹) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1comp := hH1.comp_tendsto hinv
  have h2comp := hH2.comp_tendsto hinv
  have h3comp := hH3.comp_tendsto hinv
  have hfactor1 : (fun t : ℝ ↦ (-(t ^ 2)⁻¹) ^ 3) =O[atTop]
      (fun t : ℝ ↦ (t ^ 6)⁻¹) := by
    apply ((isBigO_refl (fun t : ℝ ↦ (t ^ 6)⁻¹) atTop).neg_left).congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp
    · filter_upwards with t
      rfl
  have hfactor2 : (fun t : ℝ ↦ (2 * (t ^ 3)⁻¹) * (-(t ^ 2)⁻¹)) =O[atTop]
      (fun t : ℝ ↦ (t ^ 5)⁻¹) := by
    have ha := (isBigO_refl (fun t : ℝ ↦ (t ^ 3)⁻¹) atTop).const_mul_left 2
    have hb := (isBigO_refl (fun t : ℝ ↦ (t ^ 2)⁻¹) atTop).neg_left
    apply (ha.mul hb).congr'
    · filter_upwards with t
      rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp
  have hfactor3 : (fun t : ℝ ↦ -6 * (t ^ 4)⁻¹) =O[atTop]
      (fun t : ℝ ↦ (t ^ 4)⁻¹) :=
    (isBigO_refl (fun t : ℝ ↦ (t ^ 4)⁻¹) atTop).const_mul_left (-6)
  have hterm1 := h3comp.mul hfactor1
  have hterm2 := (h2comp.mul hfactor2).const_mul_left 3
  have hterm3 := h1comp.mul hfactor3
  have hnormalize {a q : ℕ} (haq : a + q = 12) :
      (fun t : ℝ ↦ (t ^ a)⁻¹ * (t ^ q)⁻¹) =ᶠ[atTop]
        (fun t ↦ (t ^ 12)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
    rw [← pow_add, haq]
  have hterm1' :
      (fun t ↦ iteratedDeriv 3 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (-(t ^ 2)⁻¹) ^ 3) =O[atTop] (fun t : ℝ ↦ (t ^ 12)⁻¹) := by
    apply hterm1.congr'
    · filter_upwards with t
      rfl
    · simpa only [Function.comp_apply, inv_pow] using
        (hnormalize (a := 6) (q := 6) rfl)
  have hterm2' :
      (fun t ↦ 3 * iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (2 * (t ^ 3)⁻¹) * (-(t ^ 2)⁻¹)) =O[atTop]
          (fun t : ℝ ↦ (t ^ 12)⁻¹) := by
    apply hterm2.congr'
    · filter_upwards with t
      simp only [Function.comp_apply]
      ring
    · simpa only [Function.comp_apply, inv_pow] using
        (hnormalize (a := 7) (q := 5) rfl)
  have hterm3' :
      (fun t ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (-6 * (t ^ 4)⁻¹)) =O[atTop] (fun t : ℝ ↦ (t ^ 12)⁻¹) := by
    apply hterm3.congr'
    · filter_upwards with t
      simp only [iteratedDeriv_one, Function.comp_apply]
    · simpa only [Function.comp_apply, inv_pow] using
        (hnormalize (a := 8) (q := 4) rfl)
  apply ((hterm1'.add hterm2').add hterm3').congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hinv.eventually hHsmooth]
      with t ht hsmooth
    simpa only [iteratedDeriv_one] using
      (defect8_third_derivative_eq F G yStar b ht.ne' hsmooth).symm
  · filter_upwards with t
    rfl

/-- The order-four case of `eq:D8-bound`. -/
theorem defect8_isBigO_four (F G : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hHsmooth : ∀ᶠ x in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 4 (reciprocalDefect8 F G yStar b) x)
    (hH1 : (fun x ↦ iteratedDeriv 1 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 8))
    (hH2 : (fun x ↦ iteratedDeriv 2 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 7))
    (hH3 : (fun x ↦ iteratedDeriv 3 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 6))
    (hH4 : (fun x ↦ iteratedDeriv 4 (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 5)) :
    (fun t ↦ iteratedDeriv 4 (defect8 F G yStar b) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 13)⁻¹) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnormalize {a q : ℕ} (haq : a + q = 13) :
      (fun t : ℝ ↦ ((fun x : ℝ ↦ x ^ a) ∘ fun s ↦ s⁻¹) t * (t ^ q)⁻¹) =ᶠ[atTop]
        (fun t ↦ (t ^ 13)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply, inv_pow]
    field_simp
    rw [← pow_add, haq]
  have hterm1 := (hH4.comp_tendsto hinv).mul
    (isBigO_refl (fun t : ℝ ↦ (t ^ 8)⁻¹) atTop)
  have hterm2 := ((hH3.comp_tendsto hinv).mul
    (isBigO_refl (fun t : ℝ ↦ (t ^ 7)⁻¹) atTop)).const_mul_left 12
  have hterm3 := ((hH2.comp_tendsto hinv).mul
    (isBigO_refl (fun t : ℝ ↦ (t ^ 6)⁻¹) atTop)).const_mul_left 36
  have hterm4 := ((hH1.comp_tendsto hinv).mul
    (isBigO_refl (fun t : ℝ ↦ (t ^ 5)⁻¹) atTop)).const_mul_left 24
  have hterm1' :
      (fun t ↦ iteratedDeriv 4 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (t ^ 8)⁻¹) =O[atTop] (fun t : ℝ ↦ (t ^ 13)⁻¹) := by
    apply hterm1.congr'
    · filter_upwards with t
      rfl
    · exact hnormalize (a := 5) (q := 8) rfl
  have hterm2' :
      (fun t ↦ 12 * iteratedDeriv 3 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (t ^ 7)⁻¹) =O[atTop] (fun t : ℝ ↦ (t ^ 13)⁻¹) := by
    apply hterm2.congr'
    · filter_upwards with t
      simp only [Function.comp_apply]
      ring
    · exact hnormalize (a := 6) (q := 7) rfl
  have hterm3' :
      (fun t ↦ 36 * iteratedDeriv 2 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (t ^ 6)⁻¹) =O[atTop] (fun t : ℝ ↦ (t ^ 13)⁻¹) := by
    apply hterm3.congr'
    · filter_upwards with t
      simp only [Function.comp_apply]
      ring
    · exact hnormalize (a := 7) (q := 6) rfl
  have hterm4' :
      (fun t ↦ 24 * iteratedDeriv 1 (reciprocalDefect8 F G yStar b) t⁻¹ *
        (t ^ 5)⁻¹) =O[atTop] (fun t : ℝ ↦ (t ^ 13)⁻¹) := by
    apply hterm4.congr'
    · filter_upwards with t
      simp only [iteratedDeriv_one, Function.comp_apply]
      ring
    · exact hnormalize (a := 8) (q := 5) rfl
  apply (((hterm1'.add hterm2').add hterm3').add hterm4').congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hinv.eventually hHsmooth]
      with t ht hsmooth
    simpa only [iteratedDeriv_one] using
      (defect8_fourth_derivative_eq F G yStar b ht.ne' hsmooth).symm
  · filter_upwards with t
    rfl

/-- The source hypotheses imply the complete `eq:D8-bound` through order four for the
recursively chosen coefficients. -/
theorem recursive_defect8_isBigO {I : Set ℝ} (F G : ℝ → ℝ)
    (yStar : ℝ) (hIopen : IsOpen I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) :
    ∀ ell ≤ 4,
      (fun t ↦ iteratedDeriv ell
        (defect8 F G yStar (recursiveCoefficients8 F G yStar 8)) t) =O[atTop]
          (fun t : ℝ ↦ (t ^ (9 + ell))⁻¹) := by
  let b := recursiveCoefficients8 F G yStar 8
  obtain ⟨η, hη, hsmooth⟩ :=
    exists_reciprocalDefect8_contDiffOn F G yStar b hIopen hyStar hF hG
  have hlocal : ∀ᶠ x in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 4 (reciprocalDefect8 F G yStar b) x := by
    have hmem : Ioo (-η) η ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, hη⟩
    filter_upwards [hmem] with x hx
    exact ((hsmooth x hx).contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by norm_num)
  have hjets := recursive_reciprocalDefect8_jet_isBigO
    F G yStar hIopen hyStar hF hG hFzero hmu
  intro ell hell
  interval_cases ell
  · apply defect8_isBigO_zero F G yStar b
    simpa only [iteratedDeriv_zero] using hjets 0 (by omega)
  · apply defect8_isBigO_one F G yStar b
    · exact hlocal.mono fun x hx ↦ hx.differentiableAt (by norm_num)
    · exact hjets 1 (by omega)
  · exact defect8_isBigO_two F G yStar b
      (hlocal.mono fun _ hx ↦ hx.of_le (by norm_num))
      (hjets 1 (by omega)) (hjets 2 (by omega))
  · exact defect8_isBigO_three F G yStar b
      (hlocal.mono fun _ hx ↦ hx.of_le (by norm_num))
      (hjets 1 (by omega)) (hjets 2 (by omega)) (hjets 3 (by omega))
  · exact defect8_isBigO_four F G yStar b hlocal
      (hjets 1 (by omega)) (hjets 2 (by omega)) (hjets 3 (by omega))
      (hjets 4 (by omega))

/-- Both terms defining `R=Y-P₈` tend to `y_*`, hence `R→0`. -/
theorem remainder8_tendsto_zero (Y : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    (hY : Tendsto Y atTop (𝓝 yStar)) :
    Tendsto (remainder8 Y yStar b) atTop (𝓝 0) := by
  change Tendsto (fun t ↦ Y t - approximation8 yStar b t) atTop (𝓝 0)
  simpa only [sub_self] using hY.sub (approximation8_tendsto yStar b)

/-- The mean-value coefficient in the exact remainder equation converges to the
linearization `F'(y_*)`. -/
theorem remainderLinearCoefficient_tendsto {I : Set ℝ} (F G Y : ℝ → ℝ)
    (yStar : ℝ) (b : Fin 8 → ℝ) (hIopen : IsOpen I) (hIconn : OrdConnected I)
    (hyStar : yStar ∈ I) (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hY : Tendsto Y atTop (𝓝 yStar)) :
    Tendsto (remainderLinearCoefficient F G Y yStar b) atTop (𝓝 (deriv F yStar)) := by
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hIopen yStar hyStar
  let radius : ℝ := epsilon / 2
  let a : ℝ := yStar - radius
  let c : ℝ := yStar + radius
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have haI : a ∈ I := by
    apply hball
    change dist a yStar < epsilon
    rw [Real.dist_eq]
    dsimp [a, radius]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hcI : c ∈ I := by
    apply hball
    change dist c yStar < epsilon
    rw [Real.dist_eq]
    dsimp [c, radius]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hIccI : Icc a c ⊆ I := by
    intro z hz
    exact hIconn.out haI hcI (by simpa only [uIcc_of_le hac] using hz)
  let clamp : ℝ → ℝ := fun z ↦ (projIcc a c hac z : ℝ)
  have hclampcont : Continuous clamp := by
    dsimp only [clamp]
    fun_prop
  have hclampI : ∀ z, clamp z ∈ I := by
    intro z
    exact hIccI (projIcc a c hac z).property
  have hderivF : ContinuousOn (deriv F) I :=
    hF.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hderivG : ContinuousOn (deriv G) I :=
    hG.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  let dF : ℝ → ℝ := (deriv F) ∘ clamp
  let dG : ℝ → ℝ := (deriv G) ∘ clamp
  have hdF : Continuous dF := hderivF.comp_continuous hclampcont hclampI
  have hdG : Continuous dG := hderivG.comp_continuous hclampcont hclampI
  let kernel : ((ℝ × ℝ) × ℝ) → ℝ → ℝ := fun q theta ↦
    dF (q.1.1 + theta * q.1.2) + q.2 * dG (q.1.1 + theta * q.1.2)
  let core : ((ℝ × ℝ) × ℝ) → ℝ := fun q ↦
    ∫ theta in Icc (0 : ℝ) 1, kernel q theta
  have hkernel : Continuous kernel.uncurry := by
    dsimp only [kernel]
    fun_prop
  have hcore : Continuous core := by
    dsimp only [core]
    exact continuous_parametric_integral_of_continuous hkernel isCompact_Icc
  have hP := approximation8_tendsto yStar b
  have hR := remainder8_tendsto_zero Y yStar b hY
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hinput : Tendsto
      (fun t ↦ ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹)) atTop
      (𝓝 ((yStar, 0), 0)) := by
    simpa only [nhds_prod_eq] using (hP.prodMk hR).prodMk hinv
  have hcoreValue : core ((yStar, 0), 0) = deriv F yStar := by
    have hyIcc : yStar ∈ Icc a c := by
      dsimp only [a, c]
      constructor <;> linarith
    have hclampY : clamp yStar = yStar := by
      dsimp only [clamp]
      simpa using congrArg Subtype.val (projIcc_of_mem hac hyIcc)
    rw [show core ((yStar, 0), 0) =
        ∫ _theta in Icc (0 : ℝ) 1, deriv F yStar by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro theta _
      simp only [kernel, dF, dG, Function.comp_apply, hclampY, mul_zero, zero_mul,
        add_zero]]
    simp
  have hcoreLimit : Tendsto
      (fun t ↦ core ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹))
      atTop (𝓝 (deriv F yStar)) := by
    rw [← hcoreValue]
    exact hcore.continuousAt.tendsto.comp hinput
  apply hcoreLimit.congr'
  have hPmem : ∀ᶠ t in atTop, approximation8 yStar b t ∈ Ioo a c := by
    apply hP.eventually
    exact isOpen_Ioo.mem_nhds ⟨by dsimp [a]; linarith, by dsimp [c]; linarith⟩
  have hYmem : ∀ᶠ t in atTop, Y t ∈ Ioo a c := by
    apply hY.eventually
    exact isOpen_Ioo.mem_nhds ⟨by dsimp [a]; linarith, by dsimp [c]; linarith⟩
  filter_upwards [hPmem, hYmem] with t hPt hYt
  have hcoreInterval : core
      ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹) =
      ∫ theta in (0 : ℝ)..1,
        kernel ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹) theta := by
    dsimp only [core]
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  rw [hcoreInterval]
  apply intervalIntegral.integral_congr
  intro theta htheta
  rw [uIcc_of_le (by norm_num)] at htheta
  have hzmem : approximation8 yStar b t + theta * remainder8 Y yStar b t ∈
      Icc a c := by
    change a ≤ approximation8 yStar b t +
        theta * (Y t - approximation8 yStar b t) ∧
      approximation8 yStar b t + theta * (Y t - approximation8 yStar b t) ≤ c
    constructor <;> nlinarith [htheta.1, htheta.2, hPt.1, hPt.2, hYt.1, hYt.2]
  have hclampZ : clamp
      (approximation8 yStar b t + theta * remainder8 Y yStar b t) =
      approximation8 yStar b t + theta * remainder8 Y yStar b t := by
    dsimp only [clamp]
    simpa using congrArg Subtype.val (projIcc_of_mem hac hzmem)
  simp only [kernel, dF, dG, Function.comp_apply, hclampZ]

/-- Taylor's theorem gives the reciprocal-coordinate estimate which precedes
`eq:D8-bound`.  The remaining reciprocal-chain calculation is deliberately kept
separate below. -/
theorem reciprocalDefect8_deriv_isBigO (F G : ℝ → ℝ) (yStar : ℝ)
    (b : Fin 8 → ℝ) (eta : ℝ) (heta : 0 < eta)
    (hsmooth : ContDiffOn ℝ 9 (reciprocalDefect8 F G yStar b) (Ioo (-eta) eta))
    (hvanish : HasVanishingReciprocalJet F G yStar b) :
    ∀ m ≤ 4, (fun x ↦ iteratedDeriv m (reciprocalDefect8 F G yStar b) x) =O[𝓝 0]
      (fun x ↦ x ^ (9 - m)) :=
  MI10_taylor_with_derivative_remainders
    (reciprocalDefect8 F G yStar b) eta heta hsmooth hvanish

/-- `eq:R-linear-equation`: subtracting the ODE for `Y` from the defect identity and
using the integral mean-value formula gives the exact scalar linear equation for `R`.
The interval-integrability assumptions are immediate from the source's `C⁹` hypotheses
once `Y(t)` and `P₈(t)` lie in the same compact subinterval of `I`. -/
theorem remainder_linear_equation (F G Y : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ)
    {t : ℝ} (hY : HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t)
    (hP : DifferentiableAt ℝ (approximation8 yStar b) t)
    (hFcontinuous : ContinuousOn (deriv F)
      (uIcc (approximation8 yStar b t) (Y t)))
    (hFderiv : ∀ z ∈ uIcc (approximation8 yStar b t) (Y t),
      HasDerivAt F (deriv F z) z)
    (hGcontinuous : ContinuousOn (deriv G)
      (uIcc (approximation8 yStar b t) (Y t)))
    (hGderiv : ∀ z ∈ uIcc (approximation8 yStar b t) (Y t),
      HasDerivAt G (deriv G z) z)
    (hFintegrable : IntervalIntegrable
      (fun theta : ℝ ↦ deriv F
        (approximation8 yStar b t + theta * remainder8 Y yStar b t)) volume 0 1)
    (hGintegrable : IntervalIntegrable
      (fun theta : ℝ ↦ deriv G
        (approximation8 yStar b t + theta * remainder8 Y yStar b t)) volume 0 1) :
    HasDerivAt (remainder8 Y yStar b)
      (remainderLinearCoefficient F G Y yStar b t * remainder8 Y yStar b t -
        defect8 F G yStar b t) t := by
  let P := approximation8 yStar b t
  let R := remainder8 Y yStar b t
  let IF := ∫ theta in (0 : ℝ)..1, deriv F (P + theta * R)
  let IG := ∫ theta in (0 : ℝ)..1, deriv G (P + theta * R)
  have hRvalue : Y t - P = R := by rfl
  have hmeanF : F (Y t) - F P = R * IF := by
    simpa only [P, R, IF, hRvalue] using
      MI06_integral_mean_value_formula F P (Y t) hFcontinuous hFderiv
  have hmeanG : G (Y t) - G P = R * IG := by
    simpa only [P, R, IG, hRvalue] using
      MI06_integral_mean_value_formula G P (Y t) hGcontinuous hGderiv
  have hA : remainderLinearCoefficient F G Y yStar b t = IF + t⁻¹ * IG := by
    rw [remainderLinearCoefficient]
    change (∫ theta in (0 : ℝ)..1,
      deriv F (P + theta * R) + t⁻¹ * deriv G (P + theta * R)) = IF + t⁻¹ * IG
    change IntervalIntegrable (fun theta : ℝ ↦ deriv F (P + theta * R)) volume 0 1 at hFintegrable
    change IntervalIntegrable (fun theta : ℝ ↦ deriv G (P + theta * R)) volume 0 1 at hGintegrable
    rw [intervalIntegral.integral_add hFintegrable (hGintegrable.const_mul t⁻¹)]
    simp only [intervalIntegral.integral_const_mul, IF, IG]
  have hrem : HasDerivAt (remainder8 Y yStar b)
      (asymptoticallyAutonomousRhs F G t (Y t) -
        deriv (approximation8 yStar b) t) t := by
    change HasDerivAt (fun s ↦ Y s - approximation8 yStar b s)
      (asymptoticallyAutonomousRhs F G t (Y t) - deriv (approximation8 yStar b) t) t
    exact hY.sub hP.hasDerivAt
  apply hrem.congr_deriv
  rw [hA]
  dsimp only [asymptoticallyAutonomousRhs, defect8, P] at hmeanF hmeanG ⊢
  linear_combination hmeanF + t⁻¹ * hmeanG

/-- Under the source hypotheses, the exact linear remainder equation holds for
all sufficiently large times. -/
theorem eventually_remainder_linear_equation {I : Set ℝ} (F G Y : ℝ → ℝ)
    (yStar T0 : ℝ) (b : Fin 8 → ℝ) (hIopen : IsOpen I)
    (hIconn : OrdConnected I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I)
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t) :
    ∀ᶠ t in atTop, HasDerivAt (remainder8 Y yStar b)
      (remainderLinearCoefficient F G Y yStar b t * remainder8 Y yStar b t -
        defect8 F G yStar b t) t := by
  have hPmem : ∀ᶠ t in atTop, approximation8 yStar b t ∈ I :=
    (approximation8_tendsto yStar b).eventually (hIopen.mem_nhds hyStar)
  filter_upwards [eventually_gt_atTop T0, hPmem] with t ht hPt
  have ht0 : t ≠ 0 := ne_of_gt (hT0.trans ht)
  have hYt : Y t ∈ I := hYmap (mem_Ici.mpr ht.le)
  have hsegment : uIcc (approximation8 yStar b t) (Y t) ⊆ I := by
    rcases le_total (approximation8 yStar b t) (Y t) with hPY | hYP
    · rw [uIcc_of_le hPY]
      exact hIconn.out hPt hYt
    · rw [uIcc_of_ge hYP]
      exact hIconn.out hYt hPt
  have hderivF : ContinuousOn (deriv F) I :=
    hF.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hderivG : ContinuousOn (deriv G) I :=
    hG.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hFcontinuous : ContinuousOn (deriv F)
      (uIcc (approximation8 yStar b t) (Y t)) := hderivF.mono hsegment
  have hGcontinuous : ContinuousOn (deriv G)
      (uIcc (approximation8 yStar b t) (Y t)) := hderivG.mono hsegment
  have hFderiv : ∀ z ∈ uIcc (approximation8 yStar b t) (Y t),
      HasDerivAt F (deriv F z) z := by
    intro z hz
    have hzI := hsegment hz
    exact (((hF z hzI).contDiffAt (hIopen.mem_nhds hzI)).differentiableAt
      (by norm_num)).hasDerivAt
  have hGderiv : ∀ z ∈ uIcc (approximation8 yStar b t) (Y t),
      HasDerivAt G (deriv G z) z := by
    intro z hz
    have hzI := hsegment hz
    exact (((hG z hzI).contDiffAt (hIopen.mem_nhds hzI)).differentiableAt
      (by norm_num)).hasDerivAt
  have hthetaMaps : MapsTo
      (fun theta : ℝ ↦ approximation8 yStar b t +
        theta * remainder8 Y yStar b t) (Icc 0 1)
      (uIcc (approximation8 yStar b t) (Y t)) := by
    intro theta htheta
    change approximation8 yStar b t +
      theta * (Y t - approximation8 yStar b t) ∈ _
    rcases le_total (approximation8 yStar b t) (Y t) with hPY | hYP
    · rw [uIcc_of_le hPY]
      constructor <;> nlinarith [htheta.1, htheta.2]
    · rw [uIcc_of_ge hYP]
      constructor <;> nlinarith [htheta.1, htheta.2]
  have hFtheta : ContinuousOn
      (fun theta : ℝ ↦ deriv F (approximation8 yStar b t +
        theta * remainder8 Y yStar b t)) (Icc 0 1) := by
    apply hFcontinuous.comp
    · fun_prop
    · exact hthetaMaps
  have hGtheta : ContinuousOn
      (fun theta : ℝ ↦ deriv G (approximation8 yStar b t +
        theta * remainder8 Y yStar b t)) (Icc 0 1) := by
    apply hGcontinuous.comp
    · fun_prop
    · exact hthetaMaps
  have hPdiff : DifferentiableAt ℝ (approximation8 yStar b) t := by
    change DifferentiableAt ℝ (fun s ↦ yStar + polynomial8 b s⁻¹) t
    unfold polynomial8
    fun_prop
  exact remainder_linear_equation F G Y yStar b (hYode t ht) hPdiff
    hFcontinuous hFderiv hGcontinuous hGderiv
    (hFtheta.intervalIntegrable_of_Icc (by norm_num))
    (hGtheta.intervalIntegrable_of_Icc (by norm_num))

/-- Continuity of the mean-value coefficient once the comparison segment stays
in one compact subinterval of the source domain. -/
theorem remainderLinearCoefficient_continuousOn_of_mem_Icc {I : Set ℝ}
    (F G Y : ℝ → ℝ) (yStar : ℝ) (b : Fin 8 → ℝ) (T a c : ℝ)
    (hIopen : IsOpen I) (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hT : 0 < T) (hac : a ≤ c) (hIccI : Icc a c ⊆ I)
    (hPmem : MapsTo (approximation8 yStar b) (Ici T) (Icc a c))
    (hYmem : MapsTo Y (Ici T) (Icc a c))
    (hYcont : ContinuousOn Y (Ici T)) :
    ContinuousOn (remainderLinearCoefficient F G Y yStar b) (Ici T) := by
  let clamp : ℝ → ℝ := fun z ↦ (projIcc a c hac z : ℝ)
  have hclampcont : Continuous clamp := by
    dsimp only [clamp]
    fun_prop
  have hclampI : ∀ z, clamp z ∈ I := by
    intro z
    exact hIccI (projIcc a c hac z).property
  have hderivF : ContinuousOn (deriv F) I :=
    hF.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hderivG : ContinuousOn (deriv G) I :=
    hG.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  let dF : ℝ → ℝ := (deriv F) ∘ clamp
  let dG : ℝ → ℝ := (deriv G) ∘ clamp
  have hdF : Continuous dF := hderivF.comp_continuous hclampcont hclampI
  have hdG : Continuous dG := hderivG.comp_continuous hclampcont hclampI
  let kernel : ((ℝ × ℝ) × ℝ) → ℝ → ℝ := fun q theta ↦
    dF (q.1.1 + theta * q.1.2) + q.2 * dG (q.1.1 + theta * q.1.2)
  let core : ((ℝ × ℝ) × ℝ) → ℝ := fun q ↦
    ∫ theta in Icc (0 : ℝ) 1, kernel q theta
  have hkernel : Continuous kernel.uncurry := by
    dsimp only [kernel]
    fun_prop
  have hcore : Continuous core := by
    dsimp only [core]
    exact continuous_parametric_integral_of_continuous hkernel isCompact_Icc
  have hPcont : ContinuousOn (approximation8 yStar b) (Ici T) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun t ↦ yStar + polynomial8 b t⁻¹) t
    have hpoly : Continuous (polynomial8 b) := by
      unfold polynomial8
      fun_prop
    exact (hpoly.continuousAt.comp
      (continuousAt_inv₀ (ne_of_gt (hT.trans_le ht)))).const_add _
  have hRcont : ContinuousOn (remainder8 Y yStar b) (Ici T) :=
    hYcont.sub hPcont
  have hinvcont : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Ici T) := by
    intro t ht
    exact continuousAt_inv₀ (ne_of_gt (hT.trans_le ht)) |>.continuousWithinAt
  have hinput : ContinuousOn
      (fun t ↦ ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹))
      (Ici T) := (hPcont.prodMk hRcont).prodMk hinvcont
  have hcoreComp : ContinuousOn
      (fun t ↦ core ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹))
      (Ici T) := hcore.comp_continuousOn hinput
  apply hcoreComp.congr
  intro t ht
  have hPt := hPmem ht
  have hYt := hYmem ht
  have hcoreInterval : core
      ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹) =
      ∫ theta in (0 : ℝ)..1,
        kernel ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹) theta := by
    dsimp only [core]
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  change remainderLinearCoefficient F G Y yStar b t =
    core ((approximation8 yStar b t, remainder8 Y yStar b t), t⁻¹)
  rw [hcoreInterval]
  apply intervalIntegral.integral_congr
  intro theta htheta
  rw [uIcc_of_le (by norm_num)] at htheta
  have hzmem : approximation8 yStar b t + theta * remainder8 Y yStar b t ∈
      Icc a c := by
    change a ≤ approximation8 yStar b t +
        theta * (Y t - approximation8 yStar b t) ∧
      approximation8 yStar b t + theta * (Y t - approximation8 yStar b t) ≤ c
    constructor <;> nlinarith [htheta.1, htheta.2, hPt.1, hPt.2, hYt.1, hYt.2]
  have hclampZ : clamp
      (approximation8 yStar b t + theta * remainder8 Y yStar b t) =
      approximation8 yStar b t + theta * remainder8 Y yStar b t := by
    dsimp only [clamp]
    simpa using congrArg Subtype.val (projIcc_of_mem hac hzmem)
  simp only [kernel, dF, dG, Function.comp_apply, hclampZ]

/-- Extend a function continuously from a closed right half-line by freezing it
at the left endpoint. -/
def extendFromIci (f : ℝ → ℝ) (T t : ℝ) : ℝ := f (max T t)

theorem continuous_extendFromIci {f : ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn f (Ici T)) : Continuous (extendFromIci f T) := by
  apply hf.comp_continuous
  · exact continuous_const.max continuous_id
  · intro t
    exact le_max_left T t

@[simp]
theorem extendFromIci_eq {f : ℝ → ℝ} {T t : ℝ} (ht : T ≤ t) :
    extendFromIci f T t = f t := by
  simp [extendFromIci, max_eq_right ht]

/-- The elementary exponential-kernel integral used in the stable convolution bound. -/
theorem intervalIntegral_exp_neg_mul_sub (alpha a t : ℝ) (halpha : 0 < alpha) :
    (∫ s in a..t, Real.exp (-alpha * (t - s))) =
      (1 - Real.exp (-alpha * (t - a))) / alpha := by
  let primitive : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (t - s)) / alpha
  have hprimitive : ∀ s : ℝ,
      HasDerivAt primitive (Real.exp (-alpha * (t - s))) s := by
    intro s
    have hlin : HasDerivAt (fun y : ℝ ↦ -alpha * (t - y)) alpha s := by
      have hraw := ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-alpha)
      apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
      · ring
      · filter_upwards with y
        simp only [Pi.sub_apply, id_eq]
    have hd := hlin.exp.div_const alpha
    dsimp [primitive]
    apply hd.congr_deriv
    field_simp [halpha.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hprimitive s)
      ((by fun_prop : Continuous (fun s ↦ Real.exp (-alpha * (t - s)))).intervalIntegrable _ _)]
  dsimp [primitive]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

/-- A positive exponential kernel has total mass at most `1/alpha` on every
forward interval. -/
theorem intervalIntegral_exp_neg_mul_sub_le (alpha a t : ℝ) (halpha : 0 < alpha)
    (_hat : a ≤ t) :
    (∫ s in a..t, Real.exp (-alpha * (t - s))) ≤ alpha⁻¹ := by
  rw [intervalIntegral_exp_neg_mul_sub alpha a t halpha]
  have hexp : 0 ≤ Real.exp (-alpha * (t - a)) := Real.exp_nonneg _
  rw [div_eq_mul_inv]
  nlinarith [inv_pos.mpr halpha]

/-- The quantitative split estimate behind the stable (`mu < 0`) branch. -/
theorem stable_exponential_convolution_bound (D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hDcont : Continuous D)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹)
    {t : ℝ} (ht : 2 * T ≤ t) :
    ‖∫ s in T..t, Real.exp (-alpha * (t - s)) * D s‖ ≤
      C * (T ^ 9)⁻¹ * (t / 2 - T) * Real.exp (-alpha * (t / 2)) +
        C * 512 * alpha⁻¹ * (t ^ 9)⁻¹ := by
  have htpos : 0 < t := lt_of_lt_of_le (by nlinarith [hT]) ht
  have hTmid : T ≤ t / 2 := by linarith
  have hmidt : t / 2 ≤ t := by linarith
  let kernel : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (t - s)) * D s
  have hkcont : Continuous kernel := by
    dsimp [kernel]
    fun_prop
  have hk1 : IntervalIntegrable kernel volume T (t / 2) := hkcont.intervalIntegrable _ _
  have hk2 : IntervalIntegrable kernel volume (t / 2) t := hkcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hk1 hk2]
  apply (norm_add_le _ _).trans
  have hfirst : ‖∫ s in T..t / 2, kernel s‖ ≤
      (C * (T ^ 9)⁻¹ * Real.exp (-alpha * (t / 2))) * |t / 2 - T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hTmid] at hs
    have hsT : T ≤ s := hs.1.le
    have hsmid : s ≤ t / 2 := hs.2
    have hD := hDbound s hsT
    have hpow : (s ^ 9)⁻¹ ≤ (T ^ 9)⁻¹ := by
      gcongr
    have hkernel : Real.exp (-alpha * (t - s)) ≤
        Real.exp (-alpha * (t / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [halpha]
    dsimp [kernel]
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      Real.exp (-alpha * (t - s)) * |D s|
          ≤ Real.exp (-alpha * (t - s)) * (C * (s ^ 9)⁻¹) := by gcongr
      _ ≤ Real.exp (-alpha * (t - s)) * (C * (T ^ 9)⁻¹) := by gcongr
      _ ≤ Real.exp (-alpha * (t / 2)) * (C * (T ^ 9)⁻¹) := by gcongr
      _ = C * (T ^ 9)⁻¹ * Real.exp (-alpha * (t / 2)) := by ring
  have hsecond : ‖∫ s in t / 2..t, kernel s‖ ≤
      C * 512 * (t ^ 9)⁻¹ * alpha⁻¹ := by
    let majorant : ℝ → ℝ := fun s ↦
      (C * 512 * (t ^ 9)⁻¹) * Real.exp (-alpha * (t - s))
    have hmajorant : IntervalIntegrable majorant volume (t / 2) t := by
      exact (by
        dsimp [majorant]
        fun_prop : Continuous majorant).intervalIntegrable _ _
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hmidt
      (f := kernel) (g := majorant) (μ := volume) (hbound := hmajorant) ?_
    · calc
        ‖∫ s in t / 2..t, kernel s‖
            ≤ ∫ s in t / 2..t, majorant s := hnorm
        _ = (C * 512 * (t ^ 9)⁻¹) *
            ∫ s in t / 2..t, Real.exp (-alpha * (t - s)) := by
              simp only [majorant, intervalIntegral.integral_const_mul]
        _ ≤ (C * 512 * (t ^ 9)⁻¹) * alpha⁻¹ := by
              gcongr
              exact intervalIntegral_exp_neg_mul_sub_le alpha (t / 2) t halpha hmidt
        _ = C * 512 * (t ^ 9)⁻¹ * alpha⁻¹ := by ring
    · filter_upwards with s hs
      have hsmid : t / 2 ≤ s := hs.1.le
      have hsT : T ≤ s := hTmid.trans hsmid
      have hspos : 0 < s := lt_of_lt_of_le hT hsT
      have hD := hDbound s hsT
      have hpow : (s ^ 9)⁻¹ ≤ 512 * (t ^ 9)⁻¹ := by
        rw [← inv_pow, ← inv_pow]
        have hinv : s⁻¹ ≤ 2 * t⁻¹ := by
          have hhalfpos : 0 < t / 2 := by positivity
          have h := one_div_le_one_div_of_le hhalfpos hsmid
          calc
            s⁻¹ = 1 / s := by rw [one_div]
            _ ≤ 1 / (t / 2) := h
            _ = 2 * t⁻¹ := by field_simp
        calc
          s⁻¹ ^ 9 ≤ (2 * t⁻¹) ^ 9 := by gcongr
          _ = 512 * t⁻¹ ^ 9 := by norm_num [mul_pow]
      dsimp [kernel, majorant]
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc
        Real.exp (-alpha * (t - s)) * |D s|
            ≤ Real.exp (-alpha * (t - s)) * (C * (s ^ 9)⁻¹) := by gcongr
        _ ≤ Real.exp (-alpha * (t - s)) * (C * (512 * (t ^ 9)⁻¹)) := by gcongr
        _ = C * 512 * (t ^ 9)⁻¹ * Real.exp (-alpha * (t - s)) := by ring
  rw [abs_of_nonneg (sub_nonneg.mpr hTmid)] at hfirst
  calc
    ‖∫ s in T..t / 2, kernel s‖ + ‖∫ s in t / 2..t, kernel s‖
        ≤ (C * (T ^ 9)⁻¹ * Real.exp (-alpha * (t / 2))) * (t / 2 - T) +
          C * 512 * (t ^ 9)⁻¹ * alpha⁻¹ := add_le_add hfirst hsecond
    _ = C * (T ^ 9)⁻¹ * (t / 2 - T) * Real.exp (-alpha * (t / 2)) +
        C * 512 * alpha⁻¹ * (t ^ 9)⁻¹ := by ring

/-- Convolution with a forward exponentially decaying kernel preserves `O(t⁻⁹)`. -/
theorem stable_exponential_convolution_isBigO (D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hDcont : Continuous D)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹) :
    (fun t ↦ ∫ s in T..t, Real.exp (-alpha * (t - s)) * D s) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let K : ℝ := C * (T ^ 9)⁻¹
  let M : ℝ := K + C * 512 * alpha⁻¹
  apply IsBigO.of_bound M
  have hpolyexp := (isLittleO_pow_exp_pos_mul_atTop 10
    (show 0 < alpha / 2 by positivity)).bound one_pos
  filter_upwards [eventually_ge_atTop (2 * T), eventually_gt_atTop (0 : ℝ), hpolyexp]
      with t ht htpos hsmall
  have hsmall' : t ^ 10 ≤ Real.exp ((alpha / 2) * t) := by
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_pos htpos,
      abs_of_pos (Real.exp_pos _), one_mul] using hsmall
  have hdecay : t ^ 10 * Real.exp (-(alpha / 2) * t) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hsmall'
      (Real.exp_nonneg (-(alpha / 2) * t))
    calc
      t ^ 10 * Real.exp (-(alpha / 2) * t)
          ≤ Real.exp ((alpha / 2) * t) * Real.exp (-(alpha / 2) * t) := hmul
      _ = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring
  have htExp : t * Real.exp (-alpha * (t / 2)) ≤ (t ^ 9)⁻¹ := by
    rw [show -alpha * (t / 2) = -(alpha / 2) * t by ring, inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos htpos 9)).mpr
    calc
      t * Real.exp (-(alpha / 2) * t) * t ^ 9 =
          t ^ 10 * Real.exp (-(alpha / 2) * t) := by ring
      _ ≤ 1 := hdecay
  have hconv := stable_exponential_convolution_bound D T C alpha hT hC halpha
    hDcont hDbound ht
  have hmid_nonneg : 0 ≤ t / 2 - T := by linarith
  have hmid_le : t / 2 - T ≤ t := by linarith
  have hfirst : K * (t / 2 - T) * Real.exp (-alpha * (t / 2)) ≤
      K * (t ^ 9)⁻¹ := by
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hmidExp : (t / 2 - T) * Real.exp (-alpha * (t / 2)) ≤
        t * Real.exp (-alpha * (t / 2)) :=
      mul_le_mul_of_nonneg_right hmid_le (Real.exp_nonneg _)
    calc
      K * (t / 2 - T) * Real.exp (-alpha * (t / 2)) =
          K * ((t / 2 - T) * Real.exp (-alpha * (t / 2))) := by ring
      _ ≤ K * (t * Real.exp (-alpha * (t / 2))) :=
        mul_le_mul_of_nonneg_left hmidExp hK
      _ ≤ K * (t ^ 9)⁻¹ := mul_le_mul_of_nonneg_left htExp hK
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (pow_pos htpos 9))]
  calc
    |∫ s in T..t, Real.exp (-alpha * (t - s)) * D s|
        ≤ K * (t / 2 - T) * Real.exp (-alpha * (t / 2)) +
          C * 512 * alpha⁻¹ * (t ^ 9)⁻¹ := by
            simpa only [K, Real.norm_eq_abs] using hconv
    _ ≤ K * (t ^ 9)⁻¹ + C * 512 * alpha⁻¹ * (t ^ 9)⁻¹ := by gcongr
    _ = M * (t ^ 9)⁻¹ := by dsimp [M]; ring

/-- If `A ≤ -alpha` on the forward half-line, its evolution kernel is bounded by
the constant exponential kernel. -/
theorem exp_intervalIntegral_le_exp_neg_mul_sub (A : ℝ → ℝ) (T alpha : ℝ)
    (_halpha : 0 < alpha) (hAcont : Continuous A)
    (hAupper : ∀ x, T ≤ x → A x ≤ -alpha)
    {s t : ℝ} (hs : T ≤ s) (hst : s ≤ t) :
    Real.exp (∫ x in s..t, A x) ≤ Real.exp (-alpha * (t - s)) := by
  apply Real.exp_le_exp.mpr
  have hAint : IntervalIntegrable A volume s t := hAcont.intervalIntegrable _ _
  have hcint : IntervalIntegrable (fun _ : ℝ ↦ -alpha) volume s t :=
    intervalIntegrable_const
  calc
    (∫ x in s..t, A x) ≤ ∫ _x in s..t, (-alpha : ℝ) := by
      apply intervalIntegral.integral_mono_on hst hAint hcint
      intro x hx
      exact hAupper x (hs.trans hx.1)
    _ = -alpha * (t - s) := by simp; ring

/-- The variable stable evolution kernel from MI11a preserves `O(t⁻⁹)`. -/
theorem stable_variable_convolution_isBigO (A D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : Continuous A) (hDcont : Continuous D)
    (hAupper : ∀ x, T ≤ x → A x ≤ -alpha)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹) :
    (fun t ↦ ∫ s in T..t, Real.exp (∫ x in s..t, A x) * D s) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  have habscont : Continuous (fun s ↦ |D s|) := hDcont.abs
  have habsbound : ∀ s, T ≤ s → |(|D s|)| ≤ C * (s ^ 9)⁻¹ := by
    intro s hs
    simpa only [abs_abs] using hDbound s hs
  have hconst := stable_exponential_convolution_isBigO
    (fun s ↦ |D s|) T C alpha hT hC halpha habscont habsbound
  obtain ⟨c, hc⟩ := hconst.bound
  apply IsBigO.of_bound c
  filter_upwards [eventually_ge_atTop T, hc] with t hTt hct
  let variableKernel : ℝ → ℝ := fun s ↦ Real.exp (∫ x in s..t, A x) * D s
  let constantKernel : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (t - s)) * |D s|
  have hvcont : Continuous variableKernel := by
    dsimp [variableKernel]
    have hint : Continuous (fun s ↦ ∫ x in s..t, A x) := by
      have hd : Differentiable ℝ (fun s ↦ ∫ x in t..s, A x) :=
        intervalIntegral.differentiable_integral_of_continuous hAcont
      have hn : Continuous (fun s ↦ -(∫ x in t..s, A x)) := hd.neg.continuous
      have heq : (fun s ↦ ∫ x in s..t, A x) =
          (fun s ↦ -(∫ x in t..s, A x)) := by
        funext s
        exact intervalIntegral.integral_symm t s
      rw [heq]
      exact hn
    fun_prop
  have hccont : Continuous constantKernel := by
    dsimp [constantKernel]
    fun_prop
  have hvint : IntervalIntegrable variableKernel volume T t := hvcont.intervalIntegrable _ _
  have hcint : IntervalIntegrable constantKernel volume T t := hccont.intervalIntegrable _ _
  have hpoint : ∀ s ∈ Icc T t, ‖variableKernel s‖ ≤ constantKernel s := by
    intro s hs
    have hk := exp_intervalIntegral_le_exp_neg_mul_sub A T alpha halpha hAcont hAupper
      hs.1 hs.2
    dsimp [variableKernel, constantKernel]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have hc_nonneg : 0 ≤ ∫ s in T..t, constantKernel s := by
    apply intervalIntegral.integral_nonneg hTt
    intro s hs
    dsimp [constantKernel]
    positivity
  have hcompare : ‖∫ s in T..t, variableKernel s‖ ≤
      ‖∫ s in T..t, constantKernel s‖ := by
    calc
      ‖∫ s in T..t, variableKernel s‖
          ≤ ∫ s in T..t, ‖variableKernel s‖ :=
            intervalIntegral.norm_integral_le_integral_norm hTt
      _ ≤ ∫ s in T..t, constantKernel s := by
            apply intervalIntegral.integral_mono_on hTt hvint.norm hcint
            exact hpoint
      _ = ‖∫ s in T..t, constantKernel s‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  exact hcompare.trans (by simpa only [variableKernel, constantKernel] using hct)

/-- The homogeneous term in the stable variation-of-constants formula is
exponentially small, hence `O(t⁻⁹)`. -/
theorem stable_homogeneous_isBigO (A : ℝ → ℝ) (T alpha r : ℝ)
    (halpha : 0 < alpha) (hAcont : Continuous A)
    (hAupper : ∀ x, T ≤ x → A x ≤ -alpha) :
    (fun t ↦ Real.exp (∫ x in T..t, A x) * r) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  obtain ⟨c, hc⟩ := (MI06_exponential_decay_isBigO_reciprocal_pow alpha 9 halpha).bound
  apply IsBigO.of_bound (|r| * Real.exp (alpha * T) * max c 0)
  filter_upwards [eventually_ge_atTop T, hc] with t hTt hct
  have hk := exp_intervalIntegral_le_exp_neg_mul_sub A T alpha halpha hAcont hAupper
    le_rfl hTt
  have hexpShift : Real.exp (-alpha * (t - T)) =
      Real.exp (alpha * T) * Real.exp (-alpha * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (∫ x in T..t, A x) * |r|
        ≤ Real.exp (-alpha * (t - T)) * |r| := by gcongr
    _ = |r| * Real.exp (alpha * T) * Real.exp (-alpha * t) := by
          rw [hexpShift]
          ring
    _ ≤ |r| * Real.exp (alpha * T) * (max c 0 * ‖(t ^ 9)⁻¹‖) := by
          gcongr
          simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
            hct.trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _))
    _ = |r| * Real.exp (alpha * T) * max c 0 * ‖(t ^ 9)⁻¹‖ := by ring

/-- Stable branch of the exact linear remainder argument, stated with a fixed
half-line on which all quantitative hypotheses hold. -/
theorem stable_linear_remainder_isBigO (A D R : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : ContinuousOn A (Ici T)) (hDcont : ContinuousOn D (Ici T))
    (hRcont : ContinuousOn R (Ici T))
    (hAupper : ∀ t ∈ Ici T, A t ≤ -alpha)
    (hDbound : ∀ t ∈ Ici T, |D t| ≤ C * (t ^ 9)⁻¹)
    (hode : ∀ t ∈ Ioi T, HasDerivAt R (A t * R t - D t) t) :
    R =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let Ae : ℝ → ℝ := extendFromIci A T
  let De : ℝ → ℝ := extendFromIci D T
  have hAecont : Continuous Ae := continuous_extendFromIci hAcont
  have hDecont : Continuous De := continuous_extendFromIci hDcont
  have hAeupper : ∀ t, T ≤ t → Ae t ≤ -alpha := by
    intro t ht
    simpa only [Ae, extendFromIci_eq ht] using hAupper t ht
  have hDebound : ∀ t, T ≤ t → |De t| ≤ C * (t ^ 9)⁻¹ := by
    intro t ht
    simpa only [De, extendFromIci_eq ht] using hDbound t ht
  have hhom := stable_homogeneous_isBigO Ae T alpha (R T) halpha hAecont hAeupper
  have hconv := stable_variable_convolution_isBigO Ae De T C alpha hT hC halpha
    hAecont hDecont hAeupper hDebound
  have hhom' : (fun t ↦ Real.exp (∫ x in T..t, A x) * R T) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    apply hhom.congr'
    · filter_upwards [eventually_ge_atTop T] with t hTt
      congr 2
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hTt] at hx
      exact extendFromIci_eq hx.1
    · filter_upwards with t
      rfl
  have hconv' :
      (fun t ↦ ∫ s in T..t, Real.exp (∫ x in s..t, A x) * D s) =O[atTop]
        (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    apply hconv.congr'
    · filter_upwards [eventually_ge_atTop T] with t hTt
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hTt] at hs
      dsimp only [Ae, De]
      rw [extendFromIci_eq hs.1]
      congr 2
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hs.2] at hx
      exact extendFromIci_eq (hs.1.trans hx.1)
    · filter_upwards with t
      rfl
  apply (hhom'.sub hconv').congr'
  · filter_upwards [eventually_ge_atTop T] with t hTt
    exact (MI11_variation_of_constants_forward A D R hTt
      (hAcont.mono fun _ hx ↦ hx.1)
      (hDcont.mono fun _ hx ↦ hx.1)
      (hRcont.mono fun _ hx ↦ hx.1)
      (fun s hs ↦ hode s hs.1)).symm
  · filter_upwards with t
    rfl

/-- The terminal constant exponential kernel is integrable on its half-line. -/
theorem integrableOn_exp_neg_mul_sub_Ici (alpha t : ℝ) (halpha : 0 < alpha) :
    IntegrableOn (fun s : ℝ ↦ Real.exp (-alpha * (s - t))) (Ici t) := by
  have hbase : IntegrableOn (fun s : ℝ ↦ Real.exp (-alpha * s)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (a := -alpha) (by linarith) t)
  have hmul := hbase.const_mul (Real.exp (alpha * t))
  apply hmul.congr
  filter_upwards with s
  rw [← Real.exp_add]
  congr 1
  ring

/-- The terminal constant exponential kernel has total mass `1 / alpha`. -/
theorem integral_exp_neg_mul_sub_Ici (alpha t : ℝ) (halpha : 0 < alpha) :
    (∫ s in Ici t, Real.exp (-alpha * (s - t))) = alpha⁻¹ := by
  rw [show (fun s : ℝ ↦ Real.exp (-alpha * (s - t))) =
      (fun s : ℝ ↦ Real.exp (-alpha * s) * Real.exp (alpha * t)) by
        funext s
        rw [← Real.exp_add]
        congr 1
        ring]
  rw [MeasureTheory.integral_mul_const, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (a := -alpha) (by linarith) t]
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  rw [show -Real.exp (-alpha * t) / -alpha = Real.exp (-alpha * t) / alpha by ring]
  rw [div_eq_mul_inv]
  calc
    Real.exp (-alpha * t) * alpha⁻¹ * Real.exp (alpha * t) =
        alpha⁻¹ * (Real.exp (-alpha * t) * Real.exp (alpha * t)) := by ring
    _ = alpha⁻¹ := by rw [← Real.exp_add]; simp

/-- The quantitative terminal (`mu > 0`) convolution estimate for the constant
exponential kernel. -/
theorem terminal_exponential_convolution_bound (D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹)
    {t : ℝ} (hTt : T ≤ t) :
    ‖∫ s in Ici t, Real.exp (-alpha * (s - t)) * D s‖ ≤
      C * alpha⁻¹ * (t ^ 9)⁻¹ := by
  have htpos : 0 < t := hT.trans_le hTt
  let kernel : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (s - t))
  let majorant : ℝ → ℝ := fun s ↦ (C * (t ^ 9)⁻¹) * kernel s
  have hkint : IntegrableOn kernel (Ici t) := by
    simpa only [kernel] using integrableOn_exp_neg_mul_sub_Ici alpha t halpha
  have hmint : IntegrableOn majorant (Ici t) := by
    change IntegrableOn (fun s ↦ (C * (t ^ 9)⁻¹) * kernel s) (Ici t)
    exact hkint.const_mul (C * (t ^ 9)⁻¹)
  have hnorm : ‖∫ s in Ici t, kernel s * D s‖ ≤ ∫ s in Ici t, majorant s := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmint
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hsT : T ≤ s := hTt.trans hs
    have hspos : 0 < s := htpos.trans_le hs
    have hpow : (s ^ 9)⁻¹ ≤ (t ^ 9)⁻¹ := by
      gcongr
      exact hs
    have hD := hDbound s hsT
    dsimp only [kernel, majorant]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-alpha * (s - t)) * |D s|
          ≤ Real.exp (-alpha * (s - t)) * (C * (s ^ 9)⁻¹) := by gcongr
      _ ≤ Real.exp (-alpha * (s - t)) * (C * (t ^ 9)⁻¹) := by gcongr
      _ = C * (t ^ 9)⁻¹ * Real.exp (-alpha * (s - t)) := by ring
  calc
    ‖∫ s in Ici t, Real.exp (-alpha * (s - t)) * D s‖
        ≤ ∫ s in Ici t, majorant s := by simpa only [kernel] using hnorm
    _ = (C * (t ^ 9)⁻¹) * ∫ s in Ici t, kernel s := by
          simp only [majorant, MeasureTheory.integral_const_mul]
    _ = (C * (t ^ 9)⁻¹) * alpha⁻¹ := by
          rw [show (∫ s in Ici t, kernel s) = alpha⁻¹ by
            simpa only [kernel] using integral_exp_neg_mul_sub_Ici alpha t halpha]
    _ = C * alpha⁻¹ * (t ^ 9)⁻¹ := by ring

/-- Convolution with a terminal exponentially decaying kernel preserves `O(t⁻⁹)`. -/
theorem terminal_exponential_convolution_isBigO (D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹) :
    (fun t ↦ ∫ s in Ici t, Real.exp (-alpha * (s - t)) * D s) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  apply IsBigO.of_bound (C * alpha⁻¹)
  filter_upwards [eventually_ge_atTop T] with t hTt
  have htpos : 0 < t := hT.trans_le hTt
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos htpos 9))] using
    terminal_exponential_convolution_bound D T C alpha hT hC halpha hDbound hTt

/-- If `A ≥ alpha` on the terminal half-line, its backwards evolution kernel is
bounded by the constant terminal exponential kernel. -/
theorem exp_neg_intervalIntegral_le_exp_neg_mul_sub (A : ℝ → ℝ) (T alpha : ℝ)
    (_halpha : 0 < alpha) (hAcont : Continuous A)
    (hAlower : ∀ x, T ≤ x → alpha ≤ A x)
    {t s : ℝ} (hTt : T ≤ t) (hts : t ≤ s) :
    Real.exp (-∫ x in t..s, A x) ≤ Real.exp (-alpha * (s - t)) := by
  apply Real.exp_le_exp.mpr
  have hAint : IntervalIntegrable A volume t s := hAcont.intervalIntegrable _ _
  have hcint : IntervalIntegrable (fun _ : ℝ ↦ alpha) volume t s :=
    intervalIntegrable_const
  have hint : ∫ _x in t..s, (alpha : ℝ) ≤ ∫ x in t..s, A x := by
    apply intervalIntegral.integral_mono_on hts hcint hAint
    intro x hx
    exact hAlower x (hTt.trans hx.1)
  calc
    -∫ x in t..s, A x ≤ -(∫ _x in t..s, (alpha : ℝ)) := neg_le_neg hint
    _ = -alpha * (s - t) := by simp; ring

/-- The absolute terminal variable-kernel integrand required by MI11b is
integrable whenever the defect is `O(t⁻⁹)`. -/
theorem terminal_variable_kernel_abs_integrableOn (A D : ℝ → ℝ)
    (T C alpha : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : Continuous A) (hDcont : Continuous D)
    (hAlower : ∀ x, T ≤ x → alpha ≤ A x)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹)
    {t : ℝ} (hTt : T ≤ t) :
    IntegrableOn (fun s ↦ Real.exp (-∫ x in t..s, A x) * |D s|) (Ici t) := by
  have htpos : 0 < t := hT.trans_le hTt
  let variableKernel : ℝ → ℝ := fun s ↦ Real.exp (-∫ x in t..s, A x) * |D s|
  let constantKernel : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (s - t))
  let majorant : ℝ → ℝ := fun s ↦ (C * (t ^ 9)⁻¹) * constantKernel s
  have hckint : IntegrableOn constantKernel (Ici t) := by
    simpa only [constantKernel] using integrableOn_exp_neg_mul_sub_Ici alpha t halpha
  have hmint : IntegrableOn majorant (Ici t) := by
    change IntegrableOn (fun s ↦ (C * (t ^ 9)⁻¹) * constantKernel s) (Ici t)
    exact hckint.const_mul (C * (t ^ 9)⁻¹)
  have hvcont : Continuous variableKernel := by
    dsimp only [variableKernel]
    have hint : Continuous (fun s ↦ ∫ x in t..s, A x) :=
      (intervalIntegral.differentiable_integral_of_continuous hAcont).continuous
    fun_prop
  have hvmeas : AEStronglyMeasurable variableKernel (volume.restrict (Ici t)) :=
    hvcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hdom : ∀ᵐ s ∂volume.restrict (Ici t), ‖variableKernel s‖ ≤ majorant s := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hsT : T ≤ s := hTt.trans hs
    have hpow : (s ^ 9)⁻¹ ≤ (t ^ 9)⁻¹ := by
      gcongr
      exact hs
    have hk := exp_neg_intervalIntegral_le_exp_neg_mul_sub A T alpha halpha hAcont
      hAlower hTt hs
    have hD := hDbound s hsT
    dsimp only [variableKernel, majorant, constantKernel]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    calc
      Real.exp (-∫ x in t..s, A x) * |D s|
          ≤ Real.exp (-alpha * (s - t)) * |D s| := by gcongr
      _ ≤ Real.exp (-alpha * (s - t)) * (C * (s ^ 9)⁻¹) := by gcongr
      _ ≤ Real.exp (-alpha * (s - t)) * (C * (t ^ 9)⁻¹) := by gcongr
      _ = C * (t ^ 9)⁻¹ * Real.exp (-alpha * (s - t)) := by ring
  change IntegrableOn variableKernel (Ici t)
  exact hmint.mono' hvmeas hdom

/-- Quantitative terminal estimate for the variable evolution kernel. -/
theorem terminal_variable_convolution_bound (A D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : Continuous A)
    (hAlower : ∀ x, T ≤ x → alpha ≤ A x)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹)
    {t : ℝ} (hTt : T ≤ t) :
    ‖∫ s in Ici t, Real.exp (-∫ x in t..s, A x) * D s‖ ≤
      C * alpha⁻¹ * (t ^ 9)⁻¹ := by
  have htpos : 0 < t := hT.trans_le hTt
  let variableKernel : ℝ → ℝ := fun s ↦ Real.exp (-∫ x in t..s, A x) * D s
  let constantKernel : ℝ → ℝ := fun s ↦ Real.exp (-alpha * (s - t))
  let majorant : ℝ → ℝ := fun s ↦ (C * (t ^ 9)⁻¹) * constantKernel s
  have hckint : IntegrableOn constantKernel (Ici t) := by
    simpa only [constantKernel] using integrableOn_exp_neg_mul_sub_Ici alpha t halpha
  have hmint : IntegrableOn majorant (Ici t) := by
    change IntegrableOn (fun s ↦ (C * (t ^ 9)⁻¹) * constantKernel s) (Ici t)
    exact hckint.const_mul (C * (t ^ 9)⁻¹)
  have hnorm : ‖∫ s in Ici t, variableKernel s‖ ≤ ∫ s in Ici t, majorant s := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmint
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hsT : T ≤ s := hTt.trans hs
    have hpow : (s ^ 9)⁻¹ ≤ (t ^ 9)⁻¹ := by
      gcongr
      exact hs
    have hk := exp_neg_intervalIntegral_le_exp_neg_mul_sub A T alpha halpha hAcont
      hAlower hTt hs
    have hD := hDbound s hsT
    dsimp only [variableKernel, majorant, constantKernel]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-∫ x in t..s, A x) * |D s|
          ≤ Real.exp (-alpha * (s - t)) * |D s| := by gcongr
      _ ≤ Real.exp (-alpha * (s - t)) * (C * (s ^ 9)⁻¹) := by gcongr
      _ ≤ Real.exp (-alpha * (s - t)) * (C * (t ^ 9)⁻¹) := by gcongr
      _ = C * (t ^ 9)⁻¹ * Real.exp (-alpha * (s - t)) := by ring
  calc
    ‖∫ s in Ici t, Real.exp (-∫ x in t..s, A x) * D s‖
        ≤ ∫ s in Ici t, majorant s := by simpa only [variableKernel] using hnorm
    _ = (C * (t ^ 9)⁻¹) * ∫ s in Ici t, constantKernel s := by
          simp only [majorant, MeasureTheory.integral_const_mul]
    _ = (C * (t ^ 9)⁻¹) * alpha⁻¹ := by
          rw [show (∫ s in Ici t, constantKernel s) = alpha⁻¹ by
            simpa only [constantKernel] using integral_exp_neg_mul_sub_Ici alpha t halpha]
    _ = C * alpha⁻¹ * (t ^ 9)⁻¹ := by ring

/-- The variable terminal evolution kernel from MI11b preserves `O(t⁻⁹)`. -/
theorem terminal_variable_convolution_isBigO (A D : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : Continuous A)
    (hAlower : ∀ x, T ≤ x → alpha ≤ A x)
    (hDbound : ∀ s, T ≤ s → |D s| ≤ C * (s ^ 9)⁻¹) :
    (fun t ↦ ∫ s in Ici t, Real.exp (-∫ x in t..s, A x) * D s) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  apply IsBigO.of_bound (C * alpha⁻¹)
  filter_upwards [eventually_ge_atTop T] with t hTt
  have htpos : 0 < t := hT.trans_le hTt
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos htpos 9))] using
    terminal_variable_convolution_bound A D T C alpha hT hC halpha hAcont hAlower
      hDbound hTt

/-- Unstable branch of the exact linear remainder argument, stated with a fixed
half-line on which all quantitative hypotheses hold. -/
theorem unstable_linear_remainder_isBigO (A D R : ℝ → ℝ) (T C alpha : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hAcont : ContinuousOn A (Ici T)) (hDcont : ContinuousOn D (Ici T))
    (hRcont : ContinuousOn R (Ici T))
    (hAlower : ∀ t ∈ Ici T, alpha ≤ A t)
    (hDbound : ∀ t ∈ Ici T, |D t| ≤ C * (t ^ 9)⁻¹)
    (hode : ∀ t ∈ Ioi T, HasDerivAt R (A t * R t - D t) t)
    (hterminal : Tendsto R atTop (𝓝 0)) :
    R =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let Ae : ℝ → ℝ := extendFromIci A T
  let De : ℝ → ℝ := extendFromIci D T
  have hAecont : Continuous Ae := continuous_extendFromIci hAcont
  have hDecont : Continuous De := continuous_extendFromIci hDcont
  have hAelower : ∀ t, T ≤ t → alpha ≤ Ae t := by
    intro t ht
    simpa only [Ae, extendFromIci_eq ht] using hAlower t ht
  have hDebound : ∀ t, T ≤ t → |De t| ≤ C * (t ^ 9)⁻¹ := by
    intro t ht
    simpa only [De, extendFromIci_eq ht] using hDbound t ht
  have hconv := terminal_variable_convolution_isBigO Ae De T C alpha hT hC halpha
    hAecont hAelower hDebound
  have habsolute : ∀ t ∈ Ici T, IntegrableOn
      (fun s ↦ Real.exp (-∫ x in t..s, A x) * |D s|) (Ici t) := by
    intro t ht
    have hext := terminal_variable_kernel_abs_integrableOn Ae De T C alpha hT hC
      halpha hAecont hDecont hAelower hDebound ht
    apply hext.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hTs : T ≤ s := ht.trans hs
    dsimp only [Ae, De]
    rw [extendFromIci_eq hTs]
    congr 3
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hs] at hx
    exact extendFromIci_eq (ht.trans hx.1)
  have hformula : ∀ t ∈ Ici T,
      R t = ∫ s in Ici t, Real.exp (-∫ x in t..s, A x) * D s :=
    MI11_variation_of_constants_terminal A D R T alpha halpha hAcont hDcont hRcont
      hAlower hode hterminal habsolute
  have hconv' :
      (fun t ↦ ∫ s in Ici t, Real.exp (-∫ x in t..s, A x) * D s) =O[atTop]
        (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    apply hconv.congr'
    · filter_upwards [eventually_ge_atTop T] with t hTt
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
      intro s hs
      have hTs : T ≤ s := hTt.trans hs
      dsimp only [Ae, De]
      rw [extendFromIci_eq hTs]
      congr 3
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hs] at hx
      exact extendFromIci_eq (hTt.trans hx.1)
    · filter_upwards with t
      rfl
  apply hconv'.congr'
  · filter_upwards [eventually_ge_atTop T] with t hTt
    exact (hformula t hTt).symm
  · filter_upwards with t
    rfl

/-- The exact eight-term remainder is `O(t⁻⁹)` under the full source
hypotheses.  This is where the stable and unstable kernel estimates are
instantiated with the mean-value coefficient. -/
theorem remainder8_isBigO {I : Set ℝ} (F G Y : ℝ → ℝ) (yStar T0 : ℝ)
    (hIopen : IsOpen I) (hIconn : OrdConnected I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I) (hYc1 : ContDiffOn ℝ 1 Y (Ici T0))
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t)
    (hYlim : Tendsto Y atTop (𝓝 yStar)) :
    remainder8 Y yStar (recursiveCoefficients8 F G yStar 8) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let b := recursiveCoefficients8 F G yStar 8
  let A := remainderLinearCoefficient F G Y yStar b
  let D := defect8 F G yStar b
  let R := remainder8 Y yStar b
  have hAtend : Tendsto A atTop (𝓝 (deriv F yStar)) :=
    remainderLinearCoefficient_tendsto F G Y yStar b hIopen hIconn hyStar hF hG hYlim
  have hDeq : D =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    simpa only [D, b, iteratedDeriv_zero] using
      recursive_defect8_isBigO F G yStar hIopen hyStar hF hG hFzero hmu 0 (by omega)
  obtain ⟨cD, hcD⟩ := hDeq.bound
  let C : ℝ := max cD 0
  have hC : 0 ≤ C := le_max_right _ _
  have hDboundEv : ∀ᶠ t in atTop, |D t| ≤ C * (t ^ 9)⁻¹ := by
    filter_upwards [hcD, eventually_gt_atTop (0 : ℝ)] with t hDt ht
    have hle := hDt.trans
      (mul_le_mul_of_nonneg_right (le_max_left cD 0) (norm_nonneg ((t ^ 9)⁻¹)))
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht 9)), C] using hle
  have hReq : ∀ᶠ t in atTop, HasDerivAt R (A t * R t - D t) t := by
    simpa only [A, D, R, b] using eventually_remainder_linear_equation
      F G Y yStar T0 b hIopen hIconn hyStar hF hG hT0 hYmap hYode
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hIopen yStar hyStar
  let radius : ℝ := epsilon / 2
  let a : ℝ := yStar - radius
  let c : ℝ := yStar + radius
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have haI : a ∈ I := by
    apply hball
    change dist a yStar < epsilon
    rw [Real.dist_eq]
    dsimp [a, radius]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hcI : c ∈ I := by
    apply hball
    change dist c yStar < epsilon
    rw [Real.dist_eq]
    dsimp [c, radius]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hIccI : Icc a c ⊆ I := by
    intro z hz
    exact hIconn.out haI hcI (by simpa only [uIcc_of_le hac] using hz)
  have hPmemEv : ∀ᶠ t in atTop, approximation8 yStar b t ∈ Icc a c := by
    apply (approximation8_tendsto yStar b).eventually
    exact Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds ⟨by dsimp [a]; linarith, by dsimp [c]; linarith⟩)
      fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩
  have hYmemEv : ∀ᶠ t in atTop, Y t ∈ Icc a c := by
    apply hYlim.eventually
    exact Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds ⟨by dsimp [a]; linarith, by dsimp [c]; linarith⟩)
      fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩
  have hfixedContinuity (T : ℝ) (hT : 0 < T) (hT0T : T0 ≤ T)
      (hPmem : MapsTo (approximation8 yStar b) (Ici T) (Icc a c))
      (hYmem : MapsTo Y (Ici T) (Icc a c)) :
      ContinuousOn A (Ici T) ∧ ContinuousOn D (Ici T) ∧ ContinuousOn R (Ici T) := by
    have hYcont : ContinuousOn Y (Ici T) :=
      hYc1.continuousOn.mono fun t ht ↦ hT0T.trans ht
    have hAcont : ContinuousOn A (Ici T) := by
      simpa only [A] using remainderLinearCoefficient_continuousOn_of_mem_Icc
        F G Y yStar b T a c hIopen hF hG hT hac hIccI hPmem hYmem hYcont
    have hPcont : ContinuousOn (approximation8 yStar b) (Ici T) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      change ContinuousAt (fun t ↦ yStar + polynomial8 b t⁻¹) t
      have hpoly : Continuous (polynomial8 b) := by unfold polynomial8; fun_prop
      exact (hpoly.continuousAt.comp
        (continuousAt_inv₀ (ne_of_gt (hT.trans_le ht)))).const_add _
    have hRcont : ContinuousOn R (Ici T) := by
      change ContinuousOn (fun t ↦ Y t - approximation8 yStar b t) (Ici T)
      exact hYcont.sub hPcont
    have hPtwo : ContDiffOn ℝ 2 (approximation8 yStar b) (Ioi 0) := by
      intro t ht
      apply ContDiffAt.contDiffWithinAt
      change ContDiffAt ℝ 2 (fun t ↦ yStar + polynomial8 b t⁻¹) t
      have ht0 : t ≠ 0 := ne_of_gt ht
      unfold polynomial8
      fun_prop
    have hPderiv : ContinuousOn (deriv (approximation8 yStar b)) (Ici T) :=
      (hPtwo.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
        fun t ht ↦ hT.trans_le ht
    have hFP : ContinuousOn (fun t ↦ F (approximation8 yStar b t)) (Ici T) :=
      hF.continuousOn.comp hPcont fun t ht ↦ hIccI (hPmem ht)
    have hGP : ContinuousOn (fun t ↦ G (approximation8 yStar b t)) (Ici T) :=
      hG.continuousOn.comp hPcont fun t ht ↦ hIccI (hPmem ht)
    have hinvcont : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Ici T) := by
      intro t ht
      exact (continuousAt_inv₀ (ne_of_gt (hT.trans_le ht))).continuousWithinAt
    have hDcont : ContinuousOn D (Ici T) := by
      change ContinuousOn (fun t ↦ deriv (approximation8 yStar b) t -
        F (approximation8 yStar b t) - t⁻¹ * G (approximation8 yStar b t)) (Ici T)
      exact (hPderiv.sub hFP).sub (hinvcont.mul hGP)
    exact ⟨hAcont, hDcont, hRcont⟩
  rcases lt_or_gt_of_ne hmu with hmuNeg | hmuPos
  · let alpha : ℝ := -(deriv F yStar) / 2
    have halpha : 0 < alpha := by dsimp [alpha]; linarith
    have hAsignEv : ∀ᶠ t in atTop, A t ≤ -alpha := by
      have hstrict : deriv F yStar < -alpha := by dsimp [alpha]; linarith
      exact (hAtend.eventually (Iio_mem_nhds hstrict)).mono fun _ ht ↦ ht.le
    obtain ⟨T, hTall⟩ := eventually_atTop.1
      (hPmemEv.and (hYmemEv.and (hDboundEv.and (hReq.and hAsignEv))))
    let T' : ℝ := max T (max T0 1)
    have hTT' : T ≤ T' := le_max_left _ _
    have hT0T' : T0 ≤ T' := le_trans (le_max_left _ _) (le_max_right _ _)
    have hT' : 0 < T' := lt_of_lt_of_le (by norm_num) <|
      le_trans (le_max_right T0 1) (le_max_right T (max T0 1))
    have hall : ∀ t ∈ Ici T', approximation8 yStar b t ∈ Icc a c ∧
        Y t ∈ Icc a c ∧ |D t| ≤ C * (t ^ 9)⁻¹ ∧
        HasDerivAt R (A t * R t - D t) t ∧ A t ≤ -alpha := by
      intro t ht
      exact hTall t (hTT'.trans ht)
    obtain ⟨hAcont, hDcont, hRcont⟩ := hfixedContinuity T' hT' hT0T'
      (fun t ht ↦ (hall t ht).1) (fun t ht ↦ (hall t ht).2.1)
    exact stable_linear_remainder_isBigO A D R T' C alpha hT' hC halpha
      hAcont hDcont hRcont (fun t ht ↦ (hall t ht).2.2.2.2)
      (fun t ht ↦ (hall t ht).2.2.1)
      (fun t ht ↦ (hall t (mem_Ici.mpr ht.le)).2.2.2.1)
  · let alpha : ℝ := deriv F yStar / 2
    have halpha : 0 < alpha := by dsimp [alpha]; linarith
    have hAsignEv : ∀ᶠ t in atTop, alpha ≤ A t := by
      have hstrict : alpha < deriv F yStar := by dsimp [alpha]; linarith
      exact (hAtend.eventually (Ioi_mem_nhds hstrict)).mono fun _ ht ↦ ht.le
    obtain ⟨T, hTall⟩ := eventually_atTop.1
      (hPmemEv.and (hYmemEv.and (hDboundEv.and (hReq.and hAsignEv))))
    let T' : ℝ := max T (max T0 1)
    have hTT' : T ≤ T' := le_max_left _ _
    have hT0T' : T0 ≤ T' := le_trans (le_max_left _ _) (le_max_right _ _)
    have hT' : 0 < T' := lt_of_lt_of_le (by norm_num) <|
      le_trans (le_max_right T0 1) (le_max_right T (max T0 1))
    have hall : ∀ t ∈ Ici T', approximation8 yStar b t ∈ Icc a c ∧
        Y t ∈ Icc a c ∧ |D t| ≤ C * (t ^ 9)⁻¹ ∧
        HasDerivAt R (A t * R t - D t) t ∧ alpha ≤ A t := by
      intro t ht
      exact hTall t (hTT'.trans ht)
    obtain ⟨hAcont, hDcont, hRcont⟩ := hfixedContinuity T' hT' hT0T'
      (fun t ht ↦ (hall t ht).1) (fun t ht ↦ (hall t ht).2.1)
    have hRterminal : Tendsto R atTop (𝓝 0) := by
      simpa only [R] using remainder8_tendsto_zero Y yStar b hYlim
    exact unstable_linear_remainder_isBigO A D R T' C alpha hT' hC halpha
      hAcont hDcont hRcont (fun t ht ↦ (hall t ht).2.2.2.2)
      (fun t ht ↦ (hall t ht).2.2.1)
      (fun t ht ↦ (hall t (mem_Ici.mpr ht.le)).2.2.2.1)
      hRterminal

/-- The first derivative bootstrap from the exact linear equation. -/
theorem remainder8_first_derivative_isBigO {I : Set ℝ} (F G Y : ℝ → ℝ)
    (yStar T0 : ℝ) (hIopen : IsOpen I) (hIconn : OrdConnected I)
    (hyStar : yStar ∈ I) (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I) (hYc1 : ContDiffOn ℝ 1 Y (Ici T0))
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t)
    (hYlim : Tendsto Y atTop (𝓝 yStar)) :
    (fun t ↦ iteratedDeriv 1
      (remainder8 Y yStar (recursiveCoefficients8 F G yStar 8)) t) =O[atTop]
        (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let b := recursiveCoefficients8 F G yStar 8
  let A := remainderLinearCoefficient F G Y yStar b
  let D := defect8 F G yStar b
  let R := remainder8 Y yStar b
  have hR : R =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    simpa only [R, b] using remainder8_isBigO F G Y yStar T0 hIopen hIconn hyStar
      hF hG hFzero hmu hT0 hYmap hYc1 hYode hYlim
  have hA : A =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) :=
    (remainderLinearCoefficient_tendsto F G Y yStar b hIopen hIconn hyStar hF hG
      hYlim).isBigO_one ℝ
  have hAR : (fun t ↦ A t * R t) =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    apply (hA.mul hR).congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      simp
  have hD : D =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    simpa only [D, b, iteratedDeriv_zero] using
      recursive_defect8_isBigO F G yStar hIopen hyStar hF hG hFzero hmu 0 (by omega)
  have hEq : ∀ᶠ t in atTop, HasDerivAt R (A t * R t - D t) t := by
    simpa only [A, D, R, b] using eventually_remainder_linear_equation F G Y yStar T0 b
      hIopen hIconn hyStar hF hG hT0 hYmap hYode
  apply (hAR.sub hD).congr'
  · filter_upwards [hEq] with t ht
    simpa only [iteratedDeriv_one, R] using ht.deriv.symm
  · filter_upwards with t
    rfl

/-- Interior regularity supplied by the ODE bootstrap interface. -/
theorem asymptoticallyAutonomousSolution_contDiffOn_ten {I : Set ℝ}
    (F G Y : ℝ → ℝ) (T0 : ℝ) (hIopen : IsOpen I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I) (hYc1 : ContDiffOn ℝ 1 Y (Ici T0))
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t) :
    ContDiffOn ℝ 10 Y (Ioi T0) := by
  let field : ℝ × ℝ → ℝ := fun p ↦ F p.2 + p.1⁻¹ * G p.2
  let domain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ I
  have hopen : IsOpen domain := isOpen_Ioi.prod hIopen
  have hsmooth : ContDiffOn ℝ 9 field domain := by
    dsimp only [field, domain]
    exact (hF.comp contDiffOn_snd fun p hp ↦ hp.2).add
      ((contDiffOn_fst.inv fun p hp ↦ ne_of_gt hp.1).mul
        (hG.comp contDiffOn_snd fun p hp ↦ hp.2))
  have hgraph : ∀ t ∈ Ioi T0, (t, Y t) ∈ domain := by
    intro t ht
    exact ⟨hT0.trans ht, hYmap (mem_Ici.mpr ht.le)⟩
  have hcOne : ContDiffOn ℝ 1 Y (Ioi T0) := hYc1.mono Ioi_subset_Ici_self
  apply MI09_ode_regularity_bootstrap_nine_to_ten field domain (Ioi T0) Y hopen
    isOpen_Ioi hsmooth hgraph hcOne
  simpa only [field, asymptoticallyAutonomousRhs] using hYode

/-- Taking a scalar iterated derivative consumes the corresponding number of
orders of local smoothness. -/
theorem ContDiffAt.contDiffAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ} {m k : ℕ}
    (hf : ContDiffAt ℝ (m + k) f x) : ContDiffAt ℝ m (iteratedDeriv k f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  have hi : ContDiffAt ℝ m (iteratedFDeriv ℝ k f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast le_refl (m + k))
  exact (ContinuousLinearEquiv.contDiff
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.toContinuousLinearEquiv).contDiffAt.comp
      x hi

/-- A locally `C¹` jet is uniformly Lipschitz along two arguments converging
to the same point. -/
theorem iteratedDeriv_comp_sub_comp_isBigO {f U V g : ℝ → ℝ} {x : ℝ} (k : ℕ)
    (hf : ContDiffAt ℝ (1 + k) f x) (hU : Tendsto U atTop (𝓝 x))
    (hV : Tendsto V atTop (𝓝 x)) (hUV : (fun t ↦ U t - V t) =O[atTop] g) :
    (fun t ↦ iteratedDeriv k f (U t) - iteratedDeriv k f (V t)) =O[atTop] g := by
  have hj : ContDiffAt ℝ 1 (iteratedDeriv k f) x :=
    ContDiffAt.contDiffAt_iteratedDeriv hf
  have hpair : Tendsto (fun t ↦ (U t, V t)) atTop (𝓝 (x, x)) := by
    simpa only [nhds_prod_eq] using hU.prodMk hV
  have hd : (fun t ↦ iteratedDeriv k f (U t) - iteratedDeriv k f (V t)) =O[atTop]
      (fun t ↦ U t - V t) := by
    apply ((hj.hasStrictFDerivAt one_ne_zero).isBigO_sub.comp_tendsto hpair).congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      rfl
  exact hd.trans hUV

/-- Product differences preserve a common error scale when the undifferenced
factors are bounded. -/
theorem mul_sub_mul_isBigO_of_isBigO_one {a b c d g : ℝ → ℝ}
    (hab : (fun t ↦ a t - b t) =O[atTop] g)
    (hc : c =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hb : b =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hcd : (fun t ↦ c t - d t) =O[atTop] g) :
    (fun t ↦ a t * c t - b t * d t) =O[atTop] g := by
  have hleft : (fun t ↦ (a t - b t) * c t) =O[atTop] g := by
    apply (hab.mul hc).congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      simp
  have hright : (fun t ↦ b t * (c t - d t)) =O[atTop] g := by
    apply (hb.mul hcd).congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      simp
  apply (hleft.add hright).congr'
  · filter_upwards with t
    ring
  · filter_upwards with t
    simp

/-- Fixed-order (`m ≤ 3`) chain-rule estimate for two curves converging to
the same point.  This is the finite jet calculation used in the derivative
bootstrap; it avoids a general ordered-partition expansion. -/
theorem comp_sub_comp_iteratedDeriv_isBigO_three (f U V g : ℝ → ℝ) (x T : ℝ)
    (hf : ContDiffAt ℝ 4 f x) (hUlim : Tendsto U atTop (𝓝 x))
    (hVlim : Tendsto V atTop (𝓝 x))
    (hfU : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 f (U t))
    (hfV : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 f (V t))
    (hUc : ContDiffOn ℝ 3 U (Ioi T)) (hVc : ContDiffOn ℝ 3 V (Ioi T))
    (m : ℕ) (hm : m ≤ 3)
    (hUbound : ∀ j ≤ m,
      (fun t ↦ iteratedDeriv j U t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hVbound : ∀ j ≤ m,
      (fun t ↦ iteratedDeriv j V t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hdiff : ∀ j ≤ m,
      (fun t ↦ iteratedDeriv j U t - iteratedDeriv j V t) =O[atTop] g) :
    (fun t ↦ iteratedDeriv m (fun s ↦ f (U s) - f (V s)) t) =O[atTop] g := by
  have houterDiff : ∀ k ≤ m,
      (fun t ↦ iteratedDeriv k f (U t) - iteratedDeriv k f (V t)) =O[atTop] g := by
    intro k hk
    apply iteratedDeriv_comp_sub_comp_isBigO k
    · exact hf.of_le (by exact_mod_cast (show 1 + k ≤ 4 by omega))
    · exact hUlim
    · exact hVlim
    · simpa only [iteratedDeriv_zero] using hdiff 0 (by omega)
  have houterU : ∀ k ≤ m,
      (fun t ↦ iteratedDeriv k f (U t)) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
    intro k hk
    have hkcont : ContinuousAt (iteratedDeriv k f) x :=
      (ContDiffAt.contDiffAt_iteratedDeriv
        (hf.of_le (by simpa using (show k ≤ 4 by omega)) : ContDiffAt ℝ (0 + k) f x)).continuousAt
    exact (hkcont.tendsto.comp hUlim).isBigO_one ℝ
  have houterV : ∀ k ≤ m,
      (fun t ↦ iteratedDeriv k f (V t)) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
    intro k hk
    have hkcont : ContinuousAt (iteratedDeriv k f) x :=
      (ContDiffAt.contDiffAt_iteratedDeriv
        (hf.of_le (by simpa using (show k ≤ 4 by omega)) : ContDiffAt ℝ (0 + k) f x)).continuousAt
    exact (hkcont.tendsto.comp hVlim).isBigO_one ℝ
  interval_cases m
  · simpa only [iteratedDeriv_zero] using houterDiff 0 (by omega)
  · have hprod := mul_sub_mul_isBigO_of_isBigO_one
        (houterDiff 1 (by omega)) (hUbound 1 (by omega)) (houterV 1 (by omega))
        (hdiff 1 (by omega))
    apply hprod.congr'
    · filter_upwards [eventually_gt_atTop T] with t ht
      have hUt : ContDiffAt ℝ 1 U t :=
        ((hUc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by norm_num)
      have hVt : ContDiffAt ℝ 1 V t :=
        ((hVc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by norm_num)
      have hfUt : ContDiffAt ℝ 1 f (U t) := (hfU t ht).of_le (by norm_num)
      have hfVt : ContDiffAt ℝ 1 f (V t) := (hfV t ht).of_le (by norm_num)
      symm
      change iteratedDeriv 1 ((f ∘ U) - (f ∘ V)) t = _
      rw [iteratedDeriv_sub (hfUt.comp t hUt) (hfVt.comp t hVt)]
      simp only [iteratedDeriv_one, Function.comp_apply, deriv_comp t hfUt.differentiableAt_one
        hUt.differentiableAt_one, deriv_comp t hfVt.differentiableAt_one hVt.differentiableAt_one]
    · filter_upwards with t
      rfl
  · have hsqU : (fun t ↦ iteratedDeriv 1 U t ^ 2) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply ((hUbound 1 (by omega)).mul (hUbound 1 (by omega))).congr'
      · filter_upwards with t
        simp [pow_two]
      · filter_upwards with t
        simp
    have hsqDiff : (fun t ↦ iteratedDeriv 1 U t ^ 2 - iteratedDeriv 1 V t ^ 2) =O[atTop]
        g := by
      simpa only [pow_two] using mul_sub_mul_isBigO_of_isBigO_one
        (hdiff 1 (by omega)) (hUbound 1 (by omega)) (hVbound 1 (by omega))
        (hdiff 1 (by omega))
    have hfirst := mul_sub_mul_isBigO_of_isBigO_one
      (houterDiff 2 (by omega)) hsqU (houterV 2 (by omega)) hsqDiff
    have hsecond := mul_sub_mul_isBigO_of_isBigO_one
      (houterDiff 1 (by omega)) (hUbound 2 (by omega)) (houterV 1 (by omega))
      (hdiff 2 (by omega))
    apply (hfirst.add hsecond).congr'
    · filter_upwards [eventually_gt_atTop T] with t ht
      have hUt : ContDiffAt ℝ 2 U t :=
        ((hUc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by norm_num)
      have hVt : ContDiffAt ℝ 2 V t :=
        ((hVc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by norm_num)
      have hfUt : ContDiffAt ℝ 2 f (U t) := (hfU t ht).of_le (by norm_num)
      have hfVt : ContDiffAt ℝ 2 f (V t) := (hfV t ht).of_le (by norm_num)
      symm
      change iteratedDeriv 2 ((f ∘ U) - (f ∘ V)) t = _
      rw [iteratedDeriv_sub (hfUt.comp t hUt) (hfVt.comp t hVt),
        iteratedDeriv_comp_two hfUt hUt, iteratedDeriv_comp_two hfVt hVt]
      simp only [Function.comp_apply, iteratedDeriv_one]
      ring
    · filter_upwards with t
      simp
  · have hsqU : (fun t ↦ iteratedDeriv 1 U t ^ 2) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply ((hUbound 1 (by omega)).mul (hUbound 1 (by omega))).congr'
      · filter_upwards with t
        simp [pow_two]
      · filter_upwards with t
        simp
    have hsqV : (fun t ↦ iteratedDeriv 1 V t ^ 2) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply ((hVbound 1 (by omega)).mul (hVbound 1 (by omega))).congr'
      · filter_upwards with t
        simp [pow_two]
      · filter_upwards with t
        simp
    have hsqDiff : (fun t ↦ iteratedDeriv 1 U t ^ 2 - iteratedDeriv 1 V t ^ 2) =O[atTop]
        g := by
      simpa only [pow_two] using mul_sub_mul_isBigO_of_isBigO_one
        (hdiff 1 (by omega)) (hUbound 1 (by omega)) (hVbound 1 (by omega))
        (hdiff 1 (by omega))
    have hcubeU : (fun t ↦ iteratedDeriv 1 U t ^ 3) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply (hsqU.mul (hUbound 1 (by omega))).congr'
      · filter_upwards with t
        simp [pow_succ]
      · filter_upwards with t
        simp
    have hcubeDiff :
        (fun t ↦ iteratedDeriv 1 U t ^ 3 - iteratedDeriv 1 V t ^ 3) =O[atTop] g := by
      simpa only [pow_succ] using mul_sub_mul_isBigO_of_isBigO_one hsqDiff
        (hUbound 1 (by omega)) hsqV (hdiff 1 (by omega))
    have hfirst := mul_sub_mul_isBigO_of_isBigO_one
      (houterDiff 3 (by omega)) hcubeU (houterV 3 (by omega)) hcubeDiff
    have hpairU : (fun t ↦ iteratedDeriv 2 f (U t) * iteratedDeriv 2 U t) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply ((houterU 2 (by omega)).mul (hUbound 2 (by omega))).congr'
      · filter_upwards with t
        rfl
      · filter_upwards with t
        simp
    have hpairV : (fun t ↦ iteratedDeriv 2 f (V t) * iteratedDeriv 2 V t) =O[atTop]
        (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply ((houterV 2 (by omega)).mul (hVbound 2 (by omega))).congr'
      · filter_upwards with t
        rfl
      · filter_upwards with t
        simp
    have hpairDiff := mul_sub_mul_isBigO_of_isBigO_one
      (houterDiff 2 (by omega)) (hUbound 2 (by omega)) (houterV 2 (by omega))
      (hdiff 2 (by omega))
    have hmiddleBase := mul_sub_mul_isBigO_of_isBigO_one hpairDiff
      (hUbound 1 (by omega)) hpairV (hdiff 1 (by omega))
    have hmiddle :
        (fun t ↦ 3 * (iteratedDeriv 2 f (U t) * iteratedDeriv 2 U t *
          iteratedDeriv 1 U t) - 3 * (iteratedDeriv 2 f (V t) * iteratedDeriv 2 V t *
          iteratedDeriv 1 V t)) =O[atTop] g := by
      apply hmiddleBase.const_mul_left (3 : ℝ) |>.congr'
      · filter_upwards with t
        ring
      · filter_upwards with t
        rfl
    have hthird := mul_sub_mul_isBigO_of_isBigO_one
      (houterDiff 1 (by omega)) (hUbound 3 (by omega)) (houterV 1 (by omega))
      (hdiff 3 (by omega))
    apply ((hfirst.add hmiddle).add hthird).congr'
    · filter_upwards [eventually_gt_atTop T] with t ht
      have hUt : ContDiffAt ℝ 3 U t :=
        (hUc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)
      have hVt : ContDiffAt ℝ 3 V t :=
        (hVc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)
      have hfUt : ContDiffAt ℝ 3 f (U t) := hfU t ht
      have hfVt : ContDiffAt ℝ 3 f (V t) := hfV t ht
      symm
      change iteratedDeriv 3 ((f ∘ U) - (f ∘ V)) t = _
      rw [iteratedDeriv_sub (hfUt.comp t hUt) (hfVt.comp t hVt),
        iteratedDeriv_comp_three hfUt hUt, iteratedDeriv_comp_three hfVt hVt]
      simp only [Function.comp_apply, iteratedDeriv_one]
      ring
    · filter_upwards with t
      simp

/-- The first three reciprocal jets are bounded at `+infinity`. -/
theorem inv_iteratedDeriv_isBigO_one : ∀ j ≤ 3,
    (fun t : ℝ ↦ iteratedDeriv j (fun s : ℝ ↦ s⁻¹) t) =O[atTop]
      (fun _t : ℝ ↦ (1 : ℝ)) := by
  intro j hj
  interval_cases j
  · simpa only [iteratedDeriv_zero] using tendsto_inv_atTop_zero.isBigO_one ℝ
  · have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hlim : Tendsto (fun t : ℝ ↦ -(t⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using (hinv.pow 2).neg
    apply hlim.isBigO_one ℝ |>.congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      simp only [iteratedDeriv_one, deriv_inv, inv_pow]
    · filter_upwards with t
      rfl
  · have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hlim : Tendsto (fun t : ℝ ↦ 2 * (t⁻¹) ^ 3) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _t : ℝ ↦ (2 : ℝ)) atTop (𝓝 2)).mul
        (hinv.pow 3)
    apply hlim.isBigO_one ℝ |>.congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      simpa only [inv_pow] using (iteratedDeriv_two_inv ht).symm
    · filter_upwards with t
      rfl
  · have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hlim : Tendsto (fun t : ℝ ↦ -6 * (t⁻¹) ^ 4) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _t : ℝ ↦ (-6 : ℝ)) atTop (𝓝 (-6))).mul
        (hinv.pow 4)
    apply hlim.isBigO_one ℝ |>.congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      simpa only [inv_pow] using (iteratedDeriv_three_inv ht).symm
    · filter_upwards with t
      rfl

/-- Every jet of the eight-term comparison function needed by the nonlinear
bootstrap is bounded at `+infinity`. -/
theorem approximation8_iteratedDeriv_isBigO_one (yStar : ℝ) (b : Fin 8 → ℝ) : ∀ j ≤ 3,
    (fun t ↦ iteratedDeriv j (approximation8 yStar b) t) =O[atTop]
      (fun _t : ℝ ↦ (1 : ℝ)) := by
  let q : ℝ → ℝ := fun x ↦ yStar + polynomial8 b x
  let inv : ℝ → ℝ := fun t ↦ t⁻¹
  have hq : ContDiff ℝ 3 q := by
    dsimp only [q]
    unfold polynomial8
    fun_prop
  have houter : ∀ k ≤ 3,
      (fun t ↦ iteratedDeriv k q (inv t)) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
    intro k hk
    exact ((hq.continuous_iteratedDeriv k (by exact_mod_cast hk)).continuousAt.tendsto.comp
      tendsto_inv_atTop_zero).isBigO_one ℝ
  intro j hj
  interval_cases j
  · simpa only [iteratedDeriv_zero] using (approximation8_tendsto yStar b).isBigO_one ℝ
  · have hprod := (houter 1 (by omega)).mul (inv_iteratedDeriv_isBigO_one 1 (by omega))
    apply hprod.congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      have hqt : ContDiffAt ℝ 1 q (inv t) := hq.contDiffAt.of_le (by norm_num)
      have hit : ContDiffAt ℝ 1 inv t := by dsimp [inv]; fun_prop
      symm
      change iteratedDeriv 1 (q ∘ inv) t = _
      rw [iteratedDeriv_one, deriv_comp t hqt.differentiableAt_one hit.differentiableAt_one]
      simp only [iteratedDeriv_one, inv]
    · filter_upwards with t
      simp
  · have hfirstRaw := (houter 2 (by omega)).mul
      ((inv_iteratedDeriv_isBigO_one 1 (by omega)).mul
        (inv_iteratedDeriv_isBigO_one 1 (by omega)))
    have hfirst : (fun t ↦ iteratedDeriv 2 q (inv t) *
        (iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t * iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t))
        =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply hfirstRaw.congr' <;> filter_upwards with t
      · rfl
      · simp
    have hsecondRaw := (houter 1 (by omega)).mul (inv_iteratedDeriv_isBigO_one 2 (by omega))
    have hsecond : (fun t ↦ iteratedDeriv 1 q (inv t) *
        iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply hsecondRaw.congr' <;> filter_upwards with t
      · rfl
      · simp
    apply (hfirst.add hsecond).congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      have hqt : ContDiffAt ℝ 2 q (inv t) := hq.contDiffAt.of_le (by norm_num)
      have hit : ContDiffAt ℝ 2 inv t := by dsimp [inv]; fun_prop
      symm
      change iteratedDeriv 2 (q ∘ inv) t = _
      rw [iteratedDeriv_comp_two hqt hit]
      simp only [iteratedDeriv_one]
      ring
    · filter_upwards with t
      simp
  · have hfirstRaw := (houter 3 (by omega)).mul
      ((inv_iteratedDeriv_isBigO_one 1 (by omega)).mul
        ((inv_iteratedDeriv_isBigO_one 1 (by omega)).mul
          (inv_iteratedDeriv_isBigO_one 1 (by omega))))
    have hfirst : (fun t ↦ iteratedDeriv 3 q (inv t) *
        (iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t *
          (iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t * iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t)))
        =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply hfirstRaw.congr' <;> filter_upwards with t
      · rfl
      · simp
    have hmiddleRaw := ((houter 2 (by omega)).mul
      (inv_iteratedDeriv_isBigO_one 2 (by omega))).mul
        (inv_iteratedDeriv_isBigO_one 1 (by omega)) |>.const_mul_left (3 : ℝ)
    have hmiddle : (fun t ↦ 3 * (iteratedDeriv 2 q (inv t) *
        iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) t * iteratedDeriv 1 (fun s : ℝ ↦ s⁻¹) t))
        =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply hmiddleRaw.congr' <;> filter_upwards with t
      · ring
      · simp
    have hthirdRaw := (houter 1 (by omega)).mul (inv_iteratedDeriv_isBigO_one 3 (by omega))
    have hthird : (fun t ↦ iteratedDeriv 1 q (inv t) *
        iteratedDeriv 3 (fun s : ℝ ↦ s⁻¹) t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
      apply hthirdRaw.congr' <;> filter_upwards with t
      · rfl
      · simp
    apply ((hfirst.add hmiddle).add hthird).congr'
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      have hqt : ContDiffAt ℝ 3 q (inv t) := hq.contDiffAt
      have hit : ContDiffAt ℝ 3 inv t := by dsimp [inv]; fun_prop
      symm
      change iteratedDeriv 3 (q ∘ inv) t = _
      rw [iteratedDeriv_comp_three hqt hit]
      simp only [iteratedDeriv_one]
      ring
    · filter_upwards with t
      simp

/-- The remainder equation before factoring the nonlinear differences by `R`.
This form is used to differentiate without differentiating the parameter
integral defining `remainderLinearCoefficient`. -/
theorem remainder_nonlinear_equation (F G Y : ℝ → ℝ) (yStar T0 : ℝ)
    (b : Fin 8 → ℝ) (hT0 : 0 < T0)
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t) :
    ∀ t ∈ Ioi T0, HasDerivAt (remainder8 Y yStar b)
      (nonlinearRemainderTerm F G Y (approximation8 yStar b) t -
        defect8 F G yStar b t) t := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (hT0.trans ht)
  have hP : DifferentiableAt ℝ (approximation8 yStar b) t := by
    change DifferentiableAt ℝ (fun s ↦ yStar + polynomial8 b s⁻¹) t
    unfold polynomial8
    fun_prop
  have hrem := (hYode t ht).sub hP.hasDerivAt
  apply hrem.congr_deriv
  dsimp only [asymptoticallyAutonomousRhs, nonlinearRemainderTerm, defect8, remainder8]
  ring

/-- Larger reciprocal powers are smaller at `+infinity`. -/
theorem reciprocal_pow_isBigO_of_le {p q : ℕ} (hpq : p ≤ q) :
    (fun t : ℝ ↦ (t ^ q)⁻¹) =O[atTop] (fun t : ℝ ↦ (t ^ p)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have htpos : 0 < t := zero_lt_one.trans_le ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos htpos q)),
    abs_of_pos (inv_pos.mpr (pow_pos htpos p)), one_mul]
  gcongr

/-- Exact reciprocal monomials gain one decay power per derivative. -/
theorem iteratedDeriv_reciprocal_pow_isBigO (n ell : ℕ) :
    (fun t : ℝ ↦ iteratedDeriv ell (fun s : ℝ ↦ (s ^ n)⁻¹) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ (n + ell))⁻¹) := by
  let C : ℝ := ∏ i ∈ Finset.range ell, ((-(n : ℤ) : ℝ) - i)
  have hbase := (isBigO_refl (fun t : ℝ ↦ (t ^ (n + ell))⁻¹) atTop).const_mul_left C
  apply hbase.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hz := (iteratedDerivWithin_zpow (𝕜 := ℝ) (s := Ioi (0 : ℝ))
      (-(n : ℤ)) ell isOpen_Ioi) ht
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht] at hz
    have heq : (fun s : ℝ ↦ (s ^ n)⁻¹) = fun s : ℝ ↦ s ^ (-(n : ℤ)) := by
      funext s
      simp [zpow_neg, inv_pow]
    have hz' : iteratedDeriv ell (fun s : ℝ ↦ (s ^ n)⁻¹) t =
        C * (t ^ (n + ell))⁻¹ := by
      rw [heq, hz]
      dsimp only [C]
      congr 1
      · simp
      · rw [show -(n : ℤ) - (ell : ℤ) = -((n + ell : ℕ) : ℤ) by omega, zpow_neg]
        norm_cast
    exact hz'.symm
  · filter_upwards with t
    rfl

/-- Splitting the eight-term comparison into its first four and last four
terms. -/
theorem approximation8_eq_approximation4_add_tail (yStar : ℝ) (b : Fin 8 → ℝ) :
    approximation8 yStar b =
      fun t ↦ approximation4 yStar (truncateCoefficients4 b) t + approximationTail8 b t := by
  funext t
  unfold approximation8 approximation4 approximationTail8 polynomial8 truncateCoefficients4
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.isValue]
  simp
  ring

/-- The omitted terms have precisely the derivative decay required for the
public four-term expansion. -/
theorem approximationTail8_iteratedDeriv_isBigO (b : Fin 8 → ℝ) : ∀ ell ≤ 4,
    (fun t ↦ iteratedDeriv ell (approximationTail8 b) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
  intro ell hell
  have hterm : ∀ j : Fin 4,
      (fun t ↦ iteratedDeriv ell
        (fun s : ℝ ↦ b ⟨j.1 + 4, by omega⟩ * (s ^ (j.1 + 5))⁻¹) t) =O[atTop]
          (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
    intro j
    have hbase := (iteratedDeriv_reciprocal_pow_isBigO (j.1 + 5) ell).const_mul_left
      (b ⟨j.1 + 4, by omega⟩)
    have hdecay := hbase.trans (reciprocal_pow_isBigO_of_le
      (p := 5 + ell) (q := j.1 + 5 + ell) (by omega))
    apply hdecay.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hc : ContDiffAt ℝ ell (fun s : ℝ ↦ (s ^ (j.1 + 5))⁻¹) t := by
        have ht0 : t ≠ 0 := ne_of_gt ht
        exact (by fun_prop : ContDiffAt ℝ ell (fun s : ℝ ↦ s ^ (j.1 + 5)) t).inv
          (pow_ne_zero _ ht0)
      exact (iteratedDeriv_const_mul (b ⟨j.1 + 4, by omega⟩) hc).symm
    · filter_upwards with t
      rfl
  have hsum := IsBigO.sum fun j (_hj : j ∈ Finset.univ) ↦ hterm j
  apply hsum.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    change (∑ j : Fin 4, iteratedDeriv ell
      (fun s : ℝ ↦ b ⟨j.1 + 4, by omega⟩ * (s ^ (j.1 + 5))⁻¹) t) =
        iteratedDeriv ell (approximationTail8 b) t
    symm
    unfold approximationTail8
    change iteratedDeriv ell (∑ j : Fin 4,
      fun s : ℝ ↦ b ⟨j.1 + 4, by omega⟩ * (s ^ (j.1 + 5))⁻¹) t = _
    rw [iteratedDeriv_sum]
    intro j _hj
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hp : ContDiffAt ℝ ell (fun s : ℝ ↦ s ^ (j.1 + 5)) t := by fun_prop
    exact contDiffAt_const.mul (hp.inv (pow_ne_zero _ ht0))
  · filter_upwards with t
    rfl

/-- Derivative bootstrap using the unfactored nonlinear remainder equation.
Only the fixed chain rules through order three enter the proof. -/
theorem nonlinear_remainder_derivative_bootstrap (F G U V D : ℝ → ℝ) (x T : ℝ)
    (hT : 0 < T) (hF : ContDiffAt ℝ 4 F x) (hG : ContDiffAt ℝ 4 G x)
    (hUlim : Tendsto U atTop (𝓝 x)) (hVlim : Tendsto V atTop (𝓝 x))
    (hFU : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 F (U t))
    (hFV : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 F (V t))
    (hGU : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 G (U t))
    (hGV : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 G (V t))
    (hUc : ContDiffOn ℝ 4 U (Ioi T)) (hVc : ContDiffOn ℝ 4 V (Ioi T))
    (hDc : ContDiffOn ℝ 4 D (Ioi T))
    (hVbound : ∀ j ≤ 3,
      (fun t ↦ iteratedDeriv j V t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hDbound : ∀ j ≤ 3,
      (fun t ↦ iteratedDeriv j D t) =O[atTop] (fun t : ℝ ↦ (t ^ (9 + j))⁻¹))
    (hode : ∀ t ∈ Ioi T, HasDerivAt (fun s ↦ U s - V s)
      (nonlinearRemainderTerm F G U V t - D t) t)
    (hzero : (fun t ↦ U t - V t) =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹)) :
    ∀ ell ≤ 4, (fun t ↦ iteratedDeriv ell (fun s ↦ U s - V s) t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let scale : ℝ → ℝ := fun t ↦ (t ^ 9)⁻¹
  have hscaleOne : scale =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
    have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hlim : Tendsto scale atTop (𝓝 0) := by
      simpa only [scale, inv_pow, zero_pow (by norm_num : (9 : ℕ) ≠ 0)] using hinv.pow 9
    exact hlim.isBigO_one ℝ
  have hderivEq : EqOn (deriv (fun s ↦ U s - V s))
      (fun t ↦ nonlinearRemainderTerm F G U V t - D t) (Ioi T) := by
    intro t ht
    exact (hode t ht).deriv
  intro ell hell
  induction ell using Nat.case_strong_induction_on with
  | hz => simpa only [iteratedDeriv_zero, scale] using hzero
  | hi m ih =>
      have hm : m ≤ 3 := by omega
      have hdiff : ∀ j ≤ m,
          (fun t ↦ iteratedDeriv j U t - iteratedDeriv j V t) =O[atTop] scale := by
        intro j hj
        apply (ih j hj (by omega)).congr'
        · filter_upwards [eventually_gt_atTop T] with t ht
          have hUt : ContDiffAt ℝ j U t :=
            ((hUc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
              (by exact_mod_cast (show j ≤ 4 by omega))
          have hVt : ContDiffAt ℝ j V t :=
            ((hVc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
              (by exact_mod_cast (show j ≤ 4 by omega))
          change iteratedDeriv j ((fun s ↦ U s) - fun s ↦ V s) t = _
          rw [iteratedDeriv_sub hUt hVt]
        · filter_upwards with t
          rfl
      have hUbound : ∀ j ≤ m,
          (fun t ↦ iteratedDeriv j U t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)) := by
        intro j hj
        have hdOne := (hdiff j hj).trans hscaleOne
        apply (hdOne.add (hVbound j (hj.trans hm))).congr'
        · filter_upwards with t
          ring
        · filter_upwards with t
          simp
      have hFcomp : ∀ r ≤ m,
          (fun t ↦ iteratedDeriv r (fun s ↦ F (U s) - F (V s)) t) =O[atTop] scale := by
        intro r hr
        exact comp_sub_comp_iteratedDeriv_isBigO_three F U V scale x T hF hUlim hVlim
          hFU hFV (hUc.of_le (by norm_num)) (hVc.of_le (by norm_num)) r (hr.trans hm)
          (fun j hj ↦ hUbound j (hj.trans hr))
          (fun j hj ↦ hVbound j ((hj.trans hr).trans hm))
          (fun j hj ↦ hdiff j (hj.trans hr))
      have hGcomp : ∀ r ≤ m,
          (fun t ↦ iteratedDeriv r (fun s ↦ G (U s) - G (V s)) t) =O[atTop] scale := by
        intro r hr
        exact comp_sub_comp_iteratedDeriv_isBigO_three G U V scale x T hG hUlim hVlim
          hGU hGV (hUc.of_le (by norm_num)) (hVc.of_le (by norm_num)) r (hr.trans hm)
          (fun j hj ↦ hUbound j (hj.trans hr))
          (fun j hj ↦ hVbound j ((hj.trans hr).trans hm))
          (fun j hj ↦ hdiff j (hj.trans hr))
      have hterm : ∀ j ∈ Finset.range (m + 1),
          (fun t ↦ (m.choose j : ℝ) * iteratedDeriv j (fun s : ℝ ↦ s⁻¹) t *
            iteratedDeriv (m - j) (fun s ↦ G (U s) - G (V s)) t) =O[atTop] scale := by
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hmul := (inv_iteratedDeriv_isBigO_one j (hjm.trans hm)).mul
          (hGcomp (m - j) (Nat.sub_le m j))
        apply hmul.const_mul_left (m.choose j : ℝ) |>.congr'
        · filter_upwards with t
          ring
        · filter_upwards with t
          simp
      have hGprod : (fun t ↦ ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * iteratedDeriv j (fun s : ℝ ↦ s⁻¹) t *
            iteratedDeriv (m - j) (fun s ↦ G (U s) - G (V s)) t) =O[atTop] scale :=
        IsBigO.sum hterm
      have hD : (fun t ↦ iteratedDeriv m D t) =O[atTop] scale := by
        exact (hDbound m hm).trans (reciprocal_pow_isBigO_of_le (by omega))
      have hexpanded := ((hFcomp m le_rfl).add hGprod).sub hD
      apply hexpanded.congr'
      · filter_upwards [eventually_gt_atTop T] with t ht
        have hiter := (hderivEq.iteratedDeriv_of_isOpen isOpen_Ioi m) ht
        rw [iteratedDeriv_succ', hiter]
        have hUt : ContDiffAt ℝ m U t :=
          ((hUc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
            (by exact_mod_cast (show m ≤ 4 by omega))
        have hVt : ContDiffAt ℝ m V t :=
          ((hVc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
            (by exact_mod_cast (show m ≤ 4 by omega))
        have hFUt : ContDiffAt ℝ m F (U t) := (hFU t ht).of_le
          (by exact_mod_cast hm)
        have hFVt : ContDiffAt ℝ m F (V t) := (hFV t ht).of_le
          (by exact_mod_cast hm)
        have hGUt : ContDiffAt ℝ m G (U t) := (hGU t ht).of_le
          (by exact_mod_cast hm)
        have hGVt : ContDiffAt ℝ m G (V t) := (hGV t ht).of_le
          (by exact_mod_cast hm)
        have hFc : ContDiffAt ℝ m (fun s ↦ F (U s) - F (V s)) t :=
          (hFUt.comp t hUt).sub (hFVt.comp t hVt)
        have hGc : ContDiffAt ℝ m (fun s ↦ G (U s) - G (V s)) t :=
          (hGUt.comp t hUt).sub (hGVt.comp t hVt)
        have hic : ContDiffAt ℝ m (fun s : ℝ ↦ s⁻¹) t := by
          have ht0 : t ≠ 0 := ne_of_gt (hT.trans ht)
          fun_prop
        have hDt : ContDiffAt ℝ m D t :=
          ((hDc t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
            (by exact_mod_cast (show m ≤ 4 by omega))
        symm
        change iteratedDeriv m ((fun s ↦ F (U s) - F (V s) +
          s⁻¹ * (G (U s) - G (V s))) - D) t = _
        rw [iteratedDeriv_sub (hFc.add (hic.mul hGc)) hDt]
        change iteratedDeriv m ((fun s ↦ F (U s) - F (V s)) +
          (fun s : ℝ ↦ s⁻¹ * (G (U s) - G (V s)))) t -
            iteratedDeriv m D t = _
        rw [iteratedDeriv_add hFc (hic.mul hGc)]
        change iteratedDeriv m (fun s ↦ F (U s) - F (V s)) t +
          iteratedDeriv m ((fun s : ℝ ↦ s⁻¹) * (fun s ↦ G (U s) - G (V s))) t -
            iteratedDeriv m D t = _
        rw [iteratedDeriv_mul hic hGc]
      · filter_upwards with t
        rfl

/-- The exact eight-term remainder and all its first four derivatives are
`O(t⁻⁹)` under the original source hypotheses. -/
theorem remainder8_all_derivatives_isBigO {I : Set ℝ} (F G Y : ℝ → ℝ)
    (yStar T0 : ℝ) (hIopen : IsOpen I) (hIconn : OrdConnected I)
    (hyStar : yStar ∈ I) (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I) (hYc1 : ContDiffOn ℝ 1 Y (Ici T0))
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t)
    (hYlim : Tendsto Y atTop (𝓝 yStar)) :
    ∀ ell ≤ 4, (fun t ↦ iteratedDeriv ell
      (remainder8 Y yStar (recursiveCoefficients8 F G yStar 8)) t) =O[atTop]
        (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  let b := recursiveCoefficients8 F G yStar 8
  let P := approximation8 yStar b
  let D := defect8 F G yStar b
  have hPevent : ∀ᶠ t in atTop, P t ∈ I := by
    apply (approximation8_tendsto yStar b).eventually
    exact hIopen.mem_nhds hyStar
  obtain ⟨Traw, hPraw⟩ := eventually_atTop.1 hPevent
  let T : ℝ := max Traw T0
  have hT0T : T0 ≤ T := le_max_right _ _
  have hTpos : 0 < T := hT0.trans_le hT0T
  have hPmap : MapsTo P (Ioi T) I := by
    intro t ht
    exact hPraw t (le_max_left Traw T0 |>.trans ht.le)
  have hYmap' : MapsTo Y (Ioi T) I := by
    intro t ht
    exact hYmap (mem_Ici.mpr (hT0T.trans ht.le))
  have hYten : ContDiffOn ℝ 10 Y (Ioi T0) :=
    asymptoticallyAutonomousSolution_contDiffOn_ten F G Y T0 hIopen hF hG hT0
      hYmap hYc1 hYode
  have hYfour : ContDiffOn ℝ 4 Y (Ioi T) :=
    (hYten.of_le (by norm_num)).mono fun t ht ↦ hT0T.trans_lt ht
  have hPfive : ContDiffOn ℝ 5 P (Ioi T) := by
    intro t ht
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 5 (fun t ↦ yStar + polynomial8 b t⁻¹) t
    have ht0 : t ≠ 0 := ne_of_gt (hTpos.trans ht)
    unfold polynomial8
    fun_prop
  have hPfour : ContDiffOn ℝ 4 P (Ioi T) := hPfive.of_le (by norm_num)
  have hDfour : ContDiffOn ℝ 4 D (Ioi T) := by
    have hPder : ContDiffOn ℝ 4 (deriv P) (Ioi T) :=
      hPfive.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have hFP : ContDiffOn ℝ 4 (fun t ↦ F (P t)) (Ioi T) := by
      change ContDiffOn ℝ 4 (F ∘ P) (Ioi T)
      exact (hF.of_le (by norm_num)).comp hPfour hPmap
    have hGP : ContDiffOn ℝ 4 (fun t ↦ G (P t)) (Ioi T) := by
      change ContDiffOn ℝ 4 (G ∘ P) (Ioi T)
      exact (hG.of_le (by norm_num)).comp hPfour hPmap
    have hinv : ContDiffOn ℝ 4 (fun t : ℝ ↦ t⁻¹) (Ioi T) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (hTpos.trans ht)
      fun_prop
    change ContDiffOn ℝ 4
      (fun t ↦ deriv P t - F (P t) - t⁻¹ * G (P t)) (Ioi T)
    exact (hPder.sub hFP).sub (hinv.mul hGP)
  have hFat : ContDiffAt ℝ 4 F yStar :=
    ((hF yStar hyStar).contDiffAt (hIopen.mem_nhds hyStar)).of_le (by norm_num)
  have hGat : ContDiffAt ℝ 4 G yStar :=
    ((hG yStar hyStar).contDiffAt (hIopen.mem_nhds hyStar)).of_le (by norm_num)
  have hFU : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 F (Y t) := by
    intro t ht
    exact ((hF (Y t) (hYmap' ht)).contDiffAt (hIopen.mem_nhds (hYmap' ht))).of_le
      (by norm_num)
  have hFV : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 F (P t) := by
    intro t ht
    exact ((hF (P t) (hPmap ht)).contDiffAt (hIopen.mem_nhds (hPmap ht))).of_le
      (by norm_num)
  have hGU : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 G (Y t) := by
    intro t ht
    exact ((hG (Y t) (hYmap' ht)).contDiffAt (hIopen.mem_nhds (hYmap' ht))).of_le
      (by norm_num)
  have hGV : ∀ t ∈ Ioi T, ContDiffAt ℝ 3 G (P t) := by
    intro t ht
    exact ((hG (P t) (hPmap ht)).contDiffAt (hIopen.mem_nhds (hPmap ht))).of_le
      (by norm_num)
  have hDbound : ∀ j ≤ 3,
      (fun t ↦ iteratedDeriv j D t) =O[atTop] (fun t : ℝ ↦ (t ^ (9 + j))⁻¹) := by
    intro j hj
    simpa only [D, b] using recursive_defect8_isBigO F G yStar hIopen hyStar hF hG
      hFzero hmu j (hj.trans (by omega))
  have hode' : ∀ t ∈ Ioi T, HasDerivAt (fun s ↦ Y s - P s)
      (nonlinearRemainderTerm F G Y P t - D t) t := by
    intro t ht
    change HasDerivAt (remainder8 Y yStar b)
      (nonlinearRemainderTerm F G Y (approximation8 yStar b) t -
        defect8 F G yStar b t) t
    exact remainder_nonlinear_equation F G Y yStar T0 b hT0 hYode t (hT0T.trans_lt ht)
  have hzero : (fun t ↦ Y t - P t) =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
    change remainder8 Y yStar b =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹)
    simpa only [b] using remainder8_isBigO F G Y yStar T0 hIopen hIconn hyStar hF hG
      hFzero hmu hT0 hYmap hYc1 hYode hYlim
  have hall := nonlinear_remainder_derivative_bootstrap F G Y P D yStar T hTpos hFat hGat
    hYlim (approximation8_tendsto yStar b) hFU hFV hGU hGV hYfour hPfour hDfour
    (approximation8_iteratedDeriv_isBigO_one yStar b) hDbound hode' hzero
  intro ell hell
  change (fun t ↦ iteratedDeriv ell (fun s ↦ Y s - P s) t) =O[atTop]
    (fun t : ℝ ↦ (t ^ 9)⁻¹)
  exact hall ell hell

/-- Repeated differentiation of `R' = A R - D` on an open half-line. -/
theorem iteratedDeriv_remainder_linear_equation (A D R : ℝ → ℝ) (T : ℝ)
    (m : ℕ) (hm : m ≤ 3) (t : ℝ) (ht : t ∈ Ioi T)
    (hA : ContDiffOn ℝ 4 A (Ioi T)) (hD : ContDiffOn ℝ 4 D (Ioi T))
    (hR : ContDiffOn ℝ 4 R (Ioi T))
    (hode : ∀ s ∈ Ioi T, HasDerivAt R (A s * R s - D s) s) :
    iteratedDeriv (m + 1) R t =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        iteratedDeriv j A t * iteratedDeriv (m - j) R t - iteratedDeriv m D t := by
  have hderivEq : Set.EqOn (deriv R) (fun s ↦ A s * R s - D s) (Ioi T) := by
    intro s hs
    exact (hode s hs).deriv
  have heq := (hderivEq.iteratedDeriv_of_isOpen isOpen_Ioi m) ht
  rw [iteratedDeriv_succ']
  rw [heq]
  have hAt : ContDiffAt ℝ m A t :=
    ((hA t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast hm.trans (by omega))
  have hRt : ContDiffAt ℝ m R t :=
    ((hR t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast hm.trans (by omega))
  have hDt : ContDiffAt ℝ m D t :=
    ((hD t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast hm.trans (by omega))
  change iteratedDeriv m ((fun x ↦ A x * R x) - D) t = _
  rw [iteratedDeriv_sub (hAt.mul hRt) hDt]
  change iteratedDeriv m (A * R) t - iteratedDeriv m D t = _
  rw [iteratedDeriv_mul hAt hRt]

/-- Abstract derivative bootstrap used after the source-specific coefficient
bounds have been established. -/
theorem linear_remainder_derivative_bootstrap (A D R : ℝ → ℝ) (T : ℝ)
    (hAcont : ContDiffOn ℝ 4 A (Ioi T)) (hDcont : ContDiffOn ℝ 4 D (Ioi T))
    (hRcont : ContDiffOn ℝ 4 R (Ioi T))
    (hode : ∀ t ∈ Ioi T, HasDerivAt R (A t * R t - D t) t)
    (hAbound : ∀ j ≤ 3,
      (fun t ↦ iteratedDeriv j A t) =O[atTop] (fun _t : ℝ ↦ (1 : ℝ)))
    (hDbound : ∀ j ≤ 3,
      (fun t ↦ iteratedDeriv j D t) =O[atTop] (fun t : ℝ ↦ (t ^ (9 + j))⁻¹))
    (hRzero : R =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹)) :
    ∀ ell ≤ 4, (fun t ↦ iteratedDeriv ell R t) =O[atTop]
      (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
  intro ell hell
  induction ell using Nat.case_strong_induction_on with
  | hz => simpa only [iteratedDeriv_zero] using hRzero
  | hi m ih =>
      have hm : m ≤ 3 := by omega
      have hterm : ∀ j ∈ Finset.range (m + 1),
          (fun t ↦ (m.choose j : ℝ) * iteratedDeriv j A t *
            iteratedDeriv (m - j) R t) =O[atTop] (fun t : ℝ ↦ (t ^ 9)⁻¹) := by
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hAj := hAbound j (hjm.trans hm)
        have hRj := ih (m - j) (Nat.sub_le m j) (by omega)
        apply ((hAj.mul hRj).const_mul_left (m.choose j : ℝ)).congr'
        · filter_upwards with t
          ring
        · filter_upwards with t
          simp
      have hsum :
          (fun t ↦ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            iteratedDeriv j A t * iteratedDeriv (m - j) R t) =O[atTop]
              (fun t : ℝ ↦ (t ^ 9)⁻¹) := IsBigO.sum hterm
      have hD : (fun t ↦ iteratedDeriv m D t) =O[atTop]
          (fun t : ℝ ↦ (t ^ 9)⁻¹) :=
        (hDbound m hm).trans (reciprocal_pow_isBigO_of_le (by omega))
      apply (hsum.sub hD).congr'
      · filter_upwards [eventually_gt_atTop T] with t ht
        exact (iteratedDeriv_remainder_linear_equation A D R T m hm t ht hAcont
          hDcont hRcont hode).symm
      · filter_upwards with t
        rfl

/-- **`lem:finite-asymptotic-ode`.**  A convergent solution of the
asymptotically autonomous scalar ODE has the source's four-term expansion,
with simultaneous remainder estimates through the fourth derivative. -/
noncomputable def finiteAsymptoticODE {I : Set ℝ} (F G Y : ℝ → ℝ) (yStar T0 : ℝ)
    (hIopen : IsOpen I) (hIconn : OrdConnected I) (hyStar : yStar ∈ I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0) (hT0 : 0 < T0)
    (hYmap : MapsTo Y (Ici T0) I) (hYc1 : ContDiffOn ℝ 1 Y (Ici T0))
    (hYode : ∀ t ∈ Ioi T0,
      HasDerivAt Y (asymptoticallyAutonomousRhs F G t (Y t)) t)
    (hYlim : Tendsto Y atTop (𝓝 yStar)) :
    FiniteAsymptoticExpansion F G Y yStar := by
  let b8 := recursiveCoefficients8 F G yStar 8
  let b4 := truncateCoefficients4 b8
  refine
    { coefficients := b4
      firstCoefficient := ?_
      derivativeRemainderBigO := ?_ }
  · change b8 (0 : Fin 8) = -G yStar / deriv F yStar
    simpa only [b8] using recursiveCoefficients8_firstCoefficient F G yStar
  · intro ell hell
    have hR8 := remainder8_all_derivatives_isBigO F G Y yStar T0 hIopen hIconn
      hyStar hF hG hFzero hmu hT0 hYmap hYc1 hYode hYlim ell hell
    have hR8' : (fun t ↦ iteratedDeriv ell (remainder8 Y yStar b8) t) =O[atTop]
        (fun t : ℝ ↦ (t ^ (5 + ell))⁻¹) := by
      have hR8b : (fun t ↦ iteratedDeriv ell (remainder8 Y yStar b8) t) =O[atTop]
          (fun t : ℝ ↦ (t ^ 9)⁻¹) := by simpa only [b8] using hR8
      exact hR8b.trans (reciprocal_pow_isBigO_of_le (by omega))
    have htail := approximationTail8_iteratedDeriv_isBigO b8 ell hell
    have hsum := hR8'.add htail
    have heq : finiteAsymptoticRemainder Y yStar b4 =
        fun t ↦ remainder8 Y yStar b8 t + approximationTail8 b8 t := by
      funext t
      have hsplit := congrFun (approximation8_eq_approximation4_add_tail yStar b8) t
      dsimp only [finiteAsymptoticRemainder, remainder8]
      dsimp only [b4] at hsplit ⊢
      linarith
    apply hsum.congr'
    · filter_upwards [eventually_gt_atTop T0] with t ht
      have hYten := asymptoticallyAutonomousSolution_contDiffOn_ten F G Y T0 hIopen
        hF hG hT0 hYmap hYc1 hYode
      have hYt : ContDiffAt ℝ ell Y t :=
        ((hYten t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
          (by exact_mod_cast (show ell ≤ 10 by omega))
      have hP8t : ContDiffAt ℝ ell (approximation8 yStar b8) t := by
        change ContDiffAt ℝ ell (fun s ↦ yStar + polynomial8 b8 s⁻¹) t
        have ht0 : t ≠ 0 := ne_of_gt (hT0.trans ht)
        unfold polynomial8
        fun_prop
      have hRt : ContDiffAt ℝ ell (remainder8 Y yStar b8) t := by
        change ContDiffAt ℝ ell (fun s ↦ Y s - approximation8 yStar b8 s) t
        exact hYt.sub hP8t
      have htailt : ContDiffAt ℝ ell (approximationTail8 b8) t := by
        unfold approximationTail8
        apply ContDiffAt.sum
        intro j _hj
        have ht0 : t ≠ 0 := ne_of_gt (hT0.trans ht)
        have hp : ContDiffAt ℝ ell (fun s : ℝ ↦ s ^ (j.1 + 5)) t := by fun_prop
        exact contDiffAt_const.mul (hp.inv (pow_ne_zero _ ht0))
      rw [heq]
      symm
      change iteratedDeriv ell (remainder8 Y yStar b8 + approximationTail8 b8) t = _
      rw [iteratedDeriv_add hRt htailt]
    · filter_upwards with t
      rfl

/-- Exact source-facing B1 wrapper.  Its only solution hypothesis is the closed-half-line
predicate with `ContDiffOn ℝ 1` and a `HasDerivWithinAt` ODE at every point of `Ici T0`. -/
noncomputable def finiteAsymptoticODE_source {I : Set ℝ} (F G Y : ℝ → ℝ)
    (yStar T0 : ℝ) (hIconn : OrdConnected I)
    (hF : ContDiffOn ℝ 9 F I) (hG : ContDiffOn ℝ 9 G I)
    (hFzero : F yStar = 0) (hmu : deriv F yStar ≠ 0)
    (hsolution : IsAsymptoticallyAutonomousSolutionSource I F G yStar T0 Y) :
    FiniteAsymptoticExpansion F G Y yStar := by
  have hinterior := hsolution.toInterior
  exact finiteAsymptoticODE F G Y yStar T0 hinterior.1 hIconn hinterior.2.1 hF hG
    hFzero hmu hinterior.2.2.1 hinterior.2.2.2.1 hinterior.2.2.2.2.1
    hinterior.2.2.2.2.2.1 hinterior.2.2.2.2.2.2

/-- `eq:forward-integral`: the stable-branch variation-of-constants identity. -/
theorem forward_integral_formula (A D R : ℝ → ℝ) {T t : ℝ} (hTt : T ≤ t)
    (hA : ContinuousOn A (Icc T t)) (hD : ContinuousOn D (Icc T t))
    (hR : ContinuousOn R (Icc T t))
    (hode : ∀ s ∈ Ioo T t, HasDerivAt R (A s * R s - D s) s) :
    R t = Real.exp (∫ x in T..t, A x) * R T -
      ∫ s in T..t, Real.exp (∫ x in s..t, A x) * D s :=
  MI11_variation_of_constants_forward A D R hTt hA hD hR hode

/-- `eq:terminal-integral`: the unstable-branch terminal representation. -/
theorem terminal_integral_formula (A D R : ℝ → ℝ) (T alpha : ℝ) (halpha : 0 < alpha)
    (hA : ContinuousOn A (Ici T)) (hD : ContinuousOn D (Ici T))
    (hR : ContinuousOn R (Ici T)) (hA_lower : ∀ t ∈ Ici T, alpha ≤ A t)
    (hode : ∀ t ∈ Ioi T, HasDerivAt R (A t * R t - D t) t)
    (hterminal : Tendsto R atTop (𝓝 0))
    (habsolute : ∀ t ∈ Ici T, IntegrableOn
      (fun s ↦ Real.exp (-(∫ x in t..s, A x)) * |D s|) (Ici t)) :
    ∀ t ∈ Ici T,
      R t = ∫ s in Ici t, Real.exp (-(∫ x in t..s, A x)) * D s :=
  MI11_variation_of_constants_terminal A D R T alpha halpha hA hD hR hA_lower hode
    hterminal habsolute

end SeriesParallel.Appendix
