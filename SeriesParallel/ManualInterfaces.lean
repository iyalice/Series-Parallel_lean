import Mathlib

/-!
# Registered classical analysis interfaces

This module is the only place where the project admits classical analysis results that are
not conveniently available from the pinned mathlib release.  Every admitted statement is
generic: none mentions an object specific to the series-parallel appendix.
-/

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Interval Topology

namespace SeriesParallel.ManualInterfaces

/-! ## MI01: global ODE existence -/

/-- **MI01.** Global Peano existence on a compact time interval under linear growth. -/
axiom MI01_global_peano_on_compact_interval
    (field : ℝ × ℝ → ℝ) {t₀ T y₀ A B : ℝ}
    (ht : t₀ < T)
    (hcontinuous : ContinuousOn field (Icc t₀ T ×ˢ univ))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ t ∈ Icc t₀ T, ∀ y : ℝ, |field (t, y)| ≤ A + B * |y|) :
    ∃ solution : ℝ → ℝ,
      solution t₀ = y₀ ∧
      ContinuousOn solution (Icc t₀ T) ∧
      ∀ t ∈ Ioo t₀ T, HasDerivAt solution (field (t, solution t)) t

/-! ## MI06: one-dimensional calculus core -/

/-- **MI06a.** Chain rule, exposed as a stable scalar wrapper. -/
theorem MI06_chain_rule {f g : ℝ → ℝ} {x f' g' : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' (f x)) : HasDerivAt (g ∘ f) (g' * f') x := by
  simpa only [Function.comp_apply] using hg.comp x hf

/-- **MI06b.** Product rule. -/
theorem MI06_product_rule {f g : ℝ → ℝ} {x f' g' : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y ↦ f y * g y) (f' * g x + f x * g') x :=
  hf.mul hg

/-- **MI06c.** Quotient rule with its nonzero-denominator hypothesis. -/
theorem MI06_quotient_rule {f g : ℝ → ℝ} {x f' g' : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (hg0 : g x ≠ 0) :
    HasDerivAt (fun y ↦ f y / g y) ((f' * g x - f x * g') / g x ^ 2) x :=
  hf.fun_div hg hg0

/-- **MI06d.** Fundamental theorem of calculus for a continuous scalar integrand. -/
theorem MI06_fundamental_theorem_of_calculus (f : ℝ → ℝ) (a : ℝ)
    (hcontinuous : Continuous f) (x : ℝ) :
    HasDerivAt (fun y ↦ ∫ t in a..y, f t) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (hcontinuous.intervalIntegrable _ _)
    hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter hcontinuous.continuousAt

/-- **MI06e.** A nonpositive derivative implies antitonicity on a compact interval. -/
theorem MI06_antitoneOn_of_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, ∃ f', HasDerivAt f f' x ∧ f' ≤ 0) :
    AntitoneOn f (Icc a b) := by
  have _hab : a ≤ b := hab
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hcontinuous ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x hx).choose_spec.1.differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨f', hf', hf'le⟩ := hderiv x hx
    rwa [hf'.deriv]

/-- **MI06f.** A nonnegative derivative implies monotonicity on a compact interval. -/
theorem MI06_monotoneOn_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, ∃ f', HasDerivAt f f' x ∧ 0 ≤ f') :
    MonotoneOn f (Icc a b) := by
  have _hab : a ≤ b := hab
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcontinuous ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x hx).choose_spec.1.differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨f', hf', hf'nonneg⟩ := hderiv x hx
    rwa [hf'.deriv]

/-- **MI06g.** The derivative vanishes at an interior local extremum. -/
theorem MI06_deriv_eq_zero_at_local_extremum {f : ℝ → ℝ} {x f' : ℝ}
    (hderiv : HasDerivAt f f' x) (hextremum : IsLocalMin f x ∨ IsLocalMax f x) : f' = 0 :=
  hextremum.elim (fun h ↦ h.hasDerivAt_eq_zero hderiv) (fun h ↦ h.hasDerivAt_eq_zero hderiv)

/-- **MI06h.** The scalar mean-value theorem with explicit endpoint regularity. -/
theorem MI06_mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcontinuous : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope f hab hcontinuous hdiff
  refine ⟨c, hc, ?_⟩
  rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]

/-- **MI06i.** Integral mean-value identity along the segment from `x` to `y`. -/
theorem MI06_integral_mean_value_formula (F : ℝ → ℝ) (x y : ℝ)
    (hcontinuous : ContinuousOn (deriv F) (uIcc x y))
    (hdiff : ∀ z ∈ uIcc x y, HasDerivAt F (deriv F z) z) :
    F y - F x = (y - x) * ∫ θ in (0 : ℝ)..1, deriv F (x + θ * (y - x)) := by
  have hparam : (fun θ : ℝ ↦ deriv F (x + θ * (y - x))) =
      fun θ : ℝ ↦ deriv F ((y - x) * θ + x) := by
    funext θ
    congr 1
    ring
  rw [hparam]
  rw [intervalIntegral.mul_integral_comp_mul_add]
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff
      (hcontinuous.intervalIntegrable)).symm

/-- **MI06k.** Exponential decay dominates each fixed reciprocal polynomial. -/
theorem MI06_exponential_decay_isBigO_reciprocal_pow (α : ℝ) (N : ℕ) (hα : 0 < α) :
    (fun t : ℝ ↦ Real.exp (-α * t)) =O[atTop] fun t : ℝ ↦ (t ^ N)⁻¹ := by
  refine ((isLittleO_exp_neg_mul_rpow_atTop hα (-(N : ℝ))).isBigO).congr' .rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht, Real.rpow_natCast]

/-! ## MI08: one-dimensional inverse functions -/

/-- **MI08a.** Inverse function on a compact interval, including the reciprocal derivative. -/
theorem MI08_compact_interval_inverse (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcontinuous : ContinuousOn f (Icc a b)) (hstrict : StrictMonoOn f (Icc a b))
    (hsmooth : ContDiffOn ℝ 1 f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    ∃ inverse : ℝ → ℝ, ContinuousOn inverse (Icc (f a) (f b)) ∧
      MapsTo inverse (Icc (f a) (f b)) (Icc a b) ∧
      (∀ x ∈ Icc a b, inverse (f x) = x) ∧
      (∀ y ∈ Icc (f a) (f b), f (inverse y) = y) ∧
      ContDiffOn ℝ 1 inverse (Ioo (f a) (f b)) ∧
      ∀ y ∈ Ioo (f a) (f b),
        HasDerivAt inverse (deriv f (inverse y))⁻¹ y := by
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hfab : f a < f b := hstrict ha_mem hb_mem hab
  have himage : f '' Icc a b = Icc (f a) (f b) :=
    hcontinuous.image_Icc_of_monotoneOn hab.le hstrict.monotoneOn
  let e : Icc a b ≃o Icc (f a) (f b) :=
    (hstrict.orderIso f (Icc a b)).trans (OrderIso.setCongr _ _ himage)
  let inverse : ℝ → ℝ := fun y ↦ (e.symm (projIcc (f a) (f b) hfab.le y) : ℝ)
  have hinverse_continuous : Continuous inverse := by
    exact continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hleft : ∀ x ∈ Icc a b, inverse (f x) = x := by
    intro x hx
    change (e.symm (projIcc (f a) (f b) hfab.le (f x)) : ℝ) = x
    have hfx_mem : f x ∈ Icc (f a) (f b) := himage ▸ ⟨x, hx, rfl⟩
    rw [show projIcc (f a) (f b) hfab.le (f x) = ⟨f x, hfx_mem⟩ from
      projIcc_of_mem hfab.le hfx_mem]
    have he_apply : e ⟨x, hx⟩ = ⟨f x, hfx_mem⟩ := by
      apply Subtype.ext
      rfl
    rw [← he_apply, e.symm_apply_apply]
  have hright : ∀ y ∈ Icc (f a) (f b), f (inverse y) = y := by
    intro y hy
    change f (e.symm (projIcc (f a) (f b) hfab.le y)) = y
    rw [projIcc_of_mem hfab.le]
    have he_symm := e.apply_symm_apply ⟨y, hy⟩
    exact congrArg Subtype.val he_symm
  have hinverse_mem : ∀ y, inverse y ∈ Icc a b := fun y ↦ (e.symm _).property
  have hinverse_Ioo : ∀ y ∈ Ioo (f a) (f b), inverse y ∈ Ioo a b := by
    intro y hy
    have hycc : y ∈ Icc (f a) (f b) := ⟨hy.1.le, hy.2.le⟩
    have hfy : f (inverse y) = y := hright y hycc
    have hxy := hinverse_mem y
    constructor
    · exact lt_of_not_ge fun hxa ↦ by
        have hxeq : inverse y = a := le_antisymm hxa hxy.1
        rw [hxeq] at hfy
        exact hy.1.ne hfy
    · exact lt_of_not_ge fun hbx ↦ by
        have hxeq : inverse y = b := le_antisymm hxy.2 hbx
        rw [hxeq] at hfy
        exact hy.2.ne hfy.symm
  have hinverse_deriv : ∀ y ∈ Ioo (f a) (f b),
      HasDerivAt inverse (deriv f (inverse y))⁻¹ y := by
    intro y hy
    have hxy := hinverse_Ioo y hy
    have hfderiv : HasDerivAt f (deriv f (inverse y)) (inverse y) :=
      ((hsmooth.contDiffAt (Ioo_mem_nhds hxy.1 hxy.2)).differentiableAt
        (by norm_num)).hasDerivAt
    apply hfderiv.of_local_left_inverse hinverse_continuous.continuousAt (hderiv _ hxy).ne'
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact hright z ⟨hz.1.le, hz.2.le⟩
  refine ⟨inverse, hinverse_continuous.continuousOn, (fun y _ ↦ hinverse_mem y), hleft, hright, ?_,
    hinverse_deriv⟩
  rw [isOpen_Ioo.contDiffOn_iff]
  intro y hy
  have hxy := hinverse_Ioo y hy
  have hfcd : ContDiffAt ℝ 1 f (inverse y) := hsmooth.contDiffAt (Ioo_mem_nhds hxy.1 hxy.2)
  have hfderiv : HasDerivAt f (deriv f (inverse y)) (inverse y) :=
    (hfcd.differentiableAt (by norm_num)).hasDerivAt
  have hne : deriv f (inverse y) ≠ 0 := (hderiv _ hxy).ne'
  let d : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hne)
  have hfd : HasFDerivAt f (d : ℝ →L[ℝ] ℝ) (inverse y) := hfderiv.hasFDerivAt_equiv hne
  have hlocal := hfcd.to_localInverse hfd (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hleft_eventual : ∀ᶠ x in 𝓝 (inverse y), inverse (f x) = x := by
    filter_upwards [Ioo_mem_nhds hxy.1 hxy.2] with x hx
    exact hleft x ⟨hx.1.le, hx.2.le⟩
  have hlocal_inverse : ContDiffAt ℝ 1 inverse (f (inverse y)) :=
    hlocal.congr_of_eventuallyEq
      ((hfcd.hasStrictFDerivAt' hfd (by norm_num)).localInverse_unique hleft_eventual)
  simpa [hright y ⟨hy.1.le, hy.2.le⟩] using hlocal_inverse

/-- **MI08b.** A smooth increasing map `(a,b) → ℝ` with infinite endpoint limits has a
global smooth inverse. -/
theorem MI08_open_interval_global_inverse (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hsmooth : ContDiffOn ℝ ∞ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 < deriv f x)
    (hleft : Tendsto f (𝓝[>] a) atBot) (hright : Tendsto f (𝓝[<] b) atTop) :
    ∃ inverse : ℝ → ℝ, MapsTo inverse univ (Ioo a b) ∧
      (∀ x ∈ Ioo a b, inverse (f x) = x) ∧ (∀ y, f (inverse y) = y) ∧
      ContDiff ℝ ∞ inverse ∧ ∀ y, HasDerivAt inverse (deriv f (inverse y))⁻¹ y := by
  have hstrict : StrictMonoOn f (Ioo a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hsmooth.continuousOn ?_
    simpa using hderiv
  let g : Ioo a b → ℝ := fun x ↦ f x
  have hgstrict : StrictMono g := strictMono_restrict.mpr hstrict
  have hgsurj : Function.Surjective g := by
    intro y
    have hleft_y : ∀ᶠ x in 𝓝[>] a, f x < y := hleft.eventually (eventually_lt_atBot y)
    have hright_y : ∀ᶠ x in 𝓝[<] b, y < f x := hright.eventually (eventually_gt_atTop y)
    have hleft_b : ∀ᶠ x in 𝓝[>] a, x < b :=
      (show ∀ᶠ x in 𝓝 a, x < b from Iio_mem_nhds hab).filter_mono nhdsWithin_le_nhds
    have hright_a : ∀ᶠ x in 𝓝[<] b, a < x :=
      (show ∀ᶠ x in 𝓝 b, a < x from Ioi_mem_nhds hab).filter_mono nhdsWithin_le_nhds
    obtain ⟨x, hxa, hxb, hfx⟩ :=
      (eventually_mem_nhdsWithin.and (hleft_b.and hleft_y)).exists
    obtain ⟨z, hzb, hza, hfz⟩ :=
      (eventually_mem_nhdsWithin.and (hright_a.and hright_y)).exists
    have hxmem : x ∈ Ioo a b := ⟨hxa, hxb⟩
    have hzmem : z ∈ Ioo a b := ⟨hza, hzb⟩
    have hxz : x < z := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hzx | rfl
      · have := hstrict hzmem hxmem hzx
        linarith
      · linarith
    have hsegment : Icc x z ⊆ Ioo a b := fun w hw ↦
      ⟨hxa.trans_le hw.1, hw.2.trans_lt hzb⟩
    obtain ⟨w, hw, hfw⟩ :=
      (intermediate_value_Icc hxz.le (hsmooth.continuousOn.mono hsegment)) ⟨hfx.le, hfz.le⟩
    exact ⟨⟨w, hsegment hw⟩, hfw⟩
  let e : Ioo a b ≃o ℝ := StrictMono.orderIsoOfSurjective g hgstrict hgsurj
  let inverse : ℝ → ℝ := fun y ↦ (e.symm y : ℝ)
  have hinverse_continuous : Continuous inverse :=
    continuous_subtype_val.comp e.symm.continuous
  have hinverse_mem : ∀ y, inverse y ∈ Ioo a b := fun y ↦ (e.symm y).property
  have hinverse_left : ∀ x ∈ Ioo a b, inverse (f x) = x := by
    intro x hx
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  have hinverse_right : ∀ y, f (inverse y) = y := by
    intro y
    exact e.apply_symm_apply y
  have hinverse_deriv : ∀ y, HasDerivAt inverse (deriv f (inverse y))⁻¹ y := by
    intro y
    have hxy := hinverse_mem y
    have hfderiv : HasDerivAt f (deriv f (inverse y)) (inverse y) :=
      ((hsmooth.contDiffAt (Ioo_mem_nhds hxy.1 hxy.2)).differentiableAt
        (by simp)).hasDerivAt
    apply hfderiv.of_local_left_inverse hinverse_continuous.continuousAt (hderiv _ hxy).ne'
    exact Filter.Eventually.of_forall hinverse_right
  refine ⟨inverse, (fun y _ ↦ hinverse_mem y), hinverse_left, hinverse_right, ?_,
    hinverse_deriv⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  have hxy := hinverse_mem y
  have hfcd : ContDiffAt ℝ ∞ f (inverse y) := hsmooth.contDiffAt (Ioo_mem_nhds hxy.1 hxy.2)
  have hfderiv : HasDerivAt f (deriv f (inverse y)) (inverse y) :=
    (hfcd.differentiableAt (by simp)).hasDerivAt
  have hne : deriv f (inverse y) ≠ 0 := (hderiv _ hxy).ne'
  let d : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hne)
  have hfd : HasFDerivAt f (d : ℝ →L[ℝ] ℝ) (inverse y) := hfderiv.hasFDerivAt_equiv hne
  have hlocal := hfcd.to_localInverse hfd (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hleft_eventual : ∀ᶠ x in 𝓝 (inverse y), inverse (f x) = x := by
    filter_upwards [Ioo_mem_nhds hxy.1 hxy.2] with x hx
    exact hinverse_left x hx
  have hlocal_inverse : ContDiffAt ℝ ∞ inverse (f (inverse y)) :=
    hlocal.congr_of_eventuallyEq
      ((hfcd.hasStrictFDerivAt' hfd (by simp)).localInverse_unique hleft_eventual)
  simpa [hinverse_right y] using hlocal_inverse

/-- **MI08c.** One-sided smooth inverse from `[0,1)` onto `[0,∞)`. -/
theorem MI08_half_open_global_inverse (f : ℝ → ℝ)
    (hzero : f 0 = 0) (hcontinuous : ContinuousOn f (Ico 0 1))
    (hsmooth : ContDiffOn ℝ ∞ f (Ico 0 1))
    (hderivZero : 0 < derivWithin f (Ici 0) 0)
    (hderiv : ∀ x ∈ Ioo 0 1, 0 < deriv f x)
    (hinfty : Tendsto f (𝓝[<] 1) atTop) :
    ∃ inverse : ℝ → ℝ, MapsTo inverse (Ici 0) (Ico 0 1) ∧ inverse 0 = 0 ∧
      (∀ x ∈ Ico 0 1, inverse (f x) = x) ∧
      (∀ y ∈ Ici (0 : ℝ), f (inverse y) = y) ∧
      ContDiffOn ℝ ∞ inverse (Ici 0) ∧
      (∀ y ∈ Ioi (0 : ℝ), HasDerivAt inverse (deriv f (inverse y))⁻¹ y) ∧
      HasDerivWithinAt inverse (derivWithin f (Ici 0) 0)⁻¹ (Ici 0) 0 := by
  have hstrict : StrictMonoOn f (Ico 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) hcontinuous ?_
    simpa using hderiv
  have hf_nonneg : ∀ x ∈ Ico (0 : ℝ) 1, 0 ≤ f x := by
    intro x hx
    simpa [hzero] using hstrict.monotoneOn (left_mem_Ico.mpr zero_lt_one) hx hx.1
  let g : Ico (0 : ℝ) 1 → Ici (0 : ℝ) := fun x ↦ ⟨f x, hf_nonneg x x.property⟩
  have hgstrict : StrictMono g := by
    intro x y hxy
    exact hstrict x.property y.property hxy
  have hgsurj : Function.Surjective g := by
    intro y
    by_cases hy0 : (y : ℝ) = 0
    · refine ⟨⟨0, left_mem_Ico.mpr zero_lt_one⟩, ?_⟩
      apply Subtype.ext
      simpa [g, hzero] using hy0.symm
    · have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property (Ne.symm hy0)
      have hright_y : ∀ᶠ x in 𝓝[<] (1 : ℝ), (y : ℝ) < f x :=
        hinfty.eventually (eventually_gt_atTop (y : ℝ))
      have hright_pos : ∀ᶠ x in 𝓝[<] (1 : ℝ), 0 < x :=
        (show ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x from Ioi_mem_nhds zero_lt_one).filter_mono
          nhdsWithin_le_nhds
      obtain ⟨z, hz1, hz0, hyz⟩ :=
        (eventually_mem_nhdsWithin.and (hright_pos.and hright_y)).exists
      have hsegment : Icc (0 : ℝ) z ⊆ Ico 0 1 := fun w hw ↦
        ⟨hw.1, hw.2.trans_lt hz1⟩
      obtain ⟨w, hw, hfw⟩ :=
        (intermediate_value_Icc hz0.le (hcontinuous.mono hsegment))
          ⟨by rw [hzero]; exact hypos.le, hyz.le⟩
      refine ⟨⟨w, hsegment hw⟩, ?_⟩
      apply Subtype.ext
      exact hfw
  let e : Ico (0 : ℝ) 1 ≃o Ici (0 : ℝ) :=
    StrictMono.orderIsoOfSurjective g hgstrict hgsurj
  let inverse : ℝ → ℝ := fun y ↦ (e.symm (projIci 0 y) : ℝ)
  have hprojIci : Continuous (projIci (0 : ℝ)) :=
    Continuous.subtype_mk (continuous_const.max continuous_id) _
  have hinverse_continuous : Continuous inverse :=
    continuous_subtype_val.comp (e.symm.continuous.comp hprojIci)
  have hinverse_mem_all : ∀ y, inverse y ∈ Ico (0 : ℝ) 1 := fun y ↦ (e.symm _).property
  have hinverse_maps : MapsTo inverse (Ici (0 : ℝ)) (Ico 0 1) :=
    fun y _ ↦ hinverse_mem_all y
  have hinverse_left : ∀ x ∈ Ico (0 : ℝ) 1, inverse (f x) = x := by
    intro x hx
    have hfx : f x ∈ Ici (0 : ℝ) := hf_nonneg x hx
    change (e.symm (projIci 0 (f x)) : ℝ) = x
    rw [show projIci 0 (f x) = ⟨f x, hfx⟩ from projIci_of_mem hfx]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  have hinverse_right : ∀ y ∈ Ici (0 : ℝ), f (inverse y) = y := by
    intro y hy
    change f (e.symm (projIci 0 y)) = y
    rw [show projIci 0 y = ⟨y, hy⟩ from projIci_of_mem hy]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have hinverse_zero : inverse 0 = 0 := by
    simpa [hzero] using hinverse_left 0 (left_mem_Ico.mpr zero_lt_one)
  let D : ℝ → ℝ := derivWithin f (Ico 0 1)
  have hsets_zero : Ico (0 : ℝ) 1 =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
    filter_upwards [Iio_mem_nhds zero_lt_one] with x hx
    apply propext
    change (0 ≤ x ∧ x < 1) ↔ 0 ≤ x
    exact and_iff_left hx
  have hD_zero : D 0 = derivWithin f (Ici 0) 0 :=
    derivWithin_congr_set hsets_zero
  have hD_pos : ∀ x ∈ Ico (0 : ℝ) 1, 0 < D x := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hxpos
    · simpa [hD_zero] using hderivZero
    · have hnhds : Ico (0 : ℝ) 1 ∈ 𝓝 x := Ico_mem_nhds hxpos hx.2
      simpa [D, derivWithin_of_mem_nhds hnhds] using hderiv x ⟨hxpos, hx.2⟩
  have hfD : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (D x) (Ico 0 1) x := by
    intro x hx
    exact (hsmooth.differentiableOn (by simp) x hx).hasDerivWithinAt
  have hinverse_derivWithin : ∀ y ∈ Ici (0 : ℝ),
      HasDerivWithinAt inverse (D (inverse y))⁻¹ (Ici 0) y := by
    intro y hy
    have hxy := hinverse_maps hy
    let d : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (hD_pos _ hxy).ne')
    have hfd : HasFDerivWithinAt f (d : ℝ →L[ℝ] ℝ) (Ico 0 1) (inverse y) := by
      apply hasFDerivWithinAt_iff_hasDerivWithinAt.mpr
      simpa [d] using hfD (inverse y) hxy
    have htend : Tendsto inverse (𝓝[Ici 0] y) (𝓝[Ico 0 1] (inverse y)) :=
      (hinverse_continuous.continuousOn y hy).tendsto_nhdsWithin hinverse_maps
    have hright_eventual : ∀ᶠ z in 𝓝[Ici 0] y, f (inverse z) = z :=
      eventually_mem_nhdsWithin.mono hinverse_right
    have hifd := hfd.of_local_left_inverse htend hy hright_eventual
    simpa [d] using hifd.hasDerivWithinAt
  have hinverse_diff : DifferentiableOn ℝ inverse (Ici (0 : ℝ)) :=
    fun y hy ↦ (hinverse_derivWithin y hy).differentiableWithinAt
  have hD_smooth : ContDiffOn ℝ ∞ D (Ico (0 : ℝ) 1) :=
    ((contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ico 0 1)).mp hsmooth).2
  have hinverse_smooth : ContDiffOn ℝ ∞ inverse (Ici (0 : ℝ)) := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero => exact contDiffOn_zero.mpr hinverse_continuous.continuousOn
    | succ n ih =>
      rw [Nat.cast_succ]
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
      refine ⟨hinverse_diff, by simp, ?_⟩
      have hcomp : ContDiffOn ℝ n (D ∘ inverse) (Ici (0 : ℝ)) :=
        (hD_smooth.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).comp ih
          hinverse_maps
      have hcomp_inv : ContDiffOn ℝ n (D ∘ inverse)⁻¹ (Ici (0 : ℝ)) :=
        hcomp.inv (fun y hy ↦ (hD_pos _ (hinverse_maps hy)).ne')
      exact hcomp_inv.congr fun y hy ↦ by
        simpa [Function.comp_apply] using
          (hinverse_derivWithin y hy).derivWithin (uniqueDiffOn_Ici 0 y hy)
  have hinverse_deriv : ∀ y ∈ Ioi (0 : ℝ),
      HasDerivAt inverse (deriv f (inverse y))⁻¹ y := by
    intro y hy
    have hyci : y ∈ Ici (0 : ℝ) := show 0 ≤ y from hy.le
    have hxy := hinverse_maps hyci
    have hfy := hinverse_right y hyci
    have hxypos : 0 < inverse y := lt_of_not_ge fun h ↦ by
      have hxeq : inverse y = 0 := le_antisymm h hxy.1
      rw [hxeq, hzero] at hfy
      exact hy.ne' hfy.symm
    have hnhds_x : Ico (0 : ℝ) 1 ∈ 𝓝 (inverse y) := Ico_mem_nhds hxypos hxy.2
    have hnhds_y : Ici (0 : ℝ) ∈ 𝓝 y := Ici_mem_nhds hy
    simpa [D, derivWithin_of_mem_nhds hnhds_x] using
      (hinverse_derivWithin y hyci).hasDerivAt hnhds_y
  refine ⟨inverse, hinverse_maps, hinverse_zero, hinverse_left, hinverse_right, hinverse_smooth,
    hinverse_deriv, ?_⟩
  simpa [hinverse_zero, hD_zero] using hinverse_derivWithin 0 (self_mem_Ici : (0 : ℝ) ∈ Ici 0)

/-! ## MI09--MI10: regularity and Taylor remainders -/

/-- **MI09a.** A `C^∞` scalar vector field bootstraps a `C¹` solution to `C^∞`. -/
theorem MI09_ode_regularity_bootstrap_infty (field : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ))
    (interval : Set ℝ) (solution : ℝ → ℝ) (hopen : IsOpen domain)
    (hsmooth : ContDiffOn ℝ ∞ field domain) (hinterval : IsOpen interval)
    (hgraph : ∀ t ∈ interval, (t, solution t) ∈ domain)
    (hsolution : ∀ t ∈ interval, HasDerivAt solution (field (t, solution t)) t) :
    ContDiffOn ℝ ∞ solution interval := by
  have _hopen : IsOpen domain := hopen
  have hdiff : DifferentiableOn ℝ solution interval := fun t ht ↦
    (hsolution t ht).differentiableAt.differentiableWithinAt
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hdiff.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_deriv_of_isOpen hinterval).mpr
    refine ⟨hdiff, by simp, ?_⟩
    have hgraph_smooth : ContDiffOn ℝ n (fun t ↦ (t, solution t)) interval :=
      contDiffOn_id.prodMk ih
    have hrhs : ContDiffOn ℝ n (fun t ↦ field (t, solution t)) interval :=
      (hsmooth.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).comp
        hgraph_smooth hgraph
    exact hrhs.congr fun t ht ↦ (hsolution t ht).deriv

/-- **MI09b.** The one-sided closed-interval version of smooth ODE bootstrapping.  The
solution is continuous on the closed interval, satisfies a right derivative equation at the
left endpoint, and satisfies the ordinary ODE at every interior point. -/
theorem MI09_ode_regularity_bootstrap_one_sided (field : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ)) {a b : ℝ} (hab : a < b) (solution : ℝ → ℝ)
    (hopen : IsOpen domain) (hsmooth : ContDiffOn ℝ ∞ field domain)
    (hgraph : ∀ t ∈ Icc a b, (t, solution t) ∈ domain)
    (hcontinuous : ContinuousOn solution (Icc a b))
    (hsolutionLeft :
      HasDerivWithinAt solution (field (a, solution a)) (Ici a) a)
    (hsolution : ∀ t ∈ Ioo a b,
      HasDerivAt solution (field (t, solution t)) t) :
    ContDiffOn ℝ ∞ solution (Icc a b) := by
  have _hopen : IsOpen domain := hopen
  let rhs : ℝ → ℝ := fun t ↦ field (t, solution t)
  have hgraph_continuous : ContinuousOn (fun t ↦ (t, solution t)) (Icc a b) :=
    continuousOn_id.prodMk hcontinuous
  have hrhs_continuous : ContinuousOn rhs (Icc a b) :=
    hsmooth.continuousOn.comp hgraph_continuous hgraph
  have hdiff_interior : DifferentiableOn ℝ solution (Ioo a b) := fun t ht ↦
    (hsolution t ht).differentiableAt.differentiableWithinAt
  have hrhs_tendsto_b : Tendsto rhs (𝓝[<] b) (𝓝 (rhs b)) := by
    exact (hrhs_continuous b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT hab)
  have hderiv_tendsto_b : Tendsto (deriv solution) (𝓝[<] b) (𝓝 (rhs b)) := by
    apply hrhs_tendsto_b.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (hsolution t ht).deriv.symm
  have hsolutionRight : HasDerivWithinAt solution (rhs b) (Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hdiff_interior
      ((hcontinuous b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsLT hab) hderiv_tendsto_b
  have hderiv_all : ∀ t ∈ Icc a b, HasDerivWithinAt solution (rhs t) (Icc a b) t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hat
    · exact hsolutionLeft.mono Icc_subset_Ici_self
    · rcases ht.2.eq_or_lt with rfl | htb
      · exact hsolutionRight.mono Icc_subset_Iic_self
      · exact (hsolution t ⟨hat, htb⟩).hasDerivWithinAt
  have hdiff : DifferentiableOn ℝ solution (Icc a b) := fun t ht ↦
    (hderiv_all t ht).differentiableWithinAt
  have hud : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hcontinuous
  | succ n ih =>
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_derivWithin hud).mpr
    refine ⟨hdiff, by simp, ?_⟩
    have hgraph_smooth : ContDiffOn ℝ n (fun t ↦ (t, solution t)) (Icc a b) :=
      contDiffOn_id.prodMk ih
    have hrhs_smooth : ContDiffOn ℝ n rhs (Icc a b) :=
      (hsmooth.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).comp
        hgraph_smooth hgraph
    exact hrhs_smooth.congr fun t ht ↦
      (hderiv_all t ht).derivWithin (hud t ht)

/-- **MI09c.** A `C⁹` vector field and a `C¹` solution give the `C¹⁰` interior regularity
needed for the finite asymptotic ODE lemma. -/
theorem MI09_ode_regularity_bootstrap_nine_to_ten (field : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ)) (interval : Set ℝ) (solution : ℝ → ℝ)
    (hfieldDomain : IsOpen domain) (hinterval : IsOpen interval)
    (hsmooth : ContDiffOn ℝ 9 field domain)
    (hgraph : ∀ t ∈ interval, (t, solution t) ∈ domain)
    (hcOne : ContDiffOn ℝ 1 solution interval)
    (hsolution : ∀ t ∈ interval, HasDerivAt solution (field (t, solution t)) t) :
    ContDiffOn ℝ 10 solution interval := by
  have _hfieldDomain : IsOpen domain := hfieldDomain
  have hdiff : DifferentiableOn ℝ solution interval := hcOne.differentiableOn_one
  have hbootstrap : ∀ n : ℕ, n ≤ 9 → ContDiffOn ℝ (n + 1) solution interval := by
    intro n hn
    induction n with
    | zero => simpa using hcOne
    | succ n ih =>
      have hn_le : n ≤ 9 := le_trans (Nat.le_succ n) hn
      have ih_smooth : ContDiffOn ℝ (n + 1) solution interval := ih hn_le
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_deriv_of_isOpen hinterval).mpr
      refine ⟨hdiff, by simp, ?_⟩
      have hgraph_smooth : ContDiffOn ℝ (n + 1) (fun t ↦ (t, solution t)) interval :=
        contDiffOn_id.prodMk ih_smooth
      have hrhs : ContDiffOn ℝ (n + 1) (fun t ↦ field (t, solution t)) interval :=
        (hsmooth.of_le (by exact_mod_cast hn)).comp hgraph_smooth hgraph
      exact hrhs.congr fun t ht ↦ (hsolution t ht).deriv
  have hfinal := hbootstrap 9 le_rfl
  norm_num at hfinal ⊢
  exact hfinal

/-- **MI10.** Taylor's theorem gives simultaneous remainder estimates through the fourth
derivative when the jets through order eight vanish. -/
theorem MI10_taylor_with_derivative_remainders (H : ℝ → ℝ) (η : ℝ) (hη : 0 < η)
    (hsmooth : ContDiffOn ℝ 9 H (Ioo (-η) η))
    (hvanish : ∀ j ≤ 8, iteratedDeriv j H 0 = 0) :
    ∀ m ≤ 4, (fun x ↦ iteratedDeriv m H x) =O[𝓝 0] fun x ↦ x ^ (9 - m) := by
  intro m hm
  let s : Set ℝ := Ioo (-η) η
  have h0 : (0 : ℝ) ∈ s := by
    dsimp [s]
    constructor <;> linarith
  have hindex : (((9 - m : ℕ) : ℕ∞ω) + m) ≤ 9 := by
    norm_cast
    omega
  have hiterF : ContDiffOn ℝ (9 - m : ℕ) (iteratedFDeriv ℝ m H) s := by
    intro z hz
    have hH : ContDiffAt ℝ 9 H z := hsmooth.contDiffAt (isOpen_Ioo.mem_nhds hz)
    exact (hH.iteratedFDeriv_right hindex).contDiffWithinAt
  have hiter : ContDiffOn ℝ (9 - m : ℕ) (iteratedDeriv m H) s := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.contDiff
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm).comp_contDiffOn hiterF
  have hnhds : 𝓝[s] (0 : ℝ) = 𝓝 0 := by
    rw [← nhdsWithin_univ, nhdsWithin_eq_iff_eventuallyEq]
    filter_upwards [isOpen_Ioo.mem_nhds h0] with z hz
    apply propext
    constructor
    · intro _
      exact mem_univ z
    · intro _
      exact hz
  have hrem := (taylor_isLittleO (convex_Ioo (-η) η) h0 hiter).isBigO
  rw [hnhds] at hrem
  let n := 9 - m
  have hzero : ∀ k < n,
      iteratedDerivWithin k (iteratedDeriv m H) s 0 = 0 := by
    intro k hk
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioo h0]
    simp only [iteratedDeriv_eq_iterate]
    rw [← Function.iterate_add_apply]
    rw [← iteratedDeriv_eq_iterate]
    apply hvanish (k + m)
    dsimp [n] at hk
    omega
  let c : ℝ := ((Nat.factorial n : ℝ)⁻¹) *
    iteratedDerivWithin n (iteratedDeriv m H) s 0
  have htaylor : (fun z ↦ taylorWithinEval (iteratedDeriv m H) n s 0 z) =
      fun z ↦ c * z ^ n := by
    funext z
    rw [taylor_within_apply, Finset.sum_range_succ]
    have hzsum : ∑ k ∈ Finset.range n,
        (((Nat.factorial k : ℝ)⁻¹ * (z - 0) ^ k) •
          iteratedDerivWithin k (iteratedDeriv m H) s 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hzero k hk]
      simp
    rw [hzsum, zero_add]
    simp only [sub_zero, smul_eq_mul]
    dsimp [c]
    ring
  have hpoly : (fun z ↦ taylorWithinEval (iteratedDeriv m H) n s 0 z) =O[𝓝 0]
      fun z ↦ z ^ n := by
    rw [htaylor]
    exact (Asymptotics.isBigO_refl (fun z : ℝ ↦ z ^ n) (𝓝 0)).const_mul_left c
  have hpoly' :
      (fun z ↦ taylorWithinEval (iteratedDeriv m H) (9 - m) (Ioo (-η) η) 0 z) =O[𝓝 0]
        fun z ↦ (z - 0) ^ (9 - m) := by
    simpa [n, s] using hpoly
  have hsum := hrem.add hpoly'
  simpa using hsum.congr_left (fun z ↦ by ring)

/-! ## MI11: variation of constants -/

/-- **MI11a.** Forward variation-of-constants formula for `R' = A R - D`. -/
theorem MI11_variation_of_constants_forward (A D R : ℝ → ℝ) {T t : ℝ} (hTt : T ≤ t)
    (hA : ContinuousOn A (Icc T t)) (hD : ContinuousOn D (Icc T t))
    (hR : ContinuousOn R (Icc T t))
    (hode : ∀ s ∈ Ioo T t, HasDerivAt R (A s * R s - D s) s) :
    R t = Real.exp (∫ x in T..t, A x) * R T -
      ∫ s in T..t, Real.exp (∫ x in s..t, A x) * D s := by
  have hP : ContinuousOn (fun s ↦ ∫ x in Ioc T s, A x) (Icc T t) :=
    intervalIntegral.continuousOn_primitive (μ := volume) hA.integrableOn_Icc
  have hJ : ContinuousOn (fun s ↦ ∫ x in s..t, A x) (Icc T t) := by
    have hc : ContinuousOn (fun _ : ℝ ↦ (∫ x in T..t, A x)) (Icc T t) := continuousOn_const
    apply (hc.sub hP).congr
    intro s hs
    have hA_Ts : ContinuousOn A (uIcc T s) := by
      rw [uIcc_of_le hs.1]
      exact hA.mono (Icc_subset_Icc_right hs.2)
    have hA_st : ContinuousOn A (uIcc s t) := by
      rw [uIcc_of_le hs.2]
      exact hA.mono (Icc_subset_Icc_left hs.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      hA_Ts.intervalIntegrable hA_st.intervalIntegrable
    rw [intervalIntegral.integral_of_le hs.1] at hadd
    dsimp only [Pi.sub_apply]
    linarith
  have hE : ContinuousOn (fun s ↦ Real.exp (∫ x in s..t, A x)) (Icc T t) :=
    Real.continuous_exp.comp_continuousOn hJ
  have hK : ContinuousOn
      (fun s ↦ Real.exp (∫ x in s..t, A x) * R s) (Icc T t) := hE.mul hR
  have hG : ContinuousOn
      (fun s ↦ -(Real.exp (∫ x in s..t, A x) * D s)) (Icc T t) := (hE.mul hD).neg
  have hKderiv : ∀ s ∈ Ioo T t,
      HasDerivAt (fun u ↦ Real.exp (∫ x in u..t, A x) * R u)
        (-(Real.exp (∫ x in s..t, A x) * D s)) s := by
    intro s hs
    have hAat : ContinuousAt A s := hA.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hAst : IntervalIntegrable A volume s t := by
      have hAu : ContinuousOn A (uIcc s t) := by
        rw [uIcc_of_le hs.2.le]
        exact hA.mono (Icc_subset_Icc_left hs.1.le)
      exact hAu.intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter A (𝓝 s) volume :=
      (hA.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    have hInt : HasDerivAt (fun u ↦ ∫ x in u..t, A x) (-A s) s :=
      intervalIntegral.integral_hasDerivAt_left hAst hmeas hAat
    change HasDerivAt ((fun u ↦ Real.exp (∫ x in u..t, A x)) * R)
      (-(Real.exp (∫ x in s..t, A x) * D s)) s
    apply (hInt.exp.mul (hode s hs)).congr_deriv
    ring
  have hGint : IntervalIntegrable
      (fun s ↦ -(Real.exp (∫ x in s..t, A x) * D s)) volume T t := by
    have hGu : ContinuousOn
        (fun s ↦ -(Real.exp (∫ x in s..t, A x) * D s)) (uIcc T t) := by
      simpa [uIcc_of_le hTt] using hG
    exact hGu.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hTt hK hKderiv hGint
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [intervalIntegral.integral_same, Real.exp_zero, one_mul] at hFTC
  linarith

/-- **MI11b.** Terminal variation-of-constants formula, with positivity, terminal decay, and
absolute convergence all explicit. -/
theorem MI11_variation_of_constants_terminal (A D R : ℝ → ℝ) (T α : ℝ) (hα : 0 < α)
    (hA : ContinuousOn A (Ici T)) (hD : ContinuousOn D (Ici T))
    (hR : ContinuousOn R (Ici T)) (hA_lower : ∀ t ∈ Ici T, α ≤ A t)
    (hode : ∀ t ∈ Ioi T, HasDerivAt R (A t * R t - D t) t)
    (hterminal : Tendsto R atTop (𝓝 0))
    (habsolute : ∀ t ∈ Ici T, IntegrableOn
      (fun s ↦ Real.exp (-(∫ x in t..s, A x)) * |D s|) (Ici t)) :
    ∀ t ∈ Ici T,
      R t = ∫ s in Ici t, Real.exp (-(∫ x in t..s, A x)) * D s := by
  intro t ht
  have hA_t : ContinuousOn A (Ici t) := hA.mono (Ici_subset_Ici.mpr ht)
  have hD_t : ContinuousOn D (Ici t) := hD.mono (Ici_subset_Ici.mpr ht)
  have hR_t : ContinuousOn R (Ici t) := hR.mono (Ici_subset_Ici.mpr ht)
  have hI : ContinuousOn (fun s ↦ ∫ x in t..s, A x) (Ici t) := by
    have hPset : ContinuousOn (fun s ↦ ∫ x in Ioc t s, A x) (Ici t) := by
      intro s hs
      let b := s + 1
      have hsb : s < b := by dsimp [b]; linarith
      have hA_b : ContinuousOn A (Icc t b) := hA_t.mono Icc_subset_Ici_self
      have hPc : ContinuousOn (fun y ↦ ∫ x in Ioc t y, A x) (Icc t b) :=
        intervalIntegral.continuousOn_primitive (μ := volume) hA_b.integrableOn_Icc
      have hfilter : 𝓝[Icc t b] s = 𝓝[Ici t] s := by
        rw [nhdsWithin_eq_iff_eventuallyEq]
        filter_upwards [Iio_mem_nhds hsb] with x hxb
        apply propext
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, hxb.le⟩
      have hPc_at := hPc s ⟨hs, hsb.le⟩
      change Tendsto _ (𝓝[Icc t b] s) _ at hPc_at
      change Tendsto _ (𝓝[Ici t] s) _
      rwa [← hfilter]
    apply hPset.congr
    intro s hs
    exact intervalIntegral.integral_of_le hs
  let E : ℝ → ℝ := fun s ↦ Real.exp (-(∫ x in t..s, A x))
  let g : ℝ → ℝ := fun s ↦ E s * D s
  have hE : ContinuousOn E (Ici t) := by
    dsimp [E]
    exact Real.continuous_exp.comp_continuousOn hI.neg
  have hg : ContinuousOn g (Ici t) := hE.mul hD_t
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ici t)) :=
    hg.aestronglyMeasurable measurableSet_Ici
  have hgnorm : Integrable (fun s ↦ ‖g s‖) (volume.restrict (Ici t)) := by
    apply (habsolute t ht).congr
    filter_upwards [] with s
    dsimp [g, E]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hgint : IntegrableOn g (Ici t) := (integrable_norm_iff hgmeas).mp hgnorm
  have hfinite : ∀ S ∈ Ici t, R t = E S * R S + ∫ s in t..S, g s := by
    intro S hS
    have hK : ContinuousOn (fun s ↦ E s * R s) (Icc t S) :=
      (hE.mul hR_t).mono Icc_subset_Ici_self
    have hnegG : ContinuousOn (fun s ↦ -g s) (Icc t S) :=
      hg.neg.mono Icc_subset_Ici_self
    have hKderiv : ∀ s ∈ Ioo t S,
        HasDerivAt (fun u ↦ E u * R u) (-g s) s := by
      intro s hs
      have hAat : ContinuousAt A s := hA.continuousAt
        (Ici_mem_nhds (ht.trans_lt hs.1))
      have hAis : IntervalIntegrable A volume t s := by
        have hAu : ContinuousOn A (uIcc t s) := by
          rw [uIcc_of_le hs.1.le]
          exact hA_t.mono Icc_subset_Ici_self
        exact hAu.intervalIntegrable
      have hmeas : StronglyMeasurableAtFilter A (𝓝 s) volume :=
        (hA.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter
          isOpen_Ioi s (ht.trans_lt hs.1)
      have hInt : HasDerivAt (fun u ↦ ∫ x in t..u, A x) (A s) s :=
        intervalIntegral.integral_hasDerivAt_right hAis hmeas hAat
      change HasDerivAt ((fun u ↦ Real.exp (-(∫ x in t..u, A x))) * R) (-g s) s
      apply (hInt.neg.exp.mul (hode s (ht.trans_lt hs.1))).congr_deriv
      dsimp [g, E]
      ring
    have hnegGint : IntervalIntegrable (fun s ↦ -g s) volume t S := by
      have hGu : ContinuousOn (fun s ↦ -g s) (uIcc t S) := by
        rw [uIcc_of_le (show t ≤ S from hS)]
        exact hnegG
      exact hGu.intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show t ≤ S from hS) hK hKderiv hnegGint
    rw [intervalIntegral.integral_neg] at hFTC
    dsimp [E] at hFTC ⊢
    simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at hFTC
    linarith
  have hdecay : Tendsto (fun S ↦ E S * R S) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun S ↦ norm_nonneg _)
      (eventually_ge_atTop t |>.mono ?_) (by simpa using hterminal.norm)
    intro S hS
    have hAnneg : 0 ≤ ∫ x in t..S, A x := by
      apply intervalIntegral.integral_nonneg hS
      intro x hx
      exact hα.le.trans (hA_lower x (ht.trans hx.1))
    have hEle : E S ≤ 1 := by
      dsimp [E]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hAnneg
    have hEnonneg : 0 ≤ E S := (Real.exp_pos _).le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hEnonneg]
    exact mul_le_of_le_one_left (abs_nonneg (R S)) hEle
  have hset : Tendsto (fun S ↦ ∫ s in Ioc t S, g s) atTop
      (𝓝 (∫ s in Ici t, g s)) := by
    have hmono : Monotone (fun S : ℝ ↦ Ioc t S) := by
      intro a b hab x hx
      exact ⟨hx.1, hx.2.trans hab⟩
    have hfi : IntegrableOn g (⋃ S : ℝ, Ioc t S) := by
      rw [iUnion_Ioc_right]
      exact hgint.mono_set Ioi_subset_Ici_self
    have hlim := tendsto_setIntegral_of_monotone (fun _ ↦ measurableSet_Ioc) hmono hfi
    rw [iUnion_Ioc_right] at hlim
    simpa only [← integral_Ici_eq_integral_Ioi] using hlim
  have hint : Tendsto (fun S ↦ ∫ s in t..S, g s) atTop
      (𝓝 (∫ s in Ici t, g s)) := by
    apply hset.congr'
    filter_upwards [eventually_ge_atTop t] with S hS
    exact (intervalIntegral.integral_of_le hS).symm
  have hsum : Tendsto (fun S ↦ E S * R S + ∫ s in t..S, g s) atTop
      (𝓝 (∫ s in Ici t, g s)) := by
    simpa using hdecay.add hint
  have hevent : (fun S ↦ E S * R S + ∫ s in t..S, g s) =ᶠ[atTop]
      (fun _ ↦ R t) := by
    filter_upwards [eventually_ge_atTop t] with S hS
    exact (hfinite S hS).symm
  have hconstlim : Tendsto (fun _ : ℝ ↦ R t) atTop (𝓝 (∫ s in Ici t, g s)) :=
    hsum.congr' hevent
  have hconst : Tendsto (fun _ : ℝ ↦ R t) atTop (𝓝 (R t)) := tendsto_const_nhds
  exact tendsto_nhds_unique hconst hconstlim

/-! ## MI13: smooth cutoff -/

/-- **MI13.** A smooth cutoff equal to one on `[-1/2,0]` and zero to the left of `-1`. -/
theorem MI13_smooth_cutoff : ∃ cutoff : ℝ → ℝ, ContDiff ℝ ∞ cutoff ∧
    (∀ x ∈ Icc (-(1 / 2 : ℝ)) 0, cutoff x = 1) ∧
    (∀ x ∈ Iic (-1 : ℝ), cutoff x = 0) ∧ ∀ x, cutoff x ∈ Icc 0 1 := by
  let cutoff : ContDiffBump (-(1 / 4 : ℝ)) :=
    ⟨1 / 4, 3 / 4, by norm_num, by norm_num⟩
  refine ⟨cutoff, cutoff.contDiff, ?_, ?_, ?_⟩
  · intro x hx
    apply cutoff.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> dsimp [cutoff] <;> linarith [hx.1, hx.2]
  · intro x hx
    have hx' : x ≤ -1 := hx
    apply cutoff.zero_of_le_dist
    rw [Real.dist_eq, abs_of_nonpos]
    · norm_num
      linarith
    · norm_num
      linarith
  · intro x
    exact ⟨cutoff.nonneg, cutoff.le_one⟩

/-! ## MI07: the square of the positive part -/

/-- `s ↦ (max s 0)² / 2`. -/
noncomputable def positivePartSquare (s : ℝ) : ℝ :=
  (max s 0) ^ 2 / 2

/-- The derivative of `positivePartSquare` is the positive part. -/
theorem MI07_positive_part_square_hasDerivAt (s : ℝ) :
    HasDerivAt positivePartSquare (max s 0) s := by
  by_cases hs : s = 0
  · subst s
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [positivePartSquare, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, zero_add, smul_eq_mul, mul_zero, sub_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.eventually_nhds_iff.mpr ⟨c * 2, mul_pos hc (by norm_num), by
      intro x hx
      simpa only [Real.dist_eq, sub_zero] using hx⟩] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hmax : |max x 0| ≤ |x| := by
      by_cases hx0 : x ≤ 0
      · simp [max_eq_right hx0]
      · simp [max_eq_left (le_of_not_ge hx0)]
    calc
      |max x 0 ^ 2 / 2| = |max x 0| ^ 2 / 2 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ |x| ^ 2 / 2 := by gcongr
      _ = (|x| / 2) * |x| := by ring
      _ ≤ c * |x| := by gcongr; linarith [hx]
  · by_cases hspos : 0 < s
    · rw [max_eq_left hspos.le]
      have hpoly : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2) s s := by
        simpa using ((hasDerivAt_id s).fun_pow 2).div_const 2
      refine hpoly.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hspos] with x hx
      simp only [positivePartSquare, max_eq_left (mem_Ioi.mp hx).le]
    · have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hspos) hs
      rw [max_eq_right hsneg.le]
      refine (hasDerivAt_const s 0).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hsneg] with x hx
      simp only [positivePartSquare, max_eq_right (mem_Iio.mp hx).le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]

/-- `positivePartSquare` is continuously differentiable and has derivative `max s 0`. -/
theorem MI07_positive_part_square :
    ContDiff ℝ 1 positivePartSquare ∧ ∀ s, deriv positivePartSquare s = max s 0 := by
  have hderiv : ∀ s, deriv positivePartSquare s = max s 0 :=
    fun s ↦ (MI07_positive_part_square_hasDerivAt s).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩, hderiv⟩
  · exact fun s ↦ (MI07_positive_part_square_hasDerivAt s).differentiableAt
  · have hcontinuous : Continuous (fun s : ℝ ↦ max s 0) :=
      continuous_id.max continuous_const
    rw [show deriv positivePartSquare = fun s ↦ max s 0 by funext s; exact hderiv s]
    exact hcontinuous

end SeriesParallel.ManualInterfaces
