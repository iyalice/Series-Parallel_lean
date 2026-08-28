import SeriesParallel.Appendix.AdmissibleParameters

/-!
# The left-endpoint phase portrait

This file records the exact auxiliary quantities and algebraic differential equations from
`lem:u0-dichotomy`.  The global crossing and limiting arguments are kept separate from these
identities so that every displayed source formula has a stable, independently checked name.
-/

open Asymptotics Filter Set
open scoped Topology

namespace SeriesParallel.Appendix

/-- The source's `H(u)=lambda W(u)-u(1-u)`. -/
def endpointH (lambda : ℝ) (W : ℝ → ℝ) (u : ℝ) : ℝ :=
  lambda * W u - u * (1 - u)

/-- On a boundary solution, `H=W^2 W'`. -/
theorem endpointH_eq_sq_mul_deriv {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) {u : ℝ} (hu : u ∈ openUnitInterval) :
    endpointH lambda W u = W u ^ 2 * deriv W u := by
  have hode := (hW.2.2.2.1 u hu).2
  unfold wODEValue at hode
  unfold endpointH
  linarith

/-- A zero of `H` in the interior forces `W'=0`. -/
theorem deriv_eq_zero_of_endpointH_eq_zero {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) {u : ℝ} (hu : u ∈ openUnitInterval)
    (hzero : endpointH lambda W u = 0) :
    deriv W u = 0 := by
  have hWpos := hW.2.2.2.2.2.2 u hu
  have heq := endpointH_eq_sq_mul_deriv hW hu
  rw [hzero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero 2 hWpos.ne')

/-- Derivative of the source's phase variable `H`. -/
theorem endpointH_hasDerivAt {lambda : ℝ} {W : ℝ → ℝ} {u : ℝ}
    (hW : IsWBoundarySolution lambda W) (hu : u ∈ openUnitInterval) :
    HasDerivAt (endpointH lambda W)
      (lambda * deriv W u - (1 - 2 * u)) u := by
  have hderiv := (hW.2.2.2.1 u hu).1.hasDerivAt
  unfold endpointH
  have hpoly : HasDerivAt (fun x : ℝ ↦ x * (1 - x)) (1 - 2 * u) u := by
    have hraw := (hasDerivAt_id u).mul
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
    change HasDerivAt (fun x : ℝ ↦ x * (1 - x))
      (1 * (1 - u) + u * (0 - 1)) u at hraw
    convert hraw using 1 <;> ring
  exact (hderiv.const_mul lambda).sub hpoly

/-- `eq:A6.1`: every zero of `H` before `1/2` is crossed with negative derivative. -/
theorem endpointH_deriv_neg_at_zero {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) (1 / 2))
    (hzero : endpointH lambda W u = 0) :
    deriv (endpointH lambda W) u < 0 := by
  have huOpen : u ∈ openUnitInterval := ⟨hu.1, hu.2.trans (by norm_num)⟩
  have hWderiv := deriv_eq_zero_of_endpointH_eq_zero hW huOpen hzero
  rw [(endpointH_hasDerivAt hW huOpen).deriv, hWderiv]
  nlinarith [hu.2]

/-- A negative derivative at a zero produces a negative value immediately to its right. -/
theorem exists_right_neg_of_hasDerivAt_neg {h : ℝ → ℝ} {v b d : ℝ}
    (hvb : v < b) (hzero : h v = 0) (hderiv : HasDerivAt h d v) (hd : d < 0) :
    ∃ x ∈ Ioo v b, h x < 0 := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (h (v + t) - h v) < 0 := by
    have ht := hderiv.tendsto_slope_zero_right
    filter_upwards [ht.eventually (Iio_mem_nhds hd)] with t ht
    simpa only [smul_eq_mul] using ht
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 ((b - v) / 2) :=
    Ioc_mem_nhdsGT (half_pos (sub_pos.mpr hvb))
  obtain ⟨t, ht, htslope⟩ := (hsmall.and hslope).exists
  have htpos : 0 < t := ht.1
  refine ⟨v + t, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
  rw [hzero, sub_zero] at htslope
  rcases mul_neg_iff.mp htslope with hcase | hcase
  · exact hcase.2
  · exact (not_lt_of_ge (inv_pos.mpr htpos).le hcase.1).elim

/-- A negative derivative at a zero produces a positive value immediately to its left. -/
theorem exists_left_pos_of_hasDerivAt_neg {h : ℝ → ℝ} {a v d : ℝ}
    (hav : a < v) (hzero : h v = 0) (hderiv : HasDerivAt h d v) (hd : d < 0) :
    ∃ x ∈ Ioo a v, 0 < h x := by
  have hslope : ∀ᶠ t in 𝓝[<] (0 : ℝ),
      t⁻¹ * (h (v + t) - h v) < 0 := by
    have ht := hderiv.tendsto_slope_zero_left
    filter_upwards [ht.eventually (Iio_mem_nhds hd)] with t ht
    simpa only [smul_eq_mul] using ht
  have hsmall : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ Ico (-(v - a) / 2) 0 :=
    Ico_mem_nhdsLT (by linarith)
  obtain ⟨t, ht, htslope⟩ := (hsmall.and hslope).exists
  have htneg : t < 0 := ht.2
  refine ⟨v + t, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
  rw [hzero, sub_zero] at htslope
  rcases mul_neg_iff.mp htslope with hcase | hcase
  · exact (not_lt_of_ge (inv_neg''.mpr htneg).le hcase.1).elim
  · exact hcase.2

/-- The downward-crossing lemma required in A6.1.  A continuous differentiable real
function whose derivative is strictly negative at every interior zero has at most one
interior zero. -/
theorem downwardCrossing_zero_unique {h : ℝ → ℝ} {a b : ℝ}
    (hcont : Continuous h)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt h (deriv h x) x)
    (hneg : ∀ x ∈ Ioo a b, h x = 0 → deriv h x < 0) :
    ∀ ⦃v₁⦄, v₁ ∈ Ioo a b → h v₁ = 0 →
      ∀ ⦃v₂⦄, v₂ ∈ Ioo a b → h v₂ = 0 → v₁ = v₂ := by
  intro v₁ hv₁ hv₁zero v₂ hv₂ hv₂zero
  by_contra hne
  suffices hordered : ∀ {x y : ℝ}, x ∈ Ioo a b → h x = 0 → y ∈ Ioo a b → h y = 0 →
      x < y → False by
    rcases lt_or_gt_of_ne hne with hvorder | hvorder
    · exact hordered hv₁ hv₁zero hv₂ hv₂zero hvorder
    · exact hordered hv₂ hv₂zero hv₁ hv₁zero hvorder
  intro x y hx hxzero hy hyzero hxy
  obtain ⟨s, hs, hsneg⟩ := exists_right_neg_of_hasDerivAt_neg hxy hxzero
    (hderiv x hx) (hneg x hx hxzero)
  obtain ⟨t, ht, htpos⟩ := exists_left_pos_of_hasDerivAt_neg hs.2 hyzero
    (hderiv y hy) (hneg y hy hyzero)
  have hst : s < t := ht.1
  have hzeroExists : ∃ c ∈ Icc s t, h c = 0 := by
    have hzeroRange := intermediate_value_Icc hst.le hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (h s) (h t) from ⟨hsneg.le, htpos.le⟩)
    simpa only [mem_image] using hzeroRange
  let Z : Set ℝ := Icc s t ∩ h ⁻¹' {0}
  have hZcompact : IsCompact Z :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hcont)
  have hZnonempty : Z.Nonempty := by
    obtain ⟨c, hc, hczero⟩ := hzeroExists
    exact ⟨c, hc, hczero⟩
  obtain ⟨c, hcZ, hcleast⟩ := hZcompact.exists_isLeast hZnonempty
  have hcI : c ∈ Icc s t := hcZ.1
  have hczero : h c = 0 := hcZ.2
  have hsc : s < c := lt_of_le_of_ne hcI.1 fun hcs ↦ by
    apply hsneg.ne
    rw [hcs, hczero]
  have hct : c < t := lt_of_le_of_ne hcI.2 fun hct ↦ by
    apply htpos.ne'
    rw [← hct, hczero]
  have hnonpos : ∀ z ∈ Icc s c, h z ≤ 0 := by
    intro z hz
    by_contra hzpos
    have hzpos' : 0 < h z := lt_of_not_ge hzpos
    have hsz : s ≤ z := hz.1
    have hzeroRange := intermediate_value_Icc hsz hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (h s) (h z) from ⟨hsneg.le, hzpos'.le⟩)
    obtain ⟨q, hqI, hqzero⟩ := hzeroRange
    have hqZ : q ∈ Z := by
      refine ⟨⟨hqI.1, hqI.2.trans (hz.2.trans hct.le)⟩, ?_⟩
      change h q ∈ ({0} : Set ℝ)
      simpa only [mem_singleton_iff] using hqzero
    have hcq := hcleast hqZ
    have hqc : q < c := hqI.2.trans_lt (lt_of_le_of_ne hz.2 fun h ↦ by
      apply hzpos'.ne'
      rw [h, hczero])
    exact (not_le_of_gt hqc) hcq
  have hlocalMax : IsLocalMaxOn h (Iic c) c := by
    have hIoi : ∀ᶠ z in 𝓝[Iic c] c, z ∈ Ioi s :=
      (show ∀ᶠ z in 𝓝 c, z ∈ Ioi s from Ioi_mem_nhds hsc).filter_mono inf_le_left
    filter_upwards [hIoi, self_mem_nhdsWithin] with z hzs hzc
    rw [hczero]
    exact hnonpos z ⟨hzs.le, hzc⟩
  have htan : (-1 : ℝ) ∈ posTangentConeAt (Iic c) c := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with q hq
    change c + q * (-1) ≤ c
    change 0 < q at hq
    nlinarith
  have hcOpen : c ∈ Ioo a b :=
    ⟨hx.1.trans (hs.1.trans hsc), hct.trans (ht.2.trans hy.2)⟩
  have hnonneg : 0 ≤ deriv h c := by
    have hfermat := hlocalMax.hasFDerivWithinAt_nonpos
      ((hderiv c hcOpen).hasFDerivAt.hasFDerivWithinAt) htan
    simpa using hfermat
  exact (not_lt_of_ge hnonneg) (hneg c hcOpen hczero)

/-- The canonical extension of a boundary solution is globally continuous. -/
theorem IsWBoundarySolution.continuous {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) : Continuous W := by
  have hclamp : Continuous unitClamp := by
    unfold unitClamp
    fun_prop
  have hcomp : Continuous (W ∘ unitClamp) :=
    hW.2.1.comp_continuous hclamp unitClamp_mem_unitInterval
  have heq : W = W ∘ unitClamp := by
    funext u
    exact hW.1 u
  rwa [heq]

/-- Global continuity of the phase function, including at the clamped endpoints. -/
theorem endpointH_continuous {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) : Continuous (endpointH lambda W) := by
  unfold endpointH
  exact (hW.continuous.const_mul lambda).sub
    (continuous_id.mul (continuous_const.sub continuous_id))

/-- A6.1: `H` has at most one zero before `1/2`. -/
theorem endpointH_zero_unique_before_half {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) :
    ∀ ⦃v₁⦄, v₁ ∈ Ioo (0 : ℝ) (1 / 2) → endpointH lambda W v₁ = 0 →
      ∀ ⦃v₂⦄, v₂ ∈ Ioo (0 : ℝ) (1 / 2) → endpointH lambda W v₂ = 0 → v₁ = v₂ := by
  apply downwardCrossing_zero_unique (endpointH_continuous hW)
  · intro u hu
    have hh := endpointH_hasDerivAt hW ⟨hu.1, hu.2.trans (by norm_num)⟩
    exact hh.congr_deriv hh.deriv.symm
  · exact fun u hu ↦ endpointH_deriv_neg_at_zero hW hu

/-- Mean-value points with `H>0` occur arbitrarily close to the left endpoint. -/
theorem exists_endpointH_pos_before {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) {u : ℝ} (hu : u ∈ openUnitInterval) :
    ∃ c ∈ Ioo (0 : ℝ) u, 0 < endpointH lambda W c := by
  have hcont : ContinuousOn W (Icc 0 u) :=
    hW.2.1.mono fun x hx ↦ ⟨hx.1, hx.2.trans hu.2.le⟩
  have hdiff : DifferentiableOn ℝ W (Ioo 0 u) := by
    intro x hx
    exact (hW.2.2.2.1 x ⟨hx.1, hx.2.trans hu.2⟩).1.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope (f := W) hu.1 hcont hdiff
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hWu : 0 < W u := hW.2.2.2.2.2.2 u hu
  have hderivPos : 0 < deriv W c := by
    rw [hslope, hW0]
    exact div_pos (by linarith [hWu]) (by linarith [hu.1])
  refine ⟨c, hc, ?_⟩
  rw [endpointH_eq_sq_mul_deriv hW ⟨hc.1, hc.2.trans hu.2⟩]
  exact mul_pos (sq_pos_of_pos (hW.2.2.2.2.2.2 c ⟨hc.1, hc.2.trans hu.2⟩)) hderivPos

/-- The conclusion of A6.1: `H` is positive on a nontrivial right neighborhood of zero. -/
theorem exists_endpointH_pos_near_zero {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) :
    ∃ u0 ∈ openUnitInterval,
      ∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u := by
  have hquarter : (1 / 4 : ℝ) ∈ openUnitInterval := ⟨by norm_num, by norm_num⟩
  obtain ⟨u0, hu0, hHu0⟩ := exists_endpointH_pos_before hW hquarter
  have hu0Open : u0 ∈ openUnitInterval := ⟨hu0.1, hu0.2.trans hquarter.2⟩
  have hu0Half : u0 < (1 / 2 : ℝ) := hu0.2.trans (by norm_num)
  refine ⟨u0, hu0Open, ?_⟩
  intro u hu
  by_contra hnotpos
  have hHunonpos : endpointH lambda W u ≤ 0 := le_of_not_gt hnotpos
  have huOpen : u ∈ openUnitInterval := ⟨hu.1, hu.2.trans_lt hu0Open.2⟩
  by_cases hHu : endpointH lambda W u = 0
  · have huu0 : u < u0 := lt_of_le_of_ne hu.2 fun heu ↦ by
      apply hHu0.ne'
      rwa [← heu]
    have hHat := endpointH_hasDerivAt hW huOpen
    have hHderivNeg : lambda * deriv W u - (1 - 2 * u) < 0 := by
      rw [← hHat.deriv]
      exact endpointH_deriv_neg_at_zero hW ⟨hu.1, hu.2.trans_lt hu0Half⟩ hHu
    obtain ⟨s, hs, hHs⟩ :=
      exists_right_neg_of_hasDerivAt_neg huu0 hHu hHat hHderivNeg
    have hzeroRange := intermediate_value_Icc hs.2.le (endpointH_continuous hW).continuousOn
      (show (0 : ℝ) ∈ Icc (endpointH lambda W s) (endpointH lambda W u0) from
        ⟨hHs.le, hHu0.le⟩)
    obtain ⟨q, hqI, hqzero⟩ := hzeroRange
    have huHalf : u ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hu.1, hu.2.trans_lt hu0Half⟩
    have hqHalf : q ∈ Ioo (0 : ℝ) (1 / 2) :=
      ⟨hu.1.trans (hs.1.trans_le hqI.1), hqI.2.trans_lt hu0Half⟩
    have heq := endpointH_zero_unique_before_half hW huHalf hHu hqHalf hqzero
    exact (hs.1.trans_le hqI.1).ne heq
  · have hHuneg : endpointH lambda W u < 0 := lt_of_le_of_ne hHunonpos hHu
    obtain ⟨p, hp, hHp⟩ := exists_endpointH_pos_before hW huOpen
    have hzeroLeft := intermediate_value_Icc' hp.2.le
      (endpointH_continuous hW).continuousOn
      (show (0 : ℝ) ∈ Icc (endpointH lambda W u) (endpointH lambda W p) from
        ⟨hHuneg.le, hHp.le⟩)
    obtain ⟨q₁, hq₁I, hq₁zero⟩ := hzeroLeft
    have hzeroRight := intermediate_value_Icc hu.2
      (endpointH_continuous hW).continuousOn
      (show (0 : ℝ) ∈ Icc (endpointH lambda W u) (endpointH lambda W u0) from
        ⟨hHuneg.le, hHu0.le⟩)
    obtain ⟨q₂, hq₂I, hq₂zero⟩ := hzeroRight
    have hq₁lt : q₁ < u := lt_of_le_of_ne hq₁I.2 fun heq ↦
      hHuneg.ne (by rw [← heq]; exact hq₁zero)
    have huq₂ : u < q₂ := lt_of_le_of_ne hq₂I.1 fun heq ↦
      hHuneg.ne (by rw [heq]; exact hq₂zero)
    have hq₁Half : q₁ ∈ Ioo (0 : ℝ) (1 / 2) :=
      ⟨hp.1.trans_le hq₁I.1, hq₁lt.trans (hu.2.trans_lt hu0Half)⟩
    have hq₂Half : q₂ ∈ Ioo (0 : ℝ) (1 / 2) :=
      ⟨hu.1.trans huq₂, hq₂I.2.trans_lt hu0Half⟩
    have heq := endpointH_zero_unique_before_half hW hq₁Half hq₁zero hq₂Half hq₂zero
    linarith

/-- Positivity of `H` on `(0,u₀]` forces strict increase of `W` on `[0,u₀]`. -/
theorem strictMonoOn_of_endpointH_pos {lambda : ℝ} {W : ℝ → ℝ} {u0 : ℝ}
    (hW : IsWBoundarySolution lambda W) (hu0 : u0 ∈ openUnitInterval)
    (hHpos : ∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u) :
    StrictMonoOn W (Icc 0 u0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) u0)
  · exact hW.2.1.mono fun u hu ↦ ⟨hu.1, hu.2.trans hu0.2.le⟩
  · rw [interior_Icc]
    intro u hu
    have huOpen : u ∈ openUnitInterval := ⟨hu.1, hu.2.trans hu0.2⟩
    have heq := endpointH_eq_sq_mul_deriv hW huOpen
    have hWpos := hW.2.2.2.2.2.2 u huOpen
    have hH := hHpos u ⟨hu.1, hu.2.le⟩
    nlinarith [sq_pos_of_pos hWpos]

/-- Once local positivity of `H` is available, MI08 supplies the compact inverse used in
`eq:r-inverse`. -/
theorem localInverse_exists_of_endpointH_pos {lambda : ℝ} {W : ℝ → ℝ} {u0 : ℝ}
    (hW : IsWBoundarySolution lambda W) (hu0 : u0 ∈ openUnitInterval)
    (hHpos : ∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Icc (W 0) (W u0)) ∧
      MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0) ∧
      (∀ u ∈ Icc 0 u0, U (W u) = u) ∧
      (∀ x ∈ Icc (W 0) (W u0), W (U x) = x) ∧
      ContDiffOn ℝ 1 U (Ioo (W 0) (W u0)) ∧
      ∀ x ∈ Ioo (W 0) (W u0), HasDerivAt U (deriv W (U x))⁻¹ x := by
  have hstrict := strictMonoOn_of_endpointH_pos hW hu0 hHpos
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) u0, 0 < deriv W u := by
    intro u hu
    have huOpen : u ∈ openUnitInterval := ⟨hu.1, hu.2.trans hu0.2⟩
    have heq := endpointH_eq_sq_mul_deriv hW huOpen
    have hWpos := hW.2.2.2.2.2.2 u huOpen
    have hH := hHpos u ⟨hu.1, hu.2.le⟩
    nlinarith [sq_pos_of_pos hWpos]
  exact ManualInterfaces.MI08_compact_interval_inverse W hu0.1
    (hW.2.1.mono fun u hu ↦ ⟨hu.1, hu.2.trans hu0.2.le⟩)
    hstrict (hW.2.2.1.mono fun u hu ↦ ⟨hu.1, hu.2.trans hu0.2⟩) hderiv

/-- An interior point in the range of the compact inverse is sent to an interior point
of its domain.  This is the endpoint bookkeeping needed before the `W` equation may be
evaluated at `U x`. -/
theorem localInverse_maps_interior {W U : ℝ → ℝ} {u0 x : ℝ}
    (hu0 : 0 < u0) (hW0 : W 0 = 0)
    (hmap : MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0))
    (hright : ∀ y ∈ Icc (W 0) (W u0), W (U y) = y)
    (hx : x ∈ Ioo (W 0) (W u0)) :
    U x ∈ Ioo 0 u0 := by
  have hUx := hmap ⟨hx.1.le, hx.2.le⟩
  constructor
  · exact lt_of_le_of_ne hUx.1 fun h ↦ by
      have hUx0 : U x = 0 := h.symm
      have hrightx := hright x ⟨hx.1.le, hx.2.le⟩
      rw [hUx0] at hrightx
      exact hx.1.ne hrightx
  · exact lt_of_le_of_ne hUx.2 fun h ↦ by
      have hUxu0 : U x = u0 := h
      have hrightx := hright x ⟨hx.1.le, hx.2.le⟩
      rw [hUxu0] at hrightx
      exact hx.2.ne' hrightx

/-- `eq:A6.2`: the reciprocal derivative supplied by MI08, rewritten using the original
`W` equation.  The denominator is recorded as positive at the same time. -/
theorem localInverse_hasDerivAt_equation {lambda : ℝ} {W U : ℝ → ℝ} {u0 x : ℝ}
    (hW : IsWBoundarySolution lambda W) (hu0 : u0 ∈ openUnitInterval)
    (hHpos : ∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u)
    (hmap : MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0))
    (hright : ∀ y ∈ Icc (W 0) (W u0), W (U y) = y)
    (hUraw : HasDerivAt U (deriv W (U x))⁻¹ x)
    (hx : x ∈ Ioo (W 0) (W u0)) :
    HasDerivAt U (x ^ 2 / (lambda * x - U x + U x ^ 2)) x ∧
      0 < lambda * x - U x + U x ^ 2 := by
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hUx := localInverse_maps_interior hu0.1 hW0 hmap hright hx
  have hUxOpen : U x ∈ openUnitInterval := ⟨hUx.1, hUx.2.trans hu0.2⟩
  have hrightx := hright x ⟨hx.1.le, hx.2.le⟩
  have hWderivPos : 0 < deriv W (U x) := by
    have heq := endpointH_eq_sq_mul_deriv hW hUxOpen
    have hWpos := hW.2.2.2.2.2.2 (U x) hUxOpen
    have hH := hHpos (U x) ⟨hUx.1, hUx.2.le⟩
    nlinarith [sq_pos_of_pos hWpos]
  have hode := (hW.2.2.2.1 (U x) hUxOpen).2
  unfold wODEValue at hode
  have hdenom : lambda * x - U x + U x ^ 2 = x ^ 2 * deriv W (U x) := by
    rw [hrightx] at hode
    linarith
  have hxpos : 0 < x := by rw [← hW0]; exact hx.1
  have hdenomPos : 0 < lambda * x - U x + U x ^ 2 := by
    rw [hdenom]
    positivity
  constructor
  · apply hUraw.congr_deriv
    rw [hdenom]
    field_simp [hWderivPos.ne', hxpos.ne']
  · exact hdenomPos

/-- The inverse `U` divided by its argument, `r(x)=U(x)/x`. -/
noncomputable def inverseRatio (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  U x / x

/-- The denominator in the inverse/ratio equations. -/
noncomputable def ratioDenominator (lambda : ℝ) (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  lambda - r x + x * r x ^ 2

/-- Factoring the inverse-equation denominator by `x`. -/
theorem inverseDenominator_factor (lambda : ℝ) (U : ℝ → ℝ) {x : ℝ}
    (hx : x ≠ 0) :
    lambda * x - U x + U x ^ 2 =
      x * ratioDenominator lambda (inverseRatio U) x := by
  unfold ratioDenominator inverseRatio
  field_simp [hx]

/-- First identity in `eq:r-inverse`, after extracting a factor of `x`. -/
theorem inverseDerivativeValue_eq_ratioValue (lambda : ℝ) (U : ℝ → ℝ) {x : ℝ}
    (hx : x ≠ 0)
    (hdenom : lambda * x - U x + U x ^ 2 ≠ 0) :
    x ^ 2 / (lambda * x - U x + U x ^ 2) =
      x / ratioDenominator lambda (inverseRatio U) x := by
  have hfactor := inverseDenominator_factor lambda U hx
  have hratioDenom : ratioDenominator lambda (inverseRatio U) x ≠ 0 := by
    intro hzero
    apply hdenom
    rw [hfactor, hzero, mul_zero]
  rw [hfactor]
  field_simp [hx, hratioDenom]

/-- Quotient-rule algebra behind the second identity in `eq:r-inverse`. -/
theorem ratioDerivativeValue_identity (lambda : ℝ) (U : ℝ → ℝ) {x Uprime : ℝ}
    (hx : x ≠ 0)
    (hUprime : Uprime = x / ratioDenominator lambda (inverseRatio U) x) :
    x * ((Uprime * x - U x) / x ^ 2) =
      x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x := by
  rw [hUprime]
  unfold inverseRatio
  field_simp [hx]

/-- The two derivative identities displayed in `eq:r-inverse`. -/
theorem inverseRatio_hasDerivAt {lambda : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0)
    (hdenom : ratioDenominator lambda (inverseRatio U) x ≠ 0)
    (hU : HasDerivAt U
      (x / ratioDenominator lambda (inverseRatio U) x) x) :
    HasDerivAt (inverseRatio U)
      ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) x ∧
    x * ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) =
      x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x := by
  have hid : HasDerivAt (fun z : ℝ ↦ z) 1 x := hasDerivAt_id x
  have hquot := ManualInterfaces.MI06_quotient_rule hU hid hx
  have hderivative :
      ((x / ratioDenominator lambda (inverseRatio U) x) * x - U x * 1) / x ^ 2 =
        (x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x := by
    unfold inverseRatio
    field_simp [hx]
  constructor
  · change HasDerivAt (fun y : ℝ ↦ U y / y)
      ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) x
    exact hquot.congr_deriv hderivative
  · field_simp [hx]

/-- The actual inverse and ratio equations obtained from local positivity of `H`; unlike the
preceding algebraic lemmas, this result is tied to the boundary solution and MI08 inverse. -/
theorem localInverse_ratio_equations {lambda : ℝ} {W : ℝ → ℝ} {u0 : ℝ}
    (hW : IsWBoundarySolution lambda W) (hu0 : u0 ∈ openUnitInterval)
    (hHpos : ∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Icc (W 0) (W u0)) ∧
      MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0) ∧
      (∀ u ∈ Icc 0 u0, U (W u) = u) ∧
      (∀ x ∈ Icc (W 0) (W u0), W (U x) = x) ∧
      ContDiffOn ℝ 1 U (Ioo (W 0) (W u0)) ∧
      ∀ x ∈ Ioo (W 0) (W u0),
        HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x ∧
        0 < ratioDenominator lambda (inverseRatio U) x ∧
        HasDerivAt (inverseRatio U)
          ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) x := by
  obtain ⟨U, hUcont, hUmap, hleft, hright, hUsmooth, hUraw⟩ :=
    localInverse_exists_of_endpointH_pos hW hu0 hHpos
  refine ⟨U, hUcont, hUmap, hleft, hright, hUsmooth, ?_⟩
  intro x hx
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hxpos : 0 < x := by rw [← hW0]; exact hx.1
  obtain ⟨hUeq, hbigDenomPos⟩ :=
    localInverse_hasDerivAt_equation hW hu0 hHpos hUmap hright (hUraw x hx) hx
  have hbigDenomNe : lambda * x - U x + U x ^ 2 ≠ 0 := hbigDenomPos.ne'
  have hratioEq := inverseDerivativeValue_eq_ratioValue lambda U hxpos.ne' hbigDenomNe
  have hratioDenomPos : 0 < ratioDenominator lambda (inverseRatio U) x := by
    have hfactor := inverseDenominator_factor lambda U hxpos.ne'
    rw [hfactor] at hbigDenomPos
    rcases mul_pos_iff.mp hbigDenomPos with hcase | hcase
    · exact hcase.2
    · linarith
  have hUratio : HasDerivAt U
      (x / ratioDenominator lambda (inverseRatio U) x) x :=
    hUeq.congr_deriv hratioEq
  exact ⟨hUratio, hratioDenomPos,
    (inverseRatio_hasDerivAt hxpos.ne' hratioDenomPos.ne' hUratio).1⟩

/-- A positive ratio above `2λ` forces the inverse value `U=xr` above `1/2`.
This is the pointwise contradiction estimate in A6.3. -/
theorem ratio_large_forces_inverse_gt_half {lambda x r : ℝ}
    (hr : 0 < r) (hlarge : 2 * lambda ≤ r)
    (hdenom : 0 < lambda - r + x * r ^ 2) :
    1 / 2 < x * r := by
  have hhalf : r / 2 ≤ r - lambda := by linarith
  have hsquare : r - lambda < x * r ^ 2 := by linarith
  nlinarith [mul_pos hr (sub_pos.mpr (hhalf.trans_lt hsquare))]

/-- Positivity of the ratio denominator gives the upper inequality used for `limsup r≤λ`. -/
theorem ratio_lt_lambda_add_error {lambda x r : ℝ}
    (hdenom : 0 < lambda - r + x * r ^ 2) :
    r < lambda + x * r ^ 2 := by
  linarith

/-- Continuity of the inverse at zero turns the pointwise A6.3 contradiction into the
eventual bound `r<2λ`. -/
theorem inverseRatio_eventually_lt_two_mul {lambda x0 : ℝ} {U : ℝ → ℝ}
    (hlambda : 0 < lambda) (hx0 : 0 < x0) (hU0 : U 0 = 0)
    (hUcont : ContinuousWithinAt U (Ici 0) 0)
    (hUpos : ∀ x ∈ Ioo (0 : ℝ) x0, 0 < U x)
    (hdenom : ∀ x ∈ Ioo (0 : ℝ) x0,
      0 < ratioDenominator lambda (inverseRatio U) x) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), inverseRatio U x < 2 * lambda := by
  have hsmallIci : ∀ᶠ x in 𝓝[Ici (0 : ℝ)] 0, U x < 1 / 2 := by
    have ht := hUcont.tendsto
    have htarget : Iio (1 / 2 : ℝ) ∈ 𝓝 (U 0) := by
      rw [hU0]
      exact Iio_mem_nhds (by norm_num)
    exact ht.eventually htarget
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), U x < 1 / 2 :=
    hsmallIci.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  filter_upwards [Ioc_mem_nhdsGT (half_pos hx0), hsmall] with x hx hUxsmall
  by_contra hnot
  have hxOpen : x ∈ Ioo (0 : ℝ) x0 := ⟨hx.1, hx.2.trans_lt (half_lt_self hx0)⟩
  have hrpos : 0 < inverseRatio U x := by
    unfold inverseRatio
    exact div_pos (hUpos x hxOpen) hx.1
  have hlarge : 2 * lambda ≤ inverseRatio U x := le_of_not_gt hnot
  have hforce := ratio_large_forces_inverse_gt_half hrpos hlarge (hdenom x hxOpen)
  unfold inverseRatio at hforce
  have hidentity : x * (U x / x) = U x := by field_simp [hx.1.ne']
  rw [hidentity] at hforce
  linarith

/-- The eventual ratio bound for the concrete MI08 inverse package. -/
theorem localInverse_ratio_eventually_lt_two_mul {lambda : ℝ} {W U : ℝ → ℝ} {u0 : ℝ}
    (hlambda : 0 < lambda) (hW : IsWBoundarySolution lambda W)
    (hu0 : u0 ∈ openUnitInterval)
    (hUcont : ContinuousOn U (Icc (W 0) (W u0)))
    (hUmap : MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0))
    (hleft : ∀ u ∈ Icc 0 u0, U (W u) = u)
    (hright : ∀ x ∈ Icc (W 0) (W u0), W (U x) = x)
    (hdenom : ∀ x ∈ Ioo (W 0) (W u0),
      0 < ratioDenominator lambda (inverseRatio U) x) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), inverseRatio U x < 2 * lambda := by
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hx0 : 0 < W u0 := hW.2.2.2.2.2.2 u0 hu0
  have hU0 : U 0 = 0 := by
    calc
      U 0 = U (W 0) := congrArg U hW0.symm
      _ = 0 := hleft 0 ⟨le_rfl, hu0.1.le⟩
  have hUcont0 : ContinuousWithinAt U (Ici 0) 0 := by
    have hwithin := hUcont 0 ⟨by rw [hW0], hx0.le⟩
    have heq : Icc (W 0) (W u0) =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
      rw [hW0]
      filter_upwards [Iio_mem_nhds hx0] with x hx
      apply propext
      change (0 ≤ x ∧ x ≤ W u0) ↔ 0 ≤ x
      constructor
      · exact fun h ↦ h.1
      · exact fun h ↦ ⟨h, hx.le⟩
    exact hwithin.congr_set heq
  apply inverseRatio_eventually_lt_two_mul hlambda hx0 hU0 hUcont0
  · intro x hx
    have hUx := localInverse_maps_interior hu0.1 hW0 hUmap hright
      (show x ∈ Ioo (W 0) (W u0) by rwa [hW0])
    exact hUx.1
  · intro x hx
    exact hdenom x (by rwa [hW0])

/-- Epsilon formulation of `eq:r-limsup`: an eventually positive ratio bounded by `2λ`
and with positive denominator is eventually below `λ+ε` for every `ε>0`. -/
theorem ratio_eventually_lt_lambda_add {lambda : ℝ} {r : ℝ → ℝ}
    (hlambda : 0 < lambda)
    (hrpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < r x)
    (hrbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), r x < 2 * lambda)
    (hdenom : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      0 < ratioDenominator lambda r x) :
    ∀ epsilon > 0, ∀ᶠ x in 𝓝[>] (0 : ℝ), r x < lambda + epsilon := by
  intro epsilon hepsilon
  have hCpos : 0 < 2 * lambda := by positivity
  have hCsqpos : 0 < (2 * lambda) ^ 2 := sq_pos_of_pos hCpos
  have hdelta : 0 < epsilon / (2 * lambda) ^ 2 := div_pos hepsilon hCsqpos
  filter_upwards [hrpos, hrbound, hdenom,
    Ioc_mem_nhdsGT hdelta] with x hrxpos hrxbound hdenx hx
  have hrsq : r x ^ 2 < (2 * lambda) ^ 2 := by
    nlinarith [sq_pos_of_pos hrxpos, sq_pos_of_pos hCpos]
  have herrLt : x * r x ^ 2 < x * (2 * lambda) ^ 2 :=
    mul_lt_mul_of_pos_left hrsq hx.1
  have hdeltaEq : (epsilon / (2 * lambda) ^ 2) * (2 * lambda) ^ 2 = epsilon := by
    field_simp [hCsqpos.ne']
  have herr : x * r x ^ 2 < epsilon := by
    calc
      x * r x ^ 2 < x * (2 * lambda) ^ 2 := herrLt
      _ ≤ (epsilon / (2 * lambda) ^ 2) * (2 * lambda) ^ 2 :=
        mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)
      _ = epsilon := hdeltaEq
  have hupper := ratio_lt_lambda_add_error (lambda := lambda) (x := x) (r := r x) hdenx
  linarith

/-- `eq:r-limsup` for the concrete local inverse, in epsilon/eventual form. -/
theorem localInverse_ratio_eventually_lt_lambda_add {lambda : ℝ} {W U : ℝ → ℝ} {u0 : ℝ}
    (hlambda : 0 < lambda) (hW : IsWBoundarySolution lambda W)
    (hu0 : u0 ∈ openUnitInterval)
    (hUcont : ContinuousOn U (Icc (W 0) (W u0)))
    (hUmap : MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0))
    (hleft : ∀ u ∈ Icc 0 u0, U (W u) = u)
    (hright : ∀ x ∈ Icc (W 0) (W u0), W (U x) = x)
    (hdenom : ∀ x ∈ Ioo (W 0) (W u0),
      0 < ratioDenominator lambda (inverseRatio U) x) :
    ∀ epsilon > 0, ∀ᶠ x in 𝓝[>] (0 : ℝ),
      inverseRatio U x < lambda + epsilon := by
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hx0 : 0 < W u0 := hW.2.2.2.2.2.2 u0 hu0
  apply ratio_eventually_lt_lambda_add hlambda
  · filter_upwards [Ioc_mem_nhdsGT (half_pos hx0)] with x hx
    unfold inverseRatio
    have hUx := localInverse_maps_interior hu0.1 hW0 hUmap hright
      (show x ∈ Ioo (W 0) (W u0) by
        rw [hW0]; exact ⟨hx.1, hx.2.trans_lt (half_lt_self hx0)⟩)
    exact div_pos hUx.1 hx.1
  · exact localInverse_ratio_eventually_lt_two_mul hlambda hW hu0 hUcont hUmap
      hleft hright hdenom
  · filter_upwards [Ioc_mem_nhdsGT (half_pos hx0)] with x hx
    exact hdenom x (by
      rw [hW0]; exact ⟨hx.1, hx.2.trans_lt (half_lt_self hx0)⟩)

/-- The horizontal upward-crossing principle used in A6.4.  Once the derivative is
positive whenever the trajectory lies on level `c`, a trajectory starting above that
level cannot later cross below it. -/
theorem upwardLevel_preserved {phi : ℝ → ℝ} {S s0 c : ℝ}
    (hcont : ContinuousOn phi (Ici S))
    (hderiv : ∀ s ∈ Ici S, HasDerivAt phi (deriv phi s) s)
    (hlevel : ∀ s ∈ Ici S, phi s = c → 0 < deriv phi s)
    (hs0 : S ≤ s0) (hstart : c ≤ phi s0) :
    ∀ s ∈ Ici s0, c ≤ phi s := by
  intro t ht
  by_contra hnot
  have htbelow : phi t < c := lt_of_not_ge hnot
  have hs0t : s0 ≤ t := ht
  have hzeroExists : ∃ q ∈ Icc s0 t, phi q = c := by
    have hrange := intermediate_value_Icc' hs0t
      (hcont.mono fun x hx ↦ hs0.trans hx.1)
      (show c ∈ Icc (phi t) (phi s0) from ⟨htbelow.le, hstart⟩)
    simpa only [mem_image] using hrange
  let Z : Set ℝ := Icc s0 t ∩ phi ⁻¹' {c}
  have hZclosed : IsClosed Z :=
    (hcont.mono fun x hx ↦ hs0.trans hx.1).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact Z :=
    IsCompact.of_isClosed_subset isCompact_Icc hZclosed inter_subset_left
  have hZnonempty : Z.Nonempty := by
    obtain ⟨q, hqI, hqzero⟩ := hzeroExists
    exact ⟨q, hqI, by simpa only [mem_singleton_iff]⟩
  obtain ⟨d, hdZ, hdgreat⟩ := hZcompact.exists_isGreatest hZnonempty
  have hdI : d ∈ Icc s0 t := hdZ.1
  have hdlevel : phi d = c := hdZ.2
  have hdt : d < t := lt_of_le_of_ne hdI.2 fun h ↦ by
    apply htbelow.ne
    rw [← h, hdlevel]
  have hbelow : ∀ z ∈ Icc d t, phi z ≤ c := by
    intro z hz
    by_contra hznot
    have hzabove : c < phi z := lt_of_not_ge hznot
    have hzeroRange := intermediate_value_Icc' hz.2
      (hcont.mono fun x hx ↦ hs0.trans (hdI.1.trans (hz.1.trans hx.1)))
      (show c ∈ Icc (phi t) (phi z) from ⟨htbelow.le, hzabove.le⟩)
    obtain ⟨q, hqI, hqlevel⟩ := hzeroRange
    have hqZ : q ∈ Z := by
      refine ⟨⟨hdI.1.trans (hz.1.trans hqI.1), hqI.2⟩, ?_⟩
      change phi q ∈ ({c} : Set ℝ)
      simpa only [mem_singleton_iff] using hqlevel
    have hqd := hdgreat hqZ
    have hdz : d < z := lt_of_le_of_ne hz.1 fun h ↦ by
      apply hzabove.ne'
      rw [← h, hdlevel]
    exact (not_le_of_gt (hdz.trans_le hqI.1)) hqd
  have hlocalMax : IsLocalMaxOn phi (Ici d) d := by
    have hIio : ∀ᶠ z in 𝓝[Ici d] d, z ∈ Iio t :=
      (show ∀ᶠ z in 𝓝 d, z ∈ Iio t from Iio_mem_nhds hdt).filter_mono inf_le_left
    filter_upwards [hIio, self_mem_nhdsWithin] with z hzt hdz
    rw [hdlevel]
    exact hbelow z ⟨hdz, hzt.le⟩
  have htan : (1 : ℝ) ∈ posTangentConeAt (Ici d) d := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with q hq
    change d + q * 1 ∈ Ici d
    change 0 < q at hq
    simp only [mul_one]
    exact le_add_of_nonneg_right hq.le
  have hdS : d ∈ Ici S := hs0.trans hdI.1
  have hnonpos : deriv phi d ≤ 0 := by
    have hfermat := hlocalMax.hasFDerivWithinAt_nonpos
      ((hderiv d hdS).hasFDerivAt.hasFDerivWithinAt) htan
    simpa using hfermat
  exact (not_lt_of_ge hnonpos) (hlevel d hdS hdlevel)

/-- A uniform positive derivative below a threshold forces that threshold to be reached
in finite time, provided the trajectory has a uniform upper bound. -/
theorem reaches_level_of_deriv_ge {phi : ℝ → ℝ} {S level drift bound : ℝ}
    (hdriftPos : 0 < drift)
    (hcont : ContinuousOn phi (Ici S))
    (hdiff : DifferentiableOn ℝ phi (Ioi S))
    (hdrift : ∀ s ∈ Ici S, phi s ≤ level → drift ≤ deriv phi s)
    (hbound : ∀ s ∈ Ici S, phi s ≤ bound) :
    ∃ s ∈ Ici S, level ≤ phi s := by
  by_contra hnever
  have hbelow : ∀ s ∈ Ici S, phi s < level := by
    intro s hs
    exact lt_of_not_ge fun h ↦ hnever ⟨s, hs, h⟩
  have hboundS := hbound S (show S ≤ S from le_rfl)
  let T : ℝ := S + (bound - phi S + 1) / drift
  have hnumerator : 0 < bound - phi S + 1 := by linarith
  have hST : S < T := by
    dsimp [T]
    exact lt_add_of_pos_right _ (div_pos hnumerator hdriftPos)
  obtain ⟨c, hc, hmv⟩ := ManualInterfaces.MI06_mean_value_theorem hST
    (hcont.mono fun x hx ↦ hx.1)
    (hdiff.mono fun x hx ↦ hx.1)
  have hcS : c ∈ Ici S := hc.1.le
  have hcDrift : drift ≤ deriv phi c := hdrift c hcS (hbelow c hcS).le
  have hboundT := hbound T hST.le
  have hTdiff : T - S = (bound - phi S + 1) / drift := by simp [T]
  rw [hTdiff] at hmv
  have hgrowth : bound - phi S + 1 ≤ phi T - phi S := by
    rw [hmv]
    have hdivPos : 0 < (bound - phi S + 1) / drift :=
      div_pos hnumerator hdriftPos
    have hmul := mul_le_mul_of_nonneg_right hcDrift hdivPos.le
    field_simp [hdriftPos.ne'] at hmul ⊢
    nlinarith
  linarith

/-- Failure to converge to zero, for an eventually nonnegative real trajectory, produces
a fixed positive level which is visited frequently. -/
theorem frequently_ge_of_eventually_nonneg_not_tendsto_zero {phi : ℝ → ℝ}
    (hnonneg : ∀ᶠ s in atTop, 0 ≤ phi s)
    (hnot : ¬ Tendsto phi atTop (𝓝 (0 : ℝ))) :
    ∃ eta > 0, ∃ᶠ s in atTop, eta ≤ phi s := by
  by_contra hfrequent
  push_neg at hfrequent
  apply hnot
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hnonneg] with s hs
    exact ha.trans_le hs
  · intro b hb
    have hnotFrequently := hfrequent b hb
    exact hnotFrequently

/-- Logarithmic time reparametrization `rho(s)=r(exp(-s))`. -/
noncomputable def logRatioFlow (r : ℝ → ℝ) (s : ℝ) : ℝ :=
  r (Real.exp (-s))

/-- The exponential change of variables approaches zero through positive values. -/
theorem tendsto_exp_neg_atTop_nhdsGT_zero :
    Tendsto (fun s : ℝ ↦ Real.exp (-s)) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨Real.tendsto_exp_neg_atTop_nhds_zero, ?_⟩
  exact Eventually.of_forall fun s ↦ Real.exp_pos (-s)

/-- Right-hand side of `eq:r-flow`. -/
noncomputable def logRatioFlowRhs (lambda : ℝ) (rho : ℝ → ℝ) (s : ℝ) : ℝ :=
  rho s - Real.exp (-s) /
    (lambda - rho s + Real.exp (-s) * rho s ^ 2)

/-- At a fixed small positive level, the log-flow vector field points strictly upward
once the exponential forcing is small enough. -/
theorem logRatioFlowRhs_pos_at_small_level {lambda eta s : ℝ} {rho : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hetalambda : eta ≤ lambda / 2)
    (hrho : rho s = eta)
    (hexp : Real.exp (-s) ≤ eta * lambda / 4) :
    0 < logRatioFlowRhs lambda rho s := by
  have hepos : 0 < Real.exp (-s) := Real.exp_pos _
  have hdenLower : lambda / 2 ≤
      lambda - rho s + Real.exp (-s) * rho s ^ 2 := by
    rw [hrho]
    have hnonneg : 0 ≤ Real.exp (-s) * eta ^ 2 := by positivity
    linarith
  have hdenPos : 0 < lambda - rho s + Real.exp (-s) * rho s ^ 2 :=
    (half_pos hlambda).trans_le hdenLower
  have heLt : Real.exp (-s) < eta * (lambda / 2) := by
    have hprod : 0 < eta * lambda := mul_pos heta hlambda
    nlinarith
  have hetaDen : eta * (lambda / 2) ≤
      eta * (lambda - rho s + Real.exp (-s) * rho s ^ 2) :=
    mul_le_mul_of_nonneg_left hdenLower heta.le
  have hfrac : Real.exp (-s) /
      (lambda - rho s + Real.exp (-s) * rho s ^ 2) < eta := by
    rw [div_lt_iff₀ hdenPos]
    exact heLt.trans_le hetaDen
  unfold logRatioFlowRhs
  rw [hrho] at hfrac ⊢
  exact sub_pos.mpr hfrac

/-- Uniform positive drift while `rho` stays in `[eta,lambda-delta]`. -/
theorem logRatioFlowRhs_ge_half_level {lambda eta delta s : ℝ} {rho : ℝ → ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hrhoLower : eta ≤ rho s) (hrhoUpper : rho s ≤ lambda - delta)
    (hexp : Real.exp (-s) ≤ eta * delta / 2) :
    eta / 2 ≤ logRatioFlowRhs lambda rho s := by
  have hdenLower : delta ≤
      lambda - rho s + Real.exp (-s) * rho s ^ 2 := by
    have hnonneg : 0 ≤ Real.exp (-s) * rho s ^ 2 := by positivity
    linarith
  have hdenPos : 0 < lambda - rho s + Real.exp (-s) * rho s ^ 2 :=
    hdelta.trans_le hdenLower
  have hfrac : Real.exp (-s) /
      (lambda - rho s + Real.exp (-s) * rho s ^ 2) ≤ eta / 2 := by
    rw [div_le_iff₀ hdenPos]
    have hmul := mul_le_mul_of_nonneg_left hdenLower (by positivity : 0 ≤ eta / 2)
    nlinarith
  unfold logRatioFlowRhs
  linarith

/-- Algebraic conversion of `x r'(x)=x/den-r` to the displayed log-time flow. -/
theorem logRatioFlow_derivative_identity {lambda : ℝ} {r : ℝ → ℝ} {s rprime : ℝ}
    (hrprime :
      Real.exp (-s) * rprime =
        Real.exp (-s) / ratioDenominator lambda r (Real.exp (-s)) -
          r (Real.exp (-s))) :
    rprime * (-Real.exp (-s)) =
      logRatioFlowRhs lambda (logRatioFlow r) s := by
  unfold ratioDenominator at hrprime
  unfold logRatioFlowRhs logRatioFlow
  linarith

/-- The genuine chain-rule form of `eq:r-flow`. -/
theorem logRatioFlow_hasDerivAt {lambda : ℝ} {r : ℝ → ℝ} {s rprime : ℝ}
    (hr : HasDerivAt r rprime (Real.exp (-s)))
    (hrprime :
      Real.exp (-s) * rprime =
        Real.exp (-s) / ratioDenominator lambda r (Real.exp (-s)) -
          r (Real.exp (-s))) :
    HasDerivAt (logRatioFlow r)
      (logRatioFlowRhs lambda (logRatioFlow r) s) s := by
  have hexp : HasDerivAt (fun z : ℝ ↦ Real.exp (-z)) (-Real.exp (-s)) s := by
    have hraw := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
    change HasDerivAt (fun z : ℝ ↦ Real.exp (-z))
      (Real.exp (-s) * (-1)) s at hraw
    simpa only [mul_neg, mul_one] using hraw
  have hcomp := hr.comp s hexp
  exact hcomp.congr_deriv (logRatioFlow_derivative_identity hrprime)

/-- The A6.4 scalar phase portrait.  A positive solution of the logarithmic ratio flow
which has the A6.3 eventual upper bound converges either to `0` or to `lambda`. -/
theorem logRatioFlow_tendsto_zero_or_lambda {lambda S : ℝ} {rho : ℝ → ℝ}
    (hlambda : 0 < lambda)
    (hcont : ContinuousOn rho (Ici S))
    (hflow : ∀ s ∈ Ici S,
      HasDerivAt rho (logRatioFlowRhs lambda rho s) s)
    (hpos : ∀ s ∈ Ici S, 0 < rho s)
    (hupper : ∀ epsilon > 0, ∀ᶠ s in atTop, rho s < lambda + epsilon) :
    Tendsto rho atTop (𝓝 (0 : ℝ)) ∨ Tendsto rho atTop (𝓝 lambda) := by
  classical
  by_cases hzero : Tendsto rho atTop (𝓝 (0 : ℝ))
  · exact Or.inl hzero
  right
  have hnonneg : ∀ᶠ s in atTop, 0 ≤ rho s := by
    filter_upwards [Ici_mem_atTop S] with s hs
    exact (hpos s hs).le
  obtain ⟨eta0, heta0, hfreq0⟩ :=
    frequently_ge_of_eventually_nonneg_not_tendsto_zero hnonneg hzero
  let eta : ℝ := min eta0 (lambda / 2)
  have heta : 0 < eta := lt_min heta0 (half_pos hlambda)
  have hetalambda : eta ≤ lambda / 2 := min_le_right _ _
  have hetaeta0 : eta ≤ eta0 := min_le_left _ _
  have hfreq : ∃ᶠ s in atTop, eta ≤ rho s :=
    hfreq0.mono fun s hs ↦ hetaeta0.trans hs
  have hsmallEta : ∀ᶠ s in atTop,
      Real.exp (-s) ≤ eta * lambda / 4 := by
    have htarget : 0 < eta * lambda / 4 := by positivity
    exact Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (Iic_mem_nhds htarget)
  have hlate : ∀ᶠ s in atTop, s ∈ Ici S := Ici_mem_atTop S
  obtain ⟨s0, hs0eta, hs0S, hs0small⟩ :=
    (hfreq.and_eventually (hlate.and hsmallEta)).exists
  have hcont0 : ContinuousOn rho (Ici s0) :=
    hcont.mono fun s hs ↦ (show S ≤ s from hs0S.trans hs)
  have hflow0 : ∀ s ∈ Ici s0,
      HasDerivAt rho (logRatioFlowRhs lambda rho s) s := by
    intro s hs
    exact hflow s (show S ≤ s from hs0S.trans hs)
  have hflowDeriv0 : ∀ s ∈ Ici s0,
      HasDerivAt rho (deriv rho s) s := by
    intro s hs
    exact (hflow0 s hs).congr_deriv (hflow0 s hs).deriv.symm
  have hlevelEta : ∀ s ∈ Ici s0, rho s = eta → 0 < deriv rho s := by
    intro s hs hrho
    rw [(hflow0 s hs).deriv]
    exact logRatioFlowRhs_pos_at_small_level hlambda heta hetalambda hrho
      (le_trans (Real.exp_le_exp.mpr (neg_le_neg hs)) hs0small)
  have hkeepEta : ∀ s ∈ Ici s0, eta ≤ rho s :=
    upwardLevel_preserved hcont0 hflowDeriv0 hlevelEta le_rfl hs0eta
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let delta : ℝ := (lambda - a) / 2
    have hdelta : 0 < delta := half_pos (sub_pos.mpr ha)
    have halevel : a < lambda - delta := by
      dsimp [delta]
      linarith
    have hsmallDelta : ∀ᶠ s in atTop,
        Real.exp (-s) ≤ eta * delta / 2 := by
      have htarget : 0 < eta * delta / 2 := by positivity
      exact Real.tendsto_exp_neg_atTop_nhds_zero.eventually
        (Iic_mem_nhds htarget)
    obtain ⟨B, hB⟩ := eventually_atTop.1
      (hsmallDelta.and (hupper lambda hlambda))
    let S1 : ℝ := max s0 B
    have hS1s0 : s0 ≤ S1 := le_max_left _ _
    have hS1B : B ≤ S1 := le_max_right _ _
    have hS1S : S ≤ S1 := hs0S.trans hS1s0
    have hcont1 : ContinuousOn rho (Ici S1) :=
      hcont.mono fun s hs ↦ hS1S.trans hs
    have hdiff1 : DifferentiableOn ℝ rho (Ioi S1) := by
      intro s hs
      exact (hflow s (hS1S.trans hs.le)).differentiableAt.differentiableWithinAt
    have hdrift1 : ∀ s ∈ Ici S1, rho s ≤ lambda - delta →
        eta / 2 ≤ deriv rho s := by
      intro s hs hsrho
      have hsB : B ≤ s := hS1B.trans hs
      have hsmall := (hB s hsB).1
      have hlower := hkeepEta s (hS1s0.trans hs)
      rw [(hflow s (hS1S.trans hs)).deriv]
      exact logRatioFlowRhs_ge_half_level heta hdelta hlower hsrho hsmall
    have hbound1 : ∀ s ∈ Ici S1, rho s ≤ 2 * lambda := by
      intro s hs
      have := (hB s (hS1B.trans hs)).2.le
      linarith
    obtain ⟨shit, hshitS1, hhit⟩ := reaches_level_of_deriv_ge
      (half_pos heta) hcont1 hdiff1 hdrift1 hbound1
    have hsmallHit : Real.exp (-shit) ≤ eta * delta / 2 :=
      (hB shit (hS1B.trans hshitS1)).1
    have hlevelHit : ∀ s ∈ Ici S1, rho s = lambda - delta →
        0 < deriv rho s := by
      intro s hs hrho
      have hlower := hkeepEta s (hS1s0.trans hs)
      have hsmall := (hB s (hS1B.trans hs)).1
      rw [(hflow s (hS1S.trans hs)).deriv]
      have hge := logRatioFlowRhs_ge_half_level heta hdelta hlower hrho.le hsmall
      exact (half_pos heta).trans_le hge
    have hkeepHit : ∀ s ∈ Ici shit, lambda - delta ≤ rho s :=
      upwardLevel_preserved hcont1
        (fun s hs ↦
          let hf := hflow s (show S ≤ s from hS1S.trans hs)
          hf.congr_deriv hf.deriv.symm)
        hlevelHit hshitS1 hhit
    filter_upwards [Ici_mem_atTop shit] with s hs
    exact halevel.trans_le (hkeepHit s hs)
  · intro b hb
    have hepsilon : 0 < b - lambda := sub_pos.mpr hb
    filter_upwards [hupper (b - lambda) hepsilon] with s hs
    simpa only [add_sub_cancel] using hs

/-- Convergence of the log-time reparametrization is equivalent in the direction needed
for A6.4 to right-hand convergence of the original ratio. -/
theorem tendsto_of_logRatioFlow_tendsto {r : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (logRatioFlow r) atTop (𝓝 L)) :
    Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hneglog : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply (h.comp hneglog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change r (Real.exp (-(-Real.log x))) = r x
  rw [neg_neg, Real.exp_log hx]

/-- A source-facing entry point through A6.1--A6.2: every boundary solution admits a
small interval and a compact inverse satisfying both differential equations in
`eq:r-inverse`, with positive denominator. -/
theorem leftEndpoint_localInverse_ratio_equations {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) :
    ∃ u0 ∈ openUnitInterval,
      (∀ u ∈ Ioc (0 : ℝ) u0, 0 < endpointH lambda W u) ∧
      ∃ U : ℝ → ℝ, ContinuousOn U (Icc (W 0) (W u0)) ∧
        MapsTo U (Icc (W 0) (W u0)) (Icc 0 u0) ∧
        (∀ u ∈ Icc 0 u0, U (W u) = u) ∧
        (∀ x ∈ Icc (W 0) (W u0), W (U x) = x) ∧
        ContDiffOn ℝ 1 U (Ioo (W 0) (W u0)) ∧
        ∀ x ∈ Ioo (W 0) (W u0),
          HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x ∧
          0 < ratioDenominator lambda (inverseRatio U) x ∧
          HasDerivAt (inverseRatio U)
            ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) x := by
  obtain ⟨u0, hu0, hHpos⟩ := exists_endpointH_pos_near_zero hW
  exact ⟨u0, hu0, hHpos, localInverse_ratio_equations hW hu0 hHpos⟩

/-- The genuine compact local inverse package used in A6.  Both functions carry explicit
`MapsTo` data, so the inverse identities cannot select an unrelated branch.  The inverse is
`C¹` on `Ioc 0 x₀`, including its right endpoint as required by the source. -/
def LeftLocalInverseData (W : ℝ → ℝ) : Prop :=
  ∃ u₀ x₀ : ℝ, 0 < u₀ ∧ 0 < x₀ ∧ ∃ U : ℝ → ℝ,
    ContinuousOn U (Icc 0 x₀) ∧
    MapsTo U (Icc 0 x₀) (Icc 0 u₀) ∧
    MapsTo W (Icc 0 u₀) (Icc 0 x₀) ∧
    (∀ u ∈ Icc 0 u₀, U (W u) = u) ∧
    (∀ x ∈ Icc 0 x₀, W (U x) = x) ∧
    ContDiffOn ℝ 1 U (Ioc 0 x₀)

/-- Source-facing local inverse construction for A6, independent of either asymptotic branch. -/
theorem leftEndpoint_sourceLocalInverse {lambda : ℝ} {W : ℝ → ℝ}
    (hW : IsWBoundarySolution lambda W) : LeftLocalInverseData W := by
  obtain ⟨v0, hv0, hHpos, U, hUcont, hUmap, hUinv, hWinv, hUsmooth, hUdata⟩ :=
    leftEndpoint_localInverse_ratio_equations hW
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hWv0 : 0 < W v0 := hW.2.2.2.2.2.2 v0 hv0
  let x0 : ℝ := min (W v0 / 2) (v0 / 2)
  have hx0 : 0 < x0 := lt_min (half_pos hWv0) (half_pos hv0.1)
  have hx0W : x0 < W v0 :=
    (min_le_left (W v0 / 2) (v0 / 2)).trans_lt (half_lt_self hWv0)
  have hx0v : x0 < v0 :=
    (min_le_right (W v0 / 2) (v0 / 2)).trans_lt (half_lt_self hv0.1)
  have hU0 : U 0 = 0 := by
    calc
      U 0 = U (W 0) := congrArg U hW0.symm
      _ = 0 := hUinv 0 ⟨le_rfl, hv0.1.le⟩
  have hUcontX : ContinuousOn U (Icc 0 x0) :=
    hUcont.mono fun x hx ↦ by
      rw [hW0]
      exact ⟨hx.1, hx.2.trans hx0W.le⟩
  have hUeq : ∀ x ∈ Ioo (0 : ℝ) x0,
      HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x := by
    intro x hx
    exact (hUdata x (by rw [hW0]; exact ⟨hx.1, hx.2.trans hx0W⟩)).1
  have hdenom : ∀ x ∈ Ioo (0 : ℝ) x0,
      0 < ratioDenominator lambda (inverseRatio U) x := by
    intro x hx
    exact (hUdata x (by rw [hW0]; exact ⟨hx.1, hx.2.trans hx0W⟩)).2.1
  have hUstrict : StrictMonoOn U (Icc 0 x0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) x0) hUcontX
    rw [interior_Icc]
    intro x hx
    rw [(hUeq x hx).deriv]
    exact div_pos hx.1 (hdenom x hx)
  have hUx0Map : U x0 ∈ Icc 0 v0 :=
    hUmap ⟨by rw [hW0]; exact hx0.le, hx0W.le⟩
  have hUx0pos : 0 < U x0 := by
    rw [← hU0]
    exact hUstrict ⟨le_rfl, hx0.le⟩ ⟨hx0.le, le_rfl⟩ hx0
  have hmapU : MapsTo U (Icc 0 x0) (Icc 0 (U x0)) := by
    intro x hx
    constructor
    · have hmono := hUstrict.monotoneOn ⟨le_rfl, hx0.le⟩ hx hx.1
      simpa only [hU0] using hmono
    · exact hUstrict.monotoneOn hx ⟨hx0.le, le_rfl⟩ hx.2
  have hright : ∀ x ∈ Icc 0 x0, W (U x) = x := by
    intro x hx
    exact hWinv x (by rw [hW0]; exact ⟨hx.1, hx.2.trans hx0W.le⟩)
  have hleft : ∀ u ∈ Icc 0 (U x0), U (W u) = u := by
    intro u hu
    exact hUinv u ⟨hu.1, hu.2.trans hUx0Map.2⟩
  have hWstrict : StrictMonoOn W (Icc 0 v0) :=
    strictMonoOn_of_endpointH_pos hW hv0 hHpos
  have hmapW : MapsTo W (Icc 0 (U x0)) (Icc 0 x0) := by
    intro u hu
    have hzeroMem : (0 : ℝ) ∈ Icc 0 v0 := ⟨le_rfl, hv0.1.le⟩
    have huMem : u ∈ Icc 0 v0 := ⟨hu.1, hu.2.trans hUx0Map.2⟩
    constructor
    · have hmono := hWstrict.monotoneOn hzeroMem huMem hu.1
      simpa only [hW0] using hmono
    · have hmono := hWstrict.monotoneOn huMem hUx0Map hu.2
      rw [hright x0 ⟨hx0.le, le_rfl⟩] at hmono
      exact hmono
  have hUsmoothX : ContDiffOn ℝ 1 U (Ioc 0 x0) :=
    hUsmooth.mono fun x hx ↦ by
      rw [hW0]
      exact ⟨hx.1, hx.2.trans_lt hx0W⟩
  exact ⟨U x0, x0, hUx0pos, hx0, U, hUcontX, hmapU, hmapW,
    hleft, hright, hUsmoothX⟩

/-- The linear comparison scale is negligible relative to the sharp square-root scale. -/
theorem linearScale_div_sharpScale_tendsto_zero {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun u : ℝ ↦ (u / lambda) / Real.sqrt (2 * lambda * u))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsqrt : Tendsto (fun u : ℝ ↦ Real.sqrt u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht0 : Tendsto (fun u : ℝ ↦ Real.sqrt u) (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.tendsto 0
    simpa only [Real.sqrt_zero] using ht0.mono_left nhdsWithin_le_nhds
  have hscaled : Tendsto
      (fun u : ℝ ↦ Real.sqrt u / (lambda * Real.sqrt (2 * lambda)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsqrt.div_const (lambda * Real.sqrt (2 * lambda))
  apply (tendsto_congr' ?_).2 hscaled
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hsqrtLambda : Real.sqrt (2 * lambda) ≠ 0 := by positivity
  have hsqrtu : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  rw [show 2 * lambda * u = (2 * lambda) * u by ring,
    Real.sqrt_mul' (2 * lambda) hu.le]
  field_simp [hlambda.ne', hsqrtLambda, hsqrtu]
  nlinarith [Real.sq_sqrt hu.le]

/-- A solution cannot satisfy both source asymptotics. -/
theorem leftEndpoint_branches_mutually_exclusive {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) :
    ¬(HasLinearBranchAtZero lambda W ∧ HasSharpBranchAtZero lambda W) := by
  rintro ⟨hlinear, hsharp⟩
  have hdenom : ∀ᶠ u in 𝓝[>] (0 : ℝ), Real.sqrt (2 * lambda * u) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (Real.sqrt_pos.2 (mul_pos (mul_pos zero_lt_two hlambda) hu)).ne'
  have hequiv :
      (fun u : ℝ ↦ u / lambda) ~[𝓝[>] (0 : ℝ)]
        (fun u : ℝ ↦ Real.sqrt (2 * lambda * u)) :=
    hlinear.symm.trans hsharp
  rw [isEquivalent_iff_tendsto_one hdenom] at hequiv
  have hzero := linearScale_div_sharpScale_tendsto_zero hlambda
  have hcontra := tendsto_nhds_unique hequiv hzero
  norm_num at hcontra

/-- A genuine local inverse transports a positive quadratic asymptotic to the source's
square-root branch.  The `MapsTo` and two-sided inverse data rule out spurious inverse
branches; this is the range control missing from the former MI12 interface. -/
theorem sharpBranch_of_inverse_quadratic {lambda eta : ℝ} {U W : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hU0 : U 0 = 0) (hW0 : W 0 = 0)
    (hWcont : ContinuousWithinAt W (Ici 0) 0)
    (hWpos : ∀ y ∈ Ioo 0 (U eta), 0 < W y)
    (hWmap : MapsTo W (Icc 0 (U eta)) (Icc 0 eta))
    (hstrict : StrictMonoOn U (Icc 0 eta))
    (hright : ∀ y ∈ Icc 0 (U eta), U (W y) = y)
    (hquadratic :
      (fun x : ℝ ↦ U x) ~[𝓝[>] (0 : ℝ)]
        (fun x : ℝ ↦ (2 * lambda)⁻¹ * x ^ (2 : ℝ))) :
    HasSharpBranchAtZero lambda W := by
  have hUeta : 0 < U eta := by
    rw [← hU0]
    exact hstrict ⟨le_rfl, heta.le⟩ ⟨heta.le, le_rfl⟩ heta
  have hWtendsto : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := hWcont.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    simpa only [hW0] using ht
  have hWposEventually : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < W y := by
    filter_upwards [Ioc_mem_nhdsGT (half_pos hUeta)] with y hy
    exact hWpos y ⟨hy.1, hy.2.trans_lt (half_lt_self hUeta)⟩
  have hWmapsZero : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hWtendsto, hWposEventually⟩
  have hmodelNe : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      (2 * lambda)⁻¹ * x ^ (2 : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by norm_num) hlambda.ne'))
      (Real.rpow_pos_of_pos hx (2 : ℝ)).ne'
  have hratio : Tendsto
      (fun x : ℝ ↦ U x / ((2 * lambda)⁻¹ * x ^ (2 : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hmodelNe).1 hquadratic
  have hcomposed : Tendsto
      (fun y : ℝ ↦ U (W y) / ((2 * lambda)⁻¹ * W y ^ (2 : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert hratio.comp hWmapsZero using 1 <;> ext y <;> rfl
  have hinverted : Tendsto
      (fun y : ℝ ↦ (U (W y) / ((2 * lambda)⁻¹ * W y ^ (2 : ℝ)))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hcomposed.inv₀ one_ne_zero
  have hsqrt := hinverted.sqrt
  have hsqrtOne : Real.sqrt (1 : ℝ) = 1 := by norm_num
  rw [hsqrtOne] at hsqrt
  unfold HasSharpBranchAtZero
  have hdenom : ∀ᶠ u in 𝓝[>] (0 : ℝ), Real.sqrt (2 * lambda * u) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (Real.sqrt_pos.2 (mul_pos (mul_pos zero_lt_two hlambda) hu)).ne'
  rw [isEquivalent_iff_tendsto_one hdenom]
  apply (tendsto_congr' ?_).2 hsqrt
  filter_upwards [Ioc_mem_nhdsGT (half_pos hUeta)] with u hu
  have huOpen : u ∈ Ioo (0 : ℝ) (U eta) :=
    ⟨hu.1, hu.2.trans_lt (half_lt_self hUeta)⟩
  have hWu : 0 < W u := hWpos u huOpen
  have _hWuRange := hWmap ⟨hu.1.le, huOpen.2.le⟩
  have hrightu := hright u ⟨hu.1.le, huOpen.2.le⟩
  have hinside :
      (U (W u) / ((2 * lambda)⁻¹ * W u ^ (2 : ℝ)))⁻¹ =
        W u ^ 2 / (2 * lambda * u) := by
    rw [hrightu, Real.rpow_two]
    field_simp [hlambda.ne', hu.1.ne', hWu.ne']
  change W u / Real.sqrt (2 * lambda * u) = _
  rw [hinside, Real.sqrt_div (sq_nonneg (W u)), Real.sqrt_sq hWu.le]

/-- The `r→λ` alternative, transported through the inverse identities, is exactly the
source's linear branch. -/
theorem linearBranch_of_inverseRatio_tendsto {lambda eta : ℝ} {U W : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hW0 : W 0 = 0)
    (hWcont : ContinuousWithinAt W (Ici 0) 0)
    (hWpos : ∀ u ∈ Ioo 0 eta, 0 < W u)
    (hleft : ∀ u ∈ Icc 0 eta, U (W u) = u)
    (hratio : Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 lambda)) :
    HasLinearBranchAtZero lambda W := by
  have hWtendsto : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := hWcont.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    simpa only [hW0] using ht
  have hWposEventually : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < W u := by
    filter_upwards [Ioc_mem_nhdsGT (half_pos heta)] with u hu
    exact hWpos u ⟨hu.1, hu.2.trans_lt (half_lt_self heta)⟩
  have hWmap : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hWtendsto, hWposEventually⟩
  have hquotRaw := hratio.comp hWmap
  have hquot : Tendsto (fun u : ℝ ↦ u / W u) (𝓝[>] (0 : ℝ)) (𝓝 lambda) := by
    apply (tendsto_congr' ?_).2 hquotRaw
    filter_upwards [Ioc_mem_nhdsGT (half_pos heta)] with u hu
    change u / W u = U (W u) / W u
    rw [hleft u ⟨hu.1.le, hu.2.trans (half_lt_self heta).le⟩]
  have hone : Tendsto (fun u : ℝ ↦ lambda / (u / W u))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℝ ↦ lambda) (𝓝[>] (0 : ℝ)) (𝓝 lambda) :=
      tendsto_const_nhds
    have ht := hconst.div hquot hlambda.ne'
    change Tendsto (fun u : ℝ ↦ lambda / (u / W u))
      (𝓝[>] (0 : ℝ)) (𝓝 (lambda / lambda)) at ht
    simpa [hlambda.ne'] using ht
  unfold HasLinearBranchAtZero
  have hdenom : ∀ᶠ u in 𝓝[>] (0 : ℝ), u / lambda ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact div_ne_zero (show u ≠ 0 from (show 0 < u from hu).ne') hlambda.ne'
  rw [isEquivalent_iff_tendsto_one hdenom]
  apply (tendsto_congr' ?_).2 hone
  filter_upwards [self_mem_nhdsWithin, hWposEventually] with u hu hWu
  change W u / (u / lambda) = lambda / (u / W u)
  have hu0 : u ≠ 0 := (show 0 < u from hu).ne'
  field_simp [hu0, hlambda.ne', hWu.ne']

/-- The derivative value in the inverse equation extends continuously to the left endpoint
when the inverse ratio tends to zero.  The endpoint value is zero. -/
theorem inverseDerivativeValue_continuousOn {lambda eta : ℝ} {U : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta)
    (hUeq : ∀ x ∈ Ioc 0 eta,
      HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x)
    (hdenom : ∀ x ∈ Ioc 0 eta,
      0 < ratioDenominator lambda (inverseRatio U) x)
    (hratio0 : Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ContinuousOn (fun x : ℝ ↦
      x / ratioDenominator lambda (inverseRatio U) x) (Icc 0 eta) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hratioSingleton : Tendsto (inverseRatio U)
        (𝓝[({0} : Set ℝ)] (0 : ℝ)) (𝓝 0) := by
      rw [nhdsWithin_singleton]
      simpa only [inverseRatio, div_zero] using
        (tendsto_pure_nhds (inverseRatio U) (0 : ℝ))
    have hratioIci : Tendsto (inverseRatio U)
        (𝓝[Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
      rw [← nhdsGT_sup_nhdsWithin_singleton]
      exact hratio0.sup hratioSingleton
    have hratioIcc : Tendsto (inverseRatio U)
        (𝓝[Icc (0 : ℝ) eta] (0 : ℝ)) (𝓝 0) :=
      hratioIci.mono_left (nhdsWithin_mono 0 Icc_subset_Ici_self)
    have hid : Tendsto (fun x : ℝ ↦ x)
        (𝓝[Icc (0 : ℝ) eta] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ ↦ lambda)
        (𝓝[Icc (0 : ℝ) eta] (0 : ℝ)) (𝓝 lambda) := tendsto_const_nhds
    have hdenlim : Tendsto
        (ratioDenominator lambda (inverseRatio U))
        (𝓝[Icc (0 : ℝ) eta] (0 : ℝ)) (𝓝 lambda) := by
      unfold ratioDenominator
      simpa using (hconst.sub hratioIcc).add (hid.mul (hratioIcc.pow 2))
    have hDlim := hid.div hdenlim hlambda.ne'
    change Tendsto
      ((fun x : ℝ ↦ x) / ratioDenominator lambda (inverseRatio U))
      (𝓝[Icc (0 : ℝ) eta] (0 : ℝ))
      (𝓝 (0 / ratioDenominator lambda (inverseRatio U) 0))
    simpa only [zero_div] using hDlim
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 fun h ↦ hx0 h.symm
    have hxIoc : x ∈ Ioc (0 : ℝ) eta := ⟨hxpos, hx.2⟩
    have hUcontAt : ContinuousAt U x := (hUeq x hxIoc).continuousAt
    have hrcont : ContinuousAt (inverseRatio U) x := by
      unfold inverseRatio
      exact hUcontAt.div continuousAt_id hx0
    have hdencont : ContinuousAt
        (ratioDenominator lambda (inverseRatio U)) x := by
      unfold ratioDenominator
      fun_prop
    exact (continuousAt_id.div hdencont (hdenom x hxIoc).ne').continuousWithinAt

/-- Direct derivative integration at the one-sided endpoint.  An epsilon bound for
`U'(x)/(x/lambda)` is integrated from `0` to `x`; no l'Hopital principle is used. -/
theorem inverseQuadratic_of_derivativeRatio {lambda eta : ℝ} {U D : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hU0 : U 0 = 0) (hD0 : D 0 = 0)
    (hUcont : ContinuousOn U (Icc 0 eta)) (hDcont : ContinuousOn D (Icc 0 eta))
    (hUderiv : ∀ x ∈ Ioo 0 eta, HasDerivAt U (D x) x)
    (hDratio : Tendsto (fun x : ℝ ↦ D x / (x / lambda))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    (fun x : ℝ ↦ U x) ~[𝓝[>] (0 : ℝ)]
      (fun x : ℝ ↦ (2 * lambda)⁻¹ * x ^ (2 : ℝ)) := by
  have hmodelNe : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      (2 * lambda)⁻¹ * x ^ (2 : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by norm_num) hlambda.ne'))
      (Real.rpow_pos_of_pos hx (2 : ℝ)).ne'
  rw [isEquivalent_iff_tendsto_one hmodelNe, Metric.tendsto_nhds]
  intro epsilon hepsilon
  let e : ℝ := min (epsilon / 2) (1 / 2)
  have hepos : 0 < e := lt_min (half_pos hepsilon) (by norm_num)
  have helt : e < epsilon :=
    (min_le_left (epsilon / 2) (1 / 2 : ℝ)).trans_lt (half_lt_self hepsilon)
  have hratioEventually : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      dist (D x / (x / lambda)) 1 < e :=
    (Metric.tendsto_nhds.1 hDratio) e hepos
  obtain ⟨delta, hdelta, hdeltaSub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.1 hratioEventually
  have hcutoff : 0 < min delta eta := lt_min hdelta heta
  filter_upwards [Ioc_mem_nhdsGT hcutoff] with x hx
  have hxeta : x ≤ eta := hx.2.trans (min_le_right delta eta)
  have hxdelta : x ≤ delta := hx.2.trans (min_le_left delta eta)
  have hDcontX : ContinuousOn D (uIcc (0 : ℝ) x) := by
    rw [uIcc_of_le hx.1.le]
    exact hDcont.mono fun s hs ↦ ⟨hs.1, hs.2.trans hxeta⟩
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 x :=
    hDcontX.intervalIntegrable
  have hUint : ContinuousOn U (Icc 0 x) :=
    hUcont.mono fun s hs ↦ ⟨hs.1, hs.2.trans hxeta⟩
  have hFTC : ∫ s in (0 : ℝ)..x, D s = U x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le hUint
      (fun s hs ↦ hUderiv s ⟨hs.1, hs.2.trans_le hxeta⟩) hDint, hU0, sub_zero]
  have hIdInt : ∫ s in (0 : ℝ)..x, s = x ^ 2 / 2 := by
    have hanti : ∀ s ∈ Ioo (0 : ℝ) x,
        HasDerivAt (fun z : ℝ ↦ z ^ 2 / 2) s s := by
      intro s _
      simpa using (hasDerivAt_pow 2 s).div_const 2
    have hint : IntervalIntegrable (fun s : ℝ ↦ s) MeasureTheory.volume 0 x :=
      continuousOn_id.intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le
      (by fun_prop : ContinuousOn (fun z : ℝ ↦ z ^ 2 / 2) (Icc 0 x)) hanti hint
    simpa using h
  have hlowerPoint : ∀ s ∈ Icc (0 : ℝ) x,
      (1 - e) * (s / lambda) ≤ D s := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | hspos
    · simp [hD0]
    · have hsDelta : s ∈ Ioc (0 : ℝ) delta := ⟨hspos, hs.2.trans hxdelta⟩
      have hb := hdeltaSub hsDelta
      change dist (D s / (s / lambda)) 1 < e at hb
      rw [Real.dist_eq] at hb
      have hb' := (abs_lt.mp hb).1
      have hsdiv : 0 < s / lambda := div_pos hspos hlambda
      have heq : (D s / (s / lambda)) * (s / lambda) = D s :=
        div_mul_cancel₀ _ hsdiv.ne'
      nlinarith [mul_le_mul_of_nonneg_right hb'.le hsdiv.le]
  have hupperPoint : ∀ s ∈ Icc (0 : ℝ) x,
      D s ≤ (1 + e) * (s / lambda) := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | hspos
    · simp [hD0]
    · have hsDelta : s ∈ Ioc (0 : ℝ) delta := ⟨hspos, hs.2.trans hxdelta⟩
      have hb := hdeltaSub hsDelta
      change dist (D s / (s / lambda)) 1 < e at hb
      rw [Real.dist_eq] at hb
      have hb' := (abs_lt.mp hb).2
      have hsdiv : 0 < s / lambda := div_pos hspos hlambda
      have heq : (D s / (s / lambda)) * (s / lambda) = D s :=
        div_mul_cancel₀ _ hsdiv.ne'
      nlinarith [mul_le_mul_of_nonneg_right hb'.le hsdiv.le]
  have hlowerInt :
      ∫ s in (0 : ℝ)..x, (1 - e) * (s / lambda) ≤ ∫ s in (0 : ℝ)..x, D s := by
    apply intervalIntegral.integral_mono_on hx.1.le
    · exact (by fun_prop : ContinuousOn (fun s : ℝ ↦ (1 - e) * (s / lambda))
        (uIcc 0 x)).intervalIntegrable
    · exact hDint
    · exact hlowerPoint
  have hupperInt :
      ∫ s in (0 : ℝ)..x, D s ≤ ∫ s in (0 : ℝ)..x, (1 + e) * (s / lambda) := by
    apply intervalIntegral.integral_mono_on hx.1.le
    · exact hDint
    · exact (by fun_prop : ContinuousOn (fun s : ℝ ↦ (1 + e) * (s / lambda))
        (uIcc 0 x)).intervalIntegrable
    · exact hupperPoint
  have hlowerEval :
      ∫ s in (0 : ℝ)..x, (1 - e) * (s / lambda) =
        (1 - e) * (x ^ 2 / (2 * lambda)) := by
    rw [show (fun s : ℝ ↦ (1 - e) * (s / lambda)) =
        fun s ↦ ((1 - e) / lambda) * s by funext s; ring,
      intervalIntegral.integral_const_mul, hIdInt]
    ring
  have hupperEval :
      ∫ s in (0 : ℝ)..x, (1 + e) * (s / lambda) =
        (1 + e) * (x ^ 2 / (2 * lambda)) := by
    rw [show (fun s : ℝ ↦ (1 + e) * (s / lambda)) =
        fun s ↦ ((1 + e) / lambda) * s by funext s; ring,
      intervalIntegral.integral_const_mul, hIdInt]
    ring
  rw [hlowerEval, hFTC] at hlowerInt
  rw [hupperEval, hFTC] at hupperInt
  have hmodelPos : 0 < x ^ 2 / (2 * lambda) :=
    div_pos (sq_pos_of_pos hx.1) (mul_pos zero_lt_two hlambda)
  have hratioLower : 1 - e ≤ U x / (x ^ 2 / (2 * lambda)) :=
    (le_div_iff₀ hmodelPos).2 hlowerInt
  have hratioUpper : U x / (x ^ 2 / (2 * lambda)) ≤ 1 + e :=
    (div_le_iff₀ hmodelPos).2 hupperInt
  have habs : |U x / (x ^ 2 / (2 * lambda)) - 1| ≤ e :=
    abs_le.2 ⟨by linarith, by linarith⟩
  rw [Real.dist_eq]
  have hmodelEq : (2 * lambda)⁻¹ * x ^ (2 : ℝ) = x ^ 2 / (2 * lambda) := by
    rw [Real.rpow_two]
    ring
  change |U x / ((2 * lambda)⁻¹ * x ^ (2 : ℝ)) - 1| < epsilon
  rw [hmodelEq]
  exact habs.trans_lt helt

/-- The `r→0` alternative: derivative bounds are integrated to obtain the quadratic
asymptotic of `U`, then the genuine local inverse is squeezed to the sharp branch of `W`. -/
theorem sharpBranch_of_inverseRatio_tendsto_zero {lambda eta : ℝ} {U W : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hU0 : U 0 = 0) (hW0 : W 0 = 0)
    (hUcont : ContinuousOn U (Icc 0 eta))
    (hWcont : ContinuousWithinAt W (Ici 0) 0)
    (hUeq : ∀ x ∈ Ioc 0 eta,
      HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x)
    (hdenom : ∀ x ∈ Ioc 0 eta,
      0 < ratioDenominator lambda (inverseRatio U) x)
    (hWpos : ∀ y ∈ Ioo 0 (U eta), 0 < W y)
    (hWmap : MapsTo W (Icc 0 (U eta)) (Icc 0 eta))
    (hstrict : StrictMonoOn U (Icc 0 eta))
    (hright : ∀ y ∈ Icc 0 (U eta), U (W y) = y)
    (hratio0 : Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasSharpBranchAtZero lambda W := by
  let D : ℝ → ℝ := fun x ↦ x / ratioDenominator lambda (inverseRatio U) x
  have hid : Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdenlim : Tendsto
      (ratioDenominator lambda (inverseRatio U)) (𝓝[>] (0 : ℝ)) (𝓝 lambda) := by
    unfold ratioDenominator
    have hconst : Tendsto (fun _ : ℝ ↦ lambda) (𝓝[>] (0 : ℝ)) (𝓝 lambda) :=
      tendsto_const_nhds
    have hsub := hconst.sub hratio0
    have hmul := hid.mul (hratio0.pow 2)
    have ht := hsub.add hmul
    change Tendsto (fun x : ℝ ↦
      (lambda - inverseRatio U x) + x * inverseRatio U x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((lambda - 0) + 0 * 0 ^ 2)) at ht
    simpa using ht
  have hDratio : Tendsto (fun x ↦ D x / (x / lambda))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℝ ↦ lambda) (𝓝[>] (0 : ℝ)) (𝓝 lambda) :=
      tendsto_const_nhds
    have ht := hconst.div hdenlim hlambda.ne'
    have ht1 : Tendsto (fun x : ℝ ↦
        lambda / ratioDenominator lambda (inverseRatio U) x)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      change Tendsto ((fun _ : ℝ ↦ lambda) /
        ratioDenominator lambda (inverseRatio U)) (𝓝[>] (0 : ℝ))
        (𝓝 (lambda / lambda)) at ht
      change Tendsto (fun x : ℝ ↦
        lambda / ratioDenominator lambda (inverseRatio U) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (lambda / lambda)) at ht
      simpa [hlambda.ne'] using ht
    apply (tendsto_congr' ?_).2 ht1
    filter_upwards [Ioc_mem_nhdsGT (half_pos heta)] with x hx
    have hxIoc : x ∈ Ioc (0 : ℝ) eta :=
      ⟨hx.1, hx.2.trans (half_lt_self heta).le⟩
    have hdenNe := (hdenom x hxIoc).ne'
    dsimp [D]
    field_simp [hx.1.ne', hlambda.ne', hdenNe]
  have hD0 : D 0 = 0 := by simp [D]
  have hDcont : ContinuousOn D (Icc 0 eta) := by
    simpa only [D] using
      inverseDerivativeValue_continuousOn hlambda heta hUeq hdenom hratio0
  have hquadratic := inverseQuadratic_of_derivativeRatio hlambda heta hU0 hD0
    hUcont hDcont (fun x hx ↦ hUeq x ⟨hx.1, hx.2.le⟩) hDratio
  exact sharpBranch_of_inverse_quadratic hlambda heta hU0 hW0 hWcont hWpos hWmap
    hstrict hright hquadratic

/-- Once A6.4 supplies the ratio-limit alternative, the two internally proved inverse branches
assemble into the exact exclusive disjunction from the source. -/
theorem leftEndpoint_xor_of_inverseRatio_dichotomy {lambda eta : ℝ} {U W : ℝ → ℝ}
    (hlambda : 0 < lambda) (heta : 0 < eta) (hU0 : U 0 = 0) (hW0 : W 0 = 0)
    (hUcont : ContinuousOn U (Icc 0 eta))
    (hWcont : ContinuousWithinAt W (Ici 0) 0)
    (hUeq : ∀ x ∈ Ioc 0 eta,
      HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x)
    (hdenom : ∀ x ∈ Ioc 0 eta,
      0 < ratioDenominator lambda (inverseRatio U) x)
    (hWpos : ∀ x ∈ Ioo 0 eta, 0 < W x)
    (hWposRange : ∀ x ∈ Ioo 0 (U eta), 0 < W x)
    (hWmap : MapsTo W (Icc 0 (U eta)) (Icc 0 eta))
    (hstrict : StrictMonoOn U (Icc 0 eta))
    (hUinv : ∀ y ∈ Icc 0 (U eta), U (W y) = y)
    (hUinvLocal : ∀ y ∈ Icc 0 eta, U (W y) = y)
    (hlimits : Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 0) ∨
      Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 lambda)) :
    HasExactlyOneLeftBranch lambda W := by
  have hnotboth := leftEndpoint_branches_mutually_exclusive (W := W) hlambda
  unfold HasExactlyOneLeftBranch
  rcases hlimits with hzero | hlambdaLimit
  · have hsharp := sharpBranch_of_inverseRatio_tendsto_zero hlambda heta hU0 hW0 hUcont
      hWcont hUeq hdenom hWposRange hWmap hstrict hUinv hzero
    exact Or.inr ⟨hsharp, fun hlinear ↦ hnotboth ⟨hlinear, hsharp⟩⟩
  · have hlinear := linearBranch_of_inverseRatio_tendsto hlambda heta hW0 hWcont
      hWpos hUinvLocal hlambdaLimit
    exact Or.inl ⟨hlinear, fun hsharp ↦ hnotboth ⟨hlinear, hsharp⟩⟩

/-- `lem:u0-dichotomy`: every positive boundary solution has exactly one of the linear
and sharp left-endpoint asymptotics. -/
theorem leftEndpointDichotomy {lambda : ℝ} {W : ℝ → ℝ}
    (hlambda : 0 < lambda) (hW : IsWBoundarySolution lambda W) :
    HasExactlyOneLeftBranch lambda W := by
  obtain ⟨u0, hu0, hHpos, U, hUcont, hUmap, hUinv, hWinv, hUsmooth, hUdata⟩ :=
    leftEndpoint_localInverse_ratio_equations hW
  have hW0 : W 0 = 0 := hW.2.2.2.2.1
  have hWu0 : 0 < W u0 := hW.2.2.2.2.2.2 u0 hu0
  let eta : ℝ := min (W u0 / 2) (u0 / 2)
  have hhalfW : 0 < W u0 / 2 := half_pos hWu0
  have hhalfu : 0 < u0 / 2 := half_pos hu0.1
  have heta : 0 < eta := lt_min hhalfW hhalfu
  have hetaW : eta < W u0 :=
    (min_le_left (W u0 / 2) (u0 / 2)).trans_lt (half_lt_self hWu0)
  have hetau : eta < u0 :=
    (min_le_right (W u0 / 2) (u0 / 2)).trans_lt (half_lt_self hu0.1)
  have hU0 : U 0 = 0 := by
    calc
      U 0 = U (W 0) := congrArg U hW0.symm
      _ = 0 := hUinv 0 ⟨le_rfl, hu0.1.le⟩
  have hUcont0 : ContinuousWithinAt U (Ici 0) 0 := by
    have hwithin := hUcont 0 ⟨by rw [hW0], hWu0.le⟩
    have heq : Icc (W 0) (W u0) =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
      rw [hW0]
      filter_upwards [Iio_mem_nhds hWu0] with x hx
      apply propext
      change (0 ≤ x ∧ x ≤ W u0) ↔ 0 ≤ x
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx.le⟩⟩
    exact hwithin.congr_set heq
  have hUcontEta : ContinuousOn U (Icc 0 eta) :=
    hUcont.mono fun x hx ↦ by
      rw [hW0]
      exact ⟨hx.1, hx.2.trans hetaW.le⟩
  have hUeq : ∀ x ∈ Ioc (0 : ℝ) eta,
      HasDerivAt U (x / ratioDenominator lambda (inverseRatio U) x) x := by
    intro x hx
    exact (hUdata x (by rw [hW0]; exact ⟨hx.1, hx.2.trans_lt hetaW⟩)).1
  have hdenom : ∀ x ∈ Ioc (0 : ℝ) eta,
      0 < ratioDenominator lambda (inverseRatio U) x := by
    intro x hx
    exact (hUdata x (by rw [hW0]; exact ⟨hx.1, hx.2.trans_lt hetaW⟩)).2.1
  have hratioDeriv : ∀ x ∈ Ioo (0 : ℝ) eta,
      HasDerivAt (inverseRatio U)
        ((x / ratioDenominator lambda (inverseRatio U) x - inverseRatio U x) / x) x := by
    intro x hx
    exact (hUdata x (by rw [hW0]; exact ⟨hx.1, hx.2.trans hetaW⟩)).2.2
  have hUdiff : DifferentiableOn ℝ U (Ioo 0 eta) := by
    intro x hx
    exact (hUeq x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
  have hUpos : ∀ x ∈ Ioo (0 : ℝ) eta, 0 < U x := by
    intro x hx
    exact (localInverse_maps_interior hu0.1 hW0 hUmap hWinv
      (by rw [hW0]; exact ⟨hx.1, hx.2.trans hetaW⟩)).1
  have hstrict : StrictMonoOn U (Icc 0 eta) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) eta)
    · exact hUcont.mono fun x hx ↦ by
        rw [hW0]
        exact ⟨hx.1, hx.2.trans hetaW.le⟩
    · rw [interior_Icc]
      intro x hx
      rw [(hUeq x ⟨hx.1, hx.2.le⟩).deriv]
      exact div_pos hx.1 (hdenom x ⟨hx.1, hx.2.le⟩)
  have hWinvEta : ∀ x ∈ Icc 0 eta, W (U x) = x := by
    intro x hx
    exact hWinv x (by rw [hW0]; exact ⟨hx.1, hx.2.trans_lt hetaW |>.le⟩)
  have hUetaLe : U eta ≤ u0 :=
    (hUmap ⟨by rw [hW0]; exact heta.le, hetaW.le⟩).2
  have hUinvRange : ∀ y ∈ Icc 0 (U eta), U (W y) = y := by
    intro y hy
    exact hUinv y ⟨hy.1, hy.2.trans hUetaLe⟩
  have hUinvEta : ∀ y ∈ Icc 0 eta, U (W y) = y := by
    intro y hy
    exact hUinv y ⟨hy.1, hy.2.trans hetau.le⟩
  have hWposEta : ∀ y ∈ Ioo (0 : ℝ) eta, 0 < W y := by
    intro y hy
    exact hW.2.2.2.2.2.2 y ⟨hy.1, (hy.2.trans_le hetau.le).trans hu0.2⟩
  have hUetaMap : U eta ∈ Icc 0 u0 :=
    hUmap ⟨by rw [hW0]; exact heta.le, hetaW.le⟩
  have hWposRange : ∀ y ∈ Ioo (0 : ℝ) (U eta), 0 < W y := by
    intro y hy
    exact hW.2.2.2.2.2.2 y ⟨hy.1, (hy.2.trans_le hUetaLe).trans hu0.2⟩
  have hWstrict : StrictMonoOn W (Icc 0 u0) :=
    strictMonoOn_of_endpointH_pos hW hu0 hHpos
  have hWmapRange : MapsTo W (Icc 0 (U eta)) (Icc 0 eta) := by
    intro y hy
    have hzeroMem : (0 : ℝ) ∈ Icc 0 u0 := ⟨le_rfl, hu0.1.le⟩
    have hyMem : y ∈ Icc 0 u0 := ⟨hy.1, hy.2.trans hUetaLe⟩
    constructor
    · have hmono := hWstrict.monotoneOn hzeroMem hyMem hy.1
      simpa only [hW0] using hmono
    · have hmono := hWstrict.monotoneOn hyMem hUetaMap hy.2
      rw [hWinvEta eta ⟨heta.le, le_rfl⟩] at hmono
      exact hmono
  have hsmallX : ∀ᶠ s in atTop, Real.exp (-s) < eta :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (Iio_mem_nhds heta)
  obtain ⟨S, hS⟩ := eventually_atTop.1 hsmallX
  let rho : ℝ → ℝ := logRatioFlow (inverseRatio U)
  have hflow : ∀ s ∈ Ici S,
      HasDerivAt rho (logRatioFlowRhs lambda rho s) s := by
    intro s hs
    have hx : Real.exp (-s) ∈ Ioo (0 : ℝ) eta := ⟨Real.exp_pos _, hS s hs⟩
    have hr := hratioDeriv _ hx
    apply logRatioFlow_hasDerivAt hr
    have hxne : Real.exp (-s) ≠ 0 := (Real.exp_pos _).ne'
    field_simp [hxne]
  have hcontRho : ContinuousOn rho (Ici S) := by
    intro s hs
    exact (hflow s hs).continuousAt.continuousWithinAt
  have hposRho : ∀ s ∈ Ici S, 0 < rho s := by
    intro s hs
    have hx : Real.exp (-s) ∈ Ioo (0 : ℝ) eta := ⟨Real.exp_pos _, hS s hs⟩
    unfold rho logRatioFlow inverseRatio
    exact div_pos (hUpos _ hx) hx.1
  have hupperRho : ∀ epsilon > 0, ∀ᶠ s in atTop, rho s < lambda + epsilon := by
    intro epsilon hepsilon
    have hrUpper := localInverse_ratio_eventually_lt_lambda_add hlambda hW hu0
      hUcont hUmap hUinv hWinv (fun x hx ↦ (hUdata x hx).2.1) epsilon hepsilon
    exact hrUpper.filter_mono tendsto_exp_neg_atTop_nhdsGT_zero
  have hrhoLimits := logRatioFlow_tendsto_zero_or_lambda hlambda hcontRho hflow
    hposRho hupperRho
  have hlimits : Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 0) ∨
      Tendsto (inverseRatio U) (𝓝[>] (0 : ℝ)) (𝓝 lambda) :=
    hrhoLimits.imp tendsto_of_logRatioFlow_tendsto tendsto_of_logRatioFlow_tendsto
  exact leftEndpoint_xor_of_inverseRatio_dichotomy hlambda heta hU0 hW0 hUcontEta
    hW.continuous.continuousWithinAt hUeq hdenom hWposEta hWposRange hWmapRange
    hstrict hUinvRange hUinvEta hlimits

/-- The positive parameter carried by membership in the admissible set. -/
theorem positive_of_mem_admissible {lambda : ℝ}
    (hadmissible : lambda ∈ admissibleSet) : 0 < lambda :=
  hadmissible.choose

/-- The shooting endpoint equation carried by admissibility, with the same proof witness used
in the canonical `WSolution`. -/
theorem shootingY_one_eq_zero_of_mem_admissible {lambda : ℝ}
    (hadmissible : lambda ∈ admissibleSet) :
    shootingY lambda (positive_of_mem_admissible hadmissible) 1 = 0 := by
  exact hadmissible.choose_spec

/-- Exact source-facing A6 wrapper (`lem:u0-dichotomy`): the canonical admissible boundary
solution has exactly one left branch, expressed as `Xor` by `HasExactlyOneLeftBranch`. -/
theorem leftEndpointDichotomy_source {lambda : ℝ}
    (hadmissible : lambda ∈ admissibleSet) :
    HasExactlyOneLeftBranch lambda
      (WSolution lambda (positive_of_mem_admissible hadmissible)) := by
  exact leftEndpointDichotomy (positive_of_mem_admissible hadmissible)
    (WSolution_isBoundarySolution (positive_of_mem_admissible hadmissible)
      (shootingY_one_eq_zero_of_mem_admissible hadmissible))

end SeriesParallel.Appendix
