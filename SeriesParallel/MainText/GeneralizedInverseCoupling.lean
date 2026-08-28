/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import SeriesParallel.MainText.CDFOperator

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.Kernel.Representation

/-!
# Generalized-inverse coupling and stochastic order

The quantile below is the closed-left-ray generalized inverse on the unit interval.
The real-valued version conjugates it by the measurable sigmoid embedding.  This
gives a concrete common-uniform coupling, rather than an existence interface.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Function unitInterval
open scoped ENNReal unitInterval

namespace SeriesParallel.MainText

/-! ## A public generalized inverse on the unit interval -/

/-- The generalized inverse of the closed-left-ray distribution function on `[0,1]`. -/
noncomputable def unitQuantile (mu : Measure I) (t : I) : I :=
  sSup {x | mu.real (Icc 0 x) < t}

/-- The generalized inverse is measurable. -/
theorem measurable_unitQuantile (mu : Measure I) [IsProbabilityMeasure mu] :
    Measurable (unitQuantile mu) := by
  let f := fun (_ : Unit) (t : I) ↦
    sSup {x | mu.real (Icc 0 x) < t}
  have hjoint : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a ↦ ?_
    simp only [preimage, uncurry, mem_Ioi]
    have hmono : Monotone (fun x ↦ mu.real (Icc 0 x)) :=
      fun x y hxy ↦ measureReal_mono (by gcongr)
    have hsSup : {z : Unit × I | a < f z.1 z.2} =
        ⋃ (q : ℚ) (hqI : (↑q : ℝ) ∈ I) (_ : a < (q : ℝ)),
          {z | mu.real (Icc 0 ⟨q, hqI⟩) < z.2} := by
      ext z
      simp_all only [lt_sSup_iff, Set.mem_setOf_eq, Subtype.exists,
        mem_Icc, Rat.cast_nonneg, Set.mem_iUnion, exists_prop,
        exists_and_left, f]
      constructor
      · rintro ⟨y, hyI, hymem, (hay : a.1 < y)⟩
        obtain ⟨q, haq, hqy⟩ := exists_rat_btwn hay
        refine ⟨q, haq, ⟨?_, hqy.le.trans hyI.2⟩,
          lt_of_lt_of_le' hymem (hmono hqy.le)⟩
        simp [← Rat.cast_nonneg (K := ℝ), a.2.1.trans haq.le]
      · intro hz
        obtain ⟨q, haq, hqI, hqmem⟩ := hz
        refine ⟨q, ⟨by simp [hqI.1], hqI.2⟩, hqmem, ?_⟩
        change a.1 < q
        simp [haq]
    rw [hsSup]
    refine MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun hqI ↦
      MeasurableSet.iUnion fun _ ↦ ?_
    exact measurableSet_lt measurable_const measurable_snd.subtype_val
  have hsection : Measurable (fun t : I ↦ uncurry f ((), t)) :=
    hjoint.comp (measurable_const.prodMk measurable_id)
  change Measurable (fun t : I ↦
    sSup {x | mu.real (Icc 0 x) < t})
  exact hsection

/-- Pushing uniform measure through `unitQuantile` recovers the input law. -/
theorem unitQuantile_map (mu : Measure I) [IsProbabilityMeasure mu] :
    (volume : Measure I).map (unitQuantile mu) = mu := by
  apply ((volume : Measure I).map (unitQuantile mu)).ext_of_Iic mu
  intro x
  have hIic : Iic x = Icc 0 x := by
    ext y
    simp
  have hmuI : mu.real (Icc 0 x) ∈ I :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  rw [Measure.map_apply (measurable_unitQuantile mu) measurableSet_Iic]
  conv_rhs => rw [hIic]
  rw [← ofReal_measureReal (measure_ne_top mu (Icc 0 x))]
  rw [← unitInterval.volume_Iic ⟨mu.real (Icc 0 x), hmuI⟩]
  congr 1
  ext t
  simp only [Set.mem_preimage, mem_Iic]
  constructor
  · intro ht
    change t ≤ mu.real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, t.2.2]
    let g := fun y ↦ mu.real (Icc 0 y)
    letI : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g)
      continuousWithinAt_const ?_ ?_
    · let c := ProbabilityTheory.cdf (mu.map Subtype.val)
      have hc := continuousWithinAt_Ioi_iff_Ici.mpr (c.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real mu]
      exact hc.comp (Continuous.continuousWithinAt (by fun_prop))
        fun y hy ↦ hy
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      by_contra hnot
      simp only [unitQuantile, sSup_le_iff] at ht
      specialize ht y (lt_of_not_ge hnot)
      grind
  · intro ht
    simp only [unitQuantile, sSup_le_iff]
    intro c hc
    by_contra hnot
    have hbad : ¬mu.real (Icc 0 x) ≤ mu.real (Icc 0 c) :=
      not_le.mpr (lt_of_le_of_lt' ht hc)
    apply hbad
    apply measureReal_mono (h₂ := measure_ne_top mu (Icc 0 c))
    intro y hy
    exact ⟨hy.1, hy.2.trans (le_of_not_ge hnot)⟩

/-! ## Real quantiles via the sigmoid measurable embedding -/

/-- The input law transported into the open sigmoid range in `[0,1]`. -/
noncomputable def sigmoidLaw (mu : Measure ℝ) : Measure I :=
  mu.map unitInterval.sigmoid

private theorem sigmoidLaw_isProbabilityMeasure (mu : Measure ℝ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (sigmoidLaw mu) := by
  unfold sigmoidLaw
  exact Measure.isProbabilityMeasure_map
    measurableEmbedding_sigmoid.measurable.aemeasurable

/-- A concrete generalized inverse for a real probability law. -/
noncomputable def realQuantile (mu : Measure ℝ) (t : I) : ℝ :=
  measurableEmbedding_sigmoid.invFun (unitQuantile (sigmoidLaw mu) t)

/-- The real generalized inverse is measurable. -/
theorem measurable_realQuantile (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Measurable (realQuantile mu) := by
  letI : IsProbabilityMeasure (sigmoidLaw mu) :=
    sigmoidLaw_isProbabilityMeasure mu
  unfold realQuantile
  exact measurableEmbedding_sigmoid.measurable_invFun.comp
    (measurable_unitQuantile (sigmoidLaw mu))

/-- The common-uniform real quantile has exactly the requested law. -/
theorem realQuantile_map (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (volume : Measure I).map (realQuantile mu) = mu := by
  letI : IsProbabilityMeasure (sigmoidLaw mu) :=
    sigmoidLaw_isProbabilityMeasure mu
  have hrecover : mu =
      (sigmoidLaw mu).map measurableEmbedding_sigmoid.invFun := by
    unfold sigmoidLaw
    rw [Measure.map_map measurableEmbedding_sigmoid.measurable_invFun
      measurableEmbedding_sigmoid.measurable]
    rw [measurableEmbedding_sigmoid.leftInverse_invFun.id]
    rw [Measure.map_id]
  change (volume : Measure I).map
    (measurableEmbedding_sigmoid.invFun ∘
      unitQuantile (sigmoidLaw mu)) = mu
  rw [← Measure.map_map
    measurableEmbedding_sigmoid.measurable_invFun
    (measurable_unitQuantile (sigmoidLaw mu))]
  rw [unitQuantile_map]
  exact hrecover.symm

/-! ## Stochastic order and the common-uniform coupling -/

/-- Closed-left-ray stochastic order.  `CDFOrdered mu nu` means that `mu` is
stochastically larger than `nu`. -/
def CDFOrdered (mu nu : Measure ℝ) : Prop :=
  ∀ x, ProbabilityTheory.cdf mu x ≤ ProbabilityTheory.cdf nu x

theorem CDFOrdered.refl (mu : Measure ℝ) : CDFOrdered mu mu :=
  fun _ ↦ le_rfl

theorem CDFOrdered.trans {mu nu xi : Measure ℝ}
    (hmunu : CDFOrdered mu nu) (hnuxi : CDFOrdered nu xi) :
    CDFOrdered mu xi :=
  fun x ↦ (hmunu x).trans (hnuxi x)

private theorem sigmoidLaw_Icc (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (x : ℝ) :
    (sigmoidLaw mu).real (Icc 0 (unitInterval.sigmoid x)) =
      ProbabilityTheory.cdf mu x := by
  unfold sigmoidLaw
  rw [map_measureReal_apply measurableEmbedding_sigmoid.measurable
    measurableSet_Icc]
  have hpreimage : unitInterval.sigmoid ⁻¹'
      Icc 0 (unitInterval.sigmoid x) = Iic x := by
    ext y
    simp only [Set.mem_preimage, mem_Icc, mem_Iic]
    constructor
    · exact fun hy ↦ unitInterval.sigmoid_le_iff.mp hy.2
    · exact fun hy ↦ ⟨(unitInterval.sigmoid_pos y).le,
        unitInterval.sigmoid_le_iff.mpr hy⟩
  rw [hpreimage]
  exact (ProbabilityTheory.cdf_eq_real mu x).symm

private theorem sigmoidLaw_ordered {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) :
    ∀ x : I, (sigmoidLaw mu).real (Icc 0 x) ≤
      (sigmoidLaw nu).real (Icc 0 x) := by
  letI : IsProbabilityMeasure (sigmoidLaw mu) :=
    sigmoidLaw_isProbabilityMeasure mu
  letI : IsProbabilityMeasure (sigmoidLaw nu) :=
    sigmoidLaw_isProbabilityMeasure nu
  intro x
  rcases eq_or_ne x 0 with rfl | hxzero
  · have hzero (xi : Measure ℝ) [IsProbabilityMeasure xi] :
        (sigmoidLaw xi).real (Icc 0 0) = 0 := by
      unfold sigmoidLaw
      rw [map_measureReal_apply measurableEmbedding_sigmoid.measurable
        measurableSet_Icc]
      have hpreimage : unitInterval.sigmoid ⁻¹' Icc 0 0 = ∅ := by
        ext y
        simp only [Set.mem_preimage, mem_Icc, Set.mem_empty_iff_false,
          iff_false]
        exact fun hy ↦ (not_le_of_gt (unitInterval.sigmoid_pos y)) hy.2
      rw [hpreimage]
      simp
    rw [hzero mu, hzero nu]
  · rcases eq_or_ne x 1 with rfl | hxone
    · rw [← univ_eq_Icc, probReal_univ, probReal_univ]
    · have hxpos : 0 < x := lt_of_le_of_ne x.2.1 (Ne.symm hxzero)
      have hxlt : x < 1 := lt_of_le_of_ne x.2.2 hxone
      have hxrange : x ∈ range unitInterval.sigmoid := by
        rw [unitInterval.range_sigmoid]
        exact ⟨hxpos, hxlt⟩
      obtain ⟨y, rfl⟩ := hxrange
      rw [sigmoidLaw_Icc, sigmoidLaw_Icc]
      exact h y

/-- CDF order reverses the pointwise order of unit generalized inverses. -/
theorem unitQuantile_antitone {mu nu : Measure I}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : ∀ x, mu.real (Icc 0 x) ≤ nu.real (Icc 0 x)) (t : I) :
    unitQuantile nu t ≤ unitQuantile mu t := by
  unfold unitQuantile
  apply sSup_le_sSup
  intro x hx
  exact (h x).trans_lt hx

private theorem unitQuantile_sigmoidLaw_mem_Ioo (mu : Measure ℝ)
    [IsProbabilityMeasure mu] {t : I} (ht : t ∈ Ioo 0 1) :
    unitQuantile (sigmoidLaw mu) t ∈ Ioo 0 1 := by
  letI : IsProbabilityMeasure (sigmoidLaw mu) :=
    sigmoidLaw_isProbabilityMeasure mu
  have hlowEventually : ∀ᶠ y in atBot,
      ProbabilityTheory.cdf mu y < t :=
    (ProbabilityTheory.tendsto_cdf_atBot mu).eventually
      (Iio_mem_nhds ht.1)
  obtain ⟨yLow, hyLow⟩ := hlowEventually.exists
  have hlowMem : unitInterval.sigmoid yLow ∈
      {q : I | (sigmoidLaw mu).real (Icc 0 q) < t} := by
    rw [Set.mem_setOf_eq, sigmoidLaw_Icc]
    exact hyLow
  have hlower : 0 < unitQuantile (sigmoidLaw mu) t :=
    (unitInterval.sigmoid_pos yLow).trans_le (le_sSup hlowMem)
  have hhighEventually : ∀ᶠ y in atTop,
      t < ProbabilityTheory.cdf mu y :=
    (ProbabilityTheory.tendsto_cdf_atTop mu).eventually
      (Ioi_mem_nhds ht.2)
  obtain ⟨yHigh, hyHigh⟩ := hhighEventually.exists
  have hupper : unitQuantile (sigmoidLaw mu) t ≤
      unitInterval.sigmoid yHigh := by
    unfold unitQuantile
    apply sSup_le
    intro q hq
    by_contra hnot
    have hstrict : unitInterval.sigmoid yHigh < q := lt_of_not_ge hnot
    have hmono : (sigmoidLaw mu).real
        (Icc 0 (unitInterval.sigmoid yHigh)) ≤
        (sigmoidLaw mu).real (Icc 0 q) := by
      apply measureReal_mono
        (h₂ := measure_ne_top (sigmoidLaw mu) (Icc 0 q))
      intro z hz
      exact ⟨hz.1, hz.2.trans hstrict.le⟩
    rw [sigmoidLaw_Icc] at hmono
    change (sigmoidLaw mu).real (Icc 0 q) < t at hq
    linarith
  exact ⟨hlower, hupper.trans_lt (unitInterval.sigmoid_lt_one yHigh)⟩

private theorem sigmoid_invFun_apply {q : I} (hq : q ∈ Ioo 0 1) :
    unitInterval.sigmoid (measurableEmbedding_sigmoid.invFun q) = q := by
  rw [← unitInterval.range_sigmoid] at hq
  obtain ⟨x, rfl⟩ := hq
  rw [measurableEmbedding_sigmoid.leftInverse_invFun]

private theorem volume_ae_mem_Ioo :
    ∀ᵐ t ∂(volume : Measure I), t ∈ Ioo 0 1 := by
  rw [ae_iff]
  have hboundary : {t : I | ¬t ∈ Ioo 0 1} = ({0} ∪ {1}) := by
    ext t
    simp only [Set.mem_setOf_eq, mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff]
    constructor
    · intro ht
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      · exact Or.inr (le_antisymm t.2.2 (le_of_not_gt fun hlt ↦
          ht ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), hlt⟩))
    · rintro (rfl | rfl) <;> simp
  rw [hboundary]
  exact measure_union_null (measure_singleton 0) (measure_singleton 1)

/-- The common-uniform coupling realizes stochastic order almost surely. -/
theorem realQuantile_antitone_ae {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) :
    realQuantile nu ≤ᵐ[volume] realQuantile mu := by
  letI : IsProbabilityMeasure (sigmoidLaw mu) :=
    sigmoidLaw_isProbabilityMeasure mu
  letI : IsProbabilityMeasure (sigmoidLaw nu) :=
    sigmoidLaw_isProbabilityMeasure nu
  have hunit (t : I) : unitQuantile (sigmoidLaw nu) t ≤
      unitQuantile (sigmoidLaw mu) t :=
    unitQuantile_antitone (sigmoidLaw_ordered h) t
  filter_upwards [volume_ae_mem_Ioo] with t ht
  have hmu := unitQuantile_sigmoidLaw_mem_Ioo mu ht
  have hnu := unitQuantile_sigmoidLaw_mem_Ioo nu ht
  unfold realQuantile
  rw [← unitInterval.sigmoid_le_iff]
  rw [sigmoid_invFun_apply hnu, sigmoid_invFun_apply hmu]
  exact hunit t

/-! ## Translation compatibility -/

/-- Translating the concrete quantile coupling translates its represented law. -/
theorem realQuantile_add_map (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (a : ℝ) :
    (volume : Measure I).map (fun t ↦ realQuantile mu t + a) =
      translateLaw a mu := by
  unfold translateLaw
  calc
    (volume : Measure I).map (fun t ↦ realQuantile mu t + a) =
        ((volume : Measure I).map (realQuantile mu)).map
          (fun x ↦ x + a) := by
      rw [Measure.map_map (by fun_prop) (measurable_realQuantile mu)]
      rfl
    _ = mu.map (fun x ↦ x + a) := by rw [realQuantile_map]

/-- Translation preserves closed-left-ray stochastic order. -/
theorem CDFOrdered.translate {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) (a : ℝ) :
    CDFOrdered (translateLaw a mu) (translateLaw a nu) := by
  intro x
  rw [congrFun (cdf_translateLaw a mu) x]
  rw [congrFun (cdf_translateLaw a nu) x]
  exact h (x - a)

/-! ## Monotone gates under the quantile coupling -/

private noncomputable def quantilePair (mu : Measure ℝ) (z : I × I) :
    ℝ × ℝ :=
  (realQuantile mu z.1, realQuantile mu z.2)

private theorem measurable_quantilePair (mu : Measure ℝ)
    [IsProbabilityMeasure mu] : Measurable (quantilePair mu) := by
  exact ((measurable_realQuantile mu).comp measurable_fst).prodMk
    ((measurable_realQuantile mu).comp measurable_snd)

private theorem quantilePair_map (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    ((volume : Measure I).prod volume).map (quantilePair mu) =
      mu.prod mu := by
  change ((volume : Measure I).prod volume).map
    (Prod.map (realQuantile mu) (realQuantile mu)) = mu.prod mu
  rw [← Measure.map_prod_map (volume : Measure I) volume
    (measurable_realQuantile mu) (measurable_realQuantile mu)]
  rw [realQuantile_map]

private theorem seriesCDF_eq_quantileEvent (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    seriesCDF mu x =
      ((volume : Measure I).prod volume).real
        {z | logSeriesGate (realQuantile mu z.1)
          (realQuantile mu z.2) ≤ x} := by
  letI : IsProbabilityMeasure (seriesLaw mu) :=
    seriesLaw_isProbabilityMeasure mu
  unfold seriesCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold seriesLaw
  rw [map_measureReal_apply measurable_logSeriesGate_pair measurableSet_Iic]
  rw [← quantilePair_map mu]
  rw [map_measureReal_apply (measurable_quantilePair mu)]
  · rfl
  · exact measurableSet_le measurable_logSeriesGate_pair measurable_const

private theorem parallelCDF_eq_quantileEvent (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (x : ℝ) :
    parallelCDF mu x =
      ((volume : Measure I).prod volume).real
        {z | logParallelGate .resistance (realQuantile mu z.1)
          (realQuantile mu z.2) ≤ x} := by
  letI : IsProbabilityMeasure (parallelLaw mu) :=
    parallelLaw_isProbabilityMeasure mu
  unfold parallelCDF
  rw [ProbabilityTheory.cdf_eq_real]
  unfold parallelLaw
  rw [map_measureReal_apply measurable_logResistanceParallelGate_pair
    measurableSet_Iic]
  rw [← quantilePair_map mu]
  rw [map_measureReal_apply (measurable_quantilePair mu)]
  · rfl
  · exact measurableSet_le
      measurable_logResistanceParallelGate_pair measurable_const

private theorem quantilePair_antitone_ae {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) :
    ∀ᵐ z ∂((volume : Measure I).prod volume),
      realQuantile nu z.1 ≤ realQuantile mu z.1 ∧
        realQuantile nu z.2 ≤ realQuantile mu z.2 := by
  have hq := realQuantile_antitone_ae h
  apply (Measure.ae_prod_iff_ae_ae ?_).2
  · filter_upwards [hq] with u hu
    filter_upwards [hq] with v hv
    exact ⟨hu, hv⟩
  · exact (measurableSet_le
      ((measurable_realQuantile nu).comp measurable_fst)
      ((measurable_realQuantile mu).comp measurable_fst)).inter
      (measurableSet_le
        ((measurable_realQuantile nu).comp measurable_snd)
        ((measurable_realQuantile mu).comp measurable_snd))

/-- The series-gate CDF preserves closed-left-ray stochastic order. -/
theorem seriesCDF_mono_of_CDFOrdered {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) (x : ℝ) :
    seriesCDF mu x ≤ seriesCDF nu x := by
  rw [seriesCDF_eq_quantileEvent, seriesCDF_eq_quantileEvent]
  have hsubset :
      {z : I × I | logSeriesGate (realQuantile mu z.1)
        (realQuantile mu z.2) ≤ x} ≤ᵐ[(volume : Measure I).prod volume]
      {z : I × I | logSeriesGate (realQuantile nu z.1)
        (realQuantile nu z.2) ≤ x} := by
    filter_upwards [quantilePair_antitone_ae h] with z hz hzx
    have hgate : logSeriesGate (realQuantile nu z.1)
        (realQuantile nu z.2) ≤
        logSeriesGate (realQuantile mu z.1)
          (realQuantile mu z.2) :=
      (logSeriesGate_mono_left hz.1).trans
        (logSeriesGate_mono_right hz.2)
    exact hgate.trans hzx
  unfold Measure.real
  apply ENNReal.toReal_mono
    (measure_ne_top ((volume : Measure I).prod volume) _)
  exact measure_mono_ae hsubset

/-- The resistance-parallel CDF preserves closed-left-ray stochastic order. -/
theorem parallelCDF_mono_of_CDFOrdered {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) (x : ℝ) :
    parallelCDF mu x ≤ parallelCDF nu x := by
  rw [parallelCDF_eq_quantileEvent, parallelCDF_eq_quantileEvent]
  have hsubset :
      {z : I × I | logParallelGate .resistance (realQuantile mu z.1)
        (realQuantile mu z.2) ≤ x} ≤ᵐ[(volume : Measure I).prod volume]
      {z : I × I | logParallelGate .resistance (realQuantile nu z.1)
        (realQuantile nu z.2) ≤ x} := by
    filter_upwards [quantilePair_antitone_ae h] with z hz hzx
    have hgate : logParallelGate .resistance (realQuantile nu z.1)
        (realQuantile nu z.2) ≤
        logParallelGate .resistance (realQuantile mu z.1)
          (realQuantile mu z.2) :=
      (logParallelGate_mono_left .resistance hz.1).trans
        (logParallelGate_mono_right .resistance hz.2)
    exact hgate.trans hzx
  unfold Measure.real
  apply ENNReal.toReal_mono
    (measure_ne_top ((volume : Measure I).prod volume) _)
  exact measure_mono_ae hsubset

/-- The one-step CDF operator preserves the stochastic-order direction used in
barrier iteration. -/
theorem cdfOperator_mono_of_CDFOrdered (p : unitInterval)
    {mu nu : Measure ℝ} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (h : CDFOrdered mu nu) (x : ℝ) :
    cdfOperator p mu x ≤ cdfOperator p nu x := by
  unfold cdfOperator
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (seriesCDF_mono_of_CDFOrdered h x) p.2.1
  · exact mul_le_mul_of_nonneg_left
      (parallelCDF_mono_of_CDFOrdered h x) (sub_nonneg.mpr p.2.2)

/-! ## Expectation order and the atom-at-zero regression -/

/-- For integrable laws, closed-left-ray stochastic order gives the expected
first-moment order in the same direction as the quantile coupling. -/
theorem integral_id_mono_of_CDFOrdered {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : CDFOrdered mu nu) (hmu : Integrable id mu)
    (hnu : Integrable id nu) :
    (∫ x, x ∂nu) ≤ ∫ x, x ∂mu := by
  have hmuPreserving : MeasurePreserving (realQuantile mu)
      (volume : Measure I) mu :=
    ⟨measurable_realQuantile mu, realQuantile_map mu⟩
  have hnuPreserving : MeasurePreserving (realQuantile nu)
      (volume : Measure I) nu :=
    ⟨measurable_realQuantile nu, realQuantile_map nu⟩
  have hqmu : Integrable (realQuantile mu) (volume : Measure I) := by
    simpa only [id_eq, id_comp] using
      (hmuPreserving.integrable_comp aestronglyMeasurable_id).2 hmu
  have hqnu : Integrable (realQuantile nu) (volume : Measure I) := by
    simpa only [id_eq, id_comp] using
      (hnuPreserving.integrable_comp aestronglyMeasurable_id).2 hnu
  have hmuIntegral : (∫ t : I, realQuantile mu t) = ∫ x, x ∂mu := by
    have hmap := integral_map (μ := (volume : Measure I))
      (measurable_realQuantile mu).aemeasurable
      (f := id) aestronglyMeasurable_id
    rw [realQuantile_map mu] at hmap
    simpa only [id_eq] using hmap.symm
  have hnuIntegral : (∫ t : I, realQuantile nu t) = ∫ x, x ∂nu := by
    have hmap := integral_map (μ := (volume : Measure I))
      (measurable_realQuantile nu).aemeasurable
      (f := id) aestronglyMeasurable_id
    rw [realQuantile_map nu] at hmap
    simpa only [id_eq] using hmap.symm
  rw [← hnuIntegral, ← hmuIntegral]
  exact integral_mono_ae hqnu hqmu (realQuantile_antitone_ae h)

/-- Push a law through the nonnegative-part map.  This is the exact law used
when an upper barrier is truncated at zero. -/
noncomputable def nonnegativePartLaw (mu : Measure ℝ) : Measure ℝ :=
  mu.map fun x ↦ max x 0

theorem nonnegativePartLaw_isProbabilityMeasure (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (nonnegativePartLaw mu) := by
  unfold nonnegativePartLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Regression theorem: truncation creates precisely the original lower-tail
mass as an atom at zero.  No absolute-continuity hypothesis is used. -/
theorem nonnegativePartLaw_atom_zero (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    nonnegativePartLaw mu {0} = mu (Iic 0) := by
  unfold nonnegativePartLaw
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℝ))]
  congr 1
  ext x
  simp

/-- The CDF of zero truncation has the expected jump at zero. -/
theorem cdf_nonnegativePartLaw (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (x : ℝ) :
    ProbabilityTheory.cdf (nonnegativePartLaw mu) x =
      if x < 0 then 0 else ProbabilityTheory.cdf mu x := by
  letI : IsProbabilityMeasure (nonnegativePartLaw mu) :=
    nonnegativePartLaw_isProbabilityMeasure mu
  rw [ProbabilityTheory.cdf_eq_real]
  unfold nonnegativePartLaw
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  by_cases hx : x < 0
  · rw [if_pos hx]
    have hpreimage : (fun y : ℝ ↦ max y 0) ⁻¹' Iic x = ∅ := by
      ext y
      simp only [Set.mem_preimage, mem_Iic, Set.mem_empty_iff_false,
        iff_false]
      exact fun hy ↦ (not_le_of_gt hx) ((le_max_right y 0).trans hy)
    rw [hpreimage]
    simp
  · rw [if_neg hx]
    have hxzero : 0 ≤ x := le_of_not_gt hx
    have hpreimage : (fun y : ℝ ↦ max y 0) ⁻¹' Iic x = Iic x := by
      ext y
      simp [hxzero]
    rw [hpreimage]
    exact (ProbabilityTheory.cdf_eq_real mu x).symm

/-- The generalized inverse reconstruction remains exact for the truncated law,
including its atom at zero. -/
theorem realQuantile_map_nonnegativePartLaw (mu : Measure ℝ)
    [IsProbabilityMeasure mu] :
    (volume : Measure I).map (realQuantile (nonnegativePartLaw mu)) =
      nonnegativePartLaw mu := by
  letI : IsProbabilityMeasure (nonnegativePartLaw mu) :=
    nonnegativePartLaw_isProbabilityMeasure mu
  exact realQuantile_map (nonnegativePartLaw mu)

end SeriesParallel.MainText
