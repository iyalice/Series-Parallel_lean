# Main-text manuscript–Lean source map

Authoritative manuscript: `Distance_and_resistance_SPA_revised_blue.tex`. This is the exact main-text subset of
[`SOURCE_MAP.md`](SOURCE_MAP.md), ending before `\appendix`. It contains **98**
active labels in physical TeX order.

| TeX label | Label line / TeX owner | Kind | Implementation owner | Lean declaration | Module | Status | Trust boundary |
|---|---:|---|---|---|---|---|---|
| `sec:introduction` | 149 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:main-results` | 230 / main | section | manuscript | — | — | doc-only | doc-only |
| `fig:series-parallel-replacement` | 303 / main | figure | manuscript | — | — | doc-only | doc-only |
| `thm:logarithmic-speeds` | 312 / main | theorem | main | `GraphSemantics.graphLogarithmicSpeeds; logarithmicSpeeds` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:full-range-L1` | 320 / main | equation | main | `logarithmicSpeeds` | `MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:supercritical-speed-bounds` | 331 / main | equation | main | `supercritical_logarithmic_speed_bounds` | `MainText.RemainingParameters` | proved | standard |
| `thm:first-moment-logarithmic-rates` | 336 / main | theorem | main | `GraphSemantics.graphFirstMomentLogarithmicRates; firstMomentLogarithmicRates` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:resistance-first-moment-dichotomy` | 345 / main | equation | main | `gammaR_ereal_eq_max_vR_paperLog` | `MainText.RemainingParameters` | proved | standard |
| `eq:supercritical-resistance-identification` | 354 / main | equation | main | `gammaR_eq_vR_supercritical` | `MainText.JensenAndCenter` | proved | standard |
| `fig:resistance-speed-comparison` | 427 / main | figure | manuscript | — | — | doc-only | doc-only |
| `thm:near-critical-speed` | 431 / main | theorem | main | `GraphSemantics.graphResistanceSpeedNearCritical; resistanceSpeedNearCritical` | `MainText.GraphSemantics.MainTheorems; MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:main-W-bvp` | 439 / main | equation | main | `lambdaStar_isLeast_mainAdmissible` | `MainText.NearCriticalAssembly` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:main-near-critical-limit` | 449 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:resistance-first-moment-near-critical` | 457 / main | equation | main | `gammaR_plus_isEquivalent_of_vR; gammaR_minus_isEquivalent_of_vR` | `MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `prop_G` | 521 / main | equation | main | `upperBarrier_global_translation; upperBarrier_CDF_translation_induction; integrable_id_upperBarrierLaw` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `sec:organization-conventions` | 611 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:preliminaries` | 652 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:gate-properties` | 664 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:unified-rde` | 696 / main | equation | main | `Z_succ; root_subtrees_indep; left_right_Z_indep` | `MainText.RandomModel; MainText.LogarithmicDrift; MainText.StructuralProperties` | proved | internal/mathlib |
| `eq:gate-translation` | 730 / main | equation | main | `logSeriesGate_translation; logParallelGate_translation` | `MainText.LogGates` | proved | internal/mathlib |
| `eq:log-series-gate` | 743 / main | equation | main | `logSeriesGate_eq_max_add_h; logParallelGate_eq_min_sub_h` | `MainText.LogGates` | proved | internal/mathlib |
| `lem:logarithmic-drift` | 753 / main | lemma | main | `X_succ_hasLaw; logarithmic_drift` | `MainText.LogarithmicDrift` | proved | standard |
| `eq:log-rde` | 763 / main | equation | main | `X_succ_hasLaw` | `MainText.LogarithmicDrift` | proved | internal/mathlib |
| `eq:drift-identity` | 771 / main | equation | main | `LogarithmicDrift.logarithmic_drift` | `MainText.LogarithmicDrift` | proved | internal/mathlib |
| `sec:canonical-refinement-coupling` | 787 / main | section | manuscript | — | — | doc-only | doc-only |
| `prop:conditional-refinement` | 797 / main | proposition | main | `conditional_refinement_core` | `MainText.ConditionalRefinement` | proved | standard |
| `lem:deterministic-bound` | 811 / main | lemma | main | `adjacent_Z_rpow; X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText.AdjacentBounds` | proved | standard |
| `eq:adjacent-Z` | 818 / main | equation | main | `adjacent_Z_rpow` | `MainText.AdjacentBounds` | proved | internal/mathlib |
| `eq:deterministic-bound` | 829 / main | equation | main | `X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText.AdjacentBounds` | proved | internal/mathlib |
| `lem:first-moment-bounds` | 845 / main | lemma | main | `firstMoment_succ_lower_bound; firstMoment_geometric_bounds` | `MainText.FirstMomentBounds` | proved | standard |
| `eq:first-moment-recursion` | 851 / main | equation | main | `firstMoment_succ_lower_bound` | `MainText.FirstMomentBounds` | proved | internal/mathlib |
| `lem:resistance-duality` | 872 / main | lemma | main | `log_resistanceValue_complement; complementEnvironment_map` | `MainText.RandomModel; MainText.TreeEnvironment` | proved | standard |
| `eq:resistance-duality` | 877 / main | equation | main | `resistanceValue_complement; log_resistanceValue_complement` | `MainText.RandomModel` | proved | internal/mathlib |
| `sec:cdf-operator` | 882 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:CDF-operator-definition` | 899 / main | equation | main | `oneStepLaw; cdfOperator; oneStepLaw_hasCDF` | `MainText.CDFOperator` | proved | internal/mathlib |
| `lem:exact-cdf` | 920 / main | lemma | main | `exact_cdf_operator_density; cdfOperator_mono_of_CDFOrdered; cdfOperator_translate` | `MainText.DensityGateRegions; MainText.GeneralizedInverseCoupling; MainText.CDFOperator` | proved | standard |
| `eq:series-parallel-cdf` | 927 / main | equation | main | `seriesCDF_density_formula; parallelCDF_density_formula` | `MainText.DensityGateRegions` | proved | internal/mathlib |
| `eq:exact-cdf-operator` | 933 / main | equation | main | `exact_cdf_operator_density` | `MainText.DensityGateRegions` | proved | internal/mathlib |
| `sec:ballistic-proof` | 1024 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:first-moment-exponent` | 1047 / main | section | manuscript | — | — | doc-only | doc-only |
| `lem:first-moment-submultiplicativity` | 1050 / main | lemma | main | `firstMoment_submultiplicative; normalizedLogFirstMoment_tendsto_feketeLimit` | `MainText.FirstMomentSubmultiplicative` | proved | standard |
| `eq:first-moment-submultiplicativity` | 1054 / main | equation | main | `firstMoment_submultiplicative` | `MainText.FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `eq:annealed-fekete` | 1060 / main | equation | main | `normalizedLogFirstMoment_tendsto_feketeLimit` | `MainText.FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `sec:annealed-to-typical` | 1113 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:jensen-gap` | 1117 / main | equation | main | `JensenBasic.jensenGap; jensenGap_nonneg` | `MainText.JensenBasic` | proved | internal/mathlib |
| `prop:bounded-Jensen-gap` | 1127 / main | proposition | main | `jensenGap_le_uniform_bound; normalizedMeanLog_tendsto_firstMomentLimit` | `MainText.JensenAndCenter` | proved | standard |
| `eq:mean-log-limit` | 1137 / main | equation | main | `normalizedMeanLog_tendsto_firstMomentLimit` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `lem:center-tracking` | 1146 / main | lemma | main | `centered_X_uniform_bound; centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `MainText.JensenAndCenter` | proved | standard |
| `eq:uniform-width` | 1153 / main | equation | main | `centered_X_uniform_bound` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `eq:center-tracking` | 1159 / main | equation | main | `centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `eq:fixed-supercritical-convergence` | 1213 / main | equation | main | `convergesASAndL1AtLinearRate_supercritical` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `lem:normalized-L2` | 1239 / main | lemma | main | `normalizedSecondMoment_le_bound` | `MainText.NormalizedSecondMoment` | proved | standard |
| `eq:normalized-L2-recursion` | 1267 / main | equation | main | `normalizedSecondMoment_succ_le` | `MainText.NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:Paley-Zygmund` | 1279 / main | equation | main | `paleyZygmund_half_probability_lower_bound` | `MainText.NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:jensen-event-comparison` | 1284 / main | equation | main | `jensenGap_le_uniform_bound` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `eq:Jensen-gap-bound` | 1300 / main | equation | main | `jensenGap_le_uniform_bound` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `sec:remaining-ranges` | 1314 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:distance-nonpositive-annealed-speed` | 1323 / main | equation | main | `gammaD_eq_zero_of_le_half` | `MainText.RemainingParameters` | proved | standard |
| `sec:two-sided-barriers` | 1437 / main | section | manuscript | — | — | doc-only | doc-only |
| `lem:diffusion-coefficient` | 1451 / main | lemma | main | `diffusionCoefficient_eq_two_mul_zetaThree` | `MainText.DiffusionCoefficientClosedForm` | proved | standard |
| `eq:beta-kappa` | 1485 / main | equation | main | `diffusionMainInput_kappa_eq` | `MainText.DiffusionCoefficientClosedForm` | proved | internal/mathlib |
| `prop:full-line-distribution` | 1496 / main | proposition | appendix/façade | `full_line_distribution; full_line_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `eq:Phi-phase-definition` | 1506 / main | equation | appendix/façade | `ProfileFacade.full_line_phase_definition` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:upper-profile-equation` | 1514 / main | equation | appendix/façade | `ProfileFacade.upper_profile_equation` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:full-line-relative-bounds` | 1521 / main | equation | appendix/façade | `ProfileFacade.full_line_relative_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:full-line-tail-ratios` | 1530 / main | equation | appendix/façade | `ProfileFacade.full_line_tail_ratios` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:hard-edge-distribution` | 1545 / main | proposition | appendix/façade | `hard_edge_distribution; hard_edge_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `eq:Psi-subcritical-definition` | 1555 / main | equation | appendix/façade | `ProfileFacade.hard_edge_phase_definition` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:lower-profile-equation` | 1569 / main | equation | appendix/façade | `ProfileFacade.lower_profile_equation` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:subcritical-relative-bounds` | 1576 / main | equation | appendix/façade | `ProfileFacade.subcritical_relative_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-extension-bounds` | 1586 / main | equation | appendix/façade | `ProfileFacade.hard_edge_density_extension_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:subcritical-right-tail` | 1593 / main | equation | appendix/façade | `ProfileFacade.subcritical_right_tail` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `upp_barrier_init` | 1622 / main | equation | main | `upperBarrier_CDF_translation_induction; cdfOrdered_nonnegativePart_dirac` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `upp_barrier_ineq` | 1625 / main | equation | main | `upperBarrier_global_translation` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:upper-speed-fixed-lambda` | 1660 / main | equation | main | `vR_half_add_cube_le_kappa_sq_eventually` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:sharp-upper-bound` | 1675 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `MainText.ResistanceNearCritical` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:weighted-consistency` | 1698 / main | lemma | main | `full_line_weighted_consistency` | `MainText.WeightedConsistency` | proved | standard |
| `eq:weighted-difference` | 1707 / main | equation | main | `weightedIntegral_difference_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:weighted-sum` | 1710 / main | equation | main | `weightedIntegral_sum_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:strict-untruncated-upper` | 1736 / main | equation | main | `affineWaveProfile_strict_upper_margin_quantitative` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:upper-cutoff-error` | 1767 / main | lemma | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `MainText.UpperBarrier` | partial (theorem-path bound proved) | standard |
| `eq:upper-operator-cutoff-error` | 1775 / main | equation | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `MainText.UpperBarrier` | partial (theorem-path bound proved) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-log-lipschitz` | 1849 / main | equation | main | `density_shift_bounds` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-uniform-bound` | 1858 / main | equation | main | `full_line_density_sq_le_exp` | `MainText.WeightedConsistency` | partial (theorem-path bound proved) | internal/mathlib; MI01-transitive after profile instantiation |
| `low_barrier_init` | 2039 / main | equation | main | `hardEdgeScaledLaw_initial_CDFOrdered` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `low_one_step` | 2042 / main | equation | main | `hard_edge_global_lower_barrier` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:sharp-lower-bound` | 2070 / main | equation | main | `kappa_sq_le_vR_half_add_cube_eventually` | `MainText.ResistanceNearCritical` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:hard-edge-consistency` | 2102 / main | lemma | main | `hard_edge_weighted_lower_consistency` | `MainText.HardEdgeConsistency` | proved | standard |
| `eq:hard-edge-one-sided-consistency` | 2109 / main | equation | main | `hard_edge_weighted_lower_consistency` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:hard-edge-barrier` | 2132 / main | proposition | main | `hard_edge_global_lower_barrier` | `MainText.HardEdgeConsistency` | proved | standard |
| `eq:hard-edge-extension-comparison` | 2177 / main | equation | main | `Iplus_zeroExtension_scaled_eq_weightedIplus` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-extension-difference` | 2198 / main | equation | main | `weightedDifference_remainder_identity` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-symmetric-Taylor` | 2213 / main | equation | main | `weightedProduct_symmetric_remainder_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:extension-log-Lipschitz` | 2226 / main | equation | main | `density_shift_bounds` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:extension-positive-halfline-bound` | 2243 / main | equation | main | `half_line_density_sq_le_exp` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-extended-consistency` | 2302 / main | equation | main | `weightedIntegral_difference_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:boundary-layer-positive-mass` | 2399 / main | equation | main | `hard_edge_transition_Iplus_lower` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `rem:two-thirds-heuristic` | 2447 / main | remark | manuscript | — | — | doc-only | doc-only |
