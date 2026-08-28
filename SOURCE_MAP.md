# Canonical full-paper source map

Authoritative source: `Series-Parallel_SPA_submission.tex`. Active labels are
collected after TeX comments and inactive `\iffalse` branches are removed.
The exhaustive census is **156 unique labels = 112 main + 44 appendix**.

Status `partial (theorem-path bound proved)` records the few displays whose exact
two-sided standalone wrapper is not exported, although the inequality used by the
three closed main theorems is proved internally. The remaining distance near-critical
literature-citation display is outside the three-theorem scope and introduces no project axiom.
Declaration names are relative to `SeriesParallel.MainText` for main-owned rows and to
`SeriesParallel.Appendix` for appendix-owned rows unless an explicit namespace is shown.

| TeX label | Source span / TeX owner | Kind | Implementation owner | Lean declaration | Module | Status | Trust class |
|---|---:|---|---|---|---|---|---|
| `sec:introduction` | 91 / main | section | main | `—` | `MainText foundation` | doc-only | doc-only |
| `sec:main-results` | 174 / main | section | main | `—` | `MainText foundation` | doc-only | doc-only |
| `thm:logarithmic-speeds` | 194 / main | theorem | main | `logarithmicSpeeds` | `MainTheorems` | proved | core literature + internal |
| `eq:full-range-L1` | 202 / main | equation | main | `logarithmicSpeeds` | `MainTheorems` | proved | core literature + internal |
| `eq:speed-values` | 209 / main | equation | main | `logarithmicSpeeds` | `MainTheorems` | proved | core literature + internal |
| `eq:supercritical-speed-bounds` | 214 / main | equation | main | `supercritical_logarithmic_speed_bounds` | `RemainingParameters` | proved | core literature + internal |
| `thm:first-moment-logarithmic-rates` | 219 / main | theorem | main | `firstMomentLogarithmicRates` | `MainTheorems` | proved | core literature + internal |
| `eq:first-moment-rate-definitions` | 225 / main | equation | main | `firstMomentLogarithmicRates_convergence` | `FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `eq:resistance-first-moment-dichotomy` | 234 / main | equation | main | `gammaR_ereal_eq_max_vR_paperLog` | `RemainingParameters` | proved | core literature + internal |
| `eq:supercritical-resistance-identification` | 239 / main | equation | main | `gammaR_eq_vR_supercritical` | `JensenAndCenter` | proved | core literature + internal |
| `fig:resistance-speed-comparison` | 303 / main | figure | main | `—` | `MainText foundation` | doc-only | doc-only |
| `thm:near-critical-speed` | 308 / main | theorem | main | `resistanceSpeedNearCritical` | `ResistanceNearCritical` | proved | internal/mathlib |
| `eq:main-W-bvp` | 317 / main | equation | main | `lambdaStar_isLeast_mainAdmissible` | `NearCriticalAssembly` | proved | internal/mathlib |
| `eq:main-near-critical-limit` | 325 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `ResistanceNearCritical` | proved | internal/mathlib |
| `eq:resistance-first-moment-near-critical` | 333 / main | equation | main | `gammaR_plus_isEquivalent_of_vR; gammaR_minus_isEquivalent_of_vR` | `ResistanceNearCritical` | proved | internal/mathlib |
| `eq:distance-near-critical-speed` | 349 / main | equation | main | `—` | `—` | out of scope (literature citation) | no project axiom |
| `prop_G` | 403 / main | equation | main | `upperBarrier_global_translation; upperBarrier_CDF_translation_induction; integrable_id_upperBarrierLaw` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `sec:organization-conventions` | 486 / main | section | main | `—` | `MainText foundation` | doc-only | doc-only |
| `sec:preliminaries` | 507 / main | section | main | `—` | `TreeEnvironment; Networks; RandomModel` | doc-only | doc-only |
| `sec:gate-properties` | 519 / main | section | main | `—` | `LogGates` | doc-only | doc-only |
| `eq:parallel-gate` | 538 / main | equation | main | `parallelGate; parallelGate_distance; parallelGate_resistance_eq_harmonic` | `LogGates` | proved | internal/mathlib |
| `eq:unified-rde` | 552 / main | equation | main | `Z_succ; root_subtrees_indep; left_right_Z_indep` | `RandomModel; LogarithmicDrift; StructuralProperties` | proved | internal/mathlib |
| `eq:gate-translation` | 585 / main | equation | main | `logSeriesGate_translation; logParallelGate_translation` | `MainText foundation` | proved | internal/mathlib |
| `eq:log-series-gate` | 598 / main | equation | main | `logSeriesGate_eq_max_add_h; logParallelGate_eq_min_sub_h` | `MainText foundation` | proved | internal/mathlib |
| `lem:logarithmic-drift` | 608 / main | lemma | main | `LogarithmicDrift.X_succ_hasLaw; logarithmic_drift` | `MainText foundation` | proved | internal/mathlib |
| `eq:log-rde` | 618 / main | equation | main | `X_succ_hasLaw` | `MainText foundation` | proved | internal/mathlib |
| `eq:drift-identity` | 626 / main | equation | main | `LogarithmicDrift.logarithmic_drift` | `MainText foundation` | proved | internal/mathlib |
| `sec:canonical-refinement-coupling` | 642 / main | section | main | `—` | `ConditionalRefinement` | doc-only | doc-only |
| `prop:conditional-refinement` | 652 / main | proposition | main | `conditional_refinement_core` | `MainText foundation` | proved | internal/mathlib |
| `lem:deterministic-bound` | 666 / main | lemma | main | `adjacent_Z_rpow; X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText foundation` | proved | internal/mathlib |
| `eq:adjacent-Z` | 673 / main | equation | main | `adjacent_Z_rpow` | `MainText foundation` | proved | internal/mathlib |
| `eq:deterministic-bound` | 684 / main | equation | main | `X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText foundation` | proved | internal/mathlib |
| `lem:first-moment-bounds` | 700 / main | lemma | main | `firstMoment_succ_lower_bound; firstMoment_geometric_bounds` | `MainText foundation` | proved | internal/mathlib |
| `eq:first-moment-recursion` | 706 / main | equation | main | `firstMoment_succ_lower_bound` | `FirstMomentBounds` | proved | internal/mathlib |
| `lem:resistance-duality` | 727 / main | lemma | main | `log_resistanceValue_complement; complementEnvironment_map` | `MainText foundation` | proved | internal/mathlib |
| `eq:resistance-duality` | 732 / main | equation | main | `resistanceValue_complement; log_resistanceValue_complement` | `RandomModel` | proved | internal/mathlib |
| `sec:cdf-operator` | 737 / main | section | main | `CDFOperator` | `MainText foundation` | doc-only | doc-only |
| `eq:CDF-operator-definition` | 754 / main | equation | main | `oneStepLaw; cdfOperator; oneStepLaw_hasCDF` | `MainText foundation` | proved | internal/mathlib |
| `eq:Iminus` | 768 / main | equation | main | `CDFOperator.Iminus` | `MainText foundation` | proved | internal/mathlib |
| `eq:Iplus` | 772 / main | equation | main | `CDFOperator.Iplus` | `MainText foundation` | proved | internal/mathlib |
| `lem:exact-cdf` | 776 / main | lemma | main | `exact_cdf_operator_density; cdfOperator_mono_of_CDFOrdered` | `DensityGateRegions; GeneralizedInverseCoupling` | proved | internal/mathlib |
| `eq:series-parallel-cdf` | 783 / main | equation | main | `seriesCDF_density_formula; parallelCDF_density_formula` | `DensityGateRegions` | proved | internal/mathlib |
| `eq:exact-cdf-operator` | 789 / main | equation | main | `exact_cdf_operator_density` | `DensityGateRegions` | proved | internal/mathlib |
| `sec:ballistic-proof` | 880 / main | section | main | `—` | `FirstMomentSubmultiplicative` | doc-only | doc-only |
| `sec:first-moment-exponent` | 903 / main | section | main | `—` | `FirstMomentSubmultiplicative` | doc-only | doc-only |
| `lem:first-moment-submultiplicativity` | 906 / main | lemma | main | `firstMoment_submultiplicative` | `FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `eq:first-moment-submultiplicativity` | 910 / main | equation | main | `firstMoment_submultiplicative` | `FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `eq:annealed-fekete` | 916 / main | equation | main | `normalizedLogFirstMoment_tendsto_feketeLimit` | `FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `sec:annealed-to-typical` | 969 / main | section | main | `—` | `JensenAndCenter` | doc-only | doc-only |
| `eq:jensen-gap` | 973 / main | equation | main | `JensenBasic.jensenGap; jensenGap_nonneg` | `JensenAndCenter` | proved | internal/mathlib |
| `prop:bounded-Jensen-gap` | 983 / main | proposition | main | `jensenGap_le_uniform_bound` | `JensenAndCenter` | proved | internal/mathlib |
| `eq:mean-log-limit` | 993 / main | equation | main | `normalizedMeanLog_tendsto_firstMomentLimit` | `JensenAndCenter` | proved | internal/mathlib |
| `lem:center-tracking` | 1002 / main | lemma | main | `centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `JensenAndCenter` | proved | internal/mathlib |
| `eq:uniform-width` | 1009 / main | equation | main | `centered_X_uniform_bound` | `JensenAndCenter` | proved | internal/mathlib |
| `eq:center-tracking` | 1015 / main | equation | main | `centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `JensenAndCenter` | proved | internal/mathlib |
| `eq:fixed-supercritical-convergence` | 1069 / main | equation | main | `convergesASAndL1AtLinearRate_supercritical` | `JensenAndCenter` | proved | internal/mathlib |
| `lem:normalized-L2` | 1095 / main | lemma | main | `normalizedSecondMoment_le_bound` | `NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:normalized-L2` | 1101 / main | equation | main | `normalizedSecondMoment_le_bound` | `NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:normalized-L2-recursion` | 1124 / main | equation | main | `normalizedSecondMoment_succ_le` | `NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:Paley-Zygmund` | 1136 / main | equation | main | `paleyZygmund_half_probability_lower_bound` | `NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:jensen-event-comparison` | 1141 / main | equation | main | `jensenGap_le_uniform_bound` | `JensenAndCenter` | proved | internal/mathlib |
| `eq:Jensen-gap-bound` | 1157 / main | equation | main | `jensenGap_le_uniform_bound` | `JensenAndCenter` | proved | internal/mathlib |
| `sec:remaining-ranges` | 1171 / main | section | main | `—` | `RemainingParameters` | doc-only | doc-only |
| `eq:distance-nonpositive-annealed-speed` | 1180 / main | equation | main | `gammaD_eq_zero_of_le_half` | `RemainingParameters` | proved | core literature + internal |
| `sec:two-sided-barriers` | 1295 / main | section | main | `—` | `DiffusionCoefficientClosedForm` | doc-only | doc-only |
| `lem:diffusion-coefficient` | 1309 / main | lemma | main | `diffusionCoefficient_eq_two_mul_zetaThree` | `DiffusionCoefficientClosedForm` | proved | internal/mathlib |
| `eq:a-zeta` | 1313 / main | equation | main | `diffusionCoefficient_eq_two_mul_zetaThree` | `DiffusionCoefficientClosedForm` | proved | internal/mathlib |
| `eq:beta-kappa` | 1345 / main | equation | main | `diffusionMainInput_kappa_eq` | `DiffusionCoefficientClosedForm` | proved | internal/mathlib |
| `prop:full-line-distribution` | 1356 / main | proposition | appendix/façade | `ProfileFacade.full_line_distribution; full_line_density_probability; MI01` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:Phi-phase-definition` | 1366 / main | equation | appendix/façade | `ProfileFacade.full_line_phase_definition` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-profile-equation` | 1374 / main | equation | appendix/façade | `ProfileFacade.upper_profile_equation` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:full-line-relative-bounds` | 1381 / main | equation | appendix/façade | `ProfileFacade.full_line_relative_bounds` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:full-line-tail-ratios` | 1390 / main | equation | appendix/façade | `ProfileFacade.full_line_tail_ratios` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `prop:hard-edge-distribution` | 1405 / main | proposition | appendix/façade | `ProfileFacade.hard_edge_distribution; hard_edge_density_probability` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:Psi-subcritical-definition` | 1415 / main | equation | appendix/façade | `ProfileFacade.hard_edge_phase_definition` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:lower-profile-equation` | 1429 / main | equation | appendix/façade | `ProfileFacade.lower_profile_equation` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:subcritical-relative-bounds` | 1436 / main | equation | appendix/façade | `ProfileFacade.subcritical_relative_bounds` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:q-extension-bounds` | 1446 / main | equation | appendix/façade | `ProfileFacade.hard_edge_density_extension_bounds` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `eq:subcritical-right-tail` | 1453 / main | equation | appendix/façade | `ProfileFacade.subcritical_right_tail` | `ProfileFacade` | proved (facade) | internal / MI01-transitive where profiles are instantiated |
| `upp_barrier_init` | 1483 / main | equation | main | `upperBarrier_CDF_translation_induction; cdfOrdered_nonnegativePart_dirac` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `upp_barrier_ineq` | 1486 / main | equation | main | `upperBarrier_global_translation` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-speed-fixed-lambda` | 1521 / main | equation | main | `vR_half_add_cube_le_kappa_sq_eventually` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:sharp-upper-bound` | 1536 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `ResistanceNearCritical` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:weighted-consistency` | 1559 / main | lemma | main | `full_line_weighted_consistency` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:weighted-difference` | 1568 / main | equation | main | `weightedIntegral_difference_bound` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:weighted-sum` | 1571 / main | equation | main | `weightedIntegral_sum_bound` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:one-step-upper-expansion` | 1583 / main | equation | main | `affineWaveProfile_oneStep_consistency` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-translation-expansion` | 1591 / main | equation | main | `affineProfile_translation_consistency` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:strict-untruncated-upper` | 1599 / main | equation | main | `affineWaveProfile_strict_upper_margin_quantitative` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-cutoff-location` | 1615 / main | equation | main | `upperCutoff; upperCutoff_spec` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-truncated-cdf` | 1626 / main | equation | main | `cutoffProfileCDF; cdf_upperBarrierLaw` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:upper-cutoff-error` | 1632 / main | lemma | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `UpperBarrier` | partial (theorem-path bound proved) | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-operator-cutoff-error` | 1640 / main | equation | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `UpperBarrier` | partial (theorem-path bound proved) | internal / MI01-transitive where profiles are instantiated |
| `eq:global-upper-barrier` | 1672 / main | equation | main | `upperBarrier_global_translation` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:q-log-lipschitz` | 1717 / main | equation | main | `density_shift_bounds` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:q-uniform-bound` | 1726 / main | equation | main | `full_line_density_sq_le_exp` | `WeightedConsistency` | partial (theorem-path bound proved) | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-d-of-x` | 1847 / main | equation | main | `seriesCutoffLower_gap_le_log_two` | `UpperBarrier` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:upper-series-cutoff-error` | 1860 / main | equation | main | `seriesCDF_le_nonnegativePartLaw_add_atomAware` | `UpperBarrier` | partial (theorem-path bound proved) | internal / MI01-transitive where profiles are instantiated |
| `eq:sharp-lower-bound` | 1942 / main | equation | main | `kappa_sq_le_vR_half_add_cube_eventually` | `ResistanceNearCritical` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-scaled-cdf` | 1956 / main | equation | main | `hardEdgeScaledCDF; cdf_hardEdgeScaledLaw` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:hard-edge-consistency` | 1980 / main | lemma | main | `hard_edge_weighted_lower_consistency` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-one-sided-consistency` | 1987 / main | equation | main | `hard_edge_weighted_lower_consistency` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `prop:hard-edge-barrier` | 2010 / main | proposition | main | `hard_edge_global_lower_barrier` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:global-lower-barrier-negative-bias` | 2017 / main | equation | main | `hard_edge_global_lower_barrier` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-extension-comparison` | 2057 / main | equation | main | `Iplus_zeroExtension_scaled_eq_weightedIplus` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-extension-difference` | 2078 / main | equation | main | `weightedDifference_remainder_identity` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-symmetric-Taylor` | 2093 / main | equation | main | `weightedProduct_symmetric_remainder_bound` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:extension-log-Lipschitz` | 2106 / main | equation | main | `density_shift_bounds` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:extension-positive-halfline-bound` | 2123 / main | equation | main | `half_line_density_sq_le_exp` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:hard-edge-extended-consistency` | 2182 / main | equation | main | `weightedIntegral_difference_bound` | `WeightedConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:boundary-layer-positive-mass` | 2278 / main | equation | main | `hard_edge_transition_Iplus_lower` | `HardEdgeConsistency` | proved | internal / MI01-transitive where profiles are instantiated |
| `rem:two-thirds-heuristic` | 2323 / main | remark | main | `—` | `HardEdgeConsistency; LowerBarrier; WeightedConsistency` | doc-only | doc-only |
| `app:ode` | 2343 / appendix A | section | appendix | `—` | `SeriesParallel.Appendix` | doc-only | doc-only |
| `eq:W-ode` | 2348 / appendix A | equation | appendix | `wODEValue; SatisfiesWODEAt` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-boundary` | 2354 / appendix A | equation | appendix | `SatisfiesWBoundary; IsWBoundarySolution` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:y-ODE` | 2369 / appendix A | equation | appendix | `yRhs; SatisfiesYODEAt` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:y-boundary` | 2373 / appendix A | equation | appendix | `SatisfiesYBoundary; IsYBoundarySolution` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:y-shooting` | 2379 / appendix A | equation | appendix | `IsShootingSolution` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:cuberoot-comparison` | 2391 / appendix A1 | lemma | appendix | `cuberoot_comparison_source` | `Appendix.CubeRootComparison` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:property of y` | 2423 / appendix A2 | lemma | appendix | `shootingProperties` | `Appendix.Shooting` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:y>0` | 2427 / appendix A | equation | appendix | `shootingY_pos` | `Appendix.Shooting` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:shooting-strict-order` | 2435 / appendix A | equation | appendix | `shootingY_strictAnti` | `Appendix.Shooting` | proved | internal / MI01-transitive where profiles are instantiated |
| `prop:Cstar-halfline` | 2530 / appendix A3 | proposition | appendix | `cstarHalfline; existsUnique_boundarySolution_iff_lambdaStar_le` | `Appendix.AdmissibleHalfline` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:Z-halfline` | 2534 / appendix A | equation | appendix | `admissibleSet_eq_Ici_lambdaStar` | `Appendix.AdmissibleHalfline` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:rough-Cstar-bounds` | 2540 / appendix A | equation | appendix | `lambdaLower_eq_rpow; lambdaLower_le_lambdaStar; lambdaStar_le_upper` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:ODE divide W` | 2579 / appendix A | equation | appendix | `WSolution_sq_hasDerivAt; WSolution_sq_deriv_le` | `Appendix.AdmissibleLowerBound` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:lambda-integral-W` | 2598 / appendix A | equation | appendix | `WSolution_compact_integral_identity; lambda_eq_integral` | `Appendix.AdmissibleLowerBound` | proved | internal / MI01-transitive where profiles are instantiated |
| `prop:subcritical-W` | 2630 / appendix A4 | proposition | appendix | `subcriticalW` | `Appendix.SubcriticalW` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:subcritical-positive-W` | 2637 / appendix A | equation | appendix | `WSolution_zero_pos_of_lt_lambdaStar; WSolution_pos_Ico_of_lt_lambdaStar` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:linear-u1` | 2681 / appendix A5 | lemma | appendix | `linearAtOne; WSolution_linearAtOne` | `Appendix.EndpointAsymptotics` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:u0-dichotomy` | 2729 / appendix A6 | lemma | appendix | `Xor; leftEndpointDichotomy_source` | `Appendix.LeftEndpointDichotomy` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:u0-linear` | 2734 / appendix A | equation | appendix | `HasLinearBranchAtZero` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:u0-sharp` | 2737 / appendix A | equation | appendix | `HasSharpBranchAtZero` | `Appendix.BasicDefs` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:r-inverse` | 2773 / appendix A | equation | appendix | `LeftLocalInverseData; leftEndpoint_sourceLocalInverse` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:r-limsup` | 2785 / appendix A | equation | appendix | `localInverse_ratio_eventually_lt_lambda_add` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:r-flow` | 2792 / appendix A | equation | appendix | `logRatioFlowRhs; logRatioFlow_derivative_identity` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `prop:critical-branches` | 2849 / appendix A7 | proposition | appendix | `criticalBranches` | `Appendix.CriticalBranches` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:critical-sharp-branch` | 2854 / appendix A | equation | appendix | `lambdaStar_not_linearBranch; criticalBranches_of_dichotomy` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:supercritical-linear-branch` | 2860 / appendix A | equation | appendix | `supercritical_linear_of_dichotomy` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `app:regularity` | 2917 / appendix B | section | appendix | `—` | `SeriesParallel/Appendix` | doc-only | doc-only |
| `lem:finite-asymptotic-ode` | 2928 / appendix B1 | lemma | appendix | `finiteAsymptoticODE_source` | `Appendix.FiniteAsymptoticODE` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:asymptotically-autonomous-ode` | 2943 / appendix B | equation | appendix | `IsAsymptoticallyAutonomousSolutionSource; asymptoticallyAutonomousRhs` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:finite-asymptotic-expansion` | 2955 / appendix B | equation | appendix | `FiniteAsymptoticExpansion; finiteAsymptoticRemainder` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:D8-bound` | 2991 / appendix B | equation | appendix | `recursive_defect8_isBigO; reciprocalDefect8_deriv_isBigO` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:R-linear-equation` | 2999 / appendix B | equation | appendix | `remainder_linear_equation; eventually_remainder_linear_equation` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:forward-integral` | 3015 / appendix B | equation | appendix | `forward_integral_formula` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:terminal-integral` | 3046 / appendix B | equation | appendix | `terminal_integral_formula` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `lem:linear-branch-regularity` | 3074 / appendix B2 | lemma | appendix | `leftLinearBranchRegularity_source; rightLinearBranchRegularity_source; linearBranchRegularity_source` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-expansion-zero` | 3084 / appendix B | equation | appendix | `LeftLinearBranchRegularity.secondOrder; leftEndpoint_secondOrder_of_finiteAsymptoticExpansion` | `Appendix.LinearBranchRegularity` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-expansion-zero-differentiable` | 3095 / appendix B | equation | appendix | `LeftLinearBranchRegularity.differentiableExpansion; leftEndpointDifferentiableExpansion_exactQuadratic` | `Appendix.LinearBranchRegularity` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-expansion-one` | 3108 / appendix B | equation | appendix | `RightLinearBranchRegularity.secondOrder; rightEndpoint_secondOrder_of_finiteAsymptoticExpansion` | `Appendix.LinearBranchRegularity` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-expansion-one-differentiable` | 3120 / appendix B | equation | appendix | `RightLinearBranchRegularity.differentiableExpansion; rightEndpointDifferentiableExpansion_exactQuadratic` | `Appendix.LinearBranchRegularity` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:W-relative-derivative-bounds` | 3130 / appendix B | equation | appendix | `RelativeDerivativeBoundsAtZero; RelativeDerivativeBoundsAtOne` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:Y-zero-equation` | 3148 / appendix B | equation | appendix | `rescaledLeftEquation; leftRescaling_isAsymptoticallyAutonomousSolution` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:Y-one-equation` | 3191 / appendix B | equation | appendix | `rescaledRightEquation; rightRescaling_isAsymptoticallyAutonomousSolution` | `SeriesParallel/Appendix` | proved | internal / MI01-transitive where profiles are instantiated |
| `eq:full-line-profile-coordinate` | 3253 / appendix B support | equation | appendix | `fullLineCoordinateIntegrand; fullLineCoordinate` | `Appendix.Profiles` | proved | internal / MI01-transitive where profiles are instantiated |

## Moved-label ownership

The eleven profile labels at TeX lines 1356–1453 remain owned by the main text
and are implemented through `ProfileFacade` over appendix results. They occur once
in this census; hard-edge uniqueness remains `EqOn` on `Set.Ici 0`.
