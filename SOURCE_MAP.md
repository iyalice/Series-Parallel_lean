# Manuscript--Lean source map

Authoritative TeX: `Distance_and_resistance_arxiv_amsart.tex`
SHA-256: `d7cb8c59d41fc37d566b3daeaa5b5e7ab48f75b303ad40a38c22329c46348777`

The table contains every active TeX label, in source order, after comments and literal
`\iffalse` branches are removed. The `\appendix` command is at line 2421. There are **136 distinct
labels: 98 in the main text and 38 in the appendices**.

`proved` means that the named Lean declaration covers the labelled statement. `covered by a
stronger theorem` and `proof-local` identify statements present in a closed proof path but not
exported verbatim as separate Lean theorems. `partial` is used only for the qualified cutoff
estimate described in the correspondence report. `standard` abbreviates `propext`,
`Classical.choice`, and `Quot.sound`; the two project assumptions are stated in
`AXIOM_REPORT.md`.

| TeX label | Label line / TeX owner | Kind | Implementation owner | Lean declaration | Module | Status | Trust boundary |
|---|---:|---|---|---|---|---|---|
| `sec:introduction` | 125 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:main-results` | 206 / main | section | manuscript | — | — | doc-only | doc-only |
| `fig:series-parallel-replacement` | 279 / main | figure | manuscript | — | — | doc-only | doc-only |
| `thm:logarithmic-speeds` | 288 / main | theorem | main | `GraphSemantics.graphLogarithmicSpeeds; logarithmicSpeeds` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:full-range-L1` | 296 / main | equation | main | `logarithmicSpeeds` | `MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:supercritical-speed-bounds` | 307 / main | equation | main | `supercritical_logarithmic_speed_bounds` | `MainText.RemainingParameters` | proved | standard |
| `thm:first-moment-logarithmic-rates` | 312 / main | theorem | main | `GraphSemantics.graphFirstMomentLogarithmicRates; firstMomentLogarithmicRates` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `eq:resistance-first-moment-dichotomy` | 321 / main | equation | main | `gammaD_eq_vD_all; gammaR_ereal_eq_max_vR_paperLog` | `MainText.RemainingParameters` | proved | standard |
| `eq:supercritical-resistance-identification` | 330 / main | equation | main | `gammaR_eq_vR_supercritical` | `MainText.JensenAndCenter` | proved | standard |
| `fig:resistance-speed-comparison` | 402 / main | figure | manuscript | — | — | doc-only | doc-only |
| `thm:near-critical-speed` | 406 / main | theorem | main | `GraphSemantics.graphResistanceSpeedNearCritical; resistanceSpeedNearCritical` | `MainText.GraphSemantics.MainTheorems; MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:main-W-bvp` | 414 / main | equation | main | `lambdaStar_isLeast_mainAdmissible` | `MainText.NearCriticalAssembly` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:main-near-critical-limit` | 424 / main | equation | main | `vR_nearCritical_duality; vR_plus_isEquivalent_of_diffusion_barriers` | `MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:resistance-first-moment-near-critical` | 432 / main | equation | main | `gammaR_plus_isEquivalent_of_vR; gammaR_minus_isEquivalent_of_vR` | `MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `prop_G` | 496 / main | equation | main | `cdfOrdered_nonnegativePart_dirac; upperBarrier_global_translation; upperBarrier_CDF_translation_induction; integrable_id_upperBarrierLaw` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `sec:organization-conventions` | 586 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:preliminaries` | 605 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:gate-properties` | 617 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:unified-rde` | 649 / main | equation | main | `Z_succ; root_subtrees_indep; left_right_Z_indep` | `MainText.RandomModel; MainText.LogarithmicDrift; MainText.StructuralProperties` | proved | internal/mathlib |
| `eq:gate-translation` | 683 / main | equation | main | `logSeriesGate_translation; logParallelGate_translation` | `MainText.LogGates` | proved | internal/mathlib |
| `eq:log-series-gate` | 696 / main | equation | main | `logSeriesGate_eq_max_add_h; logParallelGate_eq_min_sub_h` | `MainText.LogGates` | proved | internal/mathlib |
| `lem:logarithmic-drift` | 706 / main | lemma | main | `X_succ_hasLaw; logarithmic_drift` | `MainText.LogarithmicDrift` | proved | standard |
| `eq:log-rde` | 716 / main | equation | main | `X_succ_hasLaw` | `MainText.LogarithmicDrift` | proved | internal/mathlib |
| `eq:drift-identity` | 724 / main | equation | main | `LogarithmicDrift.logarithmic_drift` | `MainText.LogarithmicDrift` | proved | internal/mathlib |
| `sec:canonical-refinement-coupling` | 740 / main | section | manuscript | — | — | doc-only | doc-only |
| `prop:conditional-refinement` | 750 / main | proposition | main | `conditional_refinement_core` | `MainText.ConditionalRefinement` | proved | standard |
| `lem:deterministic-bound` | 764 / main | lemma | main | `adjacent_Z_rpow; X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText.AdjacentBounds` | proved | standard |
| `eq:adjacent-Z` | 771 / main | equation | main | `adjacent_Z_rpow` | `MainText.AdjacentBounds` | proved | internal/mathlib |
| `eq:deterministic-bound` | 782 / main | equation | main | `X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText.AdjacentBounds` | proved | internal/mathlib |
| `lem:first-moment-bounds` | 798 / main | lemma | main | `firstMoment_succ_lower_bound; firstMoment_geometric_bounds` | `MainText.FirstMomentBounds` | proved | standard |
| `eq:first-moment-recursion` | 804 / main | equation | main | `firstMoment_succ_lower_bound; firstMoment_geometric_bounds` | `MainText.FirstMomentBounds` | proved | internal/mathlib |
| `lem:resistance-duality` | 825 / main | lemma | main | `log_resistanceValue_complement; complementEnvironment_map` | `MainText.RandomModel; MainText.TreeEnvironment` | proved | standard |
| `eq:resistance-duality` | 830 / main | equation | main | `resistanceValue_complement; log_resistanceValue_complement` | `MainText.RandomModel` | proved | internal/mathlib |
| `sec:cdf-operator` | 835 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:CDF-operator-definition` | 852 / main | equation | main | `oneStepLaw; cdfOperator; oneStepLaw_hasCDF` | `MainText.CDFOperator` | proved | internal/mathlib |
| `lem:exact-cdf` | 873 / main | lemma | main | `seriesCDF_density_formula; parallelCDF_density_formula; exact_cdf_operator_density; cdfOperator_mono_of_CDFOrdered; cdfOperator_translate` | `MainText.DensityGateRegions; MainText.GeneralizedInverseCoupling; MainText.CDFOperator` | proved | standard |
| `eq:series-parallel-cdf` | 880 / main | equation | main | `seriesCDF_density_formula; parallelCDF_density_formula` | `MainText.DensityGateRegions` | proved | internal/mathlib |
| `eq:exact-cdf-operator` | 886 / main | equation | main | `exact_cdf_operator_density` | `MainText.DensityGateRegions` | proved | internal/mathlib |
| `sec:ballistic-proof` | 977 / main | section | manuscript | — | — | doc-only | doc-only |
| `sec:first-moment-exponent` | 1000 / main | section | manuscript | — | — | doc-only | doc-only |
| `lem:first-moment-submultiplicativity` | 1003 / main | lemma | main | `firstMoment_submultiplicative; normalizedLogFirstMoment_tendsto_feketeLimit` | `MainText.FirstMomentSubmultiplicative` | proved | standard |
| `eq:first-moment-submultiplicativity` | 1007 / main | equation | main | `firstMoment_submultiplicative` | `MainText.FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `eq:annealed-fekete` | 1013 / main | equation | main | `normalizedLogFirstMoment_tendsto_feketeLimit` | `MainText.FirstMomentSubmultiplicative` | proved | internal/mathlib |
| `sec:annealed-to-typical` | 1066 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:jensen-gap` | 1070 / main | equation | main | `JensenBasic.jensenGap; jensenGap_nonneg` | `MainText.JensenBasic` | proved | internal/mathlib |
| `prop:bounded-Jensen-gap` | 1080 / main | proposition | main | `jensenGap_le_uniform_bound; normalizedMeanLog_tendsto_firstMomentLimit` | `MainText.JensenAndCenter` | proved | standard |
| `eq:mean-log-limit` | 1090 / main | equation | main | `normalizedMeanLog_tendsto_firstMomentLimit` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `lem:center-tracking` | 1099 / main | lemma | main | `left_right_X_hasLaw; descendant_pair_width_le; centered_X_uniform_bound; centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `MainText.LogarithmicDrift; MainText.JensenAndCenter` | proved | standard |
| `eq:uniform-width` | 1106 / main | equation | main | `descendant_pair_width_le; centered_X_uniform_bound` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `eq:center-tracking` | 1112 / main | equation | main | `centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `eq:fixed-supercritical-convergence` | 1166 / main | equation | main | `convergesASAndL1AtLinearRate_supercritical` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `lem:normalized-L2` | 1192 / main | lemma | main | `normalizedSecondMoment_le_bound` | `MainText.NormalizedSecondMoment` | proved | standard |
| `eq:normalized-L2-recursion` | 1220 / main | equation | main | `normalizedSecondMoment_succ_le` | `MainText.NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:Paley-Zygmund` | 1232 / main | equation | main | `paleyZygmund_half_probability_lower_bound` | `MainText.NormalizedSecondMoment` | proved | internal/mathlib |
| `eq:jensen-event-comparison` | 1237 / main | equation | main | `jensenGap_le_uniform_bound` | `MainText.JensenAndCenter` | proof-local step in the named theorem | internal/mathlib |
| `eq:Jensen-gap-bound` | 1253 / main | equation | main | `jensenGap_le_uniform_bound` | `MainText.JensenAndCenter` | proved | internal/mathlib |
| `sec:remaining-ranges` | 1267 / main | section | manuscript | — | — | doc-only | doc-only |
| `eq:distance-nonpositive-annealed-speed` | 1276 / main | equation | main | `gammaD_eq_zero_of_le_half` | `MainText.RemainingParameters` | proved | standard |
| `sec:two-sided-barriers` | 1390 / main | section | manuscript | — | — | doc-only | doc-only |
| `lem:diffusion-coefficient` | 1404 / main | lemma | main | `integral_diffusionIntegrand_eq_zetaThree; diffusionCoefficient_eq_two_mul_zetaThree` | `MainText.DiffusionCoefficientClosedForm` | proved | standard |
| `eq:beta-kappa` | 1438 / main | equation | main | `MainInput.beta; MainInput.kappa; diffusionCoefficient_eq_two_mul_zetaThree; diffusionMainInput_kappa_eq` | `MainTextInterface; MainText.DiffusionCoefficientClosedForm` | proved | internal/mathlib |
| `prop:full-line-distribution` | 1449 / main | proposition | appendix/façade | `full_line_distribution; full_line_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `eq:Phi-phase-definition` | 1459 / main | equation | appendix/façade | `ProfileFacade.full_line_phase_definition` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:upper-profile-equation` | 1467 / main | equation | appendix/façade | `ProfileFacade.upper_profile_equation` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:full-line-relative-bounds` | 1474 / main | equation | appendix/façade | `ProfileFacade.full_line_relative_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:full-line-tail-ratios` | 1483 / main | equation | appendix/façade | `ProfileFacade.full_line_tail_ratios` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:hard-edge-distribution` | 1498 / main | proposition | appendix/façade | `hard_edge_distribution; hard_edge_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `eq:Psi-subcritical-definition` | 1508 / main | equation | appendix/façade | `ProfileFacade.hard_edge_phase_definition` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:lower-profile-equation` | 1522 / main | equation | appendix/façade | `ProfileFacade.lower_profile_equation` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:subcritical-relative-bounds` | 1529 / main | equation | appendix/façade | `ProfileFacade.subcritical_relative_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-extension-bounds` | 1539 / main | equation | appendix/façade | `ProfileFacade.hard_edge_density_extension_bounds` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:subcritical-right-tail` | 1546 / main | equation | appendix/façade | `ProfileFacade.subcritical_right_tail` | `MainText.ProfileFacade` | proved (facade) | internal/mathlib; MI01-transitive after profile instantiation |
| `upp_barrier_init` | 1575 / main | equation | main | `upperBarrier_CDF_translation_induction; cdfOrdered_nonnegativePart_dirac` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `upp_barrier_ineq` | 1578 / main | equation | main | `upperBarrier_global_translation` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:upper-speed-fixed-lambda` | 1613 / main | equation | main | `vR_half_add_cube_le_kappa_sq_eventually` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:sharp-upper-bound` | 1628 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `MainText.ResistanceNearCritical` | covered by a stronger theorem | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:weighted-consistency` | 1649 / main | lemma | main | `full_line_weighted_consistency` | `MainText.WeightedConsistency` | proved | standard |
| `eq:weighted-difference` | 1657 / main | equation | main | `weightedIntegral_difference_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:weighted-sum` | 1660 / main | equation | main | `weightedIntegral_sum_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:strict-untruncated-upper` | 1686 / main | equation | main | `affineWaveProfile_strict_upper_margin_quantitative` | `MainText.UpperBarrier` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:upper-cutoff-error` | 1716 / main | lemma | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `MainText.UpperBarrier` | partial (theorem-path bound proved) | standard |
| `eq:upper-operator-cutoff-error` | 1724 / main | equation | main | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `MainText.UpperBarrier` | partial (theorem-path bound proved) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-log-lipschitz` | 1798 / main | equation | main | `density_shift_bounds` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:q-uniform-bound` | 1807 / main | equation | main | `full_line_density_sq_le_exp` | `MainText.WeightedConsistency` | partial (theorem-path bound proved) | internal/mathlib; MI01-transitive after profile instantiation |
| `low_barrier_init` | 1988 / main | equation | main | `hardEdgeScaledLaw_initial_CDFOrdered` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `low_one_step` | 1991 / main | equation | main | `hard_edge_global_lower_barrier` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:sharp-lower-bound` | 2019 / main | equation | main | `vR_plus_isEquivalent_of_diffusion_barriers` | `MainText.ResistanceNearCritical` | covered by a stronger theorem | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:hard-edge-consistency` | 2051 / main | lemma | main | `hard_edge_weighted_lower_consistency` | `MainText.HardEdgeConsistency` | proved | standard |
| `eq:hard-edge-one-sided-consistency` | 2058 / main | equation | main | `hard_edge_weighted_lower_consistency` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:hard-edge-barrier` | 2081 / main | proposition | main | `hard_edge_global_lower_barrier` | `MainText.HardEdgeConsistency` | proved | standard |
| `eq:hard-edge-extension-comparison` | 2126 / main | equation | main | `Iplus_zeroExtension_scaled_eq_weightedIplus; Iminus_zeroExtension_scaled_le_weightedIminus` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-extension-difference` | 2147 / main | equation | main | `weightedDifference_remainder_identity` | `MainText.WeightedConsistency` | covered in the theorem path (proof-level definitional identity) | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-symmetric-Taylor` | 2162 / main | equation | main | `weightedProduct_symmetric_remainder_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:extension-log-Lipschitz` | 2175 / main | equation | main | `density_shift_bounds` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:extension-positive-halfline-bound` | 2192 / main | equation | main | `half_line_density_sq_le_exp` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:hard-edge-extended-consistency` | 2251 / main | equation | main | `weightedIntegral_difference_bound` | `MainText.WeightedConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:boundary-layer-positive-mass` | 2348 / main | equation | main | `hard_edge_transition_Iplus_lower` | `MainText.HardEdgeConsistency` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `rem:two-thirds-heuristic` | 2396 / main | remark | manuscript | — | — | doc-only | doc-only |
| `app:ode` | 2423 / appendix | section | manuscript | — | — | doc-only | doc-only |
| `eq:W-ode` | 2428 / appendix | equation | appendix | `wODEValue; SatisfiesWODEAt` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:W-boundary` | 2434 / appendix | equation | appendix | `SatisfiesWBoundary; IsWBoundarySolution` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:y-ODE` | 2449 / appendix | equation | appendix | `yRhs; SatisfiesYODEAt` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:y-boundary` | 2453 / appendix | equation | appendix | `SatisfiesYBoundary; IsYBoundarySolution` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:y-shooting` | 2459 / appendix | equation | appendix | `IsShootingSolution` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:cuberoot-comparison` | 2471 / appendix | lemma | appendix | `cuberoot_comparison_source` | `Appendix.CubeRootComparison` | proved | standard |
| `lem:shooting-properties` | 2503 / appendix | lemma | appendix | `shootingProperties; shootingYMap_norm_sub_le` | `Appendix.Shooting` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:y>0` | 2507 / appendix | equation | appendix | `shootingY_pos` | `Appendix.Shooting` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:shooting-strict-order` | 2515 / appendix | equation | appendix | `shootingY_strictAnti` | `Appendix.Shooting` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:Cstar-halfline` | 2610 / appendix | proposition | appendix | `cstarHalfline; existsUnique_boundarySolution_iff_lambdaStar_le; lambdaLower_eq_rpow` | `Appendix.AdmissibleHalfline; Appendix.AdmissibleParameters` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:Z-halfline` | 2614 / appendix | equation | appendix | `admissibleSet_eq_Ici_lambdaStar` | `Appendix.AdmissibleHalfline` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:rough-Cstar-bounds` | 2620 / appendix | equation | appendix | `lambdaLower_eq_rpow; lambdaLower_le_lambdaStar; lambdaStar_le_upper` | `Appendix.AdmissibleParameters; Appendix.AdmissibleLowerBound` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:ODE divide W` | 2659 / appendix | equation | appendix | `WSolution_sq_hasDerivAt; WSolution_sq_deriv_le` | `Appendix.AdmissibleLowerBound` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:lambda-integral-W` | 2678 / appendix | equation | appendix | `WSolution_compact_integral_identity; lambda_eq_integral` | `Appendix.AdmissibleLowerBound` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:subcritical-W` | 2710 / appendix | proposition | appendix | `subcriticalW` | `Appendix.SubcriticalW` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:subcritical-positive-W` | 2717 / appendix | equation | appendix | `WSolution_zero_pos_of_lt_lambdaStar; WSolution_pos_Ico_of_lt_lambdaStar` | `Appendix.SubcriticalW` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:linear-u1` | 2761 / appendix | lemma | appendix | `linearAtOne; WSolution_linearAtOne` | `Appendix.EndpointAsymptotics` | proved | standard + MI01_global_peano_on_compact_interval |
| `lem:u0-dichotomy` | 2809 / appendix | lemma | appendix | `leftEndpointDichotomy_source` | `Appendix.LeftEndpointDichotomy` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:u0-linear` | 2814 / appendix | equation | appendix | `HasLinearBranchAtZero` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:u0-sharp` | 2817 / appendix | equation | appendix | `HasSharpBranchAtZero` | `Appendix.BasicDefs` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:r-inverse` | 2853 / appendix | equation | appendix | `LeftLocalInverseData; leftEndpoint_sourceLocalInverse` | `Appendix.LeftEndpointDichotomy` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:r-limsup` | 2865 / appendix | equation | appendix | `localInverse_ratio_eventually_lt_lambda_add` | `Appendix.LeftEndpointDichotomy` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:r-flow` | 2872 / appendix | equation | appendix | `logRatioFlowRhs; logRatioFlow_derivative_identity` | `Appendix.LeftEndpointDichotomy` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `prop:critical-branches` | 2929 / appendix | proposition | appendix | `criticalBranches` | `Appendix.CriticalBranches` | proved | standard + MI01_global_peano_on_compact_interval |
| `eq:critical-sharp-branch` | 2934 / appendix | equation | appendix | `lambdaStar_not_linearBranch; criticalBranches_of_dichotomy` | `Appendix.CriticalBranches` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:supercritical-linear-branch` | 2940 / appendix | equation | appendix | `supercritical_linear_of_dichotomy` | `Appendix.CriticalBranches` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `app:regularity` | 2997 / appendix | section | manuscript | — | — | doc-only | doc-only |
| `lem:finite-asymptotic-ode` | 3008 / appendix | lemma | appendix | `finiteAsymptoticODE_source` | `Appendix.FiniteAsymptoticODE` | proved | standard |
| `eq:asymptotically-autonomous-ode` | 3023 / appendix | equation | appendix | `IsAsymptoticallyAutonomousSolutionSource; asymptoticallyAutonomousRhs` | `Appendix.FiniteAsymptoticODE` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:finite-asymptotic-expansion` | 3035 / appendix | equation | appendix | `FiniteAsymptoticExpansion; finiteAsymptoticRemainder` | `Appendix.FiniteAsymptoticODE` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:D8-bound` | 3071 / appendix | equation | appendix | `recursive_defect8_isBigO; reciprocalDefect8_deriv_isBigO` | `Appendix.FiniteAsymptoticODE` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:R-linear-equation` | 3079 / appendix | equation | appendix | `remainder_linear_equation; eventually_remainder_linear_equation` | `Appendix.FiniteAsymptoticODE` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:terminal-integral` | 3125 / appendix | equation | appendix | `terminal_integral_formula` | `Appendix.FiniteAsymptoticODE` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `lem:linear-branch-regularity` | 3153 / appendix | lemma | appendix | `leftLinearBranchRegularity_source; rightLinearBranchRegularity_source; linearBranchRegularity_source` | `Appendix.LinearBranchRegularity` | proved | standard |
| `eq:W-expansion-zero-differentiable` | 3173 / appendix | equation | appendix | `LeftLinearBranchRegularity.differentiableExpansion; leftEndpointDifferentiableExpansion_exactQuadratic` | `Appendix.LinearBranchRegularity` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:W-expansion-one-differentiable` | 3197 / appendix | equation | appendix | `RightLinearBranchRegularity.differentiableExpansion; rightEndpointDifferentiableExpansion_exactQuadratic` | `Appendix.LinearBranchRegularity` | proved | internal/mathlib; MI01-transitive after profile instantiation |
| `eq:W-relative-derivative-bounds` | 3207 / appendix | equation | appendix | `RelativeDerivativeBoundsAtZero; RelativeDerivativeBoundsAtOne` | `Appendix.LinearBranchRegularity` | proved | internal/mathlib; MI01-transitive after profile instantiation |
