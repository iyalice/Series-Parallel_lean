# Manuscript--Lean correspondence

Authoritative manuscript source: `Series-Parallel_arxiv_submission.tex`. The table follows its
printed numbering. It contains all 29 theorem, proposition, and lemma environments: 21 in the main
text and 8 in the appendices. TeX labels and TeX line numbers are intentionally confined to
[SOURCE_MAP.md](SOURCE_MAP.md).

Unqualified Lean names below lie in `SeriesParallel.MainText` or `SeriesParallel.Appendix` as
appropriate.

## Main theorems

| PDF result | Lean declaration(s) | Coverage |
|---|---|---|
| Theorem 1.1 (logarithmic speeds) | `GraphSemantics.graphLogarithmicSpeeds`; `logarithmicSpeeds` | complete |
| Theorem 1.2 (first-moment logarithmic rates) | `GraphSemantics.graphFirstMomentLogarithmicRates`; `firstMomentLogarithmicRates` | complete |
| Theorem 1.3 (resistance speed near criticality) | `GraphSemantics.graphResistanceSpeedNearCritical`; `resistanceSpeedNearCritical` | complete |

## Supporting results in the main text

| PDF result | Lean declaration(s) | Coverage |
|---|---|---|
| Lemma 2.1 | `X_succ_hasLaw`; `logarithmic_drift` | exact |
| Proposition 2.2 | `conditional_refinement_core` | exact |
| Lemma 2.3 | `adjacent_Z_rpow`; `X_iterated_bounds`; `abs_integral_X_increment_le_log_two` | exact |
| Lemma 2.4 | `firstMoment_succ_lower_bound`; `firstMoment_geometric_bounds` | exact |
| Lemma 2.5 | `log_resistanceValue_complement`; `complementEnvironment_map` | exact |
| Lemma 2.6 | `seriesCDF_density_formula`; `parallelCDF_density_formula`; `exact_cdf_operator_density`; `cdfOperator_mono_of_CDFOrdered`; `cdfOperator_translate` | exact |
| Lemma 3.1 | `firstMoment_submultiplicative`; `normalizedLogFirstMoment_tendsto_feketeLimit` | exact |
| Proposition 3.2 | `jensenGap_le_uniform_bound`; `normalizedMeanLog_tendsto_firstMomentLimit` | exact |
| Lemma 3.3 | `left_right_X_hasLaw`; `descendant_pair_width_le`; `centered_X_uniform_bound`; `centered_X_ae_tendsto_zero_signed`; `centered_X_div_L1_tendsto_zero` | exact |
| Lemma 3.4 | `normalizedSecondMoment_le_bound` | exact |
| Proposition 4.1 | `cstarHalfline`; `existsUnique_boundarySolution_iff_lambdaStar_le`; `lambdaLower_eq_rpow` | exact |
| Lemma 4.3 | `integral_diffusionIntegrand_eq_zetaThree`; `diffusionCoefficient_eq_two_mul_zetaThree` | exact; the second declaration gives the displayed normalization $a=2\zeta(3)$ |
| Proposition 4.5 | `full_line_distribution`; `full_line_density_probability` | exact |
| Proposition 4.6 | `hard_edge_distribution`; `hard_edge_density_probability` | exact |
| Lemma 4.7 | `full_line_weighted_consistency` | exact |
| Lemma 4.8 | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | the estimate used in Theorem 1.3 is proved; the complete displayed lemma is not exported as one declaration |
| Lemma 4.9 | `hard_edge_weighted_lower_consistency` | exact |
| Proposition 4.10 | `hard_edge_global_lower_barrier` | exact |

## Appendix results

| PDF result | Lean declaration(s) | Coverage |
|---|---|---|
| Lemma A.1 | `cuberoot_comparison_source` | exact |
| Lemma A.2 | `shootingProperties`; `shootingYMap_norm_sub_le` | covers the stated continuity; Lean additionally proves a parameter Lipschitz estimate |
| Proposition A.3 | `subcriticalW` | exact |
| Lemma A.4 | `linearAtOne`; `WSolution_linearAtOne` | exact |
| Lemma A.5 | `leftEndpointDichotomy_source` | exact |
| Proposition A.6 | `criticalBranches` | exact |
| Lemma B.1 | `finiteAsymptoticODE_source` | exact |
| Lemma B.2 | `leftLinearBranchRegularity_source`; `rightLinearBranchRegularity_source`; `linearBranchRegularity_source` | exact |

The qualification for Lemma 4.8 does not affect the closure of any of Theorems 1.1--1.3.
