# Manuscript–Lean proposition correspondence

Authoritative manuscript: `Distance_and_resistance_SPA_revised_blue.tex`. This report covers every active labelled theorem,
proposition, lemma, and corollary exactly once. The census is **29 statements =
20 main + 9 appendix**. Equation-, figure-, remark-, and
section-level correspondence is recorded separately in [`SOURCE_MAP.md`](SOURCE_MAP.md).

## Principal graph-facing statements

The three principal results are exported in both traditional-graph and scalar forms. Their
equivalence is proved pointwise through the structural realization bridge; the graph-facing
statements therefore do not duplicate the probabilistic or asymptotic arguments.

| Manuscript label | Traditional-graph theorem | Scalar theorem | Contract equivalence |
|---|---|---|---|
| `thm:logarithmic-speeds` | `GraphSemantics.graphLogarithmicSpeeds` | `logarithmicSpeeds` | `GraphSemantics.graphLogarithmicSpeedsStatement_iff` |
| `thm:first-moment-logarithmic-rates` | `GraphSemantics.graphFirstMomentLogarithmicRates` | `firstMomentLogarithmicRates` | `GraphSemantics.graphFirstMomentLogarithmicRatesStatement_iff` |
| `thm:near-critical-speed` | `GraphSemantics.graphResistanceSpeedNearCritical` | `resistanceSpeedNearCritical` | `GraphSemantics.graphResistanceSpeedNearCriticalStatement_iff` |

The deterministic semantic bridge is `SPNetwork.traditionalDistance_realize` for walk distance
and `SPNetwork.traditionalResistance_realize` for Thomson resistance. The graph random variables
are identified with their recursive counterparts by `graphDistanceValue_eq_distanceValue`,
`graphResistanceValue_eq_resistanceValue`, `graphZ_eq_Z`, and `graphX_eq_X`.

## Main-text statements

| Manuscript statement | Label line | Kind | Lean declaration(s) | Defining module(s) | Coverage | Direct axiom fingerprint |
|---|---:|---|---|---|---|---|
| `thm:logarithmic-speeds` | 312 | theorem | `GraphSemantics.graphLogarithmicSpeeds; logarithmicSpeeds` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `thm:first-moment-logarithmic-rates` | 336 | theorem | `GraphSemantics.graphFirstMomentLogarithmicRates; firstMomentLogarithmicRates` | `MainText.GraphSemantics.MainTheorems; MainText.MainTheorems` | proved | standard + distanceGamma_half_eq_zero |
| `thm:near-critical-speed` | 431 | theorem | `GraphSemantics.graphResistanceSpeedNearCritical; resistanceSpeedNearCritical` | `MainText.GraphSemantics.MainTheorems; MainText.ResistanceNearCritical` | proved | standard + MI01_global_peano_on_compact_interval |
| `lem:logarithmic-drift` | 753 | lemma | `X_succ_hasLaw; logarithmic_drift` | `MainText.LogarithmicDrift` | proved | standard |
| `prop:conditional-refinement` | 797 | proposition | `conditional_refinement_core` | `MainText.ConditionalRefinement` | proved | standard |
| `lem:deterministic-bound` | 811 | lemma | `adjacent_Z_rpow; X_iterated_bounds; abs_integral_X_increment_le_log_two` | `MainText.AdjacentBounds` | proved | standard |
| `lem:first-moment-bounds` | 845 | lemma | `firstMoment_succ_lower_bound; firstMoment_geometric_bounds` | `MainText.FirstMomentBounds` | proved | standard |
| `lem:resistance-duality` | 872 | lemma | `log_resistanceValue_complement; complementEnvironment_map` | `MainText.RandomModel; MainText.TreeEnvironment` | proved | standard |
| `lem:exact-cdf` | 920 | lemma | `exact_cdf_operator_density; cdfOperator_mono_of_CDFOrdered; cdfOperator_translate` | `MainText.DensityGateRegions; MainText.GeneralizedInverseCoupling; MainText.CDFOperator` | proved | standard |
| `lem:first-moment-submultiplicativity` | 1050 | lemma | `firstMoment_submultiplicative; normalizedLogFirstMoment_tendsto_feketeLimit` | `MainText.FirstMomentSubmultiplicative` | proved | standard |
| `prop:bounded-Jensen-gap` | 1127 | proposition | `jensenGap_le_uniform_bound; normalizedMeanLog_tendsto_firstMomentLimit` | `MainText.JensenAndCenter` | proved | standard |
| `lem:center-tracking` | 1146 | lemma | `centered_X_uniform_bound; centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero` | `MainText.JensenAndCenter` | proved | standard |
| `lem:normalized-L2` | 1239 | lemma | `normalizedSecondMoment_le_bound` | `MainText.NormalizedSecondMoment` | proved | standard |
| `lem:diffusion-coefficient` | 1451 | lemma | `diffusionCoefficient_eq_two_mul_zetaThree` | `MainText.DiffusionCoefficientClosedForm` | proved | standard |
| `prop:full-line-distribution` | 1496 | proposition | `full_line_distribution; full_line_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `prop:hard-edge-distribution` | 1545 | proposition | `hard_edge_distribution; hard_edge_density_probability` | `MainText.ProfileFacade` | proved (façade) | standard + MI01_global_peano_on_compact_interval |
| `lem:weighted-consistency` | 1698 | lemma | `full_line_weighted_consistency` | `MainText.WeightedConsistency` | proved | standard |
| `lem:upper-cutoff-error` | 1767 | lemma | `affineWaveProfile_cdfOperator_le_upperBarrier_add_error` | `MainText.UpperBarrier` | partial (theorem-path bound proved) | standard |
| `lem:hard-edge-consistency` | 2102 | lemma | `hard_edge_weighted_lower_consistency` | `MainText.HardEdgeConsistency` | proved | standard |
| `prop:hard-edge-barrier` | 2132 | proposition | `hard_edge_global_lower_barrier` | `MainText.HardEdgeConsistency` | proved | standard |

## Appendix statements

| Manuscript statement | Label line | Kind | Lean declaration(s) | Defining module(s) | Coverage | Direct axiom fingerprint |
|---|---:|---|---|---|---|---|
| `lem:cuberoot-comparison` | 2522 | lemma | `cuberoot_comparison_source` | `Appendix.CubeRootComparison` | proved | standard |
| `lem:shooting-properties` | 2554 | lemma | `shootingProperties` | `Appendix.Shooting` | proved | standard + MI01_global_peano_on_compact_interval |
| `prop:Cstar-halfline` | 2661 | proposition | `cstarHalfline; existsUnique_boundarySolution_iff_lambdaStar_le; lambdaLower_eq_rpow` | `Appendix.AdmissibleHalfline; Appendix.AdmissibleParameters` | proved | standard + MI01_global_peano_on_compact_interval |
| `prop:subcritical-W` | 2761 | proposition | `subcriticalW` | `Appendix.SubcriticalW` | proved | standard + MI01_global_peano_on_compact_interval |
| `lem:linear-u1` | 2812 | lemma | `linearAtOne; WSolution_linearAtOne` | `Appendix.EndpointAsymptotics` | proved | standard + MI01_global_peano_on_compact_interval |
| `lem:u0-dichotomy` | 2860 | lemma | `leftEndpointDichotomy_source` | `Appendix.LeftEndpointDichotomy` | proved | standard + MI01_global_peano_on_compact_interval |
| `prop:critical-branches` | 2980 | proposition | `criticalBranches` | `Appendix.CriticalBranches` | proved | standard + MI01_global_peano_on_compact_interval |
| `lem:finite-asymptotic-ode` | 3059 | lemma | `finiteAsymptoticODE_source` | `Appendix.FiniteAsymptoticODE` | proved | standard |
| `lem:linear-branch-regularity` | 3204 | lemma | `leftLinearBranchRegularity_source; rightLinearBranchRegularity_source; linearBranchRegularity_source` | `Appendix.LinearBranchRegularity` | proved | standard |

## Coverage boundary

The only theorem-like row marked partial is `lem:upper-cutoff-error`. For that row, the Lean project proves
the estimate used along the closed main-theorem path, but does not expose the complete displayed
manuscript lemma as a single standalone declaration. In the fingerprint column, `standard` means
exactly `propext`, `Classical.choice`, and `Quot.sound`. The two project axioms that occur are
`distanceGamma_half_eq_zero` (the cited critical distance input) and
`MI01_global_peano_on_compact_interval` (the external compact-interval ODE existence input).
Several analytic declarations take a profile as a theorem parameter and therefore have a
standard direct fingerprint even though a closed profile construction used downstream may invoke
`MI01_global_peano_on_compact_interval`. No row should be read as formalization of surrounding
explanatory prose beyond the labelled mathematical statement.
