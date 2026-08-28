# Canonical statement inventory

The authoritative TeX contains **156 active unique labels**:

| Region | Metadata | Statement environments | Formula labels | Total |
|---|---:|---:|---:|---:|
| main | 14 | 20 | 78 | 112 |
| appendix | 2 | 9 | 33 | 44 |
| total | 16 | 29 | 111 | 156 |

## Main text

The 20 statement environments comprise 3 theorems, 12 lemmas, and 5 propositions.

- All three source-facing theorems are compiled with their complete contract:
  `logarithmicSpeeds`, `firstMomentLogarithmicRates`, and
  `resistanceSpeedNearCritical`. The first two use equivalent limit packaging; the third is a
  direct semantic translation of the manuscript theorem.
- The path/flow, exact-CDF, Fekete, normalized-L2, Jensen/center, diffusion,
  weighted-consistency, and hard-edge statements are compiled.
- Both profile propositions are closed through `ProfileFacade`; their canonical instantiation
  is MI01-transitive.
- Nineteen statement environments have exact exported closure. The upper cutoff-error lemma is
  marked partial only because the exported theorem gives the bound consumed by the global
  barrier without separately packaging every displayed two-sided clause.

Among the 78 main formula labels, 74 are closed, 1 literature-citation display is outside the
three-theorem formalization scope, and 3 retain the same non-blocking standalone-wrapper
qualification. The exact per-label status, module, declaration, and trust class are in
`SOURCE_MAP.md`.

## Appendix

All 9 appendix result environments (A1–A7 and B1–B2) and their 33 formula labels are compiled.
The 11 profile labels moved by the current TeX remain `TeX owner = main` and
`implementation owner = appendix/façade`; they are counted once. Hard-edge profile uniqueness
is `EqOn` on `Set.Ici 0`, not an unjustified whole-line equality.
