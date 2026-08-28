# Encoding notes

## Core model

- One common uniform-coordinate Bernoulli environment realizes every parameter and makes
  parameter monotonicity samplewise.
- `SPNetwork` is a two-terminal syntax tree rather than a Mathlib general graph. Its recursive
  distance evaluator is proved equal to the minimum recursive path length, and its recursive
  resistance evaluator is proved equal to the minimum unit-flow energy. These are verified
  encoding equivalences, not definitional equalities with general graph APIs.
- `Z_succ` is a stronger samplewise recursion on the common environment; subtree independence
  and `X_succ_hasLaw` recover the manuscript's independent-copy distributional recursion.
- `paperLog` maps zero to `EReal.bot`, preserving the paper's `log 0 = -∞` convention while
  keeping `gammaD` and `gammaR` real-valued.

## CDF and barriers

- The CDF operator remains measure-backed. Exact integral formulas are restricted to density
  laws; generalized-inverse coupling proves monotonicity for arbitrary probability laws,
  including a zero atom after the upper cutoff.
- Full-line and half-line weighted Taylor estimates use relative derivative bounds. The
  hard-edge positive extension is analytic scaffolding only; it is never declared a probability
  density.
- The lower barrier has three explicit regions. In the transition strip a fixed rectangle gives
  `Iplus ≥ c ε²`, while `Iminus = 0`; this dominates the translated `O(ε³)` profile mass.

## Limits and ODE bridge

- Near-critical powers use `Real.rpow delta ((2 : ℝ) / 3)` and
  `Real.cbrt zetaThree`; no natural-number division is involved.
- Cubing and `Real.cbrt` are proved cofinal inverse maps on `𝓝[>] 0`, so the result covers the
  full right filter rather than a subsequence.
- `SourceWSolution` is the literal `[0,1]` BVP. Canonical unit extension gives the appendix
  predicate in the reverse direction. Hard-edge uniqueness remains only `EqOn (Set.Ici 0)`.

## Report semantics

`SOURCE_MAP.md` is the sole 156-label map. A `partial (theorem-path bound proved)` row means the
exact display has no exported standalone two-sided wrapper; it does not mean a main theorem is
conditional or incomplete.
