# Axiom report

The project contains exactly two mathematical `axiom` declarations.

## External interfaces

### A1. Critical distance first-moment rate

With

$$\\
\gamma_D(p)=\lim_{n\to\infty}\frac1n\log\mathbb E[D_n(p)],
$$

the admitted statement is

$$\\
\gamma_D\!\left(\frac12\right)=0.
$$

The existence of this limit is proved inside the project; only its critical value is external.
The Lean declaration is
`SeriesParallel.MainText.distanceGamma_half_eq_zero`.

### A2. Compact-interval Peano existence

Let $t_0<T$, $y_0\in\mathbb R$, and let
$F:[t_0,T]\times\mathbb R\to\mathbb R$ be continuous. If $A,B\geq0$ and

$$\\
|F(t,y)|\leq A+B|y|
\qquad(t\in[t_0,T],\ y\in\mathbb R),
$$

then there is a function $y:\mathbb R\to\mathbb R$ such that

$$\\
y(t_0)=y_0,\qquad y|_{[t_0,T]}\in C([t_0,T]),qquad
y'(t)=F(t,y(t))\quad(t_0<t<T).
$$

The Lean declaration is
`SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval`.

## Main-theorem fingerprints

After omitting Lean's standard logical principles, the project-axiom dependencies are exactly:

| PDF result | Lean theorem | Project axiom |
|---|---|---|
| Theorem 1.1 | `SeriesParallel.MainText.logarithmicSpeeds` | A1 only |
| Theorem 1.2 | `SeriesParallel.MainText.firstMomentLogarithmicRates` | A1 only |
| Theorem 1.3 | `SeriesParallel.MainText.resistanceSpeedNearCritical` | A2 only |

In particular, Theorem 1.3 is independent of A1, while Theorems 1.1 and 1.2 are independent of A2.
The closed-form identity for the diffusion coefficient, including
$a=2\zeta(3)$, is proved internally and is not an external interface.

The complete `#print axioms` output also contains `propext`, `Classical.choice`, and `Quot.sound`.
These are standard Lean logical principles, not additional mathematical assumptions about the
series--parallel model.

The lexical audit reports exactly these two project axioms and no `sorry`, `admit`, `unsafe`, or
opaque proof escape.
