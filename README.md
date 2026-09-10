# Lean formalization of random series--parallel graphs

This repository accompanies *Distance and resistance on random series--parallel graphs:
logarithmic speeds and near-critical asymptotics*. The Lean 4 formalization of all three main
theorems is complete.

## Formalized results

Let $D_n(p)$ and $R_n(p)$ be the boundary-to-boundary graph distance and effective resistance at
depth $n$.

1. **Theorem 1.1 (logarithmic speeds).** For every $p\in[0,1]$, there are deterministic constants
   $v_D(p)$ and $v_R(p)$ such that
   
   $$\\
   \frac{1}{n}\log D_n(p)\longrightarrow v_D(p),\qquad
   \frac{1}{n}\log R_n(p)\longrightarrow v_R(p)
   $$
   
   almost surely and in $L^1$. Moreover, $v_D(p)=0$ for $p\leq 1/2$,
   $v_R(1-p)=-v_R(p)$, and $v_D(p),v_R(p)\in[\log(2p),\log 2]$ for $p>1/2$.

3. **Theorem 1.2 (first-moment logarithmic rates).** For every $p\in[0,1]$, the limits
   $$
   \gamma_D(p)=\lim_{n\to\infty}\frac{1}{n}\log\mathbb E D_n(p),\qquad
   \gamma_R(p)=\lim_{n\to\infty}\frac{1}{n}\log\mathbb E R_n(p)
   $$
   exist and satisfy
   $$
   \gamma_D(p)=v_D(p),\qquad
   \gamma_R(p)=v_R(p)\vee\log(2p),
   $$
   where $\log 0=-\infty$. In particular, $\gamma_R(p)=v_R(p)$ for
   $p\in[1/2,1]$.

4. **Theorem 1.3 (resistance speed near criticality).** Let $\lambda_{\*} $ be the least positive
   $\lambda$ for which
   $$
   W^2W'-\lambda W+u(1-u)=0,\qquad W(0)=W(1)=0,
   $$
   has a solution $W\in C([0,1])\cap C^1((0,1))$ that is positive on $(0,1)$. Then, as
   $\delta\downarrow0$,
   $$
   v_R\!\left(\frac12+\delta\right)
   =-v_R\!\left(\frac12-\delta\right)
   \sim 2\zeta(3)^{1/3}\lambda_*\delta^{2/3},
   $$
   and
   $$
   \gamma_R\!\left(\frac12+\delta\right)
   \sim 2\zeta(3)^{1/3}\lambda_*\delta^{2/3},\qquad
   \gamma_R\!\left(\frac12-\delta\right)\sim-2\delta.
   $$

The corresponding Lean declarations are:

| PDF result | Lean declaration |
|---|---|
| Theorem 1.1 | `SeriesParallel.MainText.logarithmicSpeeds` |
| Theorem 1.2 | `SeriesParallel.MainText.firstMomentLogarithmicRates` |
| Theorem 1.3 | `SeriesParallel.MainText.resistanceSpeedNearCritical` |

The two external mathematical inputs are stated in [EXTERNAL_HYPOTHESES.md](EXTERNAL_HYPOTHESES.md)
and audited in [AXIOM_REPORT.md](AXIOM_REPORT.md). The numbered correspondence with the paper is
in [MANUSCRIPT_LEAN_CORRESPONDENCE.md](MANUSCRIPT_LEAN_CORRESPONDENCE.md); the complete label-level
map is [SOURCE_MAP.md](SOURCE_MAP.md).

## Build

The pinned environment is Lean 4.32.1 with mathlib v4.32.1. From the repository root, run:

```text
lake build
```

The project is released under the Apache-2.0 license.
