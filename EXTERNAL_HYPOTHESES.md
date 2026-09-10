# External mathematical hypotheses

The formalization uses exactly the following two external facts.

## 1. Critical distance first-moment rate

Let

$$\\
\gamma_D(p)=\lim_{n\to\infty}\frac1n\log\mathbb E[D_n(p)].
$$

The admitted value is

$$\\
\boxed{\gamma_D\!\left(\frac12\right)=0.}
$$

Equivalently,

$$\\
\lim_{n\to\infty}\frac1n
\log\mathbb E\!\left[D_n\!\left(\frac12\right)\right]=0.
$$

The existence of the limit is proved internally; the external input supplies only its value at
$p=1/2$. In Lean this is
`SeriesParallel.MainText.distanceGamma_half_eq_zero`. It is used only in Theorems 1.1 and 1.2.

## 2. Peano existence on a compact interval

Let $t_0<T$, $y_0\in\mathbb R$, and let

$$\\
F:[t_0,T]\times\mathbb R\longrightarrow\mathbb R
$$

be continuous. Suppose that $A,B\geq0$ and

$$\\
|F(t,y)|\leq A+B|y|
\qquad (t\in[t_0,T],\ y\in\mathbb R).
$$

Then there exists a function $y:\mathbb R\to\mathbb R$ such that

$$\\
y(t_0)=y_0,\qquad y|_{[t_0,T]}\in C([t_0,T]),
$$

and

$$\\
y'(t)=F(t,y(t))\qquad(t_0<t<T).
$$

No assertion is made about $y$ outside $[t_0,T]$. In Lean this is
`SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval`. It is used only in
Theorem 1.3.

No other external mathematical hypothesis occurs in the proof of the three main theorems.
