# Canonical dependency DAG

```text
common random model and recursion
├─ finite paths + finite flows
│  └─ first-moment submultiplicativity / Fekete
│     ├─ normalized second moment
│     └─ Jensen gap + center tracking
│        └─ remaining parameter ranges
│           ├─ distanceGamma_half_eq_zero ── logarithmicSpeeds
│           └─ distanceGamma_half_eq_zero ── firstMomentLogarithmicRates
├─ exact density CDF regions
│  └─ generalized-inverse coupling / CDF order
├─ diffusion coefficient closed form
└─ appendix profile facade ── MI01
   ├─ weighted consistency ── upper global barrier ─────────────────┐
   └─ weighted consistency ── hard-edge global barrier ── lower iteration ─┤
      parameter squeeze + ε³↔δ + BVP bridge ◀───────────────────────┘
      └─ resistanceSpeedNearCritical
```

The resistance near-critical theorem lives in `ResistanceNearCritical.lean`, separate from the
distance literature interface. This separation is verified by the kernel fingerprint, not just
by textual import inspection.

Literature statements not used by the three main theorems are outside this DAG and are not
represented by project axioms.
