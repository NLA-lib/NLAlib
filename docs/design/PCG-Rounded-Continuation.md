# Rounded PCG continuation

The consumer is the capped zero-start rounded PCG solver. A successful prefix is represented
by the existing `PCGRun n k`; positivity of earlier divisors belongs to that prefix, whereas
the next direction must be derived from input conditions. No new algorithm or operation
model is introduced.

The proof tracks the defect `r j ⬝ᵥ p j - ν j`. Its exact update uses the line-search
cross-pairing `p j ⬝ᵥ r (j+1)`. These identities remain valid for a nonlinear
`MatvecOracle`, because only its fixed reference matrix and its error guarantee are used.

The files are:

- `Krylov/FinitePrecision/PCGContinuation.lean`: exact defect identities and local norm/error
  estimates, in recurrence order.
- `Krylov/FinitePrecision/PCGContinuationSpectrum.lean`: computed pairing coercivity,
  residual growth, dimensionless direction norm growth, and relative defect propagation.
- `Krylov/FinitePrecision/PCGContinuationPrecision.lean`: scalar geometric estimates,
  simultaneous induction, and the endpoint direction certificate.
- `Krylov/CG/HSPCG/FinitePrecision/Rounds.lean`: the initialized-prefix oracle/direction
  projections and total capped-loop execution, using the same stored cache as the program.

The endpoint signature uses the existing run model directly:

```lean
theorem PCGRun.p_ne_zero_of_r_ne_zero (P : PCGRun n k)
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2)
    (hr : P.r k ≠ 0) : P.p k ≠ 0
```

Intermediate scalar estimates are implementation lemmas, not extra assumptions of a
public solver certificate. For a fixed external cap, monotonicity of the geometric
precision expression supplies this same hypothesis for every shorter prefix.
`PCGRun.p_ne_zero_of_r_ne_zero_of_le_cap` exposes that monotonicity directly.
The quantitative bounds are exposed separately as
`PCGRun.abs_dotProduct_r_p_sub_ν_le` and `PCGRun.norm_r_mul_norm_p_le`.

The quantitative bootstrap bounds both the relative pairing defect and
`‖r j‖ * ‖p j‖ / ν j`. Residual growth is first bounded using the pairing defect;
that growth controls the direction ratio, which then bounds the next defect. Thus
the argument does not assume a lower bound on residual norms along the trajectory.
The cap enters through conservative geometric bounds, not a fixed precision window
claimed to work for arbitrarily many steps.

More precisely, write `K = a'/a`, `T = m'/m`, and `F = 512*K*T`. The induction gives
`|r j ⬝ᵥ p j - ν j| ≤ ε*(2*F)^(j+1)*ν j` and
`‖r j‖*‖p j‖ ≤ F^(j+1)*ν j`. The input precision window makes the first coefficient
at most one half throughout the cap. Coercivity gives a strictly positive numerator
for every nonzero residual, so this pairing bound implies a nonzero search direction.
The sufficient window is deliberately conservative; it remains strictly positive for
each finite cap, but no practical sharpness claim is made for long floating-point runs.

The capped loop keeps a `RunPrefix` invariant for its actual four vectors and computed
stopping pairing. A functional dot law identifies cache refreshes with the adjacent
pairings inside each step; numerical dot inequalities alone do not make that claim.
Every active step derives numerator and curvature positivity from the spectral windows
and the direction continuation theorem. The output is an actual prefix of length at most
the cap; returning before the cap implies an exactly zero residual. Reaching the cap does
not assert convergence. The loop's public theorem takes no successful-run premise.

Existing material reused: `PCGRun`'s recurrence and local errors,
`specNorm_le_and_le_dotProduct` for spectral geometry,
`EuclideanSpace.abs_dotProduct_le_norm` and `norm_toLp_mulVec_le` for norm estimates.
The search of Mathlib and existing Krylov sources found no PCG cross-pairing defect
recurrence. Scalar inequalities use the existing ordered-field API. No Mathlib object
is replaced, no vocabulary definition is added, and no files outside this note and the
new continuation modules are owned by this work.

The existing documented `NLAlib.specNorm_le_and_le_dotProduct` in `CGRun.lean` is
made public: both ordinary and preconditioned CG use precisely its spectral geometry.
Its statement and proof are unchanged. This is the only addition outside the new modules.
