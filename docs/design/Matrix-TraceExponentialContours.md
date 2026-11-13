# Contour deformation for the Hermitian trace exponential

This note records the design after PR #101 merged.

The density calculation in `TraceExponentialDensity.lean` takes the real part of
a normalized exponential circle moment. Its scalar inputs are a holomorphic
function off a closed real segment, reflection symmetry, and a nonnegative
imaginary part in the open upper half-plane. The matrix proof bounds this function
on the closed disk of the contour radius. The scalar positivity theorem should
accept exactly that bound.

```lean
Complex.neg_exp_circleIntegral_re_nonneg
    {h : ℂ → ℂ} {R M C : ℝ} (hM : 0 < M) (hRM : R < M)
    (hh : DifferentiableOn ℂ h {z | z.im ≠ 0 ∨ R < ‖z‖})
    (href : ∀ z : ℂ, h (conj z) = conj (h z))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ M → ‖h z‖ ≤ C) :
    0 ≤ (-((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, M), exp z * h z))).re
```

For horizontal semiaxis M and vertical semiaxis ε between zero and M, the
ellipse lies in this disk. This follows from its squared norm and the
trigonometric identity for the sum of squares. Only such thin ellipses enter
the limiting argument. The center and exponential weight are those used by
the Hermitian pencil, where reflection and the upper half-plane determine the sign.

The circle-to-ellipse and exterior-circle deformations need a continuous free
homotopy and continuously differentiable end paths. Mathlib v4.33.1 has
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`,
which takes a twice continuously differentiable homotopy of a closed form.
Use the same bundled homotopy object for the holomorphic specialization:

```lean
ContinuousMap.Homotopy.integral_eq_of_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {a b : ℂ} {γ₀ : Path a a} {γ₁ : Path b b}
    (H : (γ₀ : C(I, ℂ)).Homotopy γ₁) {Ω : Set ℂ} {g : ℂ → E}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (himage : ∀ p, H p ∈ Ω) (hloop : ∀ t : I, H (t, 0) = H (t, 1))
    (hγ₀ : ContDiffOn ℝ 1 γ₀.extend I) (hγ₁ : ContDiffOn ℝ 1 γ₁.extend I) :
    curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₀ =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₁
```

The existing real-parameter interface constructs this homotopy by restriction
to the unit square. Its two consumers can continue supplying their explicit
parametrizations. Local primitives and the subdivision grid stay internal.
The scalar modules contain the circle and ellipse parametrizations, exterior
Cauchy identities, and homotopy invariance. The matrix consumer supplies the
positive density for [Stahl, Theorems 1 and 2](https://doi.org/10.1007/s11511-013-0104-z).

Radius independence on an exterior domain reuses the pinned
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`.
The same statement works for an arbitrary center and a normed complex range.

```lean
Complex.circleIntegral_eq_of_differentiableOn_compl_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {c : ℂ} {R r s : ℝ} (hf : DifferentiableOn ℂ f (closedBall c R)ᶜ)
    (hr : 0 < r) (hs : 0 < s) (hRr : R < r) (hRs : R < s) :
    (∮ z in C(c, r), f z) = ∮ z in C(c, s), f z
```

The exterior Cauchy kernel and the radius independence of each trace density
branch specialize this to center zero. The Schwarz positivity inequality
continues to use complex values because it orders their imaginary parts.

## Vector-valued contour integrals

The grid adds increments of local primitives in a complex Banach space.
Use `HasDerivAt G (g z) z` and the differential
`(ContinuousLinearMap.id ℂ ℂ).smulRight (g z)` for a bundled homotopy.
The scalar real-parameter form serves the ellipse and exterior-circle
consumers. Chart independence needs only a complex normed space. Integration
and existence of primitive charts use completeness.
The scalar homotopy result is Cauchy's theorem in
[Stewart and Tall, Chapter 9](https://doi.org/10.1017/9781108505468.012).
