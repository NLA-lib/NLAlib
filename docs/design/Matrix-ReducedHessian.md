# Equality constraints and the reduced Hessian

The `kkt-reduced-hessian` atlas card concerns an equality constraint `B x = g`. A solver needs
to decide when the saddle-point system is invertible, to recover its multiplier from a null-space
solution, and to know when its primal solution minimizes a quadratic on the constraint set.
The algebraic results permit an arbitrary square matrix `H`. Minimization uses `H.IsHermitian`
and permits `H` to be indefinite on the ambient space.

`Matrix/Structured/ReducedHessian.lean` uses the literal block matrix `fromBlocks H Bᴴ B 0` and
the compression `Zᴴ * H * Z`. Full row rank is `Function.Injective Bᴴ.mulVec`.
`Function.Exact Z.mulVec B.mulVec` says that the columns of `Z` span the kernel of `B`.
Together with `Function.Injective Z.mulVec` this allows any null-space basis. An orthonormal
basis supplies injectivity through `HasOrthonormalCols.mulVec_injective` and its range equality
supplies exactness through `LinearMap.exact_iff`. All index types are arbitrary finite types,
including the zero-dimensional kernel and constraint space, over either real or complex scalars.

* The block matrix is a unit exactly when the compression is a unit.
* `mulVec_fromBlocks_eq_of_mulVec_eq` reconstructs the solution. For a feasible `xp` and
  solution `y` of the compressed equation, `x = xp + Z y` and
  `l = (B Bᴴ)⁻¹ B (f − H x)` solve the two saddle-point equations. The reverse implication
  reads off the compressed equation from stationarity.
* `quadraticObjective H f x` is half the real part of `quadForm H x` minus the real part of
  `fᴴx`. The change in objective between a stationary feasible point and a feasible displacement
  is half the reduced quadratic form. The compression is positive definite exactly when every
  pair `f,g` has a unique feasible minimizer. The right side uses Mathlib's `IsMinOn` on the
  affine feasible set together with explicit membership. A Hermitian witness `hH` supplies
  `hH.forall_existsUnique_isMinOn_quadraticObjective_iff` directly.

The block, Gram, quadratic form, definiteness, and minimization APIs are already available in
Mathlib and NLAlib. The existing saddle-point inertia result assumes positivity of the ambient
block. Here full row rank supplies the inverse in multiplier recovery through the existing Gram
criterion. Exactness supplies coordinates for feasible displacements and eliminates the multiplier
from the reduced equation. These two steps are shared by the solver and minimizer proofs.

Source: Benzi, Golub and Liesen, *Numerical solution of saddle point problems*, Acta Numerica
14 (2005), §6, equations (6.1)–(6.2). The complex case uses adjoints. The minimizer equivalence
follows by completing the square and testing the homogeneous constrained problem. The original
atlas source is `tchen-research/NLAlib`, commit `77514ce`, card `kkt-reduced-hessian`.

## Public signatures

Here `B : Matrix m n 𝕜` and `Z : Matrix n r 𝕜` are indexed by arbitrary finite types over an `RCLike` field.

```lean
theorem isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul [DecidableEq m] [DecidableEq n]
    [DecidableEq r] (H : Matrix n n 𝕜) (h : Function.Exact Z.mulVec B.mulVec)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    IsUnit (fromBlocks H Bᴴ B 0) ↔ IsUnit (Zᴴ * H * Z)

theorem mulVec_fromBlocks_eq_of_mulVec_eq [DecidableEq m] (H : Matrix n n 𝕜)
    (h : Function.Exact Z.mulVec B.mulVec) (hB : Function.Injective Bᴴ.mulVec)
    {f xp : n → 𝕜} {g : m → 𝕜} {y : r → 𝕜} (hxp : B *ᵥ xp = g)
    (hy : (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp)) :
    (fromBlocks H Bᴴ B 0) *ᵥ Sum.elim (xp + Z *ᵥ y)
      ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ (f - H *ᵥ (xp + Z *ᵥ y)))) = Sum.elim f g

theorem Matrix.IsHermitian.forall_existsUnique_isMinOn_quadraticObjective_iff
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (h : Function.Exact Z.mulVec B.mulVec)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    (∀ (f : n → 𝕜) (g : m → 𝕜),
      ∃! x, B *ᵥ x = g ∧ IsMinOn (quadraticObjective H f) {v | B *ᵥ v = g} x) ↔
      (Zᴴ * H * Z).PosDef
```

## Supplying a null-space basis

A caller usually knows that the columns of `Z` span the kernel of `B`. The pinned
Mathlib theorem `LinearMap.exact_iff` converts this directly into the hypothesis
of the solver and minimizer theorems.

```lean
example (h : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin) :
    Function.Exact Z.mulVec B.mulVec :=
  (LinearMap.exact_iff (f := Z.mulVecLin) (g := B.mulVecLin)).2 h.symm
```

The public linear maps are Mathlib's matrix-vector linear maps. A numerical
null-space basis supplies exactness and independent columns as separate facts.

The numerical null-space basis certificate gives the invertibility test directly
through the following corollary in `Structured/ReducedHessian`. The other
reconstruction and optimization theorems can share the exactness proof above.

```lean
theorem isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul_of_range_eq_ker
    [DecidableEq m] [DecidableEq n] [DecidableEq r] (H : Matrix n n 𝕜)
    (h : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    IsUnit (fromBlocks H Bᴴ B 0) ↔ IsUnit (Zᴴ * H * Z)
```
