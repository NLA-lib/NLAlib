# Spectral sign and its Newton iteration

For a complex square matrix whose spectrum avoids the imaginary axis, the sign acts by
+1 or −1 on entire primary subspaces. This includes nonnormal and defective matrices.
The matrix function is total; its defining equations are used on the separated domain.

`HalfPlaneSign.lean` uses Mathlib's spectrum, coprime polynomial factors, maximal generalized
eigenspaces, and the library's Sylvester uniqueness theorem. The matrix input is complex
because the definition divides the complex spectrum into two half-planes. The half-sign
projector ranges are stated directly using the supremum of Mathlib's generalized eigenspaces.
The upper triangular Sylvester formula uses the same sign even when the coefficients have
nontrivial Jordan blocks. The Hermitian specialization agrees with the existing CFC sign on
the domain of the spectral sign.

`SignNewton.lean` states convergence of inverse averaging and the exact Cayley formula.
The spectral radius of its initial coordinate is strictly less than one, without imposing an
operator-norm contraction. The proof uses the library's spectral power convergence theorem.

Expected signatures, for arbitrary finite dimensions, include

~~~lean
IsMatrixSign A S → IsMatrixSign A T → S = T
IsMatrixSign A S → a ^ 2 = 1 →
  LinearMap.range (((2 : ℂ)⁻¹ • (1 + a • S)).toLin') =
    ⨆ z : {z : ℂ // 0 < (a*z).re}, Module.End.maxGenEigenspace A.toLin' z.val
IsPositiveStable A → IsPositiveStable B → A * X + X * B = C →
  matrixSign (Matrix.fromBlocks A C 0 (-B)) = Matrix.fromBlocks 1 ((2 : ℂ) • X) 0 (-1)
~~~

Sources are Higham, *Functions of Matrices* (2008), Chapter 5, and the sign files of the
[original atlas](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Functions).
