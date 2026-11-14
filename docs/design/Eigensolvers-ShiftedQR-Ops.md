# Shifted QR: deflation conditioning

## G15: conditioning of a deflated block

The proof of Banks–Garza-Vargas–Srivastava, Shifted QR II, Lemma 6.2, claims that every
eigenvector matrix of a block upper-triangular matrix has the same block form. Shared
eigenvalues invalidate that step. For example, the two-by-two identity is diagonalized by
the coordinate-swap matrix, whose leading one-by-one block is zero.

The conditioning statement is valid. The library proves it with a Cholesky argument:
for `M*V = V*D`, factor `(V^-1)ᴴ*V^-1 = Rᴴ*R` with R upper triangular. Then W=RV is unitary,
and `R*M*R^-1 = W*D*Wᴴ` is normal and block upper triangular. A normal block upper-triangular
matrix is block diagonal. Each block is therefore unitarily diagonalizable, and
`V_r = R_rr^-1*U_r` diagonalizes the original block with
`kappa(V_r) <= kappa(R) = kappa(V)`.

[Matrix.BlockTriangular.exists_pseudoConditionNumber_subBlock_le](../../NLAlib/Matrix/QRIteration/DeflationConditioning.lean)
proves this general block result, including shared eigenvalues.
[IsStarNormal.apply_eq_zero_of_blockTriangular](../../NLAlib/Matrix/Spectral/Normal.lean)
supplies the normal-matrix step. Both are machine-checked.

Positive separation is still needed for the perturbation theorem that precedes the block
argument. A small perturbation of a repeated-eigenvalue matrix can be defective: adding a
nonzero strictly upper-triangular entry to the two-by-two identity gives an example.
`exists_pseudoConditionNumber_add_le` keeps conditioning within a factor two when
`norm(E) <= g/(16*N*C)` and the starting condition bound is C. Taking C=B/2 gives the full
solver's threshold `g/(8*N*B)`. This proves the active-block bound B used by decoupling.
G15 is a repaired proof step; the end-to-end theorem retains its explicit gap assumption.
