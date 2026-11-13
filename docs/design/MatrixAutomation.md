# Proof automation for matrix estimates

A sketching proof often composes a measurable random matrix with a pseudoinverse, a
projector, a singular value, or a truncated SVD. These maps already have measurability
theorems. Register the public one-variable and product-domain maps for `fun_prop` in
`Probability/Measurability/Matrix`. Keep the measurable-set and integrability statements
in their own interfaces. For example, for any measurable random matrix `X`, both
`Measurable (fun ω => rangeProjector (X ω))` and
`Measurable (fun ω => singularValues (X ω) k)` should close by composition.

Use `gcongr` on the arguments that preserve or reverse order. The candidate statements
are the Loewner bound for a quadratic form, the spectral norm bound with a positive
semidefinite lower endpoint, Ky Fan order in the count of singular values, the sum of
largest entries, and Schatten antitonicity in a nonzero exponent. The invariant norm
bound permits different index types under pointwise comparison of singular values.
Congruence under a fixed matrix congruence transformation already has a direct theorem.
Its repeated multiplication head does not express monotonicity of unrestricted matrix
multiplication. Keep that statement available for direct application.

Use `simp` for scalar multiples of the nuclear, Ky Fan, Schatten and gauge norms and
for the standard identity frame and its quadratic form. The Schatten rule retains
its nonzero-exponent hypothesis. Give `positivity` access to the padded
`singularValues_nonneg`, including on empty or rank-deficient matrices.
These registrations use the existing public theorems over their original scalar and
index types. Numerical integration, sketching and perturbation proofs supply the
composition and order tests.
