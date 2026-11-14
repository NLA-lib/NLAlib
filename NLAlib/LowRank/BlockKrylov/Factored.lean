/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.GolubKahan.Band.Run
public import NLAlib.LowRank.Structural.BlockKrylov

/-!
# Randomized block Krylov iteration in factored form

Block Golub–Kahan bidiagonalization with full reorthogonalization returns the left basis
$\mathbf{U}$, the right basis $\mathbf{V}$ and the coefficient matrix $\mathbf{S}$. In exact
arithmetic their product $\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ is
$\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$ (`NLAlib.rbki`), for every input and every exact
orthogonalization scheme; this is the Krylov-layer identity
`NLAlib.IsBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rsvd` read through
`NLAlib.rbki_def`. Every theorem about `NLAlib.rbki` then holds of the factored output.
Design: `docs/design/LowRank-BlockLanczos.md` §3.1, §4.1.

## Main results

* `NLAlib.IsBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rbki`: the factored output of
  the process is `NLAlib.rbki`.
* `NLAlib.Krylov.GolubKahan.Band.IsExactStoredRun.mul_conjTranspose_mul_conjTranspose_eq_rbki`:
  the same for the stored blocks of an exact run of the program.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The factored output of block Golub–Kahan bidiagonalization in exact arithmetic is randomized
block Krylov iteration: if $\mathbf{U}$, $\mathbf{V}$, $\mathbf{R}_0$, $\mathbf{R}$, $\mathbf{S}$
are related to $\mathbf{A}$, $\mathbf{\Omega}$, $q$ by the process, then
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q),$$
for every $\mathbf{A}$, every start block $\mathbf{\Omega}$ and every exact orthogonalization
scheme: dependent start columns, rank-deficient $\mathbf{A}$ and breakdown inside the run are
included. -/
theorem IsBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rbki {𝕜 : Type*} [RCLike 𝕜]
    {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} {Ω : Matrix (Fin n) (Fin b) 𝕜}
    {U : Matrix (Fin m) (Fin (q * b)) 𝕜} {V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜}
    {R₀ : Matrix (Fin b) (Fin b) 𝕜} {R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜}
    {S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜} (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    U * Sᴴ * Vᴴ = rbki A Ω q := by
  rw [rbki_def]
  exact h.mul_conjTranspose_mul_conjTranspose_eq_rsvd

/-- The stored factors of an exact run of the block Golub–Kahan program are randomized block
Krylov iteration: if $\mathbf{U}$, $\mathbf{V}$ and the packed coefficient block columns
$\mathbf{S}_j$ are stored blocks of an exact run for $\mathbf{A}$ from $\mathbf{\Omega}$, and
$\mathbf{S}$ is the assembled $(q+1)b \times qb$ matrix, then
$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$. -/
theorem Krylov.GolubKahan.Band.IsExactStoredRun.mul_conjTranspose_mul_conjTranspose_eq_rbki
    {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {Ω : Matrix (Fin n) (Fin b) ℝ}
    {U : Matrix (Fin m) (Fin (q * b)) ℝ} {V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ}
    {G : Matrix (Fin b) (Fin b) ℝ} {R : (j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ}
    {S : (j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ}
    (h : Krylov.GolubKahan.Band.IsExactStoredRun A b q Ω U V G R S) :
    U * (Krylov.GolubKahan.Band.assembleRight b q S)ᴴ * Vᴴ = rbki A Ω q :=
  h.isBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rbki

end NLAlib
