/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.HessenbergDeflation
public import NLAlib.Matrix.Perturbation.UnitarySimilarity

/-!
# Deflation with perturbed block steps

The deflation invariant `NLAlib.DeflationInv` records the current blocks as the diagonal blocks
of $\mathbf{U}^{\mathsf H}(\mathbf{H} + \mathbf{E})\mathbf{U}$ with $\|\mathbf{E}\|_2 \le
\varepsilon$. In exact arithmetic an active block changes by a unitary similarity
(`NLAlib.DeflationInv.conj`); in floating point it changes by a **perturbed** unitary similarity,
and a small eigenvalue routine returns the roots of a perturbed block. Both add their backward
error to $\varepsilon$, because a perturbation of one diagonal block embeds into the whole matrix
with the same spectral norm and keeps the block triangular structure
(`NLAlib.IsPerturbedUnitarySimilar.exists_submatrix`). The invariant can also be re-based at the
current matrix: the accumulated perturbation becomes one perturbed unitary similarity from
$\mathbf{H}$, and the invariant holds with error $0$ from there. This is how a worklist round is
composed as a backward step ([BanksGarzaVargasSrivastava2022, §6], Theorem 6.3, backward half).

## Main results

* `NLAlib.DeflationInv.exists_isPerturbedUnitarySimilar_rebase`: re-basing at the current matrix.
* `NLAlib.DeflationInv.setSubBlock_of_isPerturbedUnitarySimilar`: a perturbed similarity of an
  active block.
* `NLAlib.DeflationInv.finish_of_specNorm_le`: a block finished with the roots of a perturbed
  block.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Re-basing the deflation invariant**: if the invariant holds for $\mathbf{H}$ with error
$\varepsilon$, there is a matrix $\mathbf{M}$, a perturbed unitary similarity of $\mathbf{H}$ with
backward error $\varepsilon$, for which the invariant holds with error $0$ and the same ranges,
current matrix and outputs. -/
theorem DeflationInv.exists_isPerturbedUnitarySimilar_rebase
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H M ε ∧
      DeflationInv M 0 active done A out := by
  obtain ⟨M, U, E, hU, hE, hM, hrest⟩ := h
  exact ⟨M, ⟨U, E, hU, hE, hM⟩, M, 1, 0, hasOrthonormalCols_one, by rw [specNorm_zero],
    by simp, hrest⟩

/-- **A perturbed unitary similarity of an active block**: if the invariant holds with error
$\varepsilon$, $r$ is an active range, and $\mathbf{B}'$ is upper Hessenberg and a perturbed
unitary similarity of the block of $\mathbf{A}$ on $r$ with backward error $e$, the invariant
holds with error $\varepsilon + e$ after writing $\mathbf{B}'$ into that block. -/
theorem DeflationInv.setSubBlock_of_isPerturbedUnitarySimilar
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε e : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) {r : ℕ × ℕ}
    (hr : r ∈ active) {B' : Matrix (Fin r.2) (Fin r.2) ℂ}
    (hB : IsPerturbedUnitarySimilar (subBlock A r) B' e) (hHess : IsUpperHessenberg B') :
    DeflationInv H (ε + e) active done (setSubBlock A r B') out := by
  sorry

/-- **Finishing a block with the roots of a perturbed block**: if the invariant holds with error
$\varepsilon$ and the first active range $r$, $\|\mathbf{F}\|_2 \le \beta$, and the output
`out'` agrees with `out` off $r$ and lists on $r$ the roots (with multiplicity) of the block of
$\mathbf{A}$ on $r$ plus $\mathbf{F}$, then $r$ is finished with error $\varepsilon + \beta$. -/
theorem DeflationInv.finish_of_specNorm_le
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε β : ℝ} {r : ℕ × ℕ}
    {rest done : List (ℕ × ℕ)} {out out' : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε (r :: rest) done A out) {F : Matrix (Fin r.2) (Fin r.2) ℂ}
    (hF : specNorm F ≤ β)
    (hout : ∀ j : Fin (n + 1), ¬(r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2) → out' j = out j)
    (hroots : (subBlock A r + F).charpoly.roots = (List.ofFn (subVec out' r) : Multiset ℂ)) :
    DeflationInv H (ε + β) rest (r :: done) A out' := by
  sorry

end NLAlib
