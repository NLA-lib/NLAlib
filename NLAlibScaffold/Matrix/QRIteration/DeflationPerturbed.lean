/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.HessenbergDeflation
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.Spectral.Schur

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
  obtain ⟨M, U, E, hUU, hE, hM, hpart, hbt, hact, hdone⟩ := h
  have hrm : r ∈ active ++ done := List.mem_append_left _ hr
  have hBM : IsPerturbedUnitarySimilar (M.submatrix (blockIndex n r) (blockIndex n r)) B' e := by
    have : subBlock M r = subBlock A r := (hact r hr).1
    rw [← this] at hB; exact hB
  obtain ⟨M', hMM', hsub, hoff, hbtk⟩ := hBM.exists_submatrix (hpart.blockIndex_injective hrm)
  obtain ⟨U', E', hU', hE', hM'⟩ := (show IsPerturbedUnitarySimilar H M ε from
    ⟨U, E, hUU, hE, hM⟩).trans hMM'
  -- a block of another range of the partition is unchanged
  have hother : ∀ r' ∈ active ++ done, r' ≠ r → subBlock M' r' = subBlock M r' := by
    intro r' hr' hne
    ext a b
    exact hoff _ _ (fun ⟨c, hc⟩ => hpart.blockIndex_ne hrm hr' hne a c hc.symm)
      (fun ⟨c, hc⟩ => hpart.blockIndex_ne hrm hr' hne b c hc.symm)
  have hset := hpart.subBlock_setSubBlock hrm A B'
  refine ⟨M', U', E', hU', hE', hM', hpart, hbtk _ r.1 (fun a => ?_) hbt, fun r' hr' => ?_,
    fun r' hr' => ?_⟩
  · have := hpart.val_blockIndex hrm a
    exact hpart.rangeLabel_eq hrm (by omega) (by omega)
  · by_cases hne : r' = r
    · subst hne
      exact ⟨hsub.trans hset.1.symm, by rw [hset.1]; exact hHess⟩
    · have hr'm := List.mem_append_left done hr'
      rw [hother r' hr'm hne, hset.2 r' hr'm hne]
      exact hact r' hr'
  · have hne : r' ≠ r := fun h => (List.nodup_append.mp hpart.1).2.2 r hr r' hr' h.symm
    rw [hother r' (List.mem_append_right _ hr') hne]
    exact hdone r' hr'

/-- The invariant reads the current matrix only through its active blocks: if two matrices have
the same active blocks, the invariant holds for one exactly when it holds for the other. -/
theorem DeflationInv.congr_active
    {H A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out)
    (hA : ∀ r ∈ active, subBlock A' r = subBlock A r) :
    DeflationInv H ε active done A' out := by
  obtain ⟨M, U, E, hUU, hE, hM, hpart, hbt, hact, hdone⟩ := h
  exact ⟨M, U, E, hUU, hE, hM, hpart, hbt, fun r hr => by rw [hA r hr]; exact hact r hr, hdone⟩

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
  -- triangularize the perturbed block: a Hessenberg perturbed similarity with error `β`
  obtain ⟨V, hV, hT⟩ := exists_hasOrthonormalCols_isUpperTriangular (subBlock A r + F)
  have hB : IsPerturbedUnitarySimilar (subBlock A r) (Vᴴ * (subBlock A r + F) * V) β := by
    simpa using ((isPerturbedUnitarySimilar_add (subBlock A r) F).trans
      (hV.isPerturbedUnitarySimilar _)).mono (by simpa using hF)
  have hHess : IsUpperHessenberg (Vᴴ * (subBlock A r + F) * V) := fun i j hij =>
    hT (show j < i by rw [Fin.lt_def]; omega)
  have h' := h.setSubBlock_of_isPerturbedUnitarySimilar List.mem_cons_self hB hHess
  have hpart : IsRangePartition (n + 1) (r :: rest ++ done) := by
    obtain ⟨_, _, _, _, _, _, hpart, -⟩ := h; exact hpart
  have hset := hpart.subBlock_setSubBlock (by simp) A (Vᴴ * (subBlock A r + F) * V)
  have hcp : (Vᴴ * (subBlock A r + F) * V).charpoly = (subBlock A r + F).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hV.mul_conjTranspose_self, Matrix.one_mul]
  have h'' := h'.finish hout (by rw [hset.1, hcp, hroots])
  refine h''.congr_active fun r' hr' => ?_
  have hne : r' ≠ r := fun h =>
    (List.nodup_cons.mp (List.nodup_append.mp hpart.1).1).1 (h ▸ hr')
  exact (hset.2 r' (by simp [hr']) hne).symm

end NLAlib
