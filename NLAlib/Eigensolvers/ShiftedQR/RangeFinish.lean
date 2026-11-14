/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistSolve

/-!
# Finishing the first active range

The exact local eigenvalue listing is written to the range's persistent output cells. The
mathematical finish transition and the stored output transition use the same listing. Earlier
finished ranges and the remaining actual stack are retained by the spatial frame.

## Main results

* `NLAlib.ShiftedQR.finishActive_writes`: one local eigenvalue call advances the full invariant.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has EigenvalueKernelOp O]

/-- Finishing the popped first range uses the actual local block, writes every root with
multiplicity, and advances the progress measure. No output for unfinished ranges is assumed. -/
theorem finishActive_writes {θ : ℝ} {K : KernelRoutines θ} {I : Interp O Q ℝ}
    (hK : IsEigenvalueKernels K I) {tape : Tape ℝ} {μ : Mem ℝ} {n lo d j : ℕ}
    {a p stack out w r : ℕ × ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {roots : Fin (n + 1) → ℂ} {τ ε : ℝ} {rest done : List (ℕ × ℕ)}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hInv : DeflationInv H ε ((lo, d) :: rest) done A roots)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix w (subBlock A (lo, d)) μ.store)
    (hOut : FinishedHolds out done roots μ.store) (hSt : StackHolds stack rest.reverse μ.store)
    (hε : ε = (((((lo, d) :: rest) ++ done).length - 1 : ℕ) : ℝ) * τ)
    (hj : 2 * done.length + ((lo, d) :: rest).length = j + 1) :
    Writes .total I tape (finishRange (O := O) (Q := Q)).body
      (Env.frame [n + 1, lo, d] [w, out])
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))
      (fun μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out (j + 1) μ') μ := by
  let eig := K.smallEig d (subBlock A (lo, d))
  let roots' := setSubVec roots (lo, d) eig
  have hbounds := hInv.active_block (r := (lo, d)) List.mem_cons_self
  have hlen := hInv.length_le
  have hrest : rest.length ≤ n + 1 := by
    simp only [List.length_append, List.length_cons] at hlen
    omega
  have hnewInv : DeflationInv H ε rest ((lo, d) :: done) A roots' := by
    refine hInv.finish (fun i hi => setSubVec_apply_of_not_mem _ _ _ _ hi) ?_
    rw [subVec_setSubVec_self roots (lo, d) eig hbounds.2.1]
    exact K.roots_smallEig _ _
  have hroom : out.2 + 2 * (n + 1) ≤ μ.store.len out.1 := hG.room.2.2.2.1
  have houtFp : Store.inBlock out.1 (out.2 + 2 * lo) (2 * d) ≤
      Store.inBlock out.1 out.2 (2 * (n + 1)) := by fp_sub
  have hOA : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa using hG.disj 3 0 (by omega)
  have hOS : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1))) := by
    simpa using hG.disj 3 2 (by omega)
  have hw := finishRange_writes (τ := tape) hK
    (by simpa [Mem.Live] using And.intro (hG.live w (by simp)) (hG.live out (by simp)))
    hW hbounds.2.1 hroom
  refine hw.mono le_rfl fun μ' hfr ⟨hp, hEig⟩ => ⟨hp, ?_⟩
  have hA' := hA.of_eqOff hfr (hOA.mono houtFp le_rfl)
  have hSt' := hSt.of_eqOff hfr (hOS.mono houtFp (by simp only [List.length_reverse]; fp_sub))
  have hNew : HoldsMatrix (out.1, out.2 + 2 * lo)
      (Matrix.of fun i (_ : Fin 1) => subVec roots' (lo, d) i) μ'.store := by
    simpa only [roots', subVec_setSubVec_self roots (lo, d) eig hbounds.2.1] using hEig
  have hOut' := hOut.cons hfr (fun q hq => (hInv.disjoint_of_mem List.mem_cons_self hq).1)
    (fun q hq => subVec_setSubVec_of_disjoint roots (lo, d) q eig
      (hInv.disjoint_of_mem List.mem_cons_self hq).2
      (hInv.disjoint_of_mem List.mem_cons_self hq).1) hNew
  refine ⟨rest, (lo, d) :: done, A, roots', ε, hnewInv, hA', hOut', hSt', ?_, ?_⟩
  · have he : (rest ++ ((lo, d) :: done)).length = (((lo, d) :: rest) ++ done).length := by
      simp only [List.length_append, List.length_cons]
      omega
    simpa only [he] using hε
  · simp only [List.length_cons] at hj ⊢
    omega

end NLAlib.ShiftedQR
