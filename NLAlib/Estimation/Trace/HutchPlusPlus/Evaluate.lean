/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Apply
public import NLAlib.Estimation.Trace.HutchPlusPlus.Accumulate
public import NLAlib.Estimation.Trace.HutchPlusPlus.Math

/-!
# Evaluating the prepared Hutch++ trace estimate

The last operator batch and column contractions evaluate the existing mathematical
estimator on the actual sketch and probes, including rank-deficient sketch images.

## Main results

* `NLAlib.HutchPlusPlus.writes_evaluate` returns the existing mathematical `hutchpp`.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜]

/-- Zero supplies the raw word padding convention in this module. -/
local instance instInhabitedEvaluate : Inhabited 𝕜 := ⟨0⟩

private theorem read_columns {n k : ℕ} {s : Store 𝕜} {b : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin k) 𝕜}
    (h : s.readBlock b.1 b.2 (k * n) = some ((EntryCodec.scalar 𝕜).packFinMatrix A))
    (j : ℕ) (hj : j < k) :
    s.readBlock b.1 (b.2 + n * j) n = some (List.ofFn (column A j)) := by
  rw [column_eq A j hj]
  have hc := Store.readBlock_scalar_matrix_column h ⟨j, hj⟩
  change s.readBlock b.1 (b.2 + j * n) n =
    some (List.ofFn fun i : Fin n => A i ⟨j, hj⟩) at hc
  simpa only [Nat.mul_comm n j] using hc

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has IndexOp Op] [Has StoredOperatorOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- The actual operator batch and trace contractions return `hutchpp` on the supplied
sketch and probes. All workspaces are explicit, with ordinary capacity and separation premises. -/
theorem writes_evaluate (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I)
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I)
    {n k ell : ℕ} {data b t c out : ℕ × ℕ} (as : List 𝕜)
    (S : Matrix (Fin n) (Fin k) 𝕜) (G : Matrix (Fin n) (Fin ell) 𝕜)
    (hl : m.Live [data, b, t, c, out])
    (hAP : Fp.Apart [data, b, t, c, out]
      [dataLength n n, (k + ell) * n, 2, (k + ell) * n, 1])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hBInput : m.store.readBlock b.1 b.2 ((k + ell) * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix
        (projectedBasis (gramSchmidtQ (matrix n n as * S)) G)))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hc : c.2 + (k + ell) * n ≤ m.store.len c.1)
    (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ evaluate.body (Env.frame [n, k, ell] [data, b, t, c, out])
      (Store.inBlock c.1 c.2 ((k + ell) * n) ⊔
        (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [hutchpp (matrix n n as) S G]) m := by
  let W := projectedBasis (gramSchmidtQ (matrix n n as * S)) G
  have hCB : Fp.Disj (Store.inBlock c.1 c.2 ((k + ell) * n))
      (Store.inBlock b.1 b.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 3) (j := 1) (by simp) (by simp) (by omega)
  have hCD : Fp.Disj (Store.inBlock c.1 c.2 ((k + ell) * n))
      (Store.inBlock data.1 data.2 (dataLength n n)) := by
    simpa using hAP.disj_getD (i := 3) (j := 0) (by simp) (by simp) (by omega)
  have hTB : Fp.Disj (Store.inBlock t.1 t.2 2)
      (Store.inBlock b.1 b.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 2) (j := 1) (by simp) (by simp) (by omega)
  have hOB : Fp.Disj (Store.inBlock out.1 out.2 1)
      (Store.inBlock b.1 b.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 4) (j := 1) (by simp) (by simp) (by omega)
  have hTC : Fp.Disj (Store.inBlock t.1 t.2 2)
      (Store.inBlock c.1 c.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 2) (j := 3) (by simp) (by simp) (by omega)
  have hOC : Fp.Disj (Store.inBlock out.1 out.2 1)
      (Store.inBlock c.1 c.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 4) (j := 3) (by simp) (by simp) (by omega)
  have hTO : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock out.1 out.2 1) := by
    simpa using hAP.disj_getD (i := 2) (j := 4) (by simp) (by simp) (by omega)
  have hl₃ : m.Live [data, b, c] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl data (by simp), hl b (by simp), hl c (by simp), trivial⟩
  unfold evaluate
  dsimp only
  refine Writes.seq_le ((writes_applyColumns hI as W hl₃ hA hBInput hCB hCD hc).in_frame
    rfl rfl hl₃) le_sup_left ?_
  intro m₁ hfr ⟨hp, hC⟩
  have hB₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hCB hBInput
  have hl₄ : m₁.Live [b, c, t, out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨(hl.congr hfr.length_eq) b (by simp), (hl.congr hfr.length_eq) c (by simp),
      (hl.congr hfr.length_eq) t (by simp), (hl.congr hfr.length_eq) out (by simp), trivial⟩
  have hsub : ∀ (z : ℕ × ℕ) j, j < k + ell →
      Store.inBlock z.1 (z.2 + n * j) n ≤ Store.inBlock z.1 z.2 ((k + ell) * n) := by
    intro z j hj
    have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ, Nat.mul_comm n (k + ell)] at hm
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  refine ((writes_accumulate hS hB hLit (fun j => List.ofFn (column W j))
    (fun j => List.ofFn (column (matrix n n as * W) j)) hl₄
    (read_columns hB₁) (read_columns hC)
    (fun j hj => (Fp.disj_sup_left.mpr ⟨hTB, hOB⟩).mono le_rfl (hsub b j hj))
    (fun j hj => (Fp.disj_sup_left.mpr ⟨hTC, hOC⟩).mono le_rfl (hsub c j hj))
    hTO (by simpa only [hfr.len_eq] using ht)
    (by simpa only [hfr.len_eq] using ho)).in_frame rfl rfl hl₄).mono le_sup_right ?_
  intro m₂ _ ⟨hp₂, hValue⟩
  refine ⟨hp₂.trans hp, ?_⟩
  have he :
      (∑ j ∈ Finset.range k,
        RCLikeBlas.dot n (List.ofFn (column W j)) (List.ofFn (column (matrix n n as * W) j))) +
      (∑ j ∈ Finset.range ell, RCLikeBlas.dot n (List.ofFn (column W (k + j)))
        (List.ofFn (column (matrix n n as * W) (k + j)))) / (ell : 𝕜) =
      hutchpp (matrix n n as) S G := by
    simpa [W, projectedBasis, RCLikeBlas.dot_ofFn, dotProduct] using
      hutchpp_eq_of_mgsSweep (matrix n n as) S G
  exact hValue.trans (congrArg (fun v => some [v]) he)

end NLAlib.HutchPlusPlus
