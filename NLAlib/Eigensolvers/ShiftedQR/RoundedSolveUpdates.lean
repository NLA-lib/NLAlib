/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolve
public import NLAlib.Matrix.FinitePrecision.StoredBlocks
public import NLAlib.Matrix.FinitePrecision.GivensReplay

/-!
# The Schur updates of a worklist round

After a round of the rounded deflation worklist in Schur mode
(`NLAlib.ShiftedQR.solveRoundedWith`), the couplings of the processed block and the accumulator
$\mathbf{U}$ are updated: after a leaf, by products with the leaf's accumulator
(`NLAlib.ShiftedQR.roundedLeafUpdate`); after a decoupled block, by the replay of its Givens log
and an exact zero at the cut (`NLAlib.ShiftedQR.roundedDecoupleUpdate`). This file gives the
words both updates store, on any tape, and the accumulator's distance to the exact product.

## Main results

* `NLAlib.ShiftedQR.roundedLeafUpdate_writes`: the words of the leaf update.
* `NLAlib.ShiftedQR.roundedDecoupleUpdate_writes`: the words of the decoupling update.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- The matrix after the leaf update of the block $[lo, lo + d)$ with the leaf accumulator
$\mathbf{U}_b$ on the machine `M`: the right coupling (rows $[lo, lo + d)$, columns
$[lo + d, N)$) becomes $\mathrm{fl}(\mathbf{U}_b^{\mathsf H}\,\cdot)$ of itself (with the
conjugate transpose as the machine forms it, `NLAlib.machineConjTranspose`), then the top
coupling (rows $[0, lo)$, columns $[lo, lo + d)$) becomes $\mathrm{fl}(\cdot\,\mathbf{U}_b)$ of
itself (`NLAlib.matMulWord`). -/
noncomputable def leafUpdateMatrix (M : Machine ℝ) {N d : ℕ} (lo : ℕ)
    (Ub : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  let A₁ := setRect A lo (lo + d)
    (matMulWord M (machineConjTranspose M Ub) (subRect A lo (lo + d) d (N - lo - d)))
  setRect A₁ 0 lo (matMulWord M (subRect A₁ 0 lo lo d) Ub)

/-- The accumulator after the leaf update of the block $[lo, lo + d)$: its columns
$[lo, lo + d)$ become $\mathrm{fl}(\cdot\,\mathbf{U}_b)$ of themselves. -/
noncomputable def leafUpdateAccumulator (M : Machine ℝ) {N d : ℕ} (lo : ℕ)
    (Ub : Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  setRect U 0 lo (matMulWord M (subRect U 0 lo N d) Ub)

/-- $\mathbf{A}$ with the entry $(r, c)$ replaced by the pair of the literal $0$ of the machine
`M` (the exact zero under the standard model). -/
noncomputable def cutEntry (M : Machine ℝ) {N : ℕ} (r c : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = r ∧ (j : ℕ) = c then ⟨M.lit 0, M.lit 0⟩ else A i j

/-- The matrix after the decoupling update of the block $[lo, lo + d)$ with the log entries `es`
and the cut after the block row $i$, on the machine `M`: the log replayed on the rows of the right
coupling (columns $[lo + d, N)$), then on the columns of the top coupling (rows $[0, lo)$), then
the entry $(lo + i + 1, lo + i)$ set to the literal $0$. -/
noncomputable def decoupleUpdateMatrix (M : Machine ℝ) {N : ℕ} (lo d i : ℕ)
    (es : List GivensEntry) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  cutEntry M (lo + i + 1) (lo + i)
    (es.foldl (replayColumnStep M lo 0 lo) (es.foldl (replayRowStep M lo (lo + d) (N - lo - d)) A))

section Programs

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The scratch context of the leaf update: the scoped product buffer `Lc` of length $2N^2$ on top
of the store, the three views below it, and room for the matrix and the accumulator. -/
private def LeafCtx (N Lc : ℕ) (ub a uo : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  m.store.length = Lc + 1 ∧ m.store.len Lc = 2 * (N * N) ∧ ub.1 < Lc ∧ a.1 < Lc ∧ uo.1 < Lc ∧
    a.2 + 2 * (N * N) ≤ m.store.len a.1 ∧ uo.2 + 2 * (N * N) ≤ m.store.len uo.1

private theorem LeafCtx.of_eqOff {N Lc : ℕ} {ub a uo : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : LeafCtx N Lc ub a uo m) (hfr : m.store.EqOff F m'.store) : LeafCtx N Lc ub a uo m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hfr.length_eq.trans h1, by rw [hfr.len_eq]; exact h2, h3, h4, h5,
    by rw [hfr.len_eq]; exact h6, by rw [hfr.len_eq]; exact h7⟩

private theorem LeafCtx.live {N Lc : ℕ} {ub a uo : ℕ × ℕ} {m : Mem ℝ}
    (h : LeafCtx N Lc ub a uo m) (l : List (ℕ × ℕ))
    (hv : ∀ v ∈ l, v.1 = ub.1 ∨ v.1 = a.1 ∨ v.1 = uo.1 ∨ v.1 = Lc) : m.Live l := by
  intro v hvl
  obtain ⟨h1, -, h3, h4, h5, -⟩ := h
  rw [h1]
  rcases hv v hvl with h | h | h | h <;> rw [h] <;> omega

/-- The environment of the leaf update after its scoped product buffer `Lc`. -/
private abbrev leafEnv (N lo d Lc : ℕ) (ub a uo : ℕ × ℕ) : Env :=
  ⟨(Env.frame [N, lo, d] [ub, a, uo]).idx, (Env.frame [N, lo, d] [ub, a, uo]).buf ++ [Lc]⟩

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The accumulator part of the leaf update: the product of the column block by $\mathbf{U}_b$ and
its copy back. -/
private theorem leafUpdate_accumulator {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {N lo d Lc : ℕ} (hN : lo + d ≤ N) {ub a uo : ℕ × ℕ}
    {Ub : Matrix (Fin d) (Fin d) ℂ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hc : LeafCtx N Lc ub a uo m) (hUb : HoldsMatrix ub Ub m.store)
    (hU : HoldsMatrix uo U m.store) :
    Writes .total I τ
      ((Stmt.frame [IExp.var 0, IExp.var 2, IExp.var 2, IExp.var 0, IExp.var 2, IExp.var 0,
          IExp.const 0]
          [{ buf := 2, off := IExp.var 5 + IExp.const 2 * (IExp.var 1 * IExp.var 0) },
            { buf := 0, off := IExp.var 3 }, { buf := 3, off := IExp.const 0 }]
          (matMulOn (O := O) (Q := Q)).body).seq
        (Stmt.frame [IExp.var 0, IExp.var 2, IExp.var 0, IExp.var 0]
          [{ buf := 3, off := IExp.const 0 },
            { buf := 2, off := IExp.var 5 + IExp.const 2 * (IExp.var 1 * IExp.var 0) }]
          (copyStrided (Op := O) (Tst := Q)).body))
      (leafEnv N lo d Lc ub a uo) (Store.inBlock uo.1 uo.2 (2 * (N * N)) ⊔ Fp.above Lc)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix uo (leafUpdateAccumulator M lo Ub U) m'.store) m := by
  obtain ⟨-, hLlen, -, -, hul, -, hru⟩ := id hc
  have hq : N * d ≤ N * N := Nat.mul_le_mul le_rfl (by omega)
  have hCu : Fp.Disj (Store.inBlock Lc 0 (2 * (N * d))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) :=
    Fp.disj_inBlock_of_ne (by omega)
  have hCb : Fp.Disj (Store.inBlock Lc 0 (2 * (N * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d))) :=
    Fp.disj_inBlock_of_ne (by have := hc.2.2.1; omega)
  refine (matMulOn_writes_view (O := O) (Q := Q) (τ := τ) hS
    (x := (uo.1, uo.2 + 2 * (lo * N))) (y := ub) (z := (Lc, 0)) (ldx := N) (ldy := d)
    (subRect U 0 lo N d) Ub hU
    (fun s hs i l => by
      simpa using HoldsMatrix.readBlock_rect (r0 := 0) (c0 := lo) hs (by omega) (by omega) i l)
    hUb (fun s hs l j => hs.read_entry l j) (hc.live _ (by simp)) (by simp only [hLlen]; omega)
    hCu.symm hCb.symm).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc.live _ (by simp)) (fun b z h => Or.inr (h.1 ▸ le_rfl)) ?_
  rintro m₅ hfr₅ ⟨hp₅, hC₅⟩
  have hc₅ := hc.of_eqOff hfr₅
  refine ((copyStrided_writes_rect (Op := O) (Tst := Q) (τ := τ) hS (w := (Lc, 0)) (a := uo)
    (r0 := 0) (c0 := lo) (hc₅.live _ (by simp)) (hU.of_eqOff hfr₅ hCu) hC₅ (by omega) (by omega)
    hc₅.2.2.2.2.2.2 (by rw [Nat.mul_comm d N]; exact hCu)).in_frame
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc₅.live _ (by simp))).mono ((rectFp_le uo (by omega) (by omega)).trans le_sup_left) ?_
  rintro m₆ - ⟨hp₆, hU₆⟩
  exact ⟨hp₆.trans hp₅, hU₆⟩

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The top coupling and the accumulator parts of the leaf update. -/
private theorem leafUpdate_top {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {N lo d Lc : ℕ} (hN : lo + d ≤ N) {ub a uo : ℕ × ℕ}
    {Ub : Matrix (Fin d) (Fin d) ℂ} {A U : Matrix (Fin N) (Fin N) ℂ}
    (hc : LeafCtx N Lc ub a uo m) (hUb : HoldsMatrix ub Ub m.store) (hA : HoldsMatrix a A m.store)
    (hU : HoldsMatrix uo U m.store)
    (hba : Fp.Disj (Store.inBlock ub.1 ub.2 (2 * (d * d))) (Store.inBlock a.1 a.2 (2 * (N * N))))
    (hau : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N)))) :
    Writes .total I τ
      ((Stmt.frame [IExp.var 1, IExp.var 2, IExp.var 2, IExp.var 0, IExp.var 2, IExp.var 1,
          IExp.const 0]
          [{ buf := 1, off := IExp.var 4 + IExp.const 2 * (IExp.var 1 * IExp.var 0) },
            { buf := 0, off := IExp.var 3 }, { buf := 3, off := IExp.const 0 }]
          (matMulOn (O := O) (Q := Q)).body).seq
        ((Stmt.frame [IExp.var 1, IExp.var 2, IExp.var 1, IExp.var 0]
            [{ buf := 3, off := IExp.const 0 },
              { buf := 1, off := IExp.var 4 + IExp.const 2 * (IExp.var 1 * IExp.var 0) }]
            (copyStrided (Op := O) (Tst := Q)).body).seq
          ((Stmt.frame [IExp.var 0, IExp.var 2, IExp.var 2, IExp.var 0, IExp.var 2, IExp.var 0,
              IExp.const 0]
              [{ buf := 2, off := IExp.var 5 + IExp.const 2 * (IExp.var 1 * IExp.var 0) },
                { buf := 0, off := IExp.var 3 }, { buf := 3, off := IExp.const 0 }]
              (matMulOn (O := O) (Q := Q)).body).seq
            (Stmt.frame [IExp.var 0, IExp.var 2, IExp.var 0, IExp.var 0]
              [{ buf := 3, off := IExp.const 0 },
                { buf := 2, off := IExp.var 5 + IExp.const 2 * (IExp.var 1 * IExp.var 0) }]
              (copyStrided (Op := O) (Tst := Q)).body))))
      (leafEnv N lo d Lc ub a uo)
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)) ⊔ Fp.above Lc)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix a (setRect A 0 lo (matMulWord M (subRect A 0 lo lo d) Ub)) m'.store ∧
        HoldsMatrix uo (leafUpdateAccumulator M lo Ub U) m'.store) m := by
  obtain ⟨-, hLlen, -, hal, hul, hra, -⟩ := id hc
  have hq : lo * d ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hCa : Fp.Disj (Store.inBlock Lc 0 (2 * (lo * d))) (Store.inBlock a.1 a.2 (2 * (N * N))) :=
    Fp.disj_inBlock_of_ne (by omega)
  have hCu : Fp.Disj (Store.inBlock Lc 0 (2 * (lo * d)))
      (Store.inBlock uo.1 uo.2 (2 * (N * N))) := Fp.disj_inBlock_of_ne (by omega)
  have hCb : Fp.Disj (Store.inBlock Lc 0 (2 * (lo * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d))) :=
    Fp.disj_inBlock_of_ne (by have := hc.2.2.1; omega)
  refine (matMulOn_writes_view (O := O) (Q := Q) (τ := τ) hS
    (x := (a.1, a.2 + 2 * (lo * N))) (y := ub) (z := (Lc, 0)) (ldx := N) (ldy := d)
    (subRect A 0 lo lo d) Ub hA
    (fun s hs i l => by
      simpa using HoldsMatrix.readBlock_rect (r0 := 0) (c0 := lo) hs (by omega) (by omega) i l)
    hUb (fun s hs l j => hs.read_entry l j) (hc.live _ (by simp)) (by simp only [hLlen]; omega)
    hCa.symm hCb.symm).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc.live _ (by simp)) (fun b z h => Or.inr (h.1 ▸ le_rfl)) ?_
  rintro m₃ hfr₃ ⟨hp₃, hC₃⟩
  have hc₃ := hc.of_eqOff hfr₃
  have hRa := rectFp_le (N := N) (r0 := 0) (c0 := lo) (m := lo) (q := d) a (by omega) (by omega)
  refine (copyStrided_writes_rect (Op := O) (Tst := Q) (τ := τ) hS (w := (Lc, 0)) (a := a)
    (r0 := 0) (c0 := lo) (hc₃.live _ (by simp)) (hA.of_eqOff hfr₃ hCa) hC₃ (by omega) (by omega)
    hc₃.2.2.2.2.2.1 (by rw [Nat.mul_comm d lo]; exact hCa)).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc₃.live _ (by simp)) (hRa.trans (le_sup_left.trans le_sup_left)) ?_
  rintro m₄ hfr₄ ⟨hp₄, hA₄⟩
  have hc₄ := hc₃.of_eqOff hfr₄
  refine (leafUpdate_accumulator (M := M) hS hN hc₄
    ((hUb.of_eqOff hfr₃ hCb).of_eqOff hfr₄ (hba.symm.mono hRa le_rfl))
    ((hU.of_eqOff hfr₃ hCu).of_eqOff hfr₄ (hau.mono hRa le_rfl))).mono
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right) ?_
  rintro m₆ hfr₆ ⟨hp₆, hU₆⟩
  exact ⟨hp₆.trans (hp₄.trans hp₃), hA₄.of_eqOff hfr₆ (Fp.disj_sup_left.mpr ⟨hau.symm,
    fun b i h h' => by rw [Fp.above_apply] at h; have := h'.1; omega⟩), hU₆⟩

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- **The words of the leaf update**: on a scalar machine and every tape,
for the block $[lo, lo + d)$ of order-$N$ matrices $\mathbf{A}$ at `a` and $\mathbf{U}$ at `uo` and
the leaf accumulator $\mathbf{U}_b$ at `ub` (three blocks apart), `roundedLeafUpdate` writes only
the matrix and the accumulator, and stores `NLAlib.ShiftedQR.leafUpdateMatrix` and
`NLAlib.ShiftedQR.leafUpdateAccumulator`. -/
theorem roundedLeafUpdate_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {N lo d : ℕ} (hN : lo + d ≤ N)
    {ub a uo : ℕ × ℕ} {Ub : Matrix (Fin d) (Fin d) ℂ} {A U : Matrix (Fin N) (Fin N) ℂ}
    (hl : μ.Live [ub, a, uo]) (hUb : HoldsMatrix ub Ub μ.store) (hA : HoldsMatrix a A μ.store)
    (hU : HoldsMatrix uo U μ.store) (hra : a.2 + 2 * (N * N) ≤ μ.store.len a.1)
    (hru : uo.2 + 2 * (N * N) ≤ μ.store.len uo.1)
    (hba : Fp.Disj (Store.inBlock ub.1 ub.2 (2 * (d * d))) (Store.inBlock a.1 a.2 (2 * (N * N))))
    (hau : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N)))) :
    Writes .total I τ (roundedLeafUpdate (O := O) (Q := Q)).body (Env.frame [N, lo, d] [ub, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix a (leafUpdateMatrix M lo Ub A) μ'.store ∧
        HoldsMatrix uo (leafUpdateAccumulator M lo Ub U) μ'.store) μ := by
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  have hbl : ub.1 < μ.store.length := hl ub (by simp)
  unfold roundedLeafUpdate
  change Writes .total I τ (Stmt.allocs [IExp.const 2 * (IExp.var 0 * IExp.var 0)] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * (N * N)])
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (fun hBelow ⟨hp, hA', hU'⟩ => ⟨hp, hA'.of_below hBelow hal, hU'.of_below hBelow hul⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hc : LeafCtx N Lc ub a uo ⟨s₁, μ.pos⟩ := ⟨by simpa using hlen,
    by simpa using hlens 0 (by simp), hbl, hal, hul, (hBelow a.1 hal).1 ▸ hra,
    (hBelow uo.1 hul).1 ▸ hru⟩
  have hq : d * (N - lo - d) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hCa : Fp.Disj (Store.inBlock Lc 0 (2 * (d * (N - lo - d))))
      (Store.inBlock a.1 a.2 (2 * (N * N))) := Fp.disj_inBlock_of_ne (by omega)
  have hCu : Fp.Disj (Store.inBlock Lc 0 (2 * (d * (N - lo - d))))
      (Store.inBlock uo.1 uo.2 (2 * (N * N))) := Fp.disj_inBlock_of_ne (by omega)
  have hCb : Fp.Disj (Store.inBlock Lc 0 (2 * (d * (N - lo - d))))
      (Store.inBlock ub.1 ub.2 (2 * (d * d))) := Fp.disj_inBlock_of_ne (by omega)
  have hA₀ := hA.of_below hBelow hal
  refine (matMulOn_machineConjTranspose_writes_view (O := O) (Q := Q) (τ := τ) hS
    (x := ub) (y := (a.1, a.2 + 2 * ((lo + d) * N + lo))) (z := (Lc, 0)) (ldx := d) (ldy := N)
    Ub (subRect A lo (lo + d) d (N - lo - d)) (hUb.of_below hBelow hbl)
    (fun s hs l i => hs.read_entry l i) hA₀
    (fun s hs l j => hs.readBlock_rect (by omega) (by omega) l j) (hc.live _ (by simp))
    (by simp only [hc.2.1]; omega) hCb.symm hCa.symm).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc.live _ (by simp)) (fun b z h => Or.inr (h.1 ▸ le_rfl)) ?_
  rintro m₁ hfr₁ ⟨hp₁, hC₁⟩
  have hc₁ := hc.of_eqOff hfr₁
  have hRa := rectFp_le (N := N) (r0 := lo) (c0 := lo + d) (m := d) (q := N - lo - d) a
    (by omega) (by omega)
  refine (copyStrided_writes_rect (Op := O) (Tst := Q) (τ := τ) hS (w := (Lc, 0)) (a := a)
    (r0 := lo) (c0 := lo + d) (hc₁.live _ (by simp)) (hA₀.of_eqOff hfr₁ hCa) hC₁ (by omega)
    (by omega) hc₁.2.2.2.2.2.1 (by rw [Nat.mul_comm (N - lo - d) d]; exact hCa)).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hc₁.live _ (by simp)) (hRa.trans (le_sup_left.trans le_sup_left)) ?_
  rintro m₂ hfr₂ ⟨hp₂, hA₂⟩
  refine (leafUpdate_top (M := M) hS hN (hc₁.of_eqOff hfr₂)
    (((hUb.of_below hBelow hbl).of_eqOff hfr₁ hCb).of_eqOff hfr₂ (hba.symm.mono hRa le_rfl)) hA₂
    (((hU.of_below hBelow hul).of_eqOff hfr₁ hCu).of_eqOff hfr₂ (hau.mono hRa le_rfl)) hba
    hau).mono le_rfl ?_
  rintro m₆ - ⟨hp₆, hA₆, hU₆⟩
  exact ⟨hp₆.trans (hp₂.trans hp₁), hA₆, hU₆⟩

omit [Has IndexOp O] in
/-- **The words of the decoupling update**: on a scalar machine with exact `toNat` and
comparisons and every tape, for the block $[lo, lo + d)$ with the cut row $i + 1 < d$, a closed
log at `lg` of `ns` slots of `w` entries whose entries have their two planes `lo + r, lo + r + 1`
inside the order $N$, and the order-$N$ matrices $\mathbf{A}$ at `a` and $\mathbf{U}$ at `uo`
(three blocks apart), `roundedDecoupleUpdate` writes only the matrix and the accumulator and
stores `NLAlib.ShiftedQR.decoupleUpdateMatrix` and the log replayed on the columns of
$\mathbf{U}$. -/
theorem roundedDecoupleUpdate_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hQ : IsToNat id I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {N lo d i ns w : ℕ}
    (hN : lo + d ≤ N) (hi : i + 1 < d) {L : List (Option (List GivensEntry))}
    {P : List GivensEntry} (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N)
    {lg a uo : ℕ × ℕ} {A U : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [lg, a, uo])
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hA : HoldsMatrix a A μ.store) (hU : HoldsMatrix uo U μ.store)
    (hra : a.2 + 2 * (N * N) ≤ μ.store.len a.1)
    (hga : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * (N * N))))
    (hgu : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock uo.1 uo.2 (2 * (N * N))))
    (hau : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N)))) :
    Writes .total I τ (roundedDecoupleUpdate (O := O) (Q := Q)).body
      (Env.frame [N, lo, d, i, ns, w] [lg, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix a (decoupleUpdateMatrix M lo d i (slotEntries w L) A) μ'.store ∧
        HoldsMatrix uo ((slotEntries w L).foldl (replayColumnStep M lo 0 N) U) μ'.store) μ := by
  have live : ∀ {m : Mem ℝ}, m.store.length = μ.store.length → ∀ l : List (ℕ × ℕ),
      (∀ v ∈ l, v.1 = lg.1 ∨ v.1 = a.1 ∨ v.1 = uo.1) → m.Live l := by
    intro m hm l hv v hvl
    rw [hm]
    rcases hv v hvl with h | h | h <;> rw [h]
    exacts [hl lg (by simp), hl a (by simp), hl uo (by simp)]
  set FA := Store.inBlock a.1 a.2 (2 * (N * N))
  set FU := Store.inBlock uo.1 uo.2 (2 * (N * N))
  unfold roundedDecoupleUpdate
  refine (givensReplayRows_writes_word (O := O) (Q := Q) (τ := τ) hS hQ hC
    (j0 := lo + d) (nc := N - lo - d) (by omega) hrow hlog hlen hA (live rfl _ (by simp))
    hga).frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (live rfl _ (by simp)) le_sup_left ?_
  rintro m₁ hfr₁ ⟨hp₁, hA₁⟩
  have hlog₁ := hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hga.symm hlog
  have hU₁ := hU.of_eqOff hfr₁ hau
  refine (givensReplayColumns_writes_word (O := O) (Q := Q) (τ := τ) hS hQ hC
    (i0 := 0) (nr := lo) (by omega) hrow hlog₁ hlen hA₁ (live hfr₁.length_eq _ (by simp))
    hga).frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (live hfr₁.length_eq _ (by simp)) le_sup_left ?_
  rintro m₂ hfr₂ ⟨hp₂, hA₂⟩
  have hl₂ : m₂.store.length = μ.store.length := hfr₂.length_eq.trans hfr₁.length_eq
  have hlog₂ := hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hga.symm hlog₁
  have hU₂ := hU₁.of_eqOff hfr₂ hau
  refine (givensReplayColumns_writes_word (O := O) (Q := Q) (τ := τ) hS hQ hC
    (i0 := 0) (nr := N) (by omega) hrow hlog₂ hlen hU₂ (live hl₂ _ (by simp))
    hgu).frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (live hl₂ _ (by simp)) le_sup_right ?_
  rintro m₃ hfr₃ ⟨hp₃, hU₃⟩
  have hA₃ := hA₂.of_eqOff hfr₃ hau.symm
  have hk : (lo + i) * N + (lo + i + 1) < N * N := Idx.add_lt_mul (by omega) (by omega)
  set o := a.2 + 2 * ((lo + i) * N + (lo + i + 1)) with ho
  have hroom : o + 1 < m₃.store.len a.1 := by
    rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; omega
  have hoF : Store.inBlock a.1 o 2 ≤ FA := Fp.inBlock_le_inBlock (by omega) (by omega)
  refine (writes_call_const (hS (.lit 0)) (z := (a.1, o))
    (by simp [Operand.eval, IExp.eval, Env.frame, ho]; ring) trivial
    (by dsimp only; omega)).seq_le ((Fp.inBlock_le_inBlock le_rfl (by omega)).trans
      (hoF.trans le_sup_left)) ?_
  rintro m₄ hfr₄ ⟨hp₄, g₄⟩
  refine (writes_call_const (hS (.lit 0)) (z := (a.1, o + 1))
    (by simp [Operand.eval, IExp.eval, Env.frame, ho]; ring) trivial
    (by dsimp only; rw [hfr₄.len_eq]; omega)).mono
    ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans
      (hoF.trans le_sup_left)) ?_
  rintro m₅ hfr₅ ⟨hp₅, g₅⟩
  have g₄' := hfr₅.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le le_rfl).symm g₄
  have hfr₄₅ : m₃.store.EqOff (Store.inBlock a.1 o 2) m₅.store :=
    (hfr₄.mono (Fp.inBlock_le_inBlock le_rfl (by omega))).trans
      (hfr₅.mono (Fp.inBlock_le_inBlock (by omega) (by omega)))
  have hW := hA₃.of_entry_write ⟨lo + i + 1, by omega⟩ ⟨lo + i, by omega⟩ ⟨M.lit 0, M.lit 0⟩
    hfr₄₅ g₄' g₅
  refine ⟨hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))), ?_,
    hU₃.of_eqOff ((hfr₄.mono (Fp.inBlock_le_inBlock le_rfl (by omega))).trans
      (hfr₅.mono (Fp.inBlock_le_inBlock (by omega) (by omega)))) (hau.mono hoF le_rfl)⟩
  convert hW using 1
  ext r c
  simp only [decoupleUpdateMatrix, cutEntry, Matrix.of_apply, Matrix.updateRow_apply,
    Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) |
    rw [show r = ⟨lo + i + 1, by omega⟩ from Fin.ext (by omega)]

end Programs

end NLAlib.ShiftedQR
