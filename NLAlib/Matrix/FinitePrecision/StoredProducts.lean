/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.GivensRotation
public import NLAlib.Matrix.FinitePrecision.StoredMatrix
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.FinitePrecision.GivensChain
public import NLAlib.Matrix.Norms.Compare

/-!
# Products of stored complex matrices on strided views

A product $\mathbf{Z} = \mathbf{X}\mathbf{Y}$, or $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$,
of complex matrices stored as word pairs in column-major order on strided views (leading dimensions
of their own), accumulated by rounded complex multiply–adds (`NLAlib.Ops.Pair.linearCombination`).
The output is a separate view. Under the standard model the stored product is within
$8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$ of the exact one, $p$
the inner dimension.

## Main definitions

* `NLAlib.matMulOn`: the strided product, with the left factor optionally conjugate-transposed.
* `NLAlib.matMulWord`: the product the program stores on a machine.
* `NLAlib.machineConjTranspose`: the conjugate transpose the program forms on a machine.

## Main results

* `NLAlib.matMulOn_writes_view`, `NLAlib.matMulOn_conjTranspose_writes_view`,
  `NLAlib.matMulOn_machineConjTranspose_writes_view`: the program stores `NLAlib.matMulWord`
  (strided views of stored matrices).
* `NLAlib.matMulOn_writes_word`, `NLAlib.matMulOn_conjTranspose_writes_word`: the program stores
  `NLAlib.matMulWord` (contiguous views).
* `NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le`,
  `NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le_growth`: the error of the stored product.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O]

/-- **The product of two stored complex matrices on strided views**: for $c = 0$,
$\mathbf{Z} = \mathbf{X}\mathbf{Y}$ with $\mathbf{X}$ of size $m \times p$ (leading dimension
`ldx`), $\mathbf{Y}$ of size $p \times q$ (`ldy`) and $\mathbf{Z}$ of size $m \times q$ (`ldz`);
for $c \ge 1$, $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$ with $\mathbf{X}$ of size
$p \times m$. Entry $(i, j)$ is accumulated from $0$ by $p$ rounded complex multiply–adds. The
interface is `[m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z)`; the output is apart from the inputs, and
the four scratch pairs are scoped. -/
def matMulOn : Stmt O Q := ops% [m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z) {
  let One ← alloc 2;
  let A ← alloc 2;
  let S ← alloc 2;
  let T ← alloc 2;
  let R ← alloc 2;
  call (Has.inj (ScalarOp.lit 1)) [] () → (One);
  call (Has.inj (ScalarOp.lit 0)) [] () → (One[1]);
  for j < q {
    for i < m {
      call (Has.inj (ScalarOp.lit 0)) [] () → (S);
      call (Has.inj (ScalarOp.lit 0)) [] () → (S[1]);
      for l < p {
        ifPos c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (i * ldx + l)]) → (A);
          call (Has.inj ScalarOp.neg) [] (X[2 * (i * ldx + l) + 1]) → (A[1])
        };
        ifPos 1 - c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i)]) → (A);
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i) + 1]) → (A[1])
        };
        run Pair.linearCombination [] (A, One, Y[2 * (j * ldy + l)], S, T, R);
        call (Has.inj ScalarOp.copy) [] (R) → (S);
        call (Has.inj ScalarOp.copy) [] (R[1]) → (S[1])
      };
      call (Has.inj ScalarOp.copy) [] (S) → (Z[2 * (j * ldz + i)]);
      call (Has.inj ScalarOp.copy) [] (S[1]) → (Z[2 * (j * ldz + i) + 1])
    }
  }
}

/-- **The product stored by `NLAlib.matMulOn`** on the machine `M`: entry $(i, j)$ is accumulated
from the pair of the literal $0$ by the rounded complex multiply–adds $s \mapsto
\mathrm{fl}(x_{il}y_{lj} + \hat 1 s)$, $l = 0, \dots, p - 1$, with $\hat 1$ the pair of the
literals $1$ and $0$ (`NLAlib.linearComplex`). -/
noncomputable def matMulWord (M : Machine ℝ) {m p q : ℕ} (X : Matrix (Fin m) (Fin p) ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j => (List.finRange p).foldl
    (fun s l => linearComplex M (X i l) ⟨M.lit 1, M.lit 0⟩ (Y l j) s) ⟨M.lit 0, M.lit 0⟩

/-- One multiply–add of `NLAlib.matMulOn`, as it appears in its innermost loop: the left entry
into `A` (conjugated when $c \ge 1$), the rounded $\mathrm{fl}(ay + \hat 1 s)$ into `R`, then `R`
copied to `S`. -/
private def matMulLBody : Stmt O Q :=
  (Stmt.ifPos (IExp.var 6)
    ((Stmt.call (Has.inj ScalarOp.copy) []
        [{ buf := 0, off := IExp.var 7 + IExp.const 2 * (IExp.var 11 * IExp.var 3 + IExp.var 12) }]
        [{ buf := 4, off := IExp.const 0 }]).seq
      (Stmt.call (Has.inj ScalarOp.neg) []
        [{ buf := 0, off := IExp.var 7 + IExp.const 2 * (IExp.var 11 * IExp.var 3 + IExp.var 12) +
          IExp.const 1 }]
        [{ buf := 4, off := IExp.const 1 }]))).seq
  ((Stmt.ifPos (IExp.const 1 - IExp.var 6)
    ((Stmt.call (Has.inj ScalarOp.copy) []
        [{ buf := 0, off := IExp.var 7 + IExp.const 2 * (IExp.var 12 * IExp.var 3 + IExp.var 11) }]
        [{ buf := 4, off := IExp.const 0 }]).seq
      (Stmt.call (Has.inj ScalarOp.copy) []
        [{ buf := 0, off := IExp.var 7 + IExp.const 2 * (IExp.var 12 * IExp.var 3 + IExp.var 11) +
          IExp.const 1 }]
        [{ buf := 4, off := IExp.const 1 }]))).seq
  ((Stmt.frame []
      [{ buf := 4, off := IExp.const 0 }, { buf := 3, off := IExp.const 0 },
        { buf := 1, off := IExp.var 8 + IExp.const 2 * (IExp.var 10 * IExp.var 4 + IExp.var 12) },
        { buf := 5, off := IExp.const 0 }, { buf := 6, off := IExp.const 0 },
        { buf := 7, off := IExp.const 0 }]
      (Pair.linearCombination (Op := O) (Tst := Q))).seq
  ((Stmt.call (Has.inj ScalarOp.copy) [] [{ buf := 7, off := IExp.const 0 }]
      [{ buf := 5, off := IExp.const 0 }]).seq
    (Stmt.call (Has.inj ScalarOp.copy) [] [{ buf := 7, off := IExp.const 1 }]
      [{ buf := 5, off := IExp.const 1 }]))))

/-- The left entry of `NLAlib.matMulOn` for the environment index `[…, c, x.2, …, i, l]`: for
$c = 0$ the words of $a$ at `X[2 (l ldx + i)]`; for $c = 1$ at `X[2 (i ldx + l)]`, the
imaginary word negated. -/
def MatMulLeftWords (M : Machine ℝ) (s : Store ℝ) (x : ℕ × ℕ) (c ldx i l : ℕ) (a : ℂ) : Prop :=
  (c = 0 ∧ s.get x.1 (x.2 + 2 * (l * ldx + i)) = some a.re ∧
    s.get x.1 (x.2 + 2 * (l * ldx + i) + 1) = some a.im) ∨
  (c = 1 ∧ s.get x.1 (x.2 + 2 * (i * ldx + l)) = some a.re ∧
    ∃ v, s.get x.1 (x.2 + 2 * (i * ldx + l) + 1) = some v ∧ M.neg v = a.im)

omit [Has ScalarOp O] in
/-- The left words are read only in the stored left factor. -/
theorem MatMulLeftWords.of_eqOff {M : Machine ℝ} {s s' : Store ℝ} {x : ℕ × ℕ} {c ldx i l : ℕ}
    {a : ℂ} {F : Fp} (h : MatMulLeftWords M s x c ldx i l a) (hfr : s.EqOff F s')
    (hd : ∀ k, ¬F x.1 k) : MatMulLeftWords M s' x c ldx i l a := by
  rcases h with ⟨hc, h0, h1⟩ | ⟨hc, h0, v, h1, hv⟩
  · exact Or.inl ⟨hc, by rw [hfr.get_eq (hd _)]; exact h0, by rw [hfr.get_eq (hd _)]; exact h1⟩
  · exact Or.inr ⟨hc, by rw [hfr.get_eq (hd _)]; exact h0, v,
      by rw [hfr.get_eq (hd _)]; exact h1, hv⟩

/-- The left entry of a multiply–add into `A`: the words of $a$ (conjugated for $c = 1$), then
the rest of the step. -/
private theorem matMulFillA {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {ρ : Env} {m p q ldx ldy ldz c Lc j i l : ℕ} {x y z : ℕ × ℕ}
    (hidx : ρ.idx = [m, p, q, ldx, ldy, ldz, c, x.2, y.2, z.2, j, i, l])
    (hbuf : ρ.buf = [x.1, y.1, z.1, Lc, Lc + 1, Lc + 2, Lc + 3, Lc + 4]) {τ : Tape ℝ} {μ : Mem ℝ}
    (hlA : 1 < μ.store.len (Lc + 1)) (hxL : x.1 < Lc) {a : ℂ}
    (ha : MatMulLeftWords M μ.store x c ldx i l a)
    (rest : Stmt O Q) (Gr : Fp) (Pr : Mem ℝ → Prop)
    (hGr : Store.inBlock (Lc + 1) 0 2 ≤ Gr)
    (hrest : ∀ μ₂ : Mem ℝ, μ.store.EqOff (Store.inBlock (Lc + 1) 0 2) μ₂.store → μ₂.pos = μ.pos →
        μ₂.store.readBlock (Lc + 1) 0 2 = some [a.re, a.im] → Writes .total I τ rest ρ Gr Pr μ₂) :
    Writes .total I τ ((Stmt.ifPos (IExp.var 6)
        ((Stmt.call (Has.inj ScalarOp.copy) []
            [{ buf := 0, off := IExp.var 7 +
              IExp.const 2 * (IExp.var 11 * IExp.var 3 + IExp.var 12) }]
            [{ buf := 4, off := IExp.const 0 }]).seq
          (Stmt.call (Has.inj ScalarOp.neg) []
            [{ buf := 0, off := IExp.var 7 +
              IExp.const 2 * (IExp.var 11 * IExp.var 3 + IExp.var 12) +
              IExp.const 1 }]
            [{ buf := 4, off := IExp.const 1 }]))).seq
      ((Stmt.ifPos (IExp.const 1 - IExp.var 6)
        ((Stmt.call (Has.inj ScalarOp.copy) []
            [{ buf := 0, off := IExp.var 7 +
              IExp.const 2 * (IExp.var 12 * IExp.var 3 + IExp.var 11) }]
            [{ buf := 4, off := IExp.const 0 }]).seq
          (Stmt.call (Has.inj ScalarOp.copy) []
            [{ buf := 0, off := IExp.var 7 +
              IExp.const 2 * (IExp.var 12 * IExp.var 3 + IExp.var 11) +
              IExp.const 1 }]
            [{ buf := 4, off := IExp.const 1 }]))).seq rest)) ρ Gr Pr μ := by
  have hA0 : Store.inBlock (Lc + 1) 0 1 ≤ Store.inBlock (Lc + 1) 0 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have hA1 : Store.inBlock (Lc + 1) 1 1 ≤ Store.inBlock (Lc + 1) 0 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hxs : ∀ k, ¬Store.inBlock (Lc + 1) 0 2 x.1 k := fun k h => by have := h.1; omega
  set Pa : Mem ℝ → Prop := fun μ₂ => μ₂.pos = μ.pos ∧
    μ.store.EqOff (Store.inBlock (Lc + 1) 0 2) μ₂.store ∧
      μ₂.store.readBlock (Lc + 1) 0 2 = some [a.re, a.im] with hPa
  have two : ∀ {μ₀ μ₂ : Mem ℝ}, μ.store.EqOff (Store.inBlock (Lc + 1) 0 1) μ₀.store →
      μ₀.store.EqOff (Store.inBlock (Lc + 1) 1 1) μ₂.store →
      μ₀.store.get (Lc + 1) 0 = some a.re → μ₂.store.get (Lc + 1) 1 = some a.im →
      μ.store.EqOff (Store.inBlock (Lc + 1) 0 2) μ₂.store ∧
        μ₂.store.readBlock (Lc + 1) 0 2 = some [a.re, a.im] := by
    intro μ₀ μ₂ h₀ h₂ g₀ g₂
    refine ⟨(h₀.mono hA0).trans (h₂.mono hA1), ?_⟩
    have g₀' := h₂.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_inBlock_of_le (b := Lc + 1) (o := 0) (n := 1) (o' := 1) (n' := 1) le_rfl).symm g₀
    simpa using Store.readBlock_succ_of (Store.readBlock_one_of_get g₀') g₂
  have hev : ∀ e : ℕ, (IExp.var 7 + IExp.const 2 * (IExp.var 12 * IExp.var 3 + IExp.var 11)).eval
      (ρ.pushIdx e).idx = some (x.2 + 2 * (l * ldx + i)) := fun e => by
    simp [IExp.eval, Env.pushIdx, hidx]
  rcases ha with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, v, h1, hv⟩
  · refine (writes_ifPos (F := ⊥) (P := fun μ' => μ' = μ) (n := 0)
      (by simp [IExp.eval, hidx]) (by simp)).seq_le bot_le ?_
    rintro μ₁ - rfl
    refine (writes_ifPos (n := 1) (P := Pa) (F := Store.inBlock (Lc + 1) 0 2)
      (by simp [IExp.eval, hidx]) ?_).seq_le hGr (fun μ₂ _ ⟨hp, hfr, hr⟩ => hrest μ₂ hfr hp hr)
    rw [if_pos one_pos]
    refine (writes_call_un (hS .copy) (x := (x.1, x.2 + 2 * (l * ldx + i))) (z := (Lc + 1, 0))
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval]) trivial
      h0 rfl (by simp; omega)).seq_le hA0 fun μ₀ h₀ ⟨p₀, g₀⟩ => ?_
    refine (writes_call_un (hS .copy) (x := (x.1, x.2 + 2 * (l * ldx + i) + 1))
      (z := (Lc + 1, 1)) (v := a.im)
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval]) trivial
      (by rw [h₀.get_eq (fun h => by have := h.1; omega)]; exact h1) rfl
      (by simp [h₀.len_eq]; omega)).mono hA1 fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
    exact ⟨p₂.trans p₀, two h₀ h₂ g₀ g₂⟩
  · refine (writes_ifPos (n := 1) (P := Pa) (F := Store.inBlock (Lc + 1) 0 2)
      (by simp [IExp.eval, hidx]) ?_).seq_le hGr ?_
    · rw [if_pos one_pos]
      refine (writes_call_un (hS .copy) (x := (x.1, x.2 + 2 * (i * ldx + l)))
        (z := (Lc + 1, 0))
        (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
        (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval]) trivial
        h0 rfl (by simp; omega)).seq_le hA0 fun μ₀ h₀ ⟨p₀, g₀⟩ => ?_
      refine (writes_call_un (hS .neg) (x := (x.1, x.2 + 2 * (i * ldx + l) + 1))
        (z := (Lc + 1, 1)) (v := a.im)
        (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
        (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval]) trivial
        (by rw [h₀.get_eq (fun h => by have := h.1; omega)]; exact h1) (by rw [hv])
        (by simp [h₀.len_eq]; omega)).mono hA1 fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
      exact ⟨p₂.trans p₀, two h₀ h₂ g₀ g₂⟩
    · rintro μ₂ hfr ⟨hp, hfr', hr⟩
      refine (writes_ifPos (F := ⊥) (P := fun μ' => μ' = μ₂) (n := 0)
        (by simp [IExp.eval, hidx]) (by simp)).seq_le (bot_le.trans hGr) ?_
      intro μ₃ _ h3
      rw [h3]
      exact (hrest μ₂ hfr' hp hr).mono le_rfl fun _ _ h => h

/-- One multiply–add of the product program stores $\mathrm{fl}(ay + \hat 1 s)$ in `S`. -/
private theorem matMulLBody_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {ρ : Env} {m p q ldx ldy ldz c Lc j i l : ℕ} {x y z : ℕ × ℕ}
    (hidx : ρ.idx = [m, p, q, ldx, ldy, ldz, c, x.2, y.2, z.2, j, i, l])
    (hbuf : ρ.buf = [x.1, y.1, z.1, Lc, Lc + 1, Lc + 2, Lc + 3, Lc + 4]) {τ : Tape ℝ} {μ : Mem ℝ}
    (hlen : μ.store.length = Lc + 5) (hlens : ∀ k < 5, μ.store.len (Lc + k) = 2)
    (hxL : x.1 < Lc) (hyL : y.1 < Lc) {a b sv : ℂ} (ha : MatMulLeftWords M μ.store x c ldx i l a)
    (hb : μ.store.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [b.re, b.im])
    (hone : μ.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0])
    (hs : μ.store.readBlock (Lc + 2) 0 2 = some [sv.re, sv.im]) :
    Writes .total I τ (matMulLBody (O := O) (Q := Q)) ρ
      (Store.inBlock (Lc + 1) 0 2 ⊔ Store.inBlock (Lc + 2) 0 2 ⊔ Store.inBlock (Lc + 3) 0 2 ⊔
        Store.inBlock (Lc + 4) 0 2)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock (Lc + 2) 0 2 = some
        [(linearComplex M a ⟨M.lit 1, M.lit 0⟩ b sv).re,
          (linearComplex M a ⟨M.lit 1, M.lit 0⟩ b sv).im]) μ := by
  have hlA : 1 < μ.store.len (Lc + 1) := by rw [hlens 1 (by omega)]; omega
  unfold matMulLBody
  refine matMulFillA (ldy := ldy) (j := j) hS hidx hbuf hlA hxL ha _ _ _
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
    fun μ₂ hfr₂ hp₂ hA₂ => ?_
  have hone₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hone
  have hb₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hb
  have hs₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs
  have g : ∀ {s : Store ℝ} {b o : ℕ} {u v : ℝ}, s.readBlock b o 2 = some [u, v] →
      s.get b o = some u ∧ s.get b (o + 1) = some v := fun h =>
    ⟨by simpa using Store.get_of_readBlock h (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h (j := 1) (by omega) 0⟩
  have hl₂ : ∀ k < 5, μ₂.store.len (Lc + k) = 2 := fun k hk => by rw [hfr₂.len_eq]; exact hlens k hk
  have hL₂ : μ₂.store.length = Lc + 5 := by rw [hfr₂.length_eq]; exact hlen
  refine (Pair.linearCombination_writes (τ := τ) (m := μ₂) hS (a := (Lc + 1, 0)) (b := (Lc, 0))
    (x := (y.1, y.2 + 2 * (j * ldy + l))) (y := (Lc + 2, 0)) (t := (Lc + 3, 0)) (z := (Lc + 4, 0))
    (av := (a.re, a.im)) (bv := (M.lit 1, M.lit 0)) (xv := (b.re, b.im)) (yv := (sv.re, sv.im))
    (by simp only [Fp.blocks]; disjoint) (by simp only [Fp.blocks]; disjoint) (by disjoint)
    (g hA₂).1 (g hA₂).2 (g hone₂).1 (g hone₂).2 (g hb₂).1 (g hb₂).2 (g hs₂).1 (g hs₂).2
    (by simp [hl₂ 3 (by omega)]) (by simp [hl₂ 4 (by omega)])).frame_seq_le rfl
    (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval])
    (by simp [Mem.Live, hL₂]; omega) (by fp_sub) ?_
  rintro μ₃ hfr₃ ⟨hp₃, hR₃⟩
  have hl₃ : ∀ k < 5, μ₃.store.len (Lc + k) = 2 := fun k hk => by
    rw [hfr₃.len_eq]; exact hl₂ k hk
  refine (writes_call_un (hS .copy) (x := (Lc + 4, 0)) (z := (Lc + 2, 0))
    (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval]) trivial
    (g hR₃).1 rfl
    (by simp [hl₃ 2 (by omega)])).seq_le (by fp_sub) fun μ₄ hfr₄ ⟨hp₄, g₄⟩ => ?_
  have hR₄ := hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hR₃
  refine (writes_call_un (hS .copy) (x := (Lc + 4, 1)) (z := (Lc + 2, 1))
    (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval]) trivial
    (g hR₄).2 rfl
    (by simp [hfr₄.len_eq, hl₃ 2 (by omega)])).mono (by fp_sub) fun μ₅ hfr₅ ⟨hp₅, g₅⟩ => ?_
  have g₄' := hfr₅.keep (Store.readsOnly_get _ _ _) (by disjoint) g₄
  refine ⟨hp₅.trans (hp₄.trans (hp₃.trans hp₂)), ?_⟩
  simpa [linearComplex] using Store.readBlock_succ_of (Store.readBlock_one_of_get g₄') g₅

/-- One entry of `NLAlib.matMulOn`, as it appears in its two outer loops: `S` from the pair of
the literal $0$, the multiply–adds, `S` copied to the entry of `Z`. -/
private def matMulEntry : Stmt O Q :=
  (Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [{ buf := 5, off := IExp.const 0 }]).seq
  ((Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [{ buf := 5, off := IExp.const 1 }]).seq
  ((Stmt.loop (IExp.var 1) (matMulLBody (O := O) (Q := Q))).seq
  ((Stmt.call (Has.inj ScalarOp.copy) [] [{ buf := 5, off := IExp.const 0 }]
      [{ buf := 2, off := IExp.var 9 +
        IExp.const 2 * (IExp.var 10 * IExp.var 5 + IExp.var 11) }]).seq
    (Stmt.call (Has.inj ScalarOp.copy) [] [{ buf := 5, off := IExp.const 1 }]
      [{ buf := 2, off := IExp.var 9 + IExp.const 2 * (IExp.var 10 * IExp.var 5 + IExp.var 11) +
        IExp.const 1 }]))))

/-- One entry of the product program stores the rounded accumulation of its products. -/
private theorem matMulEntry_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {ρ : Env} {m p q ldx ldy ldz c Lc j i : ℕ} {x y z : ℕ × ℕ}
    (hidx : ρ.idx = [m, p, q, ldx, ldy, ldz, c, x.2, y.2, z.2, j, i])
    (hbuf : ρ.buf = [x.1, y.1, z.1, Lc, Lc + 1, Lc + 2, Lc + 3, Lc + 4]) {τ : Tape ℝ} {μ : Mem ℝ}
    (hlen : μ.store.length = Lc + 5) (hlens : ∀ k < 5, μ.store.len (Lc + k) = 2)
    (hxL : x.1 < Lc) (hyL : y.1 < Lc) (hzL : z.1 < Lc) {a b : Fin p → ℂ}
    (ha : ∀ l : Fin p, MatMulLeftWords M μ.store x c ldx i l (a l))
    (hb : ∀ l : Fin p,
      μ.store.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(b l).re, (b l).im])
    (hone : μ.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0])
    (hz : z.2 + 2 * (j * ldz + i) + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (matMulEntry (O := O) (Q := Q)) ρ
      (Store.inBlock z.1 (z.2 + 2 * (j * ldz + i)) 2 ⊔ (Store.inBlock (Lc + 1) 0 2 ⊔
        Store.inBlock (Lc + 2) 0 2 ⊔ Store.inBlock (Lc + 3) 0 2 ⊔ Store.inBlock (Lc + 4) 0 2))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock z.1 (z.2 + 2 * (j * ldz + i)) 2 = some
        [((List.finRange p).foldl (fun s l => linearComplex M (a l) ⟨M.lit 1, M.lit 0⟩ (b l) s)
            ⟨M.lit 0, M.lit 0⟩).re,
          ((List.finRange p).foldl (fun s l => linearComplex M (a l) ⟨M.lit 1, M.lit 0⟩ (b l) s)
            ⟨M.lit 0, M.lit 0⟩).im]) μ := by
  set v := fun l => ((List.finRange p).take l).foldl
    (fun s l => linearComplex M (a l) ⟨M.lit 1, M.lit 0⟩ (b l) s) ⟨M.lit 0, M.lit 0⟩ with hv
  have hGx : ∀ k, ¬(Store.inBlock (Lc + 1) 0 2 ⊔ Store.inBlock (Lc + 2) 0 2 ⊔
      Store.inBlock (Lc + 3) 0 2 ⊔
      Store.inBlock (Lc + 4) 0 2) x.1 k := fun k h => by
    simp only [fpNF, Pi.sup_apply, sup_Prop_eq, Store.inBlock] at h; omega
  have g : ∀ {s : Store ℝ} {b o : ℕ} {u v : ℝ}, s.readBlock b o 2 = some [u, v] →
      s.get b o = some u ∧ s.get b (o + 1) = some v := fun h =>
    ⟨by simpa using Store.get_of_readBlock h (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h (j := 1) (by omega) 0⟩
  unfold matMulEntry
  refine (writes_call_const (hS (.lit 0)) (z := (Lc + 2, 0))
    (by simp [Operand.eval, hbuf, IExp.eval]) trivial (by simp [hlens 2 (by omega)])).seq_le
    (by fp_sub) fun μ₁ hfr₁ ⟨hp₁, g₁⟩ => ?_
  refine (writes_call_const (hS (.lit 0)) (z := (Lc + 2, 1))
    (by simp [Operand.eval, hbuf, IExp.eval]) trivial
    (by simp [hfr₁.len_eq, hlens 2 (by omega)])).seq_le (by fp_sub) fun μ₂ hfr₂ ⟨hp₂, g₂⟩ => ?_
  have g₁' := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁
  have hfr₁₂ : μ.store.EqOff (Store.inBlock (Lc + 1) 0 2 ⊔ Store.inBlock (Lc + 2) 0 2 ⊔
      Store.inBlock (Lc + 3) 0 2 ⊔
      Store.inBlock (Lc + 4) 0 2) μ₂.store := (hfr₁.mono (by fp_sub)).trans (hfr₂.mono (by fp_sub))
  have hS₀ : μ₂.store.readBlock (Lc + 2) 0 2 = some [(v 0).re, (v 0).im] := by
    simpa [hv] using Store.readBlock_succ_of (Store.readBlock_one_of_get g₁') g₂
  refine (writes_loop (N := p) (by simp [IExp.eval, hidx]) (fun _ =>
      (Store.inBlock (Lc + 1) 0 2 ⊔ Store.inBlock (Lc + 2) 0 2 ⊔ Store.inBlock (Lc + 3) 0 2 ⊔
      Store.inBlock (Lc + 4) 0 2))
    (fun _ _ => le_rfl)
    (fun l μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock (Lc + 2) 0 2 = some [(v l).re, (v l).im])
    ⟨hp₂.trans hp₁, hS₀⟩ ?_).seq_le (by fp_sub) ?_
  · intro l hl μ' hfr ⟨hp', hs'⟩
    have hfr' := hfr₁₂.trans hfr
    refine (matMulLBody_writes hS (m := m) (p := p) (q := q) (ldx := ldx) (ldy := ldy) (ldz := ldz)
      (c := c) (Lc := Lc) (j := j) (i := i) (l := l) (x := x) (y := y) (z := z)
      (by simp [Env.pushIdx, hidx]) (by simp [Env.pushIdx, hbuf])
      (by rw [hfr'.length_eq]; exact hlen) (fun k hk => by rw [hfr'.len_eq]; exact hlens k hk)
      hxL hyL ((ha ⟨l, hl⟩).of_eqOff hfr' hGx)
      (hfr'.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) (hb ⟨l, hl⟩))
      (hfr'.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hone) hs').mono le_rfl ?_
    rintro μ'' - ⟨hp'', hs''⟩
    refine ⟨hp''.trans hp', ?_⟩
    have htake : (List.finRange p).take (l + 1) = (List.finRange p).take l ++ [⟨l, hl⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hl)]
      simp
    simpa [hv, htake, List.foldl_append] using hs''
  · rintro μ₃ hfr₃ ⟨hp₃, hs₃⟩
    have hfr₃' := hfr₁₂.trans hfr₃
    refine (writes_call_un (hS .copy) (x := (Lc + 2, 0)) (z := (z.1, z.2 + 2 * (j * ldz + i)))
      (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval])
      (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval]) trivial (g hs₃).1 rfl
      (by simp [hfr₃'.len_eq]; omega)).seq_le (by fp_sub) fun μ₄ hfr₄ ⟨hp₄, g₄⟩ => ?_
    have hs₄ := hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs₃
    refine (writes_call_un (hS .copy) (x := (Lc + 2, 1)) (z := (z.1, z.2 + 2 * (j * ldz + i) + 1))
      (by simp [Operand.evalList, Operand.eval, hbuf, IExp.eval])
      (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval]) trivial (g hs₄).2 rfl
      (by simp [hfr₄.len_eq, hfr₃'.len_eq]; omega)).mono (by fp_sub)
      fun μ₅ hfr₅ ⟨hp₅, g₅⟩ => ?_
    have g₄' := hfr₅.keep (Store.readsOnly_get _ _ _) (by disjoint) g₄
    have hv' : v p = (List.finRange p).foldl
        (fun s l => linearComplex M (a l) ⟨M.lit 1, M.lit 0⟩ (b l) s) ⟨M.lit 0, M.lit 0⟩ := by
      simp [hv, List.take_of_length_le]
    rw [← hv']
    exact ⟨hp₅.trans (hp₄.trans hp₃),
      by simpa using Store.readBlock_succ_of (Store.readBlock_one_of_get g₄') g₅⟩

/-- The entries of `NLAlib.matMulOn` before the entry $(i, j)$ in the order of the program
(column by column) hold the words of `W`. -/
private def MatMulPrefix {m q : ℕ} (z : ℕ × ℕ) (W : Matrix (Fin m) (Fin q) ℂ) (j i : ℕ)
    (s : Store ℝ) : Prop :=
  ∀ (i' : Fin m) (j' : Fin q), ((j' : ℕ) < j ∨ ((j' : ℕ) = j ∧ (i' : ℕ) < i)) →
    s.readBlock z.1 (z.2 + 2 * (j' * m + i')) 2 = some [(W i' j').re, (W i' j').im]

/-- One entry step of the product program keeps its invariant: the program state, the inputs,
and the entries written so far, now with the entry $(i, j)$. The left factor is read from a
stored `Xs` at `xs`, the right one from a stored `Ys` at `ys`, through strided views. -/
private theorem matMulOn_entry_step {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m p q ldx ldy c r₁ r₂ r₃ r₄ Lc j i pos : ℕ} {x y z xs ys : ℕ × ℕ}
    {Xs : Matrix (Fin r₁) (Fin r₂) ℂ} {Ys : Matrix (Fin r₃) (Fin r₄) ℂ}
    (lf : Fin m → Fin p → ℂ) (rf : Fin p → Fin q → ℂ)
    (hsrc : ∀ s, HoldsMatrix xs Xs s → ∀ (i : Fin m) (l : Fin p),
      MatMulLeftWords M s x c ldx i l (lf i l))
    (hsrcY : ∀ s, HoldsMatrix ys Ys s → ∀ (l : Fin p) (j : Fin q),
      s.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(rf l j).re, (rf l j).im])
    (hxz : Fp.Disj (Store.inBlock xs.1 xs.2 (2 * (r₂ * r₁)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock ys.1 ys.2 (2 * (r₄ * r₃)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    {ρ : Env} (hidx : ρ.idx = [m, p, q, ldx, ldy, m, c, x.2, y.2, z.2, j, i])
    (hbuf : ρ.buf = [x.1, y.1, z.1, Lc, Lc + 1, Lc + 2, Lc + 3, Lc + 4])
    (hxL : x.1 < Lc) (hyL : y.1 < Lc) (hzL : z.1 < Lc) (hxsL : xs.1 < Lc) (hysL : ys.1 < Lc)
    (hj : j < q) (hi : i < m) {μ' : Mem ℝ}
    (h1 : μ'.pos = pos) (h2 : μ'.store.length = Lc + 5)
    (h3 : ∀ k < 5, μ'.store.len (Lc + k) = 2)
    (h4 : μ'.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0]) (h5 : HoldsMatrix xs Xs μ'.store)
    (h6 : HoldsMatrix ys Ys μ'.store)
    (h7 : MatMulPrefix z (Matrix.of fun i j => (List.finRange p).foldl
      (fun s l => linearComplex M (lf i l) ⟨M.lit 1, M.lit 0⟩ (rf l j) s) ⟨M.lit 0, M.lit 0⟩) j i
        μ'.store)
    (h8 : z.2 + 2 * (m * q) ≤ μ'.store.len z.1) :
    Writes .total I τ (matMulEntry (O := O) (Q := Q)) ρ
      (Store.inBlock z.1 z.2 (2 * (m * q)) ⊔ (Store.inBlock (Lc + 1) 0 2 ⊔
        Store.inBlock (Lc + 2) 0 2 ⊔ Store.inBlock (Lc + 3) 0 2 ⊔ Store.inBlock (Lc + 4) 0 2))
      (fun μ'' => μ''.pos = pos ∧ μ''.store.length = Lc + 5 ∧
        (∀ k < 5, μ''.store.len (Lc + k) = 2) ∧
        μ''.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0] ∧ HoldsMatrix xs Xs μ''.store ∧
        HoldsMatrix ys Ys μ''.store ∧ MatMulPrefix z (Matrix.of fun i j => (List.finRange p).foldl
          (fun s l => linearComplex M (lf i l) ⟨M.lit 1, M.lit 0⟩ (rf l j) s) ⟨M.lit 0, M.lit 0⟩)
            j (i + 1) μ''.store ∧ z.2 + 2 * (m * q) ≤ μ''.store.len z.1) μ' := by
  have hk : j * m + i < q * m := Idx.add_lt_mul hj hi
  have hent : Store.inBlock z.1 (z.2 + 2 * (j * m + i)) 2 ≤ Store.inBlock z.1 z.2 (2 * (m * q)) :=
    Fp.inBlock_le_inBlock (by omega) (by rw [Nat.mul_comm m q]; omega)
  refine (matMulEntry_writes hS (ldy := ldy) (ldz := m) hidx hbuf h2 h3 hxL hyL hzL
    (a := lf ⟨i, hi⟩) (b := fun l => rf l ⟨j, hj⟩) (fun l => hsrc _ h5 ⟨i, hi⟩ l)
    (fun l => hsrcY _ h6 l ⟨j, hj⟩) h4 (by rw [Nat.mul_comm m q] at h8; omega)).mono
    (sup_le_sup_right hent _) ?_
  rintro μ'' hfr ⟨hp, hz⟩
  refine ⟨hp.trans h1, by rw [hfr.length_eq, h2], fun k hk => by rw [hfr.len_eq]; exact h3 k hk,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) h4,
    hfr.keep (readsOnly_holdsMatrix _ _)
      (Fp.disj_sup_left.mpr ⟨(hxz.mono le_rfl hent).symm, by disjoint⟩) h5,
    hfr.keep (readsOnly_holdsMatrix _ _)
      (Fp.disj_sup_left.mpr ⟨(hyz.mono le_rfl hent).symm, by disjoint⟩) h6,
    fun i' j' h => ?_, by rw [hfr.len_eq]; exact h8⟩
  by_cases he : (j' : ℕ) = j ∧ (i' : ℕ) = i
  · obtain ⟨h₁, h₂⟩ := he
    have e1 : j' = ⟨j, hj⟩ := Fin.ext h₁
    have e2 : i' = ⟨i, hi⟩ := Fin.ext h₂
    subst e1 e2
    simpa using hz
  · have hlt : (j' : ℕ) * m + i' < j * m + i := by
      rcases h with h | ⟨h₁, h₂⟩
      · have := Nat.mul_le_mul_right m (show (j' : ℕ) + 1 ≤ j by omega)
        rw [Nat.add_mul, one_mul] at this
        have := i'.isLt
        omega
      · rw [h₁]; omega
    refine hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr
      ⟨(Fp.disj_inBlock_of_le (by omega)).symm, by disjoint⟩)
      (h7 i' j' (by rcases h with h | ⟨h₁, h₂⟩ <;> omega))

/-- The product program with the output contiguous, the left factor read by `MatMulLeftWords`
from a stored `Xs` at `xs` and the right factor read through a strided view from a stored `Ys`
at `ys`: it stores the accumulations of the entries `lf i l` against `rf l j`. -/
private theorem matMulOn_writes_gen {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {m p q ldx ldy c r₁ r₂ r₃ r₄ : ℕ} {x y z xs ys : ℕ × ℕ}
    {Xs : Matrix (Fin r₁) (Fin r₂) ℂ} {Ys : Matrix (Fin r₃) (Fin r₄) ℂ}
    (lf : Fin m → Fin p → ℂ) (rf : Fin p → Fin q → ℂ)
    (hX : HoldsMatrix xs Xs μ.store)
    (hsrc : ∀ s, HoldsMatrix xs Xs s → ∀ (i : Fin m) (l : Fin p),
      MatMulLeftWords M s x c ldx i l (lf i l))
    (hY : HoldsMatrix ys Ys μ.store)
    (hsrcY : ∀ s, HoldsMatrix ys Ys s → ∀ (l : Fin p) (j : Fin q),
      s.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(rf l j).re, (rf l j).im])
    (hl : μ.Live [x, y, z, xs, ys])
    (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock xs.1 xs.2 (2 * (r₂ * r₁)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock ys.1 ys.2 (2 * (r₄ * r₃)))
      (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q))
      (Env.frame [m, p, q, ldx, ldy, m, c] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (Matrix.of fun i j => (List.finRange p).foldl
        (fun s l => linearComplex M (lf i l) ⟨M.lit 1, M.lit 0⟩ (rf l j) s)
          ⟨M.lit 0, M.lit 0⟩) μ'.store) μ := by
  set W : Matrix (Fin m) (Fin q) ℂ := Matrix.of fun i j => (List.finRange p).foldl
    (fun s l => linearComplex M (lf i l) ⟨M.lit 1, M.lit 0⟩ (rf l j) s) ⟨M.lit 0, M.lit 0⟩
    with hW
  have hxl : x.1 < μ.store.length := hl x (by simp)
  have hyl : y.1 < μ.store.length := hl y (by simp)
  have hzl : z.1 < μ.store.length := hl z (by simp)
  have hxsl : xs.1 < μ.store.length := hl xs (by simp)
  have hysl : ys.1 < μ.store.length := hl ys (by simp)
  unfold matMulOn
  change Writes .total I τ (Stmt.allocs [.const 2, .const 2, .const 2, .const 2, .const 2] _) _ _
    _ μ
  refine writes_allocs_preserving_post (ns := [2, 2, 2, 2, 2]) rfl
    (fun hBelow ⟨hp, hW'⟩ => ⟨hp, hW'.of_below hBelow hzl⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hl5 : ∀ k < 5, s₁.len (Lc + k) = 2 := fun k hk => by
    have := hlens k (by simpa using hk)
    interval_cases k <;> simpa using this
  have hL0 : s₁.len Lc = 2 := by simpa using hl5 0 (by omega)
  set G := Store.inBlock (Lc + 1) 0 2 ⊔ Store.inBlock (Lc + 2) 0 2 ⊔ Store.inBlock (Lc + 3) 0 2 ⊔
    Store.inBlock (Lc + 4) 0 2 with hG
  set Z := Store.inBlock z.1 z.2 (2 * (m * q)) with hZ
  refine (writes_call_const (hS (.lit 1)) (z := (Lc, 0))
    (by simp [Operand.eval, Env.frame, IExp.eval]) trivial
    (by simp [hL0])).seq_le
    (fun b k h => Or.inr (show Lc ≤ b from h.1 ▸ le_rfl)) fun μ₁ hfr₁ ⟨hp₁, g₁⟩ => ?_
  refine (writes_call_const (hS (.lit 0)) (z := (Lc, 1))
    (by simp [Operand.eval, Env.frame, IExp.eval]) trivial
    (by simp [hfr₁.len_eq, hL0])).seq_le
    (fun b k h => Or.inr (show Lc ≤ b from h.1 ▸ le_rfl)) fun μ₂ hfr₂ ⟨hp₂, g₂⟩ => ?_
  have g₁' := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁
  have hone : μ₂.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0] := by
    simpa using Store.readBlock_succ_of (Store.readBlock_one_of_get g₁') g₂
  have hfr₁₂ := (hfr₁.mono (show Store.inBlock Lc 0 1 ≤ Store.inBlock Lc 0 2 by fp_sub)).trans
    (hfr₂.mono (show Store.inBlock Lc 1 1 ≤ Store.inBlock Lc 0 2 by fp_sub))
  set P : ℕ → ℕ → Mem ℝ → Prop := fun j i μ' => μ'.pos = μ.pos ∧
    μ'.store.length = Lc + 5 ∧ (∀ k < 5, μ'.store.len (Lc + k) = 2) ∧
    μ'.store.readBlock Lc 0 2 = some [M.lit 1, M.lit 0] ∧ HoldsMatrix xs Xs μ'.store ∧
    HoldsMatrix ys Ys μ'.store ∧ MatMulPrefix z W j i μ'.store ∧
    z.2 + 2 * (m * q) ≤ μ'.store.len z.1 with hP
  have hstart : P 0 0 μ₂ := by
    refine ⟨hp₂.trans hp₁, by rw [hfr₂.length_eq, hfr₁.length_eq]; simpa using hlen,
      fun k hk => by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hl5 k hk, hone,
      hfr₁₂.keep (readsOnly_holdsMatrix _ _) (by disjoint) (hX.of_below hBelow hxsl),
      hfr₁₂.keep (readsOnly_holdsMatrix _ _) (by disjoint) (hY.of_below hBelow hysl),
      fun _ _ h => by omega, ?_⟩
    rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow z.1 hzl).1]; exact hz
  refine (writes_loop₂ (M := q) (N := m) (by simp [IExp.eval, Env.frame]) (fun _ => by
      simp [IExp.eval, Env.frame, Env.pushIdx]) (fun _ _ => Z ⊔ G) (fun _ _ _ _ => le_rfl)
    (fun _ _ => le_rfl) P hstart ?_ ?_).mono (by rw [hZ, hG]; fp_sub) ?_
  · rintro j hj μ' ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, fun i' j' h => h7 i' j' (by omega), h8⟩
  · intro j hj i hi μ' _ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact matMulOn_entry_step hS lf rf hsrc hsrcY hxz hyz (by simp [Env.pushIdx, Env.frame])
      (by simp [Env.pushIdx, Env.frame, List.range_succ]) hxl hyl hzl hxsl hysl hj hi h1 h2 h3
      h4 h5 h6 h7 h8
  · rintro μ' - ⟨h1, -, -, -, -, -, h7, -⟩
    refine ⟨h1, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
    · simpa using Store.get_of_readBlock (h7 i j (Or.inl j.isLt)) (j := 0) (by omega) 0
    · simpa using Store.get_of_readBlock (h7 i j (Or.inl j.isLt)) (j := 1) (by omega) 0

section Theorems

/-- **`NLAlib.matMulOn` on strided views** with $c = 0$, on a scalar machine and every tape: if
the left view `x` (leading dimension `ldx`) reads the entries of $\mathbf{X}$ ($m \times p$) from
a matrix stored at `xs`, the right view `y` (leading dimension `ldy`) reads the entries of
$\mathbf{Y}$ ($p \times q$) from a matrix stored at `ys`, and the contiguous output `z` has room
and is apart from both stored matrices, then the program writes only the output and stores
`NLAlib.matMulWord`. -/
theorem matMulOn_writes_view {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {m p q ldx ldy r₁ r₂ r₃ r₄ : ℕ} {x y z xs ys : ℕ × ℕ}
    {Xs : Matrix (Fin r₁) (Fin r₂) ℂ} {Ys : Matrix (Fin r₃) (Fin r₄) ℂ}
    (X : Matrix (Fin m) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ)
    (hX : HoldsMatrix xs Xs μ.store)
    (hsrc : ∀ s, HoldsMatrix xs Xs s → ∀ (i : Fin m) (l : Fin p),
      s.readBlock x.1 (x.2 + 2 * (l * ldx + i)) 2 = some [(X i l).re, (X i l).im])
    (hY : HoldsMatrix ys Ys μ.store)
    (hsrcY : ∀ s, HoldsMatrix ys Ys s → ∀ (l : Fin p) (j : Fin q),
      s.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(Y l j).re, (Y l j).im])
    (hl : μ.Live [x, y, z, xs, ys]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock xs.1 xs.2 (2 * (r₂ * r₁)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock ys.1 ys.2 (2 * (r₄ * r₃)))
      (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q))
      (Env.frame [m, p, q, ldx, ldy, m, 0] [x, y, z]) (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M X Y) μ'.store) μ := by
  have g : ∀ {s : Store ℝ} {b o : ℕ} {u v : ℝ}, s.readBlock b o 2 = some [u, v] →
      s.get b o = some u ∧ s.get b (o + 1) = some v := fun h =>
    ⟨by simpa using Store.get_of_readBlock h (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h (j := 1) (by omega) 0⟩
  exact matMulOn_writes_gen hS (fun i l => X i l) (fun l j => Y l j) hX
    (fun s hs i l => Or.inl ⟨rfl, (g (hsrc s hs i l)).1, (g (hsrc s hs i l)).2⟩) hY hsrcY hl hz
    hxz hyz

/-- The conjugate transpose **as the machine forms it**: entry $(i, l)$ is the real part of
$x_{li}$ and the machine negation of its imaginary part (`NLAlib.matMulOn` with $c = 1$). Under the
standard model it is $\mathbf{X}^{\mathsf H}$ (`NLAlib.machineConjTranspose_eq`). -/
def machineConjTranspose (M : Machine ℝ) {p m : ℕ} (X : Matrix (Fin p) (Fin m) ℂ) :
    Matrix (Fin m) (Fin p) ℂ :=
  Matrix.of fun i l => ⟨(X l i).re, M.neg (X l i).im⟩

omit [Has ScalarOp O] in
/-- Under the standard model negation is exact, so the machine conjugate transpose is the
conjugate transpose. -/
theorem machineConjTranspose_eq {M : Machine ℝ} {u : ℝ} (hM : Ops.StdModel u id M) {p m : ℕ}
    (X : Matrix (Fin p) (Fin m) ℂ) : machineConjTranspose M X = Xᴴ := by
  ext i l
  apply Complex.ext <;> simp [machineConjTranspose]
  simpa using hM.neg (X l i).im

/-- **`NLAlib.matMulOn` with the left factor conjugate-transposed on strided views** ($c = 1$),
on any scalar machine: if the left view `x` (leading dimension `ldx`) reads the entries of
$\mathbf{X}$ ($p \times m$) from a matrix stored at `xs`, the right view `y` reads $\mathbf{Y}$
($p \times q$) from a matrix stored at `ys`, and the contiguous output `z` has room apart from
both, the program writes only the output and stores `NLAlib.matMulWord` of the machine conjugate
transpose `NLAlib.machineConjTranspose` and $\mathbf{Y}$. -/
theorem matMulOn_machineConjTranspose_writes_view {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {μ : Mem ℝ}
    {m p q ldx ldy r₁ r₂ r₃ r₄ : ℕ} {x y z xs ys : ℕ × ℕ}
    {Xs : Matrix (Fin r₁) (Fin r₂) ℂ} {Ys : Matrix (Fin r₃) (Fin r₄) ℂ}
    (X : Matrix (Fin p) (Fin m) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ)
    (hX : HoldsMatrix xs Xs μ.store)
    (hsrc : ∀ s, HoldsMatrix xs Xs s → ∀ (l : Fin p) (i : Fin m),
      s.readBlock x.1 (x.2 + 2 * (i * ldx + l)) 2 = some [(X l i).re, (X l i).im])
    (hY : HoldsMatrix ys Ys μ.store)
    (hsrcY : ∀ s, HoldsMatrix ys Ys s → ∀ (l : Fin p) (j : Fin q),
      s.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(Y l j).re, (Y l j).im])
    (hl : μ.Live [x, y, z, xs, ys]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock xs.1 xs.2 (2 * (r₂ * r₁)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock ys.1 ys.2 (2 * (r₄ * r₃)))
      (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q))
      (Env.frame [m, p, q, ldx, ldy, m, 1] [x, y, z]) (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix z (matMulWord M (machineConjTranspose M X) Y) μ'.store) μ := by
  have g : ∀ {s : Store ℝ} {b o : ℕ} {u v : ℝ}, s.readBlock b o 2 = some [u, v] →
      s.get b o = some u ∧ s.get b (o + 1) = some v := fun h =>
    ⟨by simpa using Store.get_of_readBlock h (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h (j := 1) (by omega) 0⟩
  exact matMulOn_writes_gen hS (fun i l => machineConjTranspose M X i l) (fun l j => Y l j) hX
    (fun s hs i l => Or.inr ⟨rfl, by simpa [machineConjTranspose] using (g (hsrc s hs l i)).1,
      (X l i).im, (g (hsrc s hs l i)).2, rfl⟩) hY hsrcY hl hz hxz hyz

/-- **`NLAlib.matMulOn` with the left factor conjugate-transposed on strided views** ($c = 1$),
under the standard model (negation is exact): as
`NLAlib.matMulOn_machineConjTranspose_writes_view`, the program stores `NLAlib.matMulWord` of
$\mathbf{X}^{\mathsf H}$ and $\mathbf{Y}$. -/
theorem matMulOn_conjTranspose_writes_view {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : Ops.StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ}
    {m p q ldx ldy r₁ r₂ r₃ r₄ : ℕ} {x y z xs ys : ℕ × ℕ}
    {Xs : Matrix (Fin r₁) (Fin r₂) ℂ} {Ys : Matrix (Fin r₃) (Fin r₄) ℂ}
    (X : Matrix (Fin p) (Fin m) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ)
    (hX : HoldsMatrix xs Xs μ.store)
    (hsrc : ∀ s, HoldsMatrix xs Xs s → ∀ (l : Fin p) (i : Fin m),
      s.readBlock x.1 (x.2 + 2 * (i * ldx + l)) 2 = some [(X l i).re, (X l i).im])
    (hY : HoldsMatrix ys Ys μ.store)
    (hsrcY : ∀ s, HoldsMatrix ys Ys s → ∀ (l : Fin p) (j : Fin q),
      s.readBlock y.1 (y.2 + 2 * (j * ldy + l)) 2 = some [(Y l j).re, (Y l j).im])
    (hl : μ.Live [x, y, z, xs, ys]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock xs.1 xs.2 (2 * (r₂ * r₁)))
      (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock ys.1 ys.2 (2 * (r₄ * r₃)))
      (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q))
      (Env.frame [m, p, q, ldx, ldy, m, 1] [x, y, z]) (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M Xᴴ Y) μ'.store) μ := by
  rw [← machineConjTranspose_eq hM]
  exact matMulOn_machineConjTranspose_writes_view hS X Y hX hsrc hY hsrcY hl hz hxz hyz

/-- `NLAlib.matMulOn` with $c = 0$ on contiguous views (leading dimensions the row counts), on a
scalar machine and every tape: from $\mathbf{X}$ ($m \times p$) at `x` and $\mathbf{Y}$
($p \times q$) at `y`, with room for the output at `z` apart from both, it writes only the output
and stores `NLAlib.matMulWord`. -/
theorem matMulOn_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ} {x y z : ℕ × ℕ} {X : Matrix (Fin m) (Fin p) ℂ}
    {Y : Matrix (Fin p) (Fin q) ℂ} (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store)
    (hl : μ.Live [x, y, z]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (m * p))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)) (Env.frame [m, p, q, m, p, m, 0] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M X Y) μ'.store) μ :=
  matMulOn_writes_view hS X Y hX (fun s hs i l => hs.read_entry i l) hY
    (fun s hs l j => hs.read_entry l j)
    (fun v hv => hl v (by simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto)) hz
    (by rw [Nat.mul_comm p m]; exact hxz) (by rw [Nat.mul_comm q p]; exact hyz)

/-- `NLAlib.matMulOn` with $c = 1$ on contiguous views, under the standard model (negation is
exact): from $\mathbf{X}$ ($p \times m$) at `x` and $\mathbf{Y}$ ($p \times q$) at `y`, it writes
only the output and stores `NLAlib.matMulWord` of $\mathbf{X}^{\mathsf H}$ and $\mathbf{Y}$. -/
theorem matMulOn_conjTranspose_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : Ops.StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ}
    {x y z : ℕ × ℕ} {X : Matrix (Fin p) (Fin m) ℂ} {Y : Matrix (Fin p) (Fin q) ℂ}
    (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store) (hl : μ.Live [x, y, z])
    (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (p * m))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)) (Env.frame [m, p, q, p, p, m, 1] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M Xᴴ Y) μ'.store) μ :=
  matMulOn_conjTranspose_writes_view hS hM X Y hX (fun s hs l i => hs.read_entry l i) hY
    (fun s hs l j => hs.read_entry l j)
    (fun v hv => hl v (by simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto)) hz
    (by rw [Nat.mul_comm m p]; exact hxz) (by rw [Nat.mul_comm q p]; exact hyz)

end Theorems

/-- One rounded multiply–add $s \mapsto \mathrm{fl}(xy + \hat 1 s)$, with $\hat 1$ the pair of the
literals $1$ and $0$, is within $5\boldsymbol{u}\lvert x\rvert\lvert y\rvert +
(6\boldsymbol{u} + 5\boldsymbol{u}^2)\lvert s\rvert$ of $xy + s$. -/
theorem Ops.StdModel.norm_linearComplex_one_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (x y s : ℂ) :
    ‖linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + s)‖ ≤
      5 * u * (‖x‖ * ‖y‖) + (6 * u + 5 * u ^ 2) * ‖s‖ := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : |M.lit 1 - 1| ≤ u := by simpa using hM.lit 1
  have hone : ‖(⟨M.lit 1, M.lit 0⟩ : ℂ) - 1‖ ≤ u := by
    rw [h0, show (⟨M.lit 1, 0⟩ : ℂ) - 1 = ((M.lit 1 - 1 : ℝ) : ℂ) by
      apply Complex.ext <;> simp, Complex.norm_real, Real.norm_eq_abs]
    exact h1
  have hn1 : ‖(⟨M.lit 1, M.lit 0⟩ : ℂ)‖ ≤ 1 + u := by
    have := norm_sub_norm_le (⟨M.lit 1, M.lit 0⟩ : ℂ) 1
    rw [norm_one] at this
    linarith
  have h := hM.norm_linearWords_sub_le hu0 hu x ⟨M.lit 1, M.lit 0⟩ y s
  have e : linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + s) =
      (linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + ⟨M.lit 1, M.lit 0⟩ * s)) +
        ((⟨M.lit 1, M.lit 0⟩ : ℂ) - 1) * s := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hs := norm_nonneg s
  have hxy := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have h' : ‖linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + ⟨M.lit 1, M.lit 0⟩ * s)‖ ≤
      5 * u * (‖x‖ * ‖y‖ + ‖(⟨M.lit 1, M.lit 0⟩ : ℂ)‖ * ‖s‖) := h
  nlinarith [mul_le_mul_of_nonneg_right hn1 hs, mul_le_mul_of_nonneg_right hone hs]

/-- The norm of a sum over a list is at most the sum of the norms. -/
theorem norm_list_sum_map_le {ι : Type*} (f : ι → ℂ) (ls : List ι) :
    ‖(ls.map f).sum‖ ≤ (ls.map fun l => ‖f l‖).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

/-- A rounded accumulation of products: the multiply–adds of `NLAlib.matMulWord`, from the
pair of the literal $0$, over a list of indices, are within
$(1 + a)^k(5\boldsymbol{u}T + k a S)$ of the exact sum, $a = 6\boldsymbol{u} + 5\boldsymbol{u}^2$,
$k$ the length, $T$ the sum of $\lvert x_l\rvert\lvert y_l\rvert$ and $S \ge T$. -/
theorem Ops.StdModel.norm_foldl_linearComplex_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) {ι : Type*} (x y : ι → ℂ)
    (ls : List ι) {S : ℝ} (hS : (ls.map fun l => ‖x l‖ * ‖y l‖).sum ≤ S) :
    ‖ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s)
        ⟨M.lit 0, M.lit 0⟩ - (ls.map fun l => x l * y l).sum‖ ≤
      (1 + (6 * u + 5 * u ^ 2)) ^ ls.length *
        (5 * u * (ls.map fun l => ‖x l‖ * ‖y l‖).sum + ls.length * (6 * u + 5 * u ^ 2) * S) := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  set a := 6 * u + 5 * u ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  induction ls using List.reverseRecOn with
  | nil => simp [h0]; rfl
  | append_singleton ls l ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at hS ⊢
    have hn := mul_nonneg (norm_nonneg (x l)) (norm_nonneg (y l))
    have ih := ih (by linarith)
    set s := ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s)
      ⟨M.lit 0, M.lit 0⟩
    set t := (ls.map fun l => x l * y l).sum
    set T := (ls.map fun l => ‖x l‖ * ‖y l‖).sum
    have hT0 : 0 ≤ T := List.sum_nonneg fun t ht => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp ht; positivity
    have ht : ‖t‖ ≤ T := by
      refine (norm_list_sum_map_le _ ls).trans (le_of_eq ?_)
      simp [T]
    have hS0 : 0 ≤ S := by linarith
    have hstep := hM.norm_linearComplex_one_sub_le hu0 hu (x l) (y l) s
    have hs : ‖s‖ ≤ ‖t‖ + ‖s - t‖ := by
      have := norm_add_le t (s - t); rwa [add_sub_cancel] at this
    have e : linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (t + x l * y l) =
        (linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (x l * y l + s)) + (s - t) := by ring
    rw [e]
    rw [← ha] at hstep
    have hP : 1 ≤ (1 + a) ^ ls.length := one_le_pow₀ (by linarith)
    set P := (1 + a) ^ ls.length
    have hP' : (1 + a) ^ (ls.length + 1) = P * (1 + a) := pow_succ _ _
    rw [hP']
    refine (norm_add_le _ _).trans ?_
    push_cast
    have h1 : a * ‖s‖ ≤ a * (S + ‖s - t‖) := mul_le_mul_of_nonneg_left (by linarith) ha0
    have h3 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + a)
    have hq : 0 ≤ 5 * u * (‖x l‖ * ‖y l‖) + a * S := add_nonneg (by positivity) (mul_nonneg ha0 hS0)
    have h4 : 5 * u * (‖x l‖ * ‖y l‖) + a * S ≤ P * (1 + a) * (5 * u * (‖x l‖ * ‖y l‖) + a * S) :=
      le_mul_of_one_le_left hq (by nlinarith)
    have e2 : P * (1 + a) * (5 * u * (T + ‖x l‖ * ‖y l‖) + ((ls.length : ℝ) + 1) * a * S) =
        (1 + a) * (P * (5 * u * T + ls.length * a * S)) +
          P * (1 + a) * (5 * u * (‖x l‖ * ‖y l‖) + a * S) := by ring
    rw [e2]
    linarith

/-- The growth of an accumulation of $p$ products: with $a = 6\boldsymbol{u} +
5\boldsymbol{u}^2$ and $32(p + 1)\boldsymbol{u} \le 1$,
$(1 + a)^p(5\boldsymbol{u} + pa) \le 8(p + 1)\boldsymbol{u}$. -/
theorem matMul_growth_le {u : ℝ} {p : ℕ} (hu0 : 0 ≤ u) (hu : 32 * ((p : ℝ) + 1) * u ≤ 1) :
    (1 + (6 * u + 5 * u ^ 2)) ^ p * (5 * u + p * (6 * u + 5 * u ^ 2)) ≤ 8 * ((p : ℝ) + 1) * u := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hu32 : u ≤ 1 / 32 := by nlinarith
  have hpu : (p : ℝ) * u ≤ 1 / 32 := by nlinarith
  have hpa : (p : ℝ) * (6 * u + 5 * u ^ 2) ≤ (6 + 5 / 32) * ((p : ℝ) * u) := by
    nlinarith [mul_nonneg hp0 hu0, mul_nonneg (mul_nonneg hp0 hu0) hu0]
  have hpa0 : 0 ≤ (p : ℝ) * (6 * u + 5 * u ^ 2) := by positivity
  have hP := one_add_pow_sub_one_le (x := 6 * u + 5 * u ^ 2) (n := p) (by positivity)
    (by nlinarith)
  have hP2 : (1 + (6 * u + 5 * u ^ 2)) ^ p ≤ 5 / 4 := by nlinarith
  have hq : 0 ≤ 5 * u + p * (6 * u + 5 * u ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hP2 hq]

/-- **The error of a stored product with its growth factor** ([Higham2002, §3.5], complex): under
the standard model at $0 \le \boldsymbol{u} \le 1/8$, with $a = 6\boldsymbol{u} +
5\boldsymbol{u}^2$ and $p$ the inner dimension,
$\|\mathrm{fl}(\mathbf{X}\mathbf{Y}) - \mathbf{X}\mathbf{Y}\|_2 \le
(1 + a)^p(5\boldsymbol{u} + pa)\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$. No
condition ties $p$ to $\boldsymbol{u}$. -/
theorem Ops.StdModel.specNorm_matMulWord_sub_le_growth {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {m p q : ℕ}
    (X : Matrix (Fin m) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ) :
    specNorm (matMulWord M X Y - X * Y) ≤
      (1 + (6 * u + 5 * u ^ 2)) ^ p * (5 * u + p * (6 * u + 5 * u ^ 2)) *
        (frobNorm X * frobNorm Y) := by
  set c := (1 + (6 * u + 5 * u ^ 2)) ^ p * (5 * u + p * (6 * u + 5 * u ^ 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  set Xa : Matrix (Fin m) (Fin p) ℂ := Matrix.of fun i l => ((‖X i l‖ : ℝ) : ℂ)
  set Ya : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun l j => ((‖Y l j‖ : ℝ) : ℂ)
  have hXa : frobNorm Xa = frobNorm X := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
  have hYa : frobNorm Ya = frobNorm Y := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
  have hent : ∀ i j, ‖(matMulWord M X Y - X * Y) i j‖ ≤ ‖((c : ℂ) • (Xa * Ya)) i j‖ := by
    intro i j
    set T := ∑ l, ‖X i l‖ * ‖Y l j‖ with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
    have hTr : ‖((c : ℂ) • (Xa * Ya)) i j‖ = c * T := by
      have e : ((c : ℂ) • (Xa * Ya)) i j = ((c * T : ℝ) : ℂ) := by
        simp [Xa, Ya, Matrix.mul_apply, T]
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hTr]
    have hL : ((List.finRange p).map fun l => ‖X i l‖ * ‖Y l j‖).sum = T :=
      (Fin.sum_univ_def _).symm
    have hF := hM.norm_foldl_linearComplex_sub_le hu0 hu8 (X i) (fun l => Y l j)
      (List.finRange p) (le_of_eq hL)
    rw [hL, List.length_finRange] at hF
    have hE : (matMulWord M X Y - X * Y) i j = (List.finRange p).foldl
        (fun s l => linearComplex M (X i l) ⟨M.lit 1, M.lit 0⟩ (Y l j) s) ⟨M.lit 0, M.lit 0⟩ -
          ((List.finRange p).map fun l => X i l * Y l j).sum := by
      simp [matMulWord, Matrix.mul_apply, Fin.sum_univ_def]
    rw [hE]
    refine hF.trans (le_of_eq ?_)
    rw [hc]
    ring
  refine (specNorm_le_frobNorm _).trans ((frobNorm_le_of_norm_apply_le hent).trans ?_)
  rw [frobNorm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
  exact mul_le_mul_of_nonneg_left ((frobNorm_mul_le Xa Ya).trans (by rw [hXa, hYa])) hc0

/-- **The error of a stored product** ([Higham2002, §3.5], complex, with the accumulation from a
rounded zero and a rounded unit): under the standard model at $\boldsymbol{u}$ with
$32(p + 1)\boldsymbol{u} \le 1$,
$\|\mathrm{fl}(\mathbf{X}\mathbf{Y}) - \mathbf{X}\mathbf{Y}\|_2 \le
8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$, $p$ the inner
dimension. Each multiply–add rounds the running sum four times (the product by the rounded unit,
the subtraction of the exact zero product, the sum), so a term passes through at most $4p$
roundings; the complex products contribute the factor $\sqrt 2$. -/
theorem Ops.StdModel.specNorm_matMulWord_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) {m p q : ℕ} (hu : 32 * ((p : ℝ) + 1) * u ≤ 1)
    (X : Matrix (Fin m) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ) :
    specNorm (matMulWord M X Y - X * Y) ≤ 8 * (p + 1) * u * (frobNorm X * frobNorm Y) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hu8 : u ≤ 1 / 8 := by
    have : (1 : ℝ) ≤ (p : ℝ) + 1 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    nlinarith
  refine (hM.specNorm_matMulWord_sub_le_growth hu0 hu8 X Y).trans ?_
  exact mul_le_mul_of_nonneg_right (matMul_growth_le hu0 hu)
    (mul_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _))

/-- **A scaled stored matrix**: if every word of a stored $\mathbf{A}$ is replaced by its rounded
product with $r$ under the standard model at $\boldsymbol{u}$, the block holds an
$\mathbf{A}'$ with $\|\mathbf{A}' - r\mathbf{A}\|_{\mathsf F} \le
\boldsymbol{u}\lvert r\rvert\,\|\mathbf{A}\|_{\mathsf F}$ whose zero entries are those of
$\mathbf{A}$ at least. -/
theorem Ops.StdModel.exists_holdsMatrix_mul {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M)
    {N : ℕ} {b : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {s s' : Store ℝ} {r : ℝ}
    (hA : HoldsMatrix b A s)
    (h : ∀ t < 2 * (N * N), ∀ w, s.get b.1 (b.2 + t) = some w →
      s'.get b.1 (b.2 + t) = some (M.mul w r)) :
    ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix b A' s' ∧
      frobNorm (A' - (r : ℂ) • A) ≤ u * |r| * frobNorm A ∧ ∀ i j, A i j = 0 → A' i j = 0 := by
  have hu : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hlt : ∀ (i j : Fin N), 2 * (j * N + i) + 1 < 2 * (N * N) := fun i j => by
    have := Idx.add_lt_mul j.isLt i.isLt; omega
  refine ⟨Matrix.of fun i j => ⟨M.mul (A i j).re r, M.mul (A i j).im r⟩, ?_, ?_, ?_⟩
  · refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
    · exact h _ (by have := hlt i j; omega) _ (hA.get_re i j)
    · rw [Nat.add_assoc]; exact h _ (hlt i j) _ (by rw [← Nat.add_assoc]; exact hA.get_im i j)
  · rw [show u * |r| * frobNorm A = ‖((u * |r| : ℝ) : ℂ)‖ * frobNorm A by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)], ← frobNorm_smul]
    refine frobNorm_le_of_norm_apply_le fun i j => ?_
    have h1 := hM.mul (A i j).re r
    have h2 := hM.mul (A i j).im r
    simp only [id] at h1 h2
    set z := A i j
    have e1 : (Matrix.of (fun i j => (⟨M.mul (A i j).re r, M.mul (A i j).im r⟩ : ℂ)) -
        (r : ℂ) • A) i j = ⟨M.mul z.re r - z.re * r, M.mul z.im r - z.im * r⟩ := by
      apply Complex.ext <;> simp [z, mul_comm]
    have e2 : (((u * |r| : ℝ) : ℂ) • A) i j = ((u * |r| : ℝ) : ℂ) * z := rfl
    rw [e1, e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [Complex.sq_norm, Complex.normSq_mk, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    rw [abs_mul] at h1 h2
    have h1' := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    have h2' := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    have hr2 : |r| ^ 2 = r ^ 2 := sq_abs r
    have hz1 : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
    have hz2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    nlinarith
  · intro i j hz
    have h0 := hM.mul (A i j).re r
    apply Complex.ext
    · simp only [Matrix.of_apply, Complex.zero_re]
      have : (A i j).re = 0 := by rw [hz]; rfl
      rw [this] at h0 ⊢; simpa using h0
    · simp only [Matrix.of_apply, Complex.zero_im]
      have h0' := hM.mul (A i j).im r
      have : (A i j).im = 0 := by rw [hz]; rfl
      rw [this] at h0' ⊢; simpa using h0'

end NLAlib
