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

## Main results

* `NLAlib.matMulOn_writes_word`, `NLAlib.matMulOn_conjTranspose_writes_word`: the program stores
  `NLAlib.matMulWord` (contiguous views).
* `NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le`: the error of the stored product.
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
def matMulOn : Impl O Q := opsImpl% [m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z) {
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
        run Pair.linearCombination.body [] (A, One, Y[2 * (j * ldy + l)], S, T, R);
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
      (Pair.linearCombination (Op := O) (Tst := Q)).body).seq
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
  have hA0 : Store.inBlock (Lc + 1) 0 1 ≤ Store.inBlock (Lc + 1) 0 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have hA1 : Store.inBlock (Lc + 1) 1 1 ≤ Store.inBlock (Lc + 1) 0 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hlA : 1 < μ.store.len (Lc + 1) := by rw [hlens 1 (by omega)]; omega
  have hxs : ∀ k, ¬Store.inBlock (Lc + 1) 0 2 x.1 k := fun k h => by have := h.1; omega
  -- the left entry into `A`
  have fillA : ∀ (rest : Stmt O Q) (Gr : Fp) (Pr : Mem ℝ → Prop),
      Store.inBlock (Lc + 1) 0 2 ≤ Gr →
      (∀ μ₂ : Mem ℝ, μ.store.EqOff (Store.inBlock (Lc + 1) 0 2) μ₂.store → μ₂.pos = μ.pos →
        μ₂.store.readBlock (Lc + 1) 0 2 = some [a.re, a.im] → Writes .total I τ rest ρ Gr Pr μ₂) →
      Writes .total I τ ((Stmt.ifPos (IExp.var 6)
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
            [{ buf := 4, off := IExp.const 1 }]))).seq rest)) ρ Gr Pr μ := by
    intro rest Gr Pr hGr hrest
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
  unfold matMulLBody
  refine fillA _ _ _ (le_sup_left.trans (le_sup_left.trans le_sup_left))
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
  refine (Pair.writes_linearCombination (τ := τ) (m := μ₂) hS (a := (Lc + 1, 0)) (b := (Lc, 0))
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
    (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval]) trivial
    (g hR₃).1 rfl
    (by simp [hl₃ 2 (by omega)])).seq_le (by fp_sub) fun μ₄ hfr₄ ⟨hp₄, g₄⟩ => ?_
  have hR₄ := hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hR₃
  refine (writes_call_un (hS .copy) (x := (Lc + 4, 1)) (z := (Lc + 2, 1))
    (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, hidx, hbuf, IExp.eval]) trivial
    (g hR₄).2 rfl
    (by simp [hfr₄.len_eq, hl₃ 2 (by omega)])).mono (by fp_sub) fun μ₅ hfr₅ ⟨hp₅, g₅⟩ => ?_
  have g₄' := hfr₅.keep (Store.readsOnly_get _ _ _) (by disjoint) g₄
  refine ⟨hp₅.trans (hp₄.trans (hp₃.trans hp₂)), ?_⟩
  simpa [linearComplex] using Store.readBlock_succ_of (Store.readBlock_one_of_get g₄') g₅

section Theorems

variable [Inhabited ℝ]

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
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, m, p, m, 0] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M X Y) μ'.store) μ :=
  by
  unfold matMulOn
  sorry

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
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, p, p, m, 1] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M Xᴴ Y) μ'.store) μ :=
  sorry

end Theorems

/-- One rounded multiply–add $s \mapsto \mathrm{fl}(xy + \hat 1 s)$, with $\hat 1$ the pair of the
literals $1$ and $0$, is within $5\boldsymbol{u}|x||y| + (6\boldsymbol{u} +
5\boldsymbol{u}^2)|s|$ of $xy + s$. -/
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

/-- **A rounded accumulation of products**: the multiply–adds of `NLAlib.matMulWord`, from the
pair of the literal $0$, over a list of indices, are within
$(1 + a)^k(5\boldsymbol{u}T + k a S)$ of the exact sum, $a = 6\boldsymbol{u} + 5\boldsymbol{u}^2$,
$k$ the length, $T$ the sum of $|x_l||y_l|$ and $S \ge T$. -/
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
    have hT0 : 0 ≤ T := List.sum_nonneg (by simp; intro _ _; positivity)
    have ht : ‖t‖ ≤ T := by
      refine (norm_list_sum_map_le _ ls).trans (le_of_eq ?_)
      simp [T, norm_mul]
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
  set c := 8 * ((p : ℝ) + 1) * u with hc
  have hc0 : 0 ≤ c := by positivity
  set Xa : Matrix (Fin m) (Fin p) ℂ := Matrix.of fun i l => ((‖X i l‖ : ℝ) : ℂ)
  set Ya : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun l j => ((‖Y l j‖ : ℝ) : ℂ)
  have hXa : frobNorm Xa = frobNorm X := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
  have hYa : frobNorm Ya = frobNorm Y := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
  have hu8 : u ≤ 1 / 8 := by
    have : (1 : ℝ) ≤ (p : ℝ) + 1 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    nlinarith
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
    refine hF.trans ?_
    have hk := matMul_growth_le hu0 hu
    nlinarith [mul_le_mul_of_nonneg_right hk hT0]
  refine (specNorm_le_frobNorm _).trans ((frobNorm_le_of_norm_apply_le hent).trans ?_)
  rw [frobNorm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
  exact mul_le_mul_of_nonneg_left ((frobNorm_mul_le Xa Ya).trans (by rw [hXa, hYa])) hc0

end NLAlib
