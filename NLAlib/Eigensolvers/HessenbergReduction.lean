/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Backward
public import NLAlib.Matrix.FinitePrecision.GivensCoefficients
public import NLAlib.Eigensolvers.ShiftedQR.Hessenberg
public import NLAlib.Matrix.FinitePrecision.GivensPrograms
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Eigensolvers.Schur.Contracts

/-!
# Bottom-up reduction to Hessenberg form by rounded rotations

A complex matrix of order $N$ is reduced to upper Hessenberg form by a unitary similarity that
fixes the last coordinate vector $\mathbf{e}_N$: row by row from the bottom, the entries of row
$r$ left of the subdiagonal are zeroed by rotations of adjacent columns $c, c + 1 < r$, each
applied on both sides. The columns rotated never include the last one, so the accumulated
unitary fixes $\mathbf{e}_N$; the entries below the subdiagonal are then written as exact
zeros. This is the "bottom-up Hessenberg form" that
[BanksGarzaVargasSrivastava2025, Definition 5.1] assumes to be stable; here it is a fixed program
over rounded scalar arithmetic, and its backward error is proved. The exact top-down reduction
(`NLAlib.hessenbergReduction`, fixing $\mathbf{e}_1$) is not a program.

## Main definitions

* `NLAlib.reduceLastStep`, `NLAlib.hessenbergReduceLast`: one step and the program
  `[N, w, j0] (A) → (A, Lg)`, which records its rotations in a slotted log
  (`NLAlib.HoldsSlottedLog`), one slot per round.
* `NLAlib.reduceLastStepEntry`, `NLAlib.hessenbergReduceLastSlots`: the entries it records.
* `NLAlib.hessenbergReduceQ`: the reduction with the accumulated unitary, `[N] (A, U) → (A, U)`.
* `NLAlib.hessenbergReduceLastWord`: the matrix it stores on a machine.

## Main results

* `NLAlib.reduceLastStep_writes_word`, `NLAlib.hessenbergReduceLast_writes_word`: the program
  stores the machine evaluation.
* `NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilarBy`: backward stability by the exact
  unitary of the recorded rotations, which fixes the last coordinate vector;
  `NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilar`: the unitary unnamed.
* `NLAlib.hessenbergReduceQ_hessenbergReducerContract`: the reduction with the accumulated
  unitary is a Hessenberg reducer stage (`NLAlib.Schur.HessenbergReducerContract`).
* `NLAlib.hessenbergReduceLast_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **One step of the bottom-up reduction** at the row $r$ and the columns $c, c + 1$, recording
its rotation: the pair $(\mathbf{A}_{r, c+1}, -\mathbf{A}_{r, c})$ into `Uv`, the entry
$(c, \mathbf{A}_{r,c+1}, -\mathbf{A}_{r,c})$ as entry $i$ of slot $j$ of the slotted log `Lg` of
slot width $w$ (`NLAlib.slottedLogWrite`), its rounded Givens coefficients into `Cf`
(`NLAlib.coefficients`), then the rotation of the columns $c, c + 1$ and of the rows $c, c + 1$ of
`A` in place. The interface is `[N, r, c, w, j, i] (A) → (A, Cf, Uv, Lg)`.
Algorithm: hessenberg-reduction -/
def reduceLastStep : Impl O Q := opsImpl% [N, r, c, w, j, i] (A) → (A, Cf, Uv, Lg) {
  call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + r)]) → (Uv);
  call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + r) + 1]) → (Uv[1]);
  call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + r)]) → (Uv[2]);
  call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + r) + 1]) → (Uv[3]);
  run (slottedLogWrite (O := O) (Q := Q)).body [w, j, i, c] (Uv, Uv[2], Lg);
  run (coefficients (Op := O) (Tst := Q)).body [] (Uv, Uv[2], Cf, Cf[2]);
  run (rotateColumns (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A);
  run (rotateRows (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A)
}

/-- **The bottom-up Hessenberg reduction, recording its rotations**
([BanksGarzaVargasSrivastava2025, Definition 5.1], as a program): for the rows
$r = N - 1, \dots, 2$ (round $i$ has $r = N - 1 - i$) and the columns $c = 0, \dots, r - 2$, the
step `NLAlib.reduceLastStep`: the Givens coefficients of the pair
$(\mathbf{A}_{r, c+1}, -\mathbf{A}_{r, c})$, recorded as entry $c$ of slot $j_0 + i$ of the
slotted log `Lg` of slot width $w \ge N - 2$, then the rotation of the columns $c, c + 1$ (which
zeros $\mathbf{A}_{r,c}$) and of the rows $c, c + 1$; each round's slot is validated at its end;
finally the entries below the subdiagonal are written as zeros. The $N - 2$ slots
$j_0, \dots, j_0 + N - 3$ are written; the log is not opened here. The interface is
`[N, w, j0] (A) → (A, Lg)`; the coefficients and the pair are scoped scratch.
Algorithm: hessenberg-reduction -/
def hessenbergReduceLast : Impl O Q := opsImpl% [N, w, j0] (A) → (A, Lg) {
  let Cf ← alloc 4;
  let Uv ← alloc 4;
  for i < N - 2 {
    for c < N - 2 - i {
      run (reduceLastStep (O := O) (Q := Q)).body [N, N - 1 - i, c, w, j0 + i, c]
        (A, A, Cf, Uv, Lg)
    };
    run (slottedLogValidate (O := O) (Q := Q)).body [w, j0 + i] (Lg)
  };
  run (clearBelowSubdiagonal (Op := O) (Tst := Q)).body [N] (A)
}

end Program

/-- One step of the reduction on a machine: the rounded Givens coefficients of
$(\mathbf{A}_{r,c+1}, -\mathbf{A}_{r,c})$, then the rounded rotation of the columns $c, c + 1$
and of the rows $c, c + 1$; the identity when $c + 1$ or $r$ is out of range. -/
noncomputable def reduceLastStepWord (M : Machine ℝ) {N : ℕ} (r c : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if h : c + 1 < N ∧ r < N then
    let i : Fin N := ⟨c, by omega⟩
    let j : Fin N := ⟨c + 1, h.1⟩
    let cs := roundedGivensCoeffs M (A ⟨r, h.2⟩ j)
      ⟨M.neg (A ⟨r, h.2⟩ i).re, M.neg (A ⟨r, h.2⟩ i).im⟩
    machineRowRotation M i j cs.1 cs.2 (machineColRotation M i j cs.1 cs.2 A)
  else A

/-- The matrix stored by `NLAlib.hessenbergReduceLast` on the machine `M`: the steps
`NLAlib.reduceLastStepWord` in the order of the program, then the entries below the subdiagonal
replaced by the pair of the literal $0$. -/
noncomputable def hessenbergReduceLastWord (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  let B := ((List.range (N - 2)).flatMap fun i =>
      (List.range (N - 2 - i)).map fun c => (i, c)).foldl
    (fun X ic => reduceLastStepWord M (N - 1 - ic.1) ic.2 X) A
  Matrix.of fun i j => if (j : ℕ) + 1 < i then ⟨M.lit 0, M.lit 0⟩ else B i j

/-- The log entry recorded by one step of the reduction on the machine `M`: the plane $c$ and the
coefficient inputs $(\mathbf{A}_{r,c+1}, \mathrm{fl}(-\mathbf{A}_{r,c}))$; the zero entry when
$c + 1$ or $r$ is out of range. -/
noncomputable def reduceLastStepEntry (M : Machine ℝ) {N : ℕ} (r c : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) : GivensEntry :=
  if h : c + 1 < N ∧ r < N then
    (c, A ⟨r, h.2⟩ ⟨c + 1, h.1⟩,
      ⟨M.neg (A ⟨r, h.2⟩ ⟨c, by omega⟩).re, M.neg (A ⟨r, h.2⟩ ⟨c, by omega⟩).im⟩)
  else (0, 0, 0)

/-- The slots recorded by `NLAlib.hessenbergReduceLast` on the machine `M`: slot $i$ holds the
entries of the steps of round $i$, in the order of the program. -/
noncomputable def hessenbergReduceLastSlots (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) : List (List GivensEntry) :=
  ((List.range (N - 2)).foldl
    (fun (st : Matrix (Fin N) (Fin N) ℂ × List (List GivensEntry)) i =>
      let r := (List.range (N - 2 - i)).foldl
        (fun (p : Matrix (Fin N) (Fin N) ℂ × List GivensEntry) c =>
          (reduceLastStepWord M (N - 1 - i) c p.1,
            p.2 ++ [reduceLastStepEntry M (N - 1 - i) c p.1])) (st.1, [])
      (r.1, st.2 ++ [r.2])) (A, [])).2

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

omit [Has IndexOp O] in
/-- The rotation part of a step of the reduction: from the pair $(u, v)$ stored at `uv`, the
rounded coefficients into `cf`, then the rounded rotation of the columns and of the rows
$c, c + 1$ of the matrix at `a`. -/
private theorem reduceLastStep_rotate {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N r c w j i : ℕ} (hc : c + 1 < N) (hr : r < N)
    {a cf uv lg : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : HoldsMatrix a A m.store)
    (hu₀ : m.store.get uv.1 uv.2 = some (A ⟨r, hr⟩ ⟨c + 1, hc⟩).re)
    (hu₁ : m.store.get uv.1 (uv.2 + 1) = some (A ⟨r, hr⟩ ⟨c + 1, hc⟩).im)
    (hv₀ : m.store.get uv.1 (uv.2 + 2) = some (M.neg (A ⟨r, hr⟩ ⟨c, by omega⟩).re))
    (hv₁ : m.store.get uv.1 (uv.2 + 3) = some (M.neg (A ⟨r, hr⟩ ⟨c, by omega⟩).im))
    (hcf : cf.2 + 4 ≤ m.store.len cf.1)
    (hac : a.1 ≠ cf.1) (hl : m.Live [a, cf, uv]) :
    Writes .total I τ ((Stmt.frame []
        [⟨3, .var 9⟩, ⟨3, .var 9 + .const 2⟩, ⟨2, .var 8⟩, ⟨2, .var 8 + .const 2⟩]
        (coefficients (Op := O) (Tst := Q)).body).seq
      ((Stmt.frame [.var 0, .var 2] [⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨2, .var 8 + .const 2⟩, ⟨0, .var 6⟩]
        (rotateColumns (Op := O) (Tst := Q)).body).seq
        (Stmt.frame [.var 0, .var 2] [⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨2, .var 8 + .const 2⟩, ⟨0, .var 6⟩]
          (rotateRows (Op := O) (Tst := Q)).body)))
      (Env.frame [N, r, c, w, j, i] [a, a, cf, uv, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (reduceLastStepWord M r c A) m'.store) m := by
  let s : ℕ × ℕ := (cf.1, cf.2 + 2)
  have hcsub : Store.inBlock cf.1 cf.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have hssub : Store.inBlock s.1 s.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock (by dsimp [s]; omega) (by dsimp [s]; omega)
  have hcf4 : Fp.blocks [cf, s] [2, 2] ≤ Store.inBlock cf.1 cf.2 4 := by
    simpa only [Fp.blocks, sup_bot_eq] using sup_le hcsub hssub
  have hla : a.1 < m.store.length := hl a (by simp)
  have hlc : cf.1 < m.store.length := hl cf (by simp)
  have hlu : uv.1 < m.store.length := hl uv (by simp)
  refine (coefficients_writes_word (τ := τ) (m := m) (a := uv) (b := (uv.1, uv.2 + 2))
    (c := cf) (s := s) (u := A ⟨r, hr⟩ ⟨c + 1, hc⟩)
    (v := ⟨M.neg (A ⟨r, hr⟩ ⟨c, by omega⟩).re, M.neg (A ⟨r, hr⟩ ⟨c, by omega⟩).im⟩) hS hC
    (Fp.disj_inBlock_of_le le_rfl) hu₀ hu₁ hv₀ hv₁ (by omega)
    (by dsimp [s]; omega)).frame_seq_le rfl rfl (by simp [Mem.Live, s, hlc, hlu])
    (hcf4.trans le_sup_right) ?_
  rintro m₅ hfr₅ ⟨hp₅, hcs₅⟩
  have hc₅ := (Mem.readBlocks_cons_iff.mp hcs₅).1
  have hs₅ := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs₅).2).1
  have hAC : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne hac
  have hA₅ := hA.of_eqOff hfr₅ (hAC.symm.mono hcf4 le_rfl)
  refine (rotateColumns_writes_word (τ := τ) (k := c) hS hc hA₅ hc₅ hs₅ (hAC.mono le_rfl hcsub)
    (hAC.mono le_rfl hssub)).frame_seq_le rfl rfl
    (by have := hfr₅.length_eq; simp [Mem.Live, s]; omega) le_sup_left ?_
  rintro m₆ hfr₆ ⟨hp₆, hA₆⟩
  have hc₆ := hfr₆.keep (Store.readsOnly_readBlock _ _ _ _) (hAC.mono le_rfl hcsub) hc₅
  have hs₆ := hfr₆.keep (Store.readsOnly_readBlock _ _ _ _) (hAC.mono le_rfl hssub) hs₅
  refine ((rotateRows_writes_word (τ := τ) (k := c) hS hc hA₆ hc₆ hs₆ (hAC.mono le_rfl hcsub)
    (hAC.mono le_rfl hssub)).in_frame rfl rfl
    (by have := hfr₅.length_eq; have := hfr₆.length_eq; simp [Mem.Live, s]; omega)).mono
    le_sup_left ?_
  rintro m₇ - ⟨hp₇, hA₇⟩
  refine ⟨hp₇.trans (hp₆.trans hp₅), ?_⟩
  unfold reduceLastStepWord
  rw [dif_pos ⟨hc, hr⟩]
  exact hA₇

/-- One step of the reduction (`NLAlib.reduceLastStep`) on any scalar machine with exact
comparisons stores the machine step `NLAlib.reduceLastStepWord` in place, for $c + 1 < N$ and
$r < N$, appends its entry `NLAlib.reduceLastStepEntry` to the pending slot of the log, and writes
only the matrix, its two scratch blocks (in buffers of their own) and the log (apart from the
matrix). The plane is an exact natural (`hNat` up to $n_{\max} \ge c$). -/
theorem reduceLastStep_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {N r c : ℕ} (hc : c + 1 < N) (hr : r < N) (hcn : c ≤ nmax)
    {a cf uv lg : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : HoldsMatrix a A m.store)
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns) (hw : P.length < w)
    (hcf : cf.2 + 4 ≤ m.store.len cf.1) (huv : uv.2 + 4 ≤ m.store.len uv.1)
    (hac : a.1 ≠ cf.1) (hau : a.1 ≠ uv.1) (hlu : lg.1 ≠ uv.1) (hlc : lg.1 ≠ cf.1)
    (hla : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))) (hl : m.Live [lg]) :
    Writes .total I τ (reduceLastStep (O := O) (Q := Q)).body
      (Env.frame [N, r, c, w, L.length, P.length] [a, a, cf, uv, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock cf.1 cf.2 4 ⊔
        Store.inBlock uv.1 uv.2 4 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (reduceLastStepWord M r c A) m'.store ∧
        HoldsSlottedLog lg ns w L (P ++ [reduceLastStepEntry M r c A]) m'.store) m := by
  let i : Fin N := ⟨c, by omega⟩
  let j : Fin N := ⟨c + 1, hc⟩
  let k : Fin N := ⟨r, hr⟩
  have hal : a.1 < m.store.length := Store.lt_length_of_get (hA.get_re k i)
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hul : uv.1 < m.store.length := Store.lt_length_of_lt_len (by omega : uv.2 < _)
  have hgl : lg.1 < m.store.length := hl lg (by simp)
  have hU : ∀ t, Fp.Disj (Store.inBlock uv.1 (uv.2 + t) 1)
      (Store.inBlock a.1 a.2 (2 * (N * N))) := fun _ => Fp.disj_inBlock_of_ne hau.symm
  have hUle : ∀ t < 4, Store.inBlock uv.1 (uv.2 + t) 1 ≤ Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
      Store.inBlock cf.1 cf.2 4 ⊔ Store.inBlock uv.1 uv.2 4 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) := fun t ht =>
    (Fp.inBlock_le_inBlock (by omega) (by omega)).trans (le_sup_right.trans le_sup_left)
  have hUL : ∀ t, Fp.Disj (Store.inBlock uv.1 (uv.2 + t) 1)
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) := fun _ => Fp.disj_inBlock_of_ne hlu.symm
  have hRL := readsOnly_holdsSlottedLog lg ns w L P
  unfold reduceLastStep
  refine (writes_call_un (hS .copy) rfl rfl trivial (hA.get_re k j) rfl
    (by omega)).seq_le (hUle 0 (by omega)) ?_
  rintro m₁ hfr₁ ⟨hp₁, hu₀⟩
  have hA₁ := hA.of_eqOff hfr₁ (hU 0)
  refine (writes_call_un (hS .copy) rfl rfl trivial (hA₁.get_im k j) rfl
    (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le (hUle 1 (by omega)) ?_
  rintro m₂ hfr₂ ⟨hp₂, hu₁⟩
  have hA₂ := hA₁.of_eqOff hfr₂ (hU 1)
  refine (writes_call_un (hS .neg) rfl rfl trivial (hA₂.get_re k i) rfl
    (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega)).seq_le (hUle 2 (by omega)) ?_
  rintro m₃ hfr₃ ⟨hp₃, hv₀⟩
  have hA₃ := hA₂.of_eqOff hfr₃ (hU 2)
  refine (writes_call_un (hS .neg) rfl rfl trivial (hA₃.get_im k i) rfl
    (by dsimp only; rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; omega)).seq_le
    (hUle 3 (by omega)) ?_
  rintro m₄ hfr₄ ⟨hp₄, hv₁⟩
  have hUU : ∀ {t t' : ℕ}, t < t' → Fp.Disj (Store.inBlock uv.1 (uv.2 + t) 1)
      (Store.inBlock uv.1 (uv.2 + t') 1) := fun h => Fp.disj_inBlock_of_le (by omega)
  have hu₀' := hfr₄.keep (Store.readsOnly_get _ _ _) (hUU (t := 0) (by omega)).symm
    (hfr₃.keep (Store.readsOnly_get _ _ _) (hUU (t := 0) (by omega)).symm
      (hfr₂.keep (Store.readsOnly_get _ _ _) (hUU (t := 0) (by omega)).symm hu₀))
  have hu₁' := hfr₄.keep (Store.readsOnly_get _ _ _) (hUU (t := 1) (by omega)).symm
    (hfr₃.keep (Store.readsOnly_get _ _ _) (hUU (t := 1) (by omega)).symm hu₁)
  have hv₀' := hfr₄.keep (Store.readsOnly_get _ _ _) (hUU (t := 2) (by omega)).symm hv₀
  have hA₄ := hA₃.of_eqOff hfr₄ (hU 3)
  have hlog₄ := hfr₄.keep hRL (hUL 3) (hfr₃.keep hRL (hUL 2)
    (hfr₂.keep hRL (hUL 1) (hfr₁.keep hRL (hUL 0) hlog)))
  have hlen₄ : m₄.store.length = m.store.length := by
    have := hfr₁.length_eq; have := hfr₂.length_eq; have := hfr₃.length_eq
    have := hfr₄.length_eq; omega
  have hlen (b : ℕ) : m₄.store.len b = m.store.len b := by
    rw [hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
  refine (slottedLogWrite_writes (τ := τ) (μ := m₄) (pw := uv) (qw := (uv.1, uv.2 + 2))
    (p := A k j) (q := ⟨M.neg (A k i).re, M.neg (A k i).im⟩) hS hL hNat hcn hlog₄ hj hw
    (by simpa using Store.readBlock_succ_of (Store.readBlock_one_of_get hu₀') hu₁')
    (by simpa using Store.readBlock_succ_of (Store.readBlock_one_of_get hv₀') hv₁)
    (by simp [Mem.Live, hlen₄, hul, hgl])
    (Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hlu, Fp.disj_inBlock_of_ne hlu⟩)).frame_seq_le
    rfl rfl (by simp [Mem.Live, hlen₄, hul, hgl]) le_sup_right ?_
  rintro m₅ hfr₅ ⟨hp₅, hlog₅⟩
  have hLU : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock uv.1 uv.2 4) :=
    Fp.disj_inBlock_of_ne hlu
  have kg := fun t (ht : t < 4) {x : ℝ} (h : m₄.store.get uv.1 (uv.2 + t) = some x) =>
    hfr₅.keep (Store.readsOnly_get _ _ _) (hLU.mono le_rfl
      (Fp.inBlock_le_inBlock (by omega) (by omega))) h
  refine ((reduceLastStep_rotate hS hC hc hr (hA₄.of_eqOff hfr₅ hla.symm)
    (kg 0 (by omega) hu₀') (kg 1 (by omega) hu₁') (kg 2 (by omega) hv₀') (kg 3 (by omega) hv₁)
    (by rw [hfr₅.len_eq, hlen]; exact hcf) hac
    (by have := hfr₅.length_eq; simp [Mem.Live]; omega)).mono
    (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans (le_sup_left.trans le_sup_left))) ?_)
  rintro m₇ hfr₇ ⟨hp₇, hA₇⟩
  refine ⟨hp₇.trans (hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁)))), hA₇, ?_⟩
  have hd : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock cf.1 cf.2 4)
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) :=
    Fp.disj_sup_left.mpr ⟨hla, Fp.disj_inBlock_of_ne hlc.symm⟩
  simpa [reduceLastStepEntry, hc, hr] using hfr₇.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hd
    hlog₅

/-- One step of round `i` of the reduction on the pair (matrix, entries of the round). -/
private noncomputable def hrRoundStep (M : Machine ℝ) {N : ℕ} (i : ℕ)
    (p : Matrix (Fin N) (Fin N) ℂ × List GivensEntry) (c : ℕ) :
    Matrix (Fin N) (Fin N) ℂ × List GivensEntry :=
  (reduceLastStepWord M (N - 1 - i) c p.1, p.2 ++ [reduceLastStepEntry M (N - 1 - i) c p.1])

/-- The first `C` steps of round `i` from the matrix `X`. -/
private noncomputable def hrRound (M : Machine ℝ) {N : ℕ} (i : ℕ) (X : Matrix (Fin N) (Fin N) ℂ)
    (C : ℕ) : Matrix (Fin N) (Fin N) ℂ × List GivensEntry :=
  (List.range C).foldl (hrRoundStep M i) (X, [])

/-- One round of the reduction on the pair (matrix, slots). -/
private noncomputable def hrOuter (M : Machine ℝ) {N : ℕ}
    (st : Matrix (Fin N) (Fin N) ℂ × List (List GivensEntry)) (i : ℕ) :
    Matrix (Fin N) (Fin N) ℂ × List (List GivensEntry) :=
  ((hrRound M i st.1 (N - 2 - i)).1, st.2 ++ [(hrRound M i st.1 (N - 2 - i)).2])

private theorem hrRound_succ (M : Machine ℝ) {N : ℕ} (i : ℕ) (X : Matrix (Fin N) (Fin N) ℂ)
    (C : ℕ) : hrRound M i X (C + 1) = hrRoundStep M i (hrRound M i X C) C := by
  simp [hrRound, List.range_succ, List.foldl_append]

private theorem hrRound_fst (M : Machine ℝ) {N : ℕ} (i : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    ∀ C, (hrRound M i X C).1 = ((List.range C).map fun c => (i, c)).foldl
      (fun X ic => reduceLastStepWord M (N - 1 - ic.1) ic.2 X) X
  | 0 => rfl
  | C + 1 => by
    rw [hrRound_succ, List.range_succ, List.map_append, List.foldl_append, ← hrRound_fst M i X C]
    rfl

private theorem hrRound_length (M : Machine ℝ) {N : ℕ} (i : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    ∀ C, (hrRound M i X C).2.length = C
  | 0 => rfl
  | C + 1 => by rw [hrRound_succ]; simp [hrRoundStep, hrRound_length M i X C]

private theorem hrOuter_fst (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ∀ I, ((List.range I).foldl (hrOuter M) (A, [])).1 = ((List.range I).flatMap fun i =>
      (List.range (N - 2 - i)).map fun c => (i, c)).foldl
        (fun X ic => reduceLastStepWord M (N - 1 - ic.1) ic.2 X) A
  | 0 => rfl
  | I + 1 => by
    rw [List.range_succ, List.foldl_append, List.flatMap_append, List.foldl_append,
      ← hrOuter_fst M A I]
    simp [hrOuter, hrRound_fst]

private theorem hrOuter_length (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ∀ I, ((List.range I).foldl (hrOuter M) (A, [])).2.length = I
  | 0 => rfl
  | I + 1 => by
    rw [List.range_succ, List.foldl_append]
    simp [hrOuter, hrOuter_length M A I]

private theorem hessenbergReduceLastSlots_eq (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) :
    hessenbergReduceLastSlots M A = ((List.range (N - 2)).foldl (hrOuter M) (A, [])).2 := rfl

/-- `NLAlib.hessenbergReduceLast` on any scalar machine with exact comparisons stores the machine
evaluation `NLAlib.hessenbergReduceLastWord` of the matrix in place, closes the $N - 2$ slots
`NLAlib.hessenbergReduceLastSlots` (each accepted) of the log after its closed slots `L`, writes
only the matrix and the log, and reads no tape. The planes and the valid words are exact
naturals (`hNat` up to `nmax`, with $N \le n_{\max} + 1$ and $1 \le n_{\max}$). -/
theorem hessenbergReduceLast_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a lg : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hN : N ≤ nmax + 1) {ns w : ℕ}
    {L : List (Option (List GivensEntry))} (hlog : HoldsSlottedLog lg ns w L [] m.store)
    (hj : L.length + (N - 2) ≤ ns) (hw : N - 2 ≤ w) (hl : m.Live [a, lg])
    (hA : HoldsMatrix a A m.store)
    (hd : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body
      (Env.frame [N, w, L.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (hessenbergReduceLastWord M A) m'.store ∧
        HoldsSlottedLog lg ns w (L ++ (hessenbergReduceLastSlots M A).map some) [] m'.store) m := by
  have hal : a.1 < m.store.length := hl a (by simp)
  have hgl : lg.1 < m.store.length := hl lg (by simp)
  have hlit1 : 0 < M.lit 1 := by
    have := hNat 1 h1
    simp only [id, Nat.cast_one] at this
    rw [this]; exact one_pos
  unfold hessenbergReduceLast
  change Writes .total I τ (Stmt.allocs [.const 4, .const 4] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [4, 4]) rfl
    (fun hBelow ⟨hp, hW, hG⟩ => ⟨hp, hW.of_below hBelow hal, hG.of_below hBelow hgl⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := m.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  set G := Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock Lc 0 4 ⊔
    Store.inBlock (Lc + 1) 0 4 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) with hG
  set St : Matrix (Fin N) (Fin N) ℂ → List (Option (List GivensEntry)) → List GivensEntry →
      Mem ℝ → Prop := fun X Lg P μ => μ.pos = m.pos ∧
    μ.store.length = Lc + 2 ∧ μ.store.len Lc = 4 ∧ μ.store.len (Lc + 1) = 4 ∧
    HoldsMatrix a X μ.store ∧ HoldsSlottedLog lg ns w Lg P μ.store with hSt
  set Ou := fun i => (List.range i).foldl (hrOuter M) (A, []) with hOu
  have hstart : St A L [] ⟨s₁, m.pos⟩ :=
    ⟨rfl, by omega, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      hA.of_below hBelow hal, hlog.of_below hBelow hgl⟩
  have hGle : G ≤ (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) ⊔ Fp.above Lc := by
    rintro b x (((h | h) | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (h.1 ▸ le_rfl)
    · exact Or.inr (h.1 ▸ Nat.le_succ Lc)
    · exact Or.inl (Or.inr h)
  refine (writes_loop (N := N - 2) rfl (fun _ => G) (fun _ _ => le_rfl)
    (fun i μ => St (Ou i).1 (L ++ (Ou i).2.map some) [] μ) (by simpa [Ou] using hstart)
    ?_).seq_le hGle ?_
  · intro i hi μ _ hμ
    refine (writes_loop (N := N - 2 - i) rfl (fun _ => G) (fun _ _ => le_rfl)
      (fun c μ' => St (hrRound M i (Ou i).1 c).1 (L ++ (Ou i).2.map some)
        (hrRound M i (Ou i).1 c).2 μ') (by simpa [hrRound] using hμ) ?_).seq_le le_rfl ?_
    · intro c hc μ' _ ⟨hp, hlen', hL0, hL1, hW, hLg⟩
      refine ((reduceLastStep_writes_word (N := N) (r := N - 1 - i) (c := c) (cf := (Lc, 0))
        (uv := (Lc + 1, 0)) hS hC hL hNat
        (by omega) (by omega) (by omega) hW hLg (by simp [Ou, hrOuter_length]; omega)
        (by rw [hrRound_length]; omega) (by simp [hL0]) (by simp [hL1]) (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega) hd
        (by simp [Mem.Live, hlen']; omega)).in_frame ?_ rfl
        (by simp [Mem.Live, hlen']; omega)).mono le_rfl ?_
      · simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx, Ou, hrOuter_length, hrRound_length]
      · rintro μ'' hfr ⟨hp', hW', hLg'⟩
        refine ⟨hp'.trans hp, by rw [hfr.length_eq, hlen'], by rw [hfr.len_eq, hL0],
          by rw [hfr.len_eq, hL1], ?_, ?_⟩
        · rw [hrRound_succ]; exact hW'
        · rw [hrRound_succ]; exact hLg'
    · intro μ' _ ⟨hp, hlen', hL0, hL1, hW, hLg⟩
      refine ((slottedLogValidate_writes_of_pos hL hlit1 hLg
        (by simp [Ou, hrOuter_length]; omega)).in_frame ?_ rfl
        (by simp [Mem.Live, hlen']; omega)).mono le_sup_right ?_
      · simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx, Ou, hrOuter_length]
      · rintro μ'' hfr ⟨hp', hLg'⟩
        refine ⟨hp'.trans hp, by rw [hfr.length_eq, hlen'], by rw [hfr.len_eq, hL0],
          by rw [hfr.len_eq, hL1], ?_, ?_⟩
        · simpa [Ou, List.range_succ, List.foldl_append, hrOuter] using hW.of_eqOff hfr hd.symm
        · simpa [Ou, List.range_succ, List.foldl_append, hrOuter] using hLg'
  · rintro μ hfr ⟨hp, hlen', -, -, hW, hLg⟩
    refine ((clearBelowSubdiagonal_writes_word (τ := τ) hS (by simp [Mem.Live, hlen']; omega)
      hW).in_frame rfl rfl (by simp [Mem.Live, hlen']; omega)).mono
      (le_sup_left.trans le_sup_left) ?_
    rintro μ' hfr' ⟨hp', hW'⟩
    refine ⟨hp'.trans hp, ?_, ?_⟩
    · simpa [hessenbergReduceLastWord, Ou, hrOuter_fst] using hW'
    · rw [hessenbergReduceLastSlots_eq]
      exact hfr'.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hd hLg

section BackwardError

variable {M : Machine ℝ} {u : ℝ} {N : ℕ}

/-- Two entries of a row have joint Euclidean norm at most the spectral norm. -/
theorem sqrt_norm_sq_add_norm_sq_le_specNorm {i j : Fin N} (hij : i ≠ j)
    (Z : Matrix (Fin N) (Fin N) ℂ) (r : Fin N) :
    √(‖Z r i‖ ^ 2 + ‖Z r j‖ ^ 2) ≤ specNorm Z := by
  have h1 := norm_toLp_col_le_specNorm Zᴴ r
  rw [specNorm_conjTranspose, EuclideanSpace.norm_eq] at h1
  refine le_trans (Real.sqrt_le_sqrt ?_) h1
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
    (f := fun k => ‖(Zᴴ.col r) k‖ ^ 2) fun _ _ _ => sq_nonneg _
  simpa [Finset.sum_pair hij, Matrix.col_apply, Matrix.conjTranspose_apply] using h2

/-- **One rounded round, columns first, is close to the exact conjugation**: on a machine with
the standard model at $0 \le \boldsymbol{u} \le 1/576$, rotating the columns $i \ne j$ of
$\mathbf{Z}$ and then its rows by the coefficients computed from $(p, q)$ is within
$49\boldsymbol{u}\|\mathbf{Z}\|_2$ of $\mathbf{G}\mathbf{Z}\mathbf{G}^{\mathsf{H}}$ for the exact
Givens rotation $\mathbf{G}$ of $(p, q)$. [Higham2002, Lemma 19.8]. -/
theorem ShiftedQR.specNorm_machineRowRotation_machineColRotation_sub_le (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 576) {i j : Fin N} (hij : i ≠ j) (p q : ℂ)
    (Z : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2
        (machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z) -
      givens i j (givensCoeffs p q).1 (givensCoeffs p q).2 * Z *
        (givens i j (givensCoeffs p q).1 (givensCoeffs p q).2)ᴴ) ≤ 49 * u * specNorm Z := by
  have hu100 : u ≤ 1 / 100 := by linarith
  set G := givens i j (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G :=
    hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add p q)
  set Z₁ := machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z
  set Z₂ := machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z₁
  have h1 := (isRoundedColRotation_machineColRotation hM hu hu100 hij p q Z).specNorm_sub_le
    (by positivity)
  have h2 := (isRoundedRowRotation_machineRowRotation hM hu hu100 hij p q Z₁).specNorm_sub_le
    (by positivity)
  have hZ₁ : specNorm Z₁ ≤ (1 + 24 * u) * specNorm Z := by
    have e : Z₁ = Z * Gᴴ + (Z₁ - Z * Gᴴ) := by abel
    have := specNorm_add_le (Z * Gᴴ) (Z₁ - Z * Gᴴ)
    rw [← e, hG.specNorm_mul_conjTranspose_right] at this
    linarith
  have e : Z₂ - G * Z * Gᴴ = (Z₂ - G * Z₁) + G * (Z₁ - Z * Gᴴ) := by
    rw [Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_left]
  have hZ : 0 ≤ specNorm Z := specNorm_nonneg Z
  nlinarith [mul_le_mul_of_nonneg_left hZ₁ (by positivity : (0 : ℝ) ≤ 2 * (12 * u)),
    mul_nonneg (mul_nonneg hu hZ) (by linarith : (0 : ℝ) ≤ 1 - 576 * u)]

/-- **The rounded column rotation nearly clears its entry**: on a machine with the standard
model at $0 \le \boldsymbol{u} \le 1/100$, rotating the columns $i \ne j$ of $\mathbf{Z}$ by the
coefficients computed from $(\mathbf{Z}_{r,j}, -\mathbf{Z}_{r,i})$ leaves an entry $(r, i)$ of
modulus at most $12\boldsymbol{u}\|\mathbf{Z}\|_2$; the exact rotation clears it.
[Higham2002, Lemma 19.8]. -/
theorem ShiftedQR.norm_machineColRotation_apply_left_le (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) {i j : Fin N} (hij : i ≠ j) (Z : Matrix (Fin N) (Fin N) ℂ) (r : Fin N) :
    ‖machineColRotation M i j (roundedGivensCoeffs M (Z r j) (-Z r i)).1
      (roundedGivensCoeffs M (Z r j) (-Z r i)).2 Z r i‖ ≤ 12 * u * specNorm Z := by
  obtain ⟨-, h⟩ := isRoundedColRotation_machineColRotation hM hu hu' hij (Z r j) (-Z r i) Z
  set c₀ := (givensCoeffs (Z r j) (-Z r i)).1
  set s₀ := (givensCoeffs (Z r j) (-Z r i)).2
  have h0 : (Z * (givens i j c₀ s₀)ᴴ) r i = 0 := by
    have hz := neg_star_givensCoeffs_snd_mul_add (Z r j) (-Z r i)
    rw [conjTranspose_givens, mul_givens_apply_left hij]
    simp only [star_neg] at hz ⊢
    linear_combination -hz
  have hr := h r
  rw [h0, sub_zero] at hr
  refine le_trans ?_ (hr.trans (mul_le_mul_of_nonneg_left
    (sqrt_norm_sq_add_norm_sq_le_specNorm hij Z r) (by positivity)))
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

/-- The entries the bottom-up reduction has cleared before its step at the row $r$ and the
column $c$, replaced by zero: the entries $(a, b)$ with $b + 1 < a$ in the rows $a > r$, and in
the row $r$ those with $b < c$. -/
private def bottomUpMask (r c : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b =>
    if (b : ℕ) + 1 < a ∧ (r < (a : ℕ) ∨ (a : ℕ) = r ∧ (b : ℕ) < c) then 0 else X a b

/-- An entry of a rounded round, columns then rows, depends only on the rows $i, j$, the entry
itself, and for the columns $i, j$ the entries $(a, i), (a, j)$. -/
private theorem rowCol_apply_congr {i j a b : Fin N} {cs : ℂ × ℂ}
    {X Z : Matrix (Fin N) (Fin N) ℂ} (hi : ∀ t, X i t = Z i t) (hj : ∀ t, X j t = Z j t)
    (hab : X a b = Z a b) (hb : b = i ∨ b = j → X a i = Z a i ∧ X a j = Z a j) :
    machineRowRotation M i j cs.1 cs.2 (machineColRotation M i j cs.1 cs.2 X) a b =
      machineRowRotation M i j cs.1 cs.2 (machineColRotation M i j cs.1 cs.2 Z) a b := by
  by_cases hbij : b = i ∨ b = j
  · obtain ⟨h1, h2⟩ := hb hbij
    simp only [machineRowRotation, machineColRotation, Matrix.of_apply, hi, hj, h1, h2, hab]
  · rw [not_or] at hbij
    simp only [machineRowRotation, machineColRotation, Matrix.of_apply, hi, hj, hab, hbij.1,
      hbij.2, if_false]

/-- An entry outside the rows $i, j$ of a rounded round, columns then rows, of a matrix that
vanishes at it (and at $(a, i), (a, j)$ when it is in the columns $i, j$) vanishes. -/
private theorem rowCol_apply_eq_zero (hM : StdModel u id M) {i j a b : Fin N} {cs : ℂ × ℂ}
    {Z : Matrix (Fin N) (Fin N) ℂ} (hai : a ≠ i) (haj : a ≠ j) (hab : Z a b = 0)
    (hb : b = i ∨ b = j → Z a i = 0 ∧ Z a j = 0) :
    machineRowRotation M i j cs.1 cs.2 (machineColRotation M i j cs.1 cs.2 Z) a b = 0 := by
  rw [machineRowRotation_apply_of_ne hai haj]
  by_cases hbij : b = i ∨ b = j
  · obtain ⟨h1, h2⟩ := hb hbij
    simp only [machineColRotation, Matrix.of_apply, h1, h2, linearComplex_zero_zero hM]
    split_ifs <;> first | rfl | exact hab
  · rw [not_or] at hbij
    rw [machineColRotation_apply_of_ne hbij.1 hbij.2]
    exact hab

/-- The step at $(r, c)$ commutes with the clearing: up to the entry $(r, c)$ it clears, the
step of the masked matrix is the masked step. -/
private theorem bottomUpMask_reduceLastStepWord (hM : StdModel u id M) {r c : ℕ}
    (hc : c + 1 < r) (hr : r < N) (X : Matrix (Fin N) (Fin N) ℂ) :
    bottomUpMask r (c + 1) (reduceLastStepWord M r c X) =
      reduceLastStepWord M r c (bottomUpMask r c X) - Matrix.single ⟨r, hr⟩ ⟨c, by omega⟩
        (reduceLastStepWord M r c (bottomUpMask r c X) ⟨r, hr⟩ ⟨c, by omega⟩) := by
  set Z := bottomUpMask r c X with hZ
  have hZa : ∀ a b : Fin N, Z a b =
      if (b : ℕ) + 1 < a ∧ (r < (a : ℕ) ∨ (a : ℕ) = r ∧ (b : ℕ) < c) then 0 else X a b :=
    fun _ _ => rfl
  have e1 : Z ⟨r, hr⟩ ⟨c + 1, by omega⟩ = X ⟨r, hr⟩ ⟨c + 1, by omega⟩ := by
    rw [hZa, if_neg (by simp only; omega)]
  have e2 : Z ⟨r, hr⟩ ⟨c, by omega⟩ = X ⟨r, hr⟩ ⟨c, by omega⟩ := by
    rw [hZa, if_neg (by simp only; omega)]
  have hd : c + 1 < N ∧ r < N := ⟨by omega, hr⟩
  simp only [reduceLastStepWord, dif_pos hd, e1, e2]
  set i : Fin N := ⟨c, by omega⟩
  set j : Fin N := ⟨c + 1, hd.1⟩
  have hi : ∀ t, X i t = Z i t := fun t => by rw [hZa, if_neg (by simp only [i]; omega)]
  have hj : ∀ t, X j t = Z j t := fun t => by rw [hZa, if_neg (by simp only [j]; omega)]
  ext a b
  simp only [bottomUpMask, Matrix.of_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases hrc : a = ⟨r, hr⟩ ∧ b = i
  · obtain ⟨rfl, rfl⟩ := hrc
    have hm : (i : ℕ) + 1 < ((⟨r, hr⟩ : Fin N) : ℕ) ∧ (r < ((⟨r, hr⟩ : Fin N) : ℕ) ∨
        ((⟨r, hr⟩ : Fin N) : ℕ) = r ∧ (i : ℕ) < c + 1) := ⟨hc, Or.inr ⟨rfl, Nat.lt_succ_self c⟩⟩
    rw [if_pos hm, if_pos ⟨rfl, rfl⟩, sub_self]
  have hrc' : ¬((a : ℕ) = r ∧ (b : ℕ) = c) := fun h => hrc ⟨Fin.ext h.1, Fin.ext h.2⟩
  have hbv : b = i ∨ b = j → (b : ℕ) = c ∨ (b : ℕ) = c + 1 := fun h =>
    h.imp (fun h => by rw [h]) (fun h => by rw [h])
  rw [if_neg (show ¬((⟨r, hr⟩ : Fin N) = a ∧ i = b) from fun h => hrc ⟨h.1.symm, h.2.symm⟩),
    sub_zero]
  by_cases hm : (b : ℕ) + 1 < a ∧ (r < (a : ℕ) ∨ (a : ℕ) = r ∧ (b : ℕ) < c + 1)
  · rw [if_pos hm]
    refine (rowCol_apply_eq_zero hM (Fin.ne_of_val_ne (by simp only [i]; omega))
      (Fin.ne_of_val_ne (by simp only [j]; omega)) ?_ fun hb => ?_).symm
    · rw [hZa, if_pos (by omega)]
    · have := hbv hb
      exact ⟨by rw [hZa, if_pos (by simp only [i]; omega)],
        by rw [hZa, if_pos (by simp only [j]; omega)]⟩
  · rw [if_neg hm]
    refine rowCol_apply_congr hi hj (by rw [hZa, if_neg (by omega)]) fun hb => ?_
    have := hbv hb
    exact ⟨by rw [hZa, if_neg (by simp only [i]; omega)],
      by rw [hZa, if_neg (by simp only [j]; omega)]⟩

/-- The clearing after the last column of the row $r \ge 1$ is the clearing before the row
$r - 1$. -/
private theorem bottomUpMask_pred {r C : ℕ} (hr : C + 1 = r) (X : Matrix (Fin N) (Fin N) ℂ) :
    bottomUpMask r C X = bottomUpMask (r - 1) 0 X := by
  ext a b
  simp only [bottomUpMask, Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The unitary of the entries of the reduction gains, with the entry of a step, the exact
rotation of the pair the step reads, which the clearing does not change. -/
private theorem givensLog_append_reduceLastStepEntry (hM : StdModel u id M) {n : ℕ}
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r c : ℕ} (hc : c + 1 < r) (hr : r < n + 1)
    (es : List GivensEntry) :
    givensLog (n + 1) (es ++ [reduceLastStepEntry M r c X]) = givensLog (n + 1) es *
      (givens (⟨c, by omega⟩ : Fin (n + 1)) ⟨c + 1, by omega⟩
        (givensCoeffs (bottomUpMask r c X ⟨r, hr⟩ ⟨c + 1, by omega⟩)
          (-bottomUpMask r c X ⟨r, hr⟩ ⟨c, by omega⟩)).1
        (givensCoeffs (bottomUpMask r c X ⟨r, hr⟩ ⟨c + 1, by omega⟩)
          (-bottomUpMask r c X ⟨r, hr⟩ ⟨c, by omega⟩)).2)ᴴ := by
  have hn (x : ℝ) : M.neg x = -x := hM.neg x
  have e1 : bottomUpMask r c X ⟨r, hr⟩ ⟨c + 1, by omega⟩ = X ⟨r, hr⟩ ⟨c + 1, by omega⟩ := by
    simp only [bottomUpMask, Matrix.of_apply]; rw [if_neg (by omega)]
  have e2 : bottomUpMask r c X ⟨r, hr⟩ ⟨c, by omega⟩ = X ⟨r, hr⟩ ⟨c, by omega⟩ := by
    simp only [bottomUpMask, Matrix.of_apply]; rw [if_neg (by omega)]
  have hneg : (⟨M.neg (X ⟨r, hr⟩ ⟨c, by omega⟩).re, M.neg (X ⟨r, hr⟩ ⟨c, by omega⟩).im⟩ : ℂ) =
      -X ⟨r, hr⟩ ⟨c, by omega⟩ := by
    apply Complex.ext <;> simp [hn]
  rw [givensLog_append, e1, e2]
  congr 1
  simp only [givensLog, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  simp only [reduceLastStepEntry, dif_pos (show c + 1 < n + 1 ∧ r < n + 1 by omega), givensAt,
    dif_pos (show c + 1 < n + 1 by omega), hneg]

/-- The invariant of the reduction after $k$ steps: within $((1 + 61\boldsymbol{u})^k - 1)
\|\mathbf{A}\|_2$ of the unitary similarity of $\mathbf{A}$ by $\mathbf{Q}$, which fixes
$\mathbf{e}_{n+1}$. -/
private def HRBound (u : ℝ) {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : ℕ)
    (Y Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  HasOrthonormalCols Q ∧
    (∀ i, Q i (Fin.last n) = if i = Fin.last n then 1 else 0) ∧
    specNorm (Y - Qᴴ * A * Q) ≤ ((1 + 61 * u) ^ k - 1) * specNorm A

/-- One step of the reduction keeps the invariant, with one more step. -/
private theorem hrBound_step (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 576) {n : ℕ}
    {A X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k r c : ℕ} (hc : c + 1 < r) (hr : r < n + 1)
    {es : List GivensEntry} (h : HRBound u A k (bottomUpMask r c X) (givensLog (n + 1) es)) :
    HRBound u A (k + 1) (bottomUpMask r (c + 1) (reduceLastStepWord M r c X))
      (givensLog (n + 1) (es ++ [reduceLastStepEntry M r c X])) := by
  obtain ⟨hQ, hlast, hE⟩ := h
  set Q := givensLog (n + 1) es
  rw [givensLog_append_reduceLastStepEntry hM hc hr]
  rw [bottomUpMask_reduceLastStepWord hM hc hr]
  set Z := bottomUpMask r c X
  set i : Fin (n + 1) := ⟨c, by omega⟩
  set j : Fin (n + 1) := ⟨c + 1, by omega⟩
  set k' : Fin (n + 1) := ⟨r, hr⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  have hn (x : ℝ) : M.neg x = -x := hM.neg x
  have hneg : (⟨M.neg (Z k' i).re, M.neg (Z k' i).im⟩ : ℂ) = -Z k' i := by
    apply Complex.ext <;> simp [hn]
  have hd : c + 1 < n + 1 ∧ r < n + 1 := ⟨by omega, hr⟩
  have hstep : reduceLastStepWord M r c Z =
      machineRowRotation M i j (roundedGivensCoeffs M (Z k' j) (-Z k' i)).1
        (roundedGivensCoeffs M (Z k' j) (-Z k' i)).2
        (machineColRotation M i j (roundedGivensCoeffs M (Z k' j) (-Z k' i)).1
          (roundedGivensCoeffs M (Z k' j) (-Z k' i)).2 Z) := by
    simp only [reduceLastStepWord, dif_pos hd]
    rw [hneg]
  rw [hstep]
  set G := givens i j (givensCoeffs (Z k' j) (-Z k' i)).1 (givensCoeffs (Z k' j) (-Z k' i)).2
  set Y := machineRowRotation M i j (roundedGivensCoeffs M (Z k' j) (-Z k' i)).1
    (roundedGivensCoeffs M (Z k' j) (-Z k' i)).2
    (machineColRotation M i j (roundedGivensCoeffs M (Z k' j) (-Z k' i)).1
      (roundedGivensCoeffs M (Z k' j) (-Z k' i)).2 Z)
  have hG : HasOrthonormalCols G :=
    hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add _ _)
  have hW : specNorm (Y - G * Z * Gᴴ) ≤ 49 * u * specNorm Z :=
    ShiftedQR.specNorm_machineRowRotation_machineColRotation_sub_le hM hu hu' hij _ _ Z
  have hYk : ‖Y k' i‖ ≤ 12 * u * specNorm Z := by
    have e : Y k' i = machineColRotation M i j (roundedGivensCoeffs M (Z k' j) (-Z k' i)).1
        (roundedGivensCoeffs M (Z k' j) (-Z k' i)).2 Z k' i :=
      machineRowRotation_apply_of_ne (Fin.ne_of_val_ne (show r ≠ c by omega))
        (Fin.ne_of_val_ne (show r ≠ c + 1 by omega)) i
    rw [e]
    exact ShiftedQR.norm_machineColRotation_apply_left_le hM hu (by linarith) hij Z k'
  have hZ : specNorm Z ≤ specNorm A + ((1 + 61 * u) ^ k - 1) * specNorm A := by
    have e : Z = (Z - Qᴴ * A * Q) + Qᴴ * A * Q := by abel
    have := specNorm_add_le (Z - Qᴴ * A * Q) (Qᴴ * A * Q)
    rw [← e, hQ.specNorm_conjTranspose_mul_mul] at this
    linarith
  refine ⟨hasOrthonormalCols_iff.mpr ((hQ.conjTranspose_mul_mul _ _).trans
    hG.conjTranspose.conjTranspose_mul_self), fun a => ?_, ?_⟩
  · rw [conjTranspose_givens, mul_givens_apply_of_ne (Fin.ne_of_val_ne (by simp [i]; omega))
      (Fin.ne_of_val_ne (by simp [j]; omega))]
    exact hlast a
  have e : Y - Matrix.single k' i (Y k' i) - (Q * Gᴴ)ᴴ * A * (Q * Gᴴ) =
      (Y - G * Z * Gᴴ) - Matrix.single k' i (Y k' i) + G * (Z - Qᴴ * A * Q) * Gᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right, hG.specNorm_mul_left]
  have h3 := (specNorm_sub_le (Y - G * Z * Gᴴ) (Matrix.single k' i (Y k' i))).trans
    (add_le_add hW ((specNorm_single_le k' i _).trans hYk))
  have hP : (1 + 61 * u) ^ (k + 1) = (1 + 61 * u) ^ k * (1 + 61 * u) := pow_succ _ _
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_left hZ (by positivity : (0 : ℝ) ≤ 61 * u)]

/-- The steps of one row of the reduction keep the invariant. -/
private theorem hrBound_row (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 576) {n : ℕ}
    {A X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {i k : ℕ} (hi : i < n + 1 - 2)
    {es : List GivensEntry} (h : HRBound u A k (bottomUpMask (n - i) 0 X) (givensLog (n + 1) es)) :
    ∀ C ≤ n + 1 - 2 - i, HRBound u A (k + C) (bottomUpMask (n - i) C (hrRound M i X C).1)
      (givensLog (n + 1) (es ++ (hrRound M i X C).2))
  | 0, _ => by simpa [hrRound] using h
  | C + 1, hC => by
    rw [hrRound_succ]
    have := hrBound_step (M := M) hM hu hu' (c := C) (r := n - i) (by omega) (by omega)
      (hrBound_row hM hu hu' hi h C (by omega))
    simpa [hrRoundStep, ← add_assoc] using this

/-- The pairs (round, column) of the steps of the first $I$ rows of the reduction. -/
private def hrSteps (N I : ℕ) : List (ℕ × ℕ) :=
  (List.range I).flatMap fun i => (List.range (N - 2 - i)).map fun c => (i, c)

/-- Twice the number of steps of the first $I$ rows. -/
private theorem two_mul_length_hrSteps (N : ℕ) :
    ∀ I ≤ N - 2, 2 * (hrSteps N I).length + (N - 2 - I) * (N - 2 - I + 1) =
      (N - 2) * (N - 2 + 1)
  | 0, _ => by simp [hrSteps]
  | I + 1, hI => by
    have ih := two_mul_length_hrSteps N I (by omega)
    have hl : (hrSteps N (I + 1)).length = (hrSteps N I).length + (N - 2 - I) := by
      simp [hrSteps, List.range_succ, List.flatMap_append]
    obtain ⟨s, hs⟩ : ∃ s, N - 2 - I = s + 1 := ⟨N - 2 - I - 1, by omega⟩
    rw [hl, show N - 2 - (I + 1) = s by omega, hs]
    rw [hs] at ih
    nlinarith

/-- The rows of the reduction keep the invariant. -/
private theorem hrBound_rows {n : ℕ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : 3 ≤ n + 1 → u ≤ 1 / 576) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∀ I ≤ n + 1 - 2, HRBound u A (hrSteps (n + 1) I).length (bottomUpMask (n - I) 0
      ((List.range I).foldl (hrOuter M) (A, [])).1)
      (givensLog (n + 1) ((List.range I).foldl (hrOuter M) (A, [])).2.flatten)
  | 0, _ => by
    refine ⟨hasOrthonormalCols_one, fun a => by simp [Matrix.one_apply], ?_⟩
    have : bottomUpMask n 0 A = A := by
      ext a b
      simp only [bottomUpMask, Matrix.of_apply]
      rw [if_neg (by omega)]
    simp [hrSteps, this]
  | I + 1, hI => by
    have ih := hrBound_rows hM hu hu' A I (by omega)
    have h := hrBound_row hM hu (hu' (by omega)) (i := I) (by omega) ih (n + 1 - 2 - I) le_rfl
    rw [bottomUpMask_pred (show n + 1 - 2 - I + 1 = n - I by omega),
      show n - I - 1 = n - (I + 1) by omega] at h
    simpa [hrSteps, List.range_succ, List.flatMap_append, List.foldl_append, add_comm,
      hrOuter] using h

/-- $K$ steps of relative error $61\boldsymbol{u}$ grow to at most $50(n + 1)^2\boldsymbol{u}$
when $2K \le (n + 1)^2$ and $100(n + 1)^2\boldsymbol{u} \le 1$. -/
private theorem hrGrowth_le {u : ℝ} {n K : ℕ} (hu : 0 ≤ u)
    (hK : 2 * (K : ℝ) ≤ ((n : ℝ) + 1) ^ 2) (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1) :
    (1 + 61 * u) ^ K - 1 ≤ 50 * ((n : ℝ) + 1) ^ 2 * u := by
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hx1 : 61 * u ≤ 1 := by nlinarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKx : (K : ℝ) * (61 * u) ≤ 61 / 2 * (((n : ℝ) + 1) ^ 2 * u) := by nlinarith
  have hB : 1 + K * (-(61 * u)) ≤ (1 + -(61 * u)) ^ K := one_add_mul_le_pow (by linarith) K
  have hAB : (1 + 61 * u) ^ K * (1 + -(61 * u)) ^ K ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 + 61 * u) ^ K := by positivity
  have h1 : (1 + 61 * u) ^ K * (1 - K * (61 * u)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hB hA
    nlinarith
  have hP : (1 + 61 * u) ^ K ≤ 200 / 139 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hP (mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ 61 * u))]

end BackwardError

/-- **The bottom-up Hessenberg reduction is backward stable by the unitary of its log**
([BanksGarzaVargasSrivastava2025, Definition 5.1], proved for rounded rotations, with the unitary
named): on a machine with the standard model at the unit roundoff $\boldsymbol{u}$,
$M.\mathrm{lit}(0) = 0$ and $100(n + 1)^2\boldsymbol{u} \le 1$, the stored matrix
$\widehat{\mathbf{H}}$ of a complex $\mathbf{A}$ of order $n + 1$ is upper Hessenberg, the exact
unitary $\mathbf{Q}$ of the recorded rotations (`NLAlib.givensLog` of the entries
`NLAlib.hessenbergReduceLastSlots`, the exact Givens rotations of the recorded pairs) fixes
$\mathbf{e}_{n+1}$, and $\widehat{\mathbf{H}} = \mathbf{Q}^{\mathsf H}(\mathbf{A} +
\mathbf{E})\mathbf{Q}$ with $\|\mathbf{E}\|_2 \le 50(n + 1)^2\boldsymbol{u}\|\mathbf{A}\|_2$. -/
theorem hessenbergReduceLast_isPerturbedUnitarySimilarBy {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hzero : M.lit 0 = 0) {n : ℕ} (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    IsUpperHessenberg (hessenbergReduceLastWord M A) ∧
      (∀ i, givensLog (n + 1) (hessenbergReduceLastSlots M A).flatten i (Fin.last n) =
        if i = Fin.last n then 1 else 0) ∧
      IsPerturbedUnitarySimilarBy (givensLog (n + 1) (hessenbergReduceLastSlots M A).flatten) A
        (hessenbergReduceLastWord M A) (50 * ((n : ℝ) + 1) ^ 2 * u * specNorm A) := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hz : (⟨M.lit 0, M.lit 0⟩ : ℂ) = 0 := by rw [hzero]; rfl
  refine ⟨fun a b hab => by simp [hessenbergReduceLastWord, hab, hz], ?_⟩
  have hu' : 3 ≤ n + 1 → u ≤ 1 / 576 := fun h3 => by
    have : (3 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h3
    nlinarith
  obtain ⟨hQ, hlast, hE⟩ := hrBound_rows (M := M) hM hu hu' A (n + 1 - 2) le_rfl
  refine ⟨hlast, IsPerturbedUnitarySimilarBy.of_specNorm_sub_le hQ ?_⟩
  have hW : hessenbergReduceLastWord M A = bottomUpMask (n - (n + 1 - 2)) 0
      ((List.range (n + 1 - 2)).foldl (hrOuter M) (A, [])).1 := by
    ext a b
    simp only [hessenbergReduceLastWord, bottomUpMask, hrOuter_fst, Matrix.of_apply, hz]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [hW]
  refine hE.trans (mul_le_mul_of_nonneg_right (hrGrowth_le hu ?_ hnu) (specNorm_nonneg A))
  have hl := two_mul_length_hrSteps (n + 1) (n + 1 - 2) le_rfl
  rw [Nat.sub_self, zero_mul, add_zero] at hl
  have : (n + 1 - 2) * (n + 1 - 2 + 1) ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * (hrSteps (n + 1) (n + 1 - 2)).length ≤ (n + 1) ^ 2 := by rw [sq]; omega
  exact_mod_cast h2

/-- **The bottom-up Hessenberg reduction is backward stable and fixes $\mathbf{e}_N$**
([BanksGarzaVargasSrivastava2025, Definition 5.1], proved for rounded rotations): on a machine
with the standard model at the unit roundoff $\boldsymbol{u}$, $M.\mathrm{lit}(0) = 0$ and
$100(n + 1)^2\boldsymbol{u} \le 1$, the stored matrix $\widehat{\mathbf{H}}$ of a complex
$\mathbf{A}$ of order $n + 1$ is upper Hessenberg and there is a unitary $\mathbf{Q}$ with
$\mathbf{Q}\mathbf{e}_{n+1} = \mathbf{e}_{n+1}$ and
$$\|\widehat{\mathbf{H}} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le
  50(n + 1)^2\boldsymbol{u}\,\|\mathbf{A}\|_2\,.$$ -/
theorem hessenbergReduceLast_isPerturbedUnitarySimilar {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hzero : M.lit 0 = 0) {n : ℕ} (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    IsUpperHessenberg (hessenbergReduceLastWord M A) ∧
      ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
        (∀ i, Q i (Fin.last n) = if i = Fin.last n then 1 else 0) ∧
        specNorm (hessenbergReduceLastWord M A - Qᴴ * A * Q) ≤
          50 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  obtain ⟨hH, hlast, hV, E, hE, he⟩ :=
    hessenbergReduceLast_isPerturbedUnitarySimilarBy hM hzero hnu A
  refine ⟨hH, _, hV, hlast, ?_⟩
  rw [he, Matrix.mul_add, Matrix.add_mul, add_sub_cancel_left, hV.specNorm_conjTranspose_mul_mul]
  exact hE

/-- `NLAlib.hessenbergReduceLast` terminates on every tape and every stored matrix: its loops are
counted and every operation succeeds on stored operands; the log gains its $N - 2$ slots. -/
theorem hessenbergReduceLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a lg : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hN : N ≤ nmax + 1) {ns w : ℕ}
    {L : List (Option (List GivensEntry))} (hlog : HoldsSlottedLog lg ns w L [] m.store)
    (hj : L.length + (N - 2) ≤ ns) (hw : N - 2 ≤ w) (hl : m.Live [a, lg])
    (hA : HoldsMatrix a A m.store)
    (hd : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body
      (Env.frame [N, w, L.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a A' m'.store ∧
        HoldsSlottedLog lg ns w (L ++ (hessenbergReduceLastSlots M A).map some) [] m'.store) m :=
  (hessenbergReduceLast_writes_word hS hC hL hNat h1 hN hlog hj hw hl hA hd).mono le_rfl
    fun _ _ h => ⟨_, h.2⟩

end Theorems

/-- An entry of the reduction is in the order or the zero fill. -/
theorem reduceLastStepEntry_plane (M : Machine ℝ) {N : ℕ} (r c : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    (reduceLastStepEntry M r c X).1 + 1 < N ∨ reduceLastStepEntry M r c X = (0, 0, 0) := by
  unfold reduceLastStepEntry
  split_ifs with h
  · exact Or.inl h.1
  · exact Or.inr rfl

private theorem hrRound_plane (M : Machine ℝ) {N : ℕ} (i : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    ∀ C, ∀ e ∈ (hrRound M i X C).2, e.1 + 1 < N ∨ e = (0, 0, 0)
  | 0 => by simp [hrRound]
  | C + 1 => by
    rw [hrRound_succ]
    intro e he
    simp only [hrRoundStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hrRound_plane M i X C e he
    · exact reduceLastStepEntry_plane M _ _ _

/-- Every recorded entry of the reduction is in the order or the zero fill. -/
theorem hessenbergReduceLastSlots_plane (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ∀ es ∈ hessenbergReduceLastSlots M A, ∀ e ∈ es, e.1 + 1 < N ∨ e = (0, 0, 0) := by
  rw [hessenbergReduceLastSlots_eq]
  suffices h : ∀ I, ∀ es ∈ ((List.range I).foldl (hrOuter M) (A, [])).2, ∀ e ∈ es,
      e.1 + 1 < N ∨ e = (0, 0, 0) from h _
  intro I
  induction I with
  | zero => simp
  | succ I ih =>
    rw [List.range_succ, List.foldl_append]
    intro es hes
    simp only [List.foldl_cons, List.foldl_nil, hrOuter, List.mem_append,
      List.mem_singleton] at hes
    rcases hes with hes | rfl
    · exact ih es hes
    · exact hrRound_plane M _ _ _

/-- The reduction records $N - 2$ slots. -/
theorem length_hessenbergReduceLastSlots (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) : (hessenbergReduceLastSlots M A).length = N - 2 := by
  rw [hessenbergReduceLastSlots_eq, hrOuter_length]

/-- The tracked relation of the reduction with the accumulated unitary, from the replay bound on
the closed log of the reduction. -/
private theorem hessenbergReduceQ_tracked {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {nmax : ℕ} (hnu : 200 * (nmax : ℝ) ^ 2 * u ≤ 1) {N : ℕ} (hN : N ≤ nmax)
    (A U U' : Matrix (Fin N) (Fin N) ℂ)
    (h : specNorm (U' - U * embedBlock 0 (givensLog N (slotEntries (N - 1)
      ((hessenbergReduceLastSlots M A).map some ++
        List.replicate (N - ((hessenbergReduceLastSlots M A).map some).length) none)))) ≤
      ((1 + 24 * u) ^ (N * (N - 1)) - 1) * specNorm U) :
    IsUpperHessenberg (hessenbergReduceLastWord M A) ∧
      IsTrackedUnitarySimilar (27 * (nmax : ℝ) ^ 2 * u) (50 * (nmax : ℝ) ^ 2 * u * specNorm A)
        U A U' (hessenbergReduceLastWord M A) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hzero : M.lit 0 = 0 := by simpa using hM.lit 0
  have hN' : (N : ℝ) ≤ nmax := by exact_mod_cast hN
  rw [slotEntries_append_replicate_none, givensLog_slotEntries_map_some, embedBlock_zero_self]
    at h
  cases N with
  | zero =>
    refine ⟨fun i => i.elim0, 1, ⟨hasOrthonormalCols_one, 0, by rw [specNorm_zero]; positivity,
      Subsingleton.elim _ _⟩, ?_⟩
    rw [Subsingleton.elim (U' - U * 1) 0, specNorm_zero]
    positivity
  | succ n =>
    have hn : ((n : ℝ) + 1) ^ 2 ≤ (nmax : ℝ) ^ 2 := by push_cast at hN'; gcongr
    obtain ⟨hH, -, hBy⟩ := hessenbergReduceLast_isPerturbedUnitarySimilarBy hM hzero
      (by nlinarith) A
    refine ⟨hH, _, hBy.mono (by gcongr), h.trans (mul_le_mul_of_nonneg_right ?_
      (specNorm_nonneg U))⟩
    have hR : ((((n + 1) * (n + 1 - 1) : ℕ)) : ℝ) ≤ (nmax : ℝ) ^ 2 := by
      push_cast [Nat.add_sub_cancel]
      nlinarith
    refine (one_add_mul_pow_sub_one_le hu0 (by nlinarith)).trans ?_
    nlinarith

section Accumulate

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The bottom-up Hessenberg reduction with the accumulated unitary**: open a slotted log of $N$
slots of $N - 1$ entries (`NLAlib.slottedLogOpen`), reduce `A` recording the rotations
(`NLAlib.hessenbergReduceLast`), then replay them on the columns of `U`
(`NLAlib.givensReplayColumns`), so that `U` becomes $\mathbf{U}\mathbf{V}$ up to rounding with
$\mathbf{V}$ the unitary of the reduction. The interface is `[N] (A, U) → (A, U)`; the log is
scoped.
Algorithm: hessenberg-reduction -/
def hessenbergReduceQ : Impl O Q := opsImpl% [N] (A, U) → (A, U) {
  let Lg ← alloc (N * (1 + 5 * (N - 1)));
  run (slottedLogOpen (O := O) (Q := Q)).body [N, N - 1] (Lg);
  run (hessenbergReduceLast (O := O) (Q := Q)).body [N, N - 1, 0] (A, A, Lg);
  run (givensReplayColumns (O := O) (Q := Q)).body [N, 0, 0, N, N, N - 1] (Lg, U, U)
}

/-- **The reduction with the accumulated unitary is a Hessenberg reducer**: on a scalar machine
with the standard model at $\boldsymbol{u}$, exact comparisons and `toNat`, index literals and
exact natural literals up to $N_{\max} \ge 1$, with $200N_{\max}^2\boldsymbol{u} \le 1$,
`NLAlib.hessenbergReduceQ` meets `NLAlib.Schur.HessenbergReducerContract` on the orders
$N \le N_{\max}$ with the relative accumulator error $27N_{\max}^2\boldsymbol{u}$ (the replay of
$N(N - 1)$ logged rotations, `NLAlib.givensReplayColumns_specNorm_sub_le` and
`NLAlib.one_add_mul_pow_sub_one_le`) and the backward error
$50N_{\max}^2\boldsymbol{u}\|\mathbf{A}\|_2$
(`NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilarBy`). -/
theorem hessenbergReduceQ_hessenbergReducerContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    (hnu : 200 * (nmax : ℝ) ^ 2 * u ≤ 1) :
    Schur.HessenbergReducerContract (27 * (nmax : ℝ) ^ 2 * u) (50 * (nmax : ℝ) ^ 2 * u) nmax
      (hessenbergReduceQ (O := O) (Q := Q)) I := by
  intro N a uo τ μ A U hN ⟨hA, hU⟩ hl hd
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hn1 : (1 : ℝ) ≤ nmax := by exact_mod_cast h1
  have hu : u ≤ 1 / 100 := by nlinarith
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  set Sl := hessenbergReduceLastSlots M A
  unfold hessenbergReduceQ
  change Writes .total I τ (Stmt.allocs [_] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [N * (1 + 5 * (N - 1))]) rfl
    (fun hBelow ⟨U', H, ⟨h₁, h₂⟩, h₃⟩ =>
      ⟨U', H, ⟨h₁.of_below hBelow hal, h₂.of_below hBelow hul⟩, h₃⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hLg : s₁.len Lc = N * (1 + 5 * (N - 1)) := by simpa using hlens 0 (by simp)
  have hA₀ := hA.of_below hBelow hal
  have hU₀ := hU.of_below hBelow hul
  have hlive : ∀ {s : Store ℝ}, s.length = Lc + 1 → ∀ {p : ℕ},
      (⟨s, p⟩ : Mem ℝ).Live [a, uo, (Lc, 0)] := fun h => by simp [Mem.Live, h]; omega
  have hFp : Store.inBlock Lc 0 (N * (1 + 5 * (N - 1))) ≤
      Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)) ⊔
        Fp.above Lc := fun b z h => Or.inr (h.1 ▸ le_rfl)
  refine (slottedLogOpen_writes (τ := τ) (μ := ⟨s₁, μ.pos⟩) (ns := N) (w := N - 1) (lg := (Lc, 0))
    hS hM (by simp [Mem.Live]; omega) (by simp [hLg])).frame_seq_le rfl rfl
    (by simp [Mem.Live]; omega) hFp ?_
  rintro μ₁ hfr₁ ⟨hp₁, hlog₁⟩
  have hdl : ∀ {b o n}, b < Lc → Fp.Disj (Store.inBlock b o n)
      (Store.inBlock Lc 0 (N * (1 + 5 * (N - 1)))) := fun hb => Fp.disj_inBlock_of_ne (by omega)
  refine (hessenbergReduceLast_writes_word (τ := τ) (m := μ₁) (L := []) hS hC hL hNat h1
    (by omega) hlog₁ (by simp) (by omega) (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (hA₀.of_eqOff hfr₁ (hdl hal).symm) (hdl hal)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (sup_le (le_sup_left.trans le_sup_left) hFp) ?_
  rintro μ₂ hfr₂ ⟨hp₂, hH₂, hlog₂⟩
  have hlog₃ := hlog₂.close
  have hU₂ : HoldsMatrix uo U μ₂.store := (hU₀.of_eqOff hfr₁ (hdl hul).symm).of_eqOff hfr₂
    (Fp.disj_sup_left.mpr ⟨hd, (hdl hul).symm⟩)
  have hpl : ∀ e ∈ slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none), e.1 + 1 < N ∨ e = (0, 0, 0) := by
    intro e he
    rw [List.nil_append, slotEntries_append_replicate_none] at he
    simp only [slotEntries, List.mem_flatMap, List.mem_map] at he
    obtain ⟨_, ⟨es, hes, rfl⟩, he⟩ := he
    simp only [Option.map_some, Option.getD_some, padEntries, List.mem_append,
      List.mem_replicate] at he
    rcases he with he | ⟨-, rfl⟩
    · exact hessenbergReduceLastSlots_plane M A es hes e he
    · exact Or.inr rfl
  have hlo : slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none) = [] ∨ 0 + 1 < N := by
    by_cases h2 : 2 ≤ N
    · exact Or.inr (by omega)
    · refine Or.inl ?_
      have : Sl = [] := List.eq_nil_of_length_eq_zero (by
        rw [length_hessenbergReduceLastSlots]; omega)
      rw [this]
      simp [slotEntries]
  refine ((givensReplayColumns_specNorm_sub_le (τ := τ) (μ := μ₂) (lo := 0) (d := N) hS hM hu0
    hu hQ hC (by omega) hpl hlo hlog₃ (by simp [Sl, length_hessenbergReduceLastSlots]) hU₂
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega) (hdl hul).symm).in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega)).mono
    (le_sup_right.trans le_sup_left) ?_
  rintro μ₃ hfr₃ ⟨U', hU', hb⟩
  obtain ⟨hH, ht⟩ := hessenbergReduceQ_tracked hM hnu hN A U U' (by simpa using hb)
  exact ⟨U', _, ⟨hH₂.of_eqOff hfr₃ hd.symm, hU'⟩, hH, ht⟩

end Accumulate

end NLAlib
