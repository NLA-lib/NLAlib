/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Backward
public import NLAlib.Eigensolvers.ShiftedQR.Coefficients
public import NLAlib.Eigensolvers.ShiftedQR.Hessenberg
public import NLAlib.Eigensolvers.ShiftedQR.RotationLoops
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Ops.Logic.Functional

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
  `[N] (A) → (A)`.
* `NLAlib.hessenbergReduceLastWord`: the matrix it stores on a machine.

## Main results

* `NLAlib.clearBelowSubdiagonal_writes_word`: the deletion below the subdiagonal on any machine.
* `NLAlib.reduceLastStep_writes_word`, `NLAlib.hessenbergReduceLast_writes_word`: the program
  stores the machine evaluation.
* `NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilar`: backward stability, with the last
  coordinate vector fixed.
* `NLAlib.hessenbergReduceLast_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops ShiftedQR

section Clear

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One complex entry set by `NLAlib.ShiftedQR.clearComplexEntry`: the two words are the
literal $0$ of the machine, whatever it is. -/
theorem clearComplexEntry_writes_lit {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {z : ℕ × ℕ}
    (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ (clearComplexEntry (Op := Op) (Tst := Tst)).body (Env.frame [] [z])
      (Store.inBlock z.1 z.2 2)
      (fun m' => (∀ u : Fin 2, m'.store.get z.1 (z.2 + u) =
        some ((EntryCodec.pair ℝ).words (M.lit 0, M.lit 0) u)) ∧
        m'.pos = m.pos) m := by
  apply Hermitian.writes_pair_of_wp (v := (M.lit 0, M.lit 0)) ?_ hz
  refine wp_seq (wp_call_const (hS (.lit 0)) rfl rfl rfl trivial
    (by simpa using (show z.2 < m.store.len z.1 by omega)) ?_)
  refine wp_call_const (hS (.lit 0)) rfl rfl rfl trivial ?_ ?_
  · simpa only [Mem.store_upd, Store.len_upd] using
      (show z.2 + 1 < m.store.len z.1 by omega)
  · rfl

/-- The entries below the subdiagonal written by `NLAlib.ShiftedQR.clearBelowSubdiagonal` are
the pair of the literal $0$ of the machine, and only they are written. -/
theorem clearBelowSubdiagonal_writes_region {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a : ℕ × ℕ}
    (hl : m.Live [a]) (ha : 0 < n → a.2 + 2 * (n * n) ≤ m.store.len a.1) :
    Writes .total I τ (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [a])
      ((EntryCodec.pair ℝ).regionFp a.1 a.2 n (fun j i => j * n + i) (fun i => i - 1))
      (fun m' => m'.store.HoldsEntryRegion (EntryCodec.pair ℝ) a.1 a.2 n
        (fun j i => j * n + i) (fun i => i - 1) (fun _ _ => (M.lit 0, M.lit 0)) ∧
        m'.pos = m.pos) m := by
  refine writes_fillEntryRegion (EntryCodec.pair ℝ) a.1 a.2 n
    (fun j i => j * n + i) (fun i => i - 1) ?_ rfl (fun _ => rfl)
    (fun _ _ => (M.lit 0, M.lit 0)) (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hp' : p.2 < n := hp.1
    have hq' : q.2 < n := hq.1
    have hd := congrArg (· / n) he
    have hm := congrArg (· % n) he
    simp only [Idx.div_add hp', Idx.div_add hq'] at hd
    simp only [Idx.mod_add hp', Idx.mod_add hq'] at hm
    exact Prod.ext hd hm
  · intro i hi j hj μ hfr hp
    have hflat : j * n + i < n * n := Idx.add_lt_mul (by omega) hi
    have hmul := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hflat)
    have hroom : a.2 + 2 * (j * n + i) + 2 ≤ μ.store.len a.1 := by
      have := ha (by omega)
      rw [hfr.len_eq]
      omega
    refine (writes_frame rfl rfl ?_
      (clearComplexEntry_writes_lit (m := μ) (z := (a.1, a.2 + 2 * (j * n + i)))
        hS hroom)).mono le_rfl ?_
    · simpa [Mem.Live, hfr.length_eq] using hl
    · intro μ' _ h
      exact ⟨h.1, h.2.trans hp⟩

/-- The deletion below the subdiagonal on any machine: `NLAlib.ShiftedQR.clearBelowSubdiagonal`
replaces every entry $(i, j)$ with $j + 1 < i$ by the pair of the literal $0$ of the machine and
keeps every other entry; the tape position is unchanged. With an exact zero literal this is
`NLAlib.ShiftedQR.clearBelowSubdiagonal_writes`. -/
theorem clearBelowSubdiagonal_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [a]) (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (Matrix.of fun i j =>
        if (j : ℕ) + 1 < i then (⟨M.lit 0, M.lit 0⟩ : ℂ) else A i j) m'.store) m := by
  let C := EntryCodec.pair ℝ
  let region := C.regionFp a.1 a.2 n (fun j i => j * n + i) (fun i => i - 1)
  have hsub : region ≤ Store.inBlock a.1 a.2 (2 * (n * n)) :=
    C.regionFp_le_inBlock a.1 a.2 n (n * n) (fun j i => j * n + i)
      (fun i => i - 1) (fun i hi j hj => Idx.add_lt_mul (by omega) hi)
  refine (clearBelowSubdiagonal_writes_region hS hl fun hn =>
    Store.le_len_of_readBlock hA (by positivity)).mono hsub fun m' hfr h => ?_
  refine ⟨h.2, HoldsMatrix.of_get ?_ ?_⟩
  all_goals
    intro i j
    by_cases hij : (j : ℕ) + 1 < (i : ℕ)
    · have hentry := h.1 i i.isLt j (by change (j : ℕ) < (i : ℕ) - 1; omega)
      first
      | simpa [hij] using hentry 0
      | simpa [hij, Nat.add_assoc] using hentry 1
    · have hdis : Fp.Disj region (C.entryBlock a.1 a.2 (j * n + i)) := by
        rintro b x ⟨c, r, hr | ⟨_, hc⟩, hx⟩ hentry
        · have hcr : c < r - 1 := hr.2
          have hne : c * n + r ≠ j * n + i := by
            intro he
            have hd := congrArg (· / n) he
            have hm := congrArg (· % n) he
            simp only [Idx.div_add hr.1, Idx.div_add i.isLt] at hd
            simp only [Idx.mod_add hr.1, Idx.mod_add i.isLt] at hm
            omega
          exact C.disj_entryBlock_of_ne hne b x hx hentry
        · omega
      have hr := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hdis (hA.read_entry i j)
      first
      | simpa [hij] using (Store.get_of_readBlock hr (j := 0) (by norm_num) (0 : ℝ))
      | simpa [hij, Nat.add_assoc] using
          (Store.get_of_readBlock hr (j := 1) (by norm_num) (0 : ℝ))

end Clear

section Program

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- **One step of the bottom-up reduction** at the row $r$ and the columns $c, c + 1$: the pair
$(\mathbf{A}_{r, c+1}, -\mathbf{A}_{r, c})$ into `Uv`, its rounded Givens coefficients into
`Cf` (`NLAlib.ShiftedQR.coefficients`), then the rotation of the columns $c, c + 1$ and of the
rows $c, c + 1$ of `A` in place. The interface is `[N, r, c] (A) → (A, Cf, Uv)`.
Algorithm: hessenberg-reduction -/
def reduceLastStep : Impl O Q := opsImpl% [N, r, c] (A) → (A, Cf, Uv) {
  call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + r)]) → (Uv);
  call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + r) + 1]) → (Uv[1]);
  call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + r)]) → (Uv[2]);
  call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + r) + 1]) → (Uv[3]);
  run (coefficients (Op := O) (Tst := Q)).body [] (Uv, Uv[2], Cf, Cf[2]);
  run (rotateColumns (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A);
  run (rotateRows (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A)
}

/-- **The bottom-up Hessenberg reduction** ([BanksGarzaVargasSrivastava2025, Definition 5.1],
as a program): for the rows $r = N - 1, \dots, 2$ (round $i$ has $r = N - 1 - i$) and the columns
$c = 0, \dots, r - 2$, the step `NLAlib.reduceLastStep`: the Givens coefficients of the pair
$(\mathbf{A}_{r, c+1}, -\mathbf{A}_{r, c})$, then the rotation of the columns $c, c + 1$ (which
zeros $\mathbf{A}_{r,c}$) and of the rows $c, c + 1$; finally the entries below the subdiagonal
are written as zeros. The interface is `[N] (A) → (A)`; the coefficients and the pair are
scoped scratch.
Algorithm: hessenberg-reduction -/
def hessenbergReduceLast : Impl O Q := opsImpl% [N] (A) → (A) {
  let Cf ← alloc 4;
  let Uv ← alloc 4;
  for i < N - 2 {
    for c < N - 2 - i {
      run (reduceLastStep (O := O) (Q := Q)).body [N, N - 1 - i, c] (A, A, Cf, Uv)
    }
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

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- One step of the reduction (`NLAlib.reduceLastStep`) on any scalar machine with exact
comparisons stores the machine step `NLAlib.reduceLastStepWord` in place, for $c + 1 < N$ and
$r < N$, and writes only the matrix and its two scratch blocks, in buffers of their own. -/
theorem reduceLastStep_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N r c : ℕ} (hc : c + 1 < N) (hr : r < N)
    {a cf uv : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : HoldsMatrix a A m.store)
    (hcf : cf.2 + 4 ≤ m.store.len cf.1) (huv : uv.2 + 4 ≤ m.store.len uv.1)
    (hac : a.1 ≠ cf.1) (hau : a.1 ≠ uv.1) :
    Writes .total I τ (reduceLastStep (O := O) (Q := Q)).body (Env.frame [N, r, c] [a, a, cf, uv])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock cf.1 cf.2 4 ⊔
        Store.inBlock uv.1 uv.2 4)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (reduceLastStepWord M r c A) m'.store) m := by
  let i : Fin N := ⟨c, by omega⟩
  let j : Fin N := ⟨c + 1, hc⟩
  let k : Fin N := ⟨r, hr⟩
  let s : ℕ × ℕ := (cf.1, cf.2 + 2)
  have hal : a.1 < m.store.length := Store.lt_length_of_get (hA.get_re k i)
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hul : uv.1 < m.store.length := Store.lt_length_of_lt_len (by omega : uv.2 < _)
  have hU : ∀ t, Fp.Disj (Store.inBlock uv.1 (uv.2 + t) 1)
      (Store.inBlock a.1 a.2 (2 * (N * N))) := fun _ => Fp.disj_inBlock_of_ne hau.symm
  have hUle : ∀ t < 4, Store.inBlock uv.1 (uv.2 + t) 1 ≤ Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
      Store.inBlock cf.1 cf.2 4 ⊔ Store.inBlock uv.1 uv.2 4 := fun t ht =>
    (Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_right
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
  have hlen₄ : m₄.store.length = m.store.length := by
    have := hfr₁.length_eq; have := hfr₂.length_eq; have := hfr₃.length_eq
    have := hfr₄.length_eq; omega
  have hcf₄ : cf.2 + 4 ≤ m₄.store.len cf.1 := by
    rw [hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hcf
  have hcsub : Store.inBlock cf.1 cf.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have hssub : Store.inBlock s.1 s.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock (by dsimp [s]; omega) (by dsimp [s]; omega)
  have hcf4 : Fp.blocks [cf, s] [2, 2] ≤ Store.inBlock cf.1 cf.2 4 := by
    simpa only [Fp.blocks, sup_bot_eq] using sup_le hcsub hssub
  have hcfG : Fp.blocks [cf, s] [2, 2] ≤ Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
      Store.inBlock cf.1 cf.2 4 ⊔ Store.inBlock uv.1 uv.2 4 :=
    hcf4.trans (le_sup_right.trans le_sup_left)
  refine (coefficients_writes_word (τ := τ) (m := m₄) (a := uv) (b := (uv.1, uv.2 + 2))
    (c := cf) (s := s) (u := A k j) (v := ⟨M.neg (A k i).re, M.neg (A k i).im⟩) hS hC
    (Fp.disj_inBlock_of_le le_rfl) hu₀' hu₁' hv₀' hv₁ (by omega)
    (by dsimp [s]; omega)).frame_seq_le rfl rfl (by simp [Mem.Live, hlen₄, s, hcl, hul]) hcfG ?_
  rintro m₅ hfr₅ ⟨hp₅, hcs₅⟩
  have hc₅ := (Mem.readBlocks_cons_iff.mp hcs₅).1
  have hs₅ := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs₅).2).1
  have hAC : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne hac
  have hA₅ := hA₄.of_eqOff hfr₅ (hAC.symm.mono hcf4 le_rfl)
  refine (rotateColumns_writes_word (τ := τ) (k := c) hS hc hA₅ hc₅ hs₅ (hAC.mono le_rfl hcsub)
    (hAC.mono le_rfl hssub)).frame_seq_le rfl rfl
    (by have := hfr₅.length_eq; simp [Mem.Live, s]; omega) (le_sup_left.trans le_sup_left) ?_
  rintro m₆ hfr₆ ⟨hp₆, hA₆⟩
  have hc₆ := hfr₆.keep (Store.readsOnly_readBlock _ _ _ _) (hAC.mono le_rfl hcsub) hc₅
  have hs₆ := hfr₆.keep (Store.readsOnly_readBlock _ _ _ _) (hAC.mono le_rfl hssub) hs₅
  refine ((rotateRows_writes_word (τ := τ) (k := c) hS hc hA₆ hc₆ hs₆ (hAC.mono le_rfl hcsub)
    (hAC.mono le_rfl hssub)).in_frame rfl rfl
    (by have := hfr₅.length_eq; have := hfr₆.length_eq; simp [Mem.Live, s]; omega)).mono
    (le_sup_left.trans le_sup_left) ?_
  rintro m₇ - ⟨hp₇, hA₇⟩
  refine ⟨hp₇.trans (hp₆.trans (hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))))), ?_⟩
  unfold reduceLastStepWord
  rw [dif_pos ⟨hc, hr⟩]
  exact hA₇

/-- `NLAlib.hessenbergReduceLast` on any scalar machine with exact comparisons stores the machine
evaluation `NLAlib.hessenbergReduceLastWord` of the matrix in place, writes only the matrix, and
reads no tape. -/
theorem hessenbergReduceLast_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (hessenbergReduceLastWord M A) m'.store) m := by
  have hal : a.1 < m.store.length := hl a (by simp)
  set step : Matrix (Fin N) (Fin N) ℂ → ℕ × ℕ → Matrix (Fin N) (Fin N) ℂ :=
    fun X ic => reduceLastStepWord M (N - 1 - ic.1) ic.2 X with hstep
  unfold hessenbergReduceLast
  change Writes .total I τ (Stmt.allocs [.const 4, .const 4] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [4, 4]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hal⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := m.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  set G := Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock L 0 4 ⊔
    Store.inBlock (L + 1) 0 4 with hG
  set St : List (ℕ × ℕ) → Mem ℝ → Prop := fun ps μ => μ.pos = m.pos ∧
    μ.store.length = L + 2 ∧ μ.store.len L = 4 ∧ μ.store.len (L + 1) = 4 ∧
    HoldsMatrix a (ps.foldl step A) μ.store with hSt
  have hround : ∀ (ps : List (ℕ × ℕ)) (i c : ℕ), i < N - 2 → c < N - 2 - i → ∀ μ, St ps μ →
      Writes .total I τ (reduceLastStep (O := O) (Q := Q)).body
        (Env.frame [N, N - 1 - i, c] [a, a, (L, 0), (L + 1, 0)]) G
        (St (ps ++ [(i, c)])) μ := by
    rintro ps i c hi hc μ ⟨hp, hlen', hL0, hL1, hW⟩
    refine (reduceLastStep_writes_word hS hC (by omega) (by omega) hW (by simp [hL0])
      (by simp [hL1]) (by simp; omega) (by simp; omega)).mono le_rfl ?_
    rintro μ' hfr ⟨hp', hW'⟩
    refine ⟨hp'.trans hp, by have := hfr.length_eq; omega, by rw [hfr.len_eq, hL0],
      by rw [hfr.len_eq, hL1], ?_⟩
    rw [List.foldl_append]
    exact hW'
  have hlive : ∀ {μ : Mem ℝ}, μ.store.length = L + 2 → μ.Live [a, a, (L, 0), (L + 1, 0)] :=
    fun h => by simp [Mem.Live, h]; omega
  have hstart : St [] ⟨s₁, m.pos⟩ :=
    ⟨rfl, by omega, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      hA.of_below hBelow hal⟩
  refine (writes_loop (N := N - 2) rfl (fun _ => G) (fun _ _ => le_rfl)
    (fun i μ => St ((List.range i).flatMap fun i =>
      (List.range (N - 2 - i)).map fun c => (i, c)) μ) (by simpa using hstart) ?_).seq_le
    (sup_le (sup_le le_sup_left fun b x hb => Or.inr (hb.1 ▸ le_rfl))
      fun b x hb => Or.inr (hb.1 ▸ Nat.le_succ L)) ?_
  · intro i hi μ _ hμ
    refine (writes_loop (N := N - 2 - i) rfl (fun _ => G) (fun _ _ => le_rfl)
      (fun c μ' => St (((List.range i).flatMap fun i =>
        (List.range (N - 2 - i)).map fun c => (i, c)) ++
          (List.range c).map fun c => (i, c)) μ') (by simpa using hμ) ?_).mono le_rfl ?_
    · intro c hc μ' _ hμ'
      refine ((hround _ i c hi hc μ' hμ').in_frame rfl rfl (hlive hμ'.2.1)).mono le_rfl ?_
      intro μ'' _ h
      simpa [List.range_succ, List.map_append, List.append_assoc] using h
    · intro μ' _ h
      simpa [List.range_succ, List.flatMap_append] using h
  · rintro μ _ ⟨hp, hlen', -, -, hW⟩
    refine ((clearBelowSubdiagonal_writes_word (τ := τ) hS (by simp [Mem.Live, hlen']; omega)
      hW).in_frame rfl rfl (by simp [Mem.Live, hlen']; omega)).mono
      le_sup_left ?_
    rintro μ' - ⟨hp', hW'⟩
    exact ⟨hp'.trans hp, hW'⟩

section BackwardError

variable {M : Machine ℝ} {u : ℝ} {N : ℕ}

/-- Under the standard model a rounded complex linear combination of two zeros is zero. -/
theorem ShiftedQR.linearComplex_zero_zero (hM : StdModel u id M) (a b : ℂ) :
    linearComplex M a b 0 0 = 0 := by
  have hmul : ∀ x : ℝ, M.mul x 0 = 0 := fun x => by simpa using hM.mul x 0
  have hadd : M.add 0 0 = 0 := by simpa using hM.add 0 0
  have hsub : M.sub 0 0 = 0 := by simpa using hM.sub 0 0
  apply Complex.ext <;> simp [linearComplex, Pair.linearWords, hmul, hadd, hsub]

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
    simp only [machineColRotation, Matrix.of_apply, h1, h2, ShiftedQR.linearComplex_zero_zero hM]
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

/-- The invariant of the reduction after $k$ steps: within $((1 + 61\boldsymbol{u})^k - 1)
\|\mathbf{A}\|_2$ of a unitary similarity of $\mathbf{A}$ fixing $\mathbf{e}_{n+1}$. -/
private def HRBound (u : ℝ) {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : ℕ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
    (∀ i, Q i (Fin.last n) = if i = Fin.last n then 1 else 0) ∧
    specNorm (Y - Qᴴ * A * Q) ≤ ((1 + 61 * u) ^ k - 1) * specNorm A

/-- One step of the reduction keeps the invariant, with one more step. -/
private theorem hrBound_step (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 576) {n : ℕ}
    {A X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k r c : ℕ} (hc : c + 1 < r) (hr : r < n + 1)
    (h : HRBound u A k (bottomUpMask r c X)) :
    HRBound u A (k + 1) (bottomUpMask r (c + 1) (reduceLastStepWord M r c X)) := by
  obtain ⟨Q, hQ, hlast, hE⟩ := h
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
  refine ⟨Q * Gᴴ, hasOrthonormalCols_iff.mpr ((hQ.conjTranspose_mul_mul _ _).trans
    hG.conjTranspose.conjTranspose_mul_self), fun a => ?_, ?_⟩
  · rw [conjTranspose_givens, mul_givens_apply_of_ne (Fin.ne_of_val_ne (by simp [i]; omega))
      (Fin.ne_of_val_ne (by simp [j]; omega)), hlast]
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
    (h : HRBound u A k (bottomUpMask (n - i) 0 X)) :
    ∀ C ≤ n + 1 - 2 - i, HRBound u A (k + C) (bottomUpMask (n - i) C
      (((List.range C).map fun c => (i, c)).foldl
        (fun X ic => reduceLastStepWord M (n + 1 - 1 - ic.1) ic.2 X) X))
  | 0, _ => by simpa using h
  | C + 1, hC => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    have := hrBound_step (M := M) hM hu hu' (c := C) (r := n - i) (by omega) (by omega)
      (hrBound_row hM hu hu' hi h C (by omega))
    simpa [← add_assoc] using this

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
      ((hrSteps (n + 1) I).foldl (fun X ic => reduceLastStepWord M (n + 1 - 1 - ic.1) ic.2 X) A))
  | 0, _ => by
    refine ⟨1, hasOrthonormalCols_one, fun a => by simp [Matrix.one_apply], ?_⟩
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
    simpa [hrSteps, List.range_succ, List.flatMap_append, List.foldl_append, add_comm] using h

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
  have hu : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hz : (⟨M.lit 0, M.lit 0⟩ : ℂ) = 0 := by rw [hzero]; rfl
  refine ⟨fun a b hab => by simp [hessenbergReduceLastWord, hab, hz], ?_⟩
  have hu' : 3 ≤ n + 1 → u ≤ 1 / 576 := fun h3 => by
    have : (3 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h3
    nlinarith
  obtain ⟨Q, hQ, hlast, hE⟩ := hrBound_rows (M := M) hM hu hu' A (n + 1 - 2) le_rfl
  refine ⟨Q, hQ, hlast, ?_⟩
  have hW : hessenbergReduceLastWord M A = bottomUpMask (n - (n + 1 - 2)) 0
      ((hrSteps (n + 1) (n + 1 - 2)).foldl
        (fun X ic => reduceLastStepWord M (n + 1 - 1 - ic.1) ic.2 X) A) := by
    ext a b
    simp only [hessenbergReduceLastWord, bottomUpMask, hrSteps, Matrix.of_apply, hz]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [hW]
  refine hE.trans (mul_le_mul_of_nonneg_right (hrGrowth_le hu ?_ hnu) (specNorm_nonneg A))
  have hl := two_mul_length_hrSteps (n + 1) (n + 1 - 2) le_rfl
  rw [Nat.sub_self, zero_mul, add_zero] at hl
  have : (n + 1 - 2) * (n + 1 - 2 + 1) ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * (hrSteps (n + 1) (n + 1 - 2)).length ≤ (n + 1) ^ 2 := by rw [sq]; omega
  exact_mod_cast h2

/-- `NLAlib.hessenbergReduceLast` terminates on every tape and every stored matrix: its loops are
counted and every operation succeeds on stored operands. -/
theorem hessenbergReduceLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun m' => ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a A' m'.store) m :=
  (hessenbergReduceLast_writes_word hS hC hl hA).mono le_rfl fun _ _ h => ⟨_, h.2⟩

end Theorems

end NLAlib
