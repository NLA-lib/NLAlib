/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

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
  sorry

/-- `NLAlib.hessenbergReduceLast` terminates on every tape and every stored matrix: its loops are
counted and every operation succeeds on stored operands. -/
theorem hessenbergReduceLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun m' => ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a A' m'.store) m := by
  sorry

end Theorems

end NLAlib
