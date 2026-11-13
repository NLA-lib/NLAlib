/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Map
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.VectorUpdate
public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Blas.HermitianEntry

/-!
# Copy and identity kernels for interleaved matrices

Matrices are stored by columns with two scalar words per entry. Copy reuses the generic unary
map. Identity explicitly writes every word, including off-diagonal entries and imaginary
components; its diagonal uses the machine literal one. No matrix-valued primitive is assumed.

## Main results

* `NLAlib.Ops.PairMatrix.copy` copies an interleaved rectangular matrix.
* `NLAlib.Ops.PairMatrix.identity` initializes a complete interleaved square identity.
* `NLAlib.Ops.PairMatrix.stmtCost_identity` counts every initialized scalar word and diagonal.
-/

@[expose] public section

namespace NLAlib.Ops.PairMatrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Copy an interleaved rectangular matrix with one scalar copy per stored word. -/
def copy : Impl Op Tst := opsImpl% [rows, cols] (X) → (Y) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (rows * cols)] (X, Y)
}

/-- The named copy program is definitionally the generic unary-map frame, so the builder
introduces no new execution mechanism and retains the caller's explicit offsets. -/
theorem body_copy_eq_frame :
    (copy (Op := Op) (Tst := Tst)).body =
      .frame [.const 2 * (.var 0 * .var 1)] [⟨0, .var 2⟩, ⟨1, .var 3⟩]
        (unaryMap (Has.inj ScalarOp.copy)).body := rfl

/-- Conjugate-transpose an interleaved rectangular matrix by scalar copies and negations. -/
def conjTranspose : Impl Op Tst := opsImpl% [rows, cols] (X) → (Y) {
  for j < cols {
    for i < rows {
      run (Hermitian.conjugatePair).body []
        (X[2 * (j * rows + i)], Y[2 * (i * cols + j)])
    }
  }
}

/-- Accumulate the real diagonal by the machine's additions, starting from literal zero. -/
def traceRe : Impl Op Tst := opsImpl% [n] (X) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for i < n { call (Has.inj ScalarOp.add) [] (out, X[2 * (i * n + i)]) → (out) }
}

/-- The actual rounded real-trace recurrence: start at literal zero and add each stored
real diagonal word from the left. The last argument is the number of entries accumulated. -/
def traceReF {K : Type} (M : Machine K) (n : ℕ) (v : ℕ → K) : ℕ → K
  | 0 => M.lit 0
  | i + 1 => M.add (traceReF M n v i) (v (2 * (i * n + i)))

/-- The real trace executes its actual left-to-right rounded recurrence on the stored matrix.
Readable input and a disjoint writable accumulator suffice; no accuracy hypothesis is used. -/
theorem writes_traceRe {K : Type} {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {m : Mem K} {n : ℕ} {x y : ℕ × ℕ} {v : ℕ → K}
    (hx : m.store.HoldsVec x.1 x.2 (2 * (n * n)) v) (hy : y.2 < m.store.len y.1)
    (hdisj : Fp.Disj (Store.inBlock y.1 y.2 1) (Store.inBlock x.1 x.2 (2 * (n * n)))) :
    Writes .total I τ (traceRe (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, y])
      (Store.inBlock y.1 y.2 1)
      (fun m' => m'.store.get y.1 y.2 = some (traceReF M n v n) ∧ m'.pos = m.pos) m := by
  have hzero : Writes .total I τ
      (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨1, .var 2⟩]) (Env.frame [n] [x, y])
      (Store.inBlock y.1 y.2 1)
      (fun m' => m'.store.get y.1 y.2 = some (M.lit 0) ∧ m'.pos = m.pos) m := by
    refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial hy ?_
    exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
      Store.get_upd_self hy _, rfl⟩
  refine hzero.seq_le le_rfl fun m₁ hfr₁ ⟨hzero₁, hp₁⟩ => ?_
  refine writes_loop rfl (fun _ => Store.inBlock y.1 y.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.store.get y.1 y.2 = some (traceReF M n v i) ∧ m'.pos = m.pos)
    ⟨hzero₁, hp₁⟩ fun i hi m' hfr₂ ⟨hacc, hpos⟩ => ?_
  have hsrc := (hfr₁.trans hfr₂).keep
    (Store.readsOnly_holdsVec x.1 x.2 (2 * (n * n)) v) hdisj hx
  have hz : y.2 < m'.store.len y.1 := by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hy
  refine wp_call_bin (hI .add) rfl rfl rfl trivial hacc
    (hsrc (2 * (i * n + i)) (by nlinarith)) rfl hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
    Store.get_upd_self hz _, hpos⟩

/-- Extract the real diagonal words of an interleaved square matrix. -/
def diagonalReal : Impl Op Tst := opsImpl% [n] (X) → (Y) {
  for i < n { call (Has.inj ScalarOp.copy) [] (X[2 * (i * n + i)]) → (Y[i]) }
}

/-- Real-diagonal extraction succeeds on a readable source and disjoint output capacity,
returning the actual stored diagonal words and preserving the tape position. -/
theorem writes_diagonalReal {K : Type} {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {m : Mem K} {n : ℕ} {x y : ℕ × ℕ} {v : ℕ → K}
    (hx : m.store.HoldsVec x.1 x.2 (2 * (n * n)) v)
    (hy : y.2 + n ≤ m.store.len y.1)
    (hdisj : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock x.1 x.2 (2 * (n * n)))) :
    Writes .total I τ (diagonalReal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.HoldsVec y.1 y.2 n (fun i => v (2 * (i * n + i))) ∧
        m'.pos = m.pos) m := by
  refine writes_fill rfl (fun i => v (2 * (i * n + i))) (fun _ => m.pos) rfl
    fun i hi m' hfr _ hpos => ?_
  have hkeep := hfr.keep (Store.readsOnly_holdsVec x.1 x.2 (2 * (n * n)) v)
    (hdisj.mono (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl) hx
  have hz : y.2 + i < m'.store.len y.1 := by rw [hfr.len_eq]; omega
  refine wp_call_un (hI .copy) rfl rfl rfl trivial
    (hkeep (2 * (i * n + i)) (by nlinarith)) rfl hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
    Store.get_upd_self hz _, hpos⟩

/-- Initialize an interleaved square identity using explicit scalar literals. -/
def identity : Impl Op Tst := opsImpl% [n] () → (Y) {
  for q < 2 * (n * n) { call (Has.inj (ScalarOp.lit 0)) [] () → (Y[q]) };
  for i < n { call (Has.inj (ScalarOp.lit 1)) [] () → (Y[2 * (i * n + i)]) }
}

/-- Identity initialization succeeds from output capacity alone and writes every word. Real
diagonal positions contain the machine literal one; every other position contains literal zero.
The statement concerns the actual machine words and does not assume exact arithmetic. -/
theorem writes_identity {K : Type} {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {m : Mem K} {n b off : ℕ}
    (hroom : off + 2 * (n * n) ≤ m.store.len b) :
    Writes .total I τ (identity (Op := Op) (Tst := Tst)).body (Env.frame [n] [(b, off)])
      (Store.inBlock b off (2 * (n * n)))
      (fun m' => m'.store.HoldsVec b off (2 * (n * n))
        (fun q => if ∃ j < n, q = 2 * (j * n + j) then M.lit 1 else M.lit 0) ∧
          m'.pos = m.pos) m := by
  classical
  let v : ℕ → ℕ → K := fun i q =>
    if ∃ j < i, q = 2 * (j * n + j) then M.lit 1 else M.lit 0
  have hzero : Writes .total I τ
      (.loop (.const 2 * (.var 0 * .var 0))
        (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨0, .var 1 + .var 2⟩]))
      (Env.frame [n] [(b, off)]) (Store.inBlock b off (2 * (n * n)))
      (fun m' => m'.store.HoldsVec b off (2 * (n * n)) (v 0) ∧ m'.pos = m.pos) m := by
    refine (writes_fill rfl (fun _ => M.lit 0) (fun _ => m.pos) rfl
      fun i hi m' hfr _ hpos => ?_).mono le_rfl ?_
    · have hz : off + i < m'.store.len b := by rw [hfr.len_eq]; omega
      refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial hz ?_
      exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
        Store.get_upd_self hz _, hpos⟩
    · intro m' _ ⟨hv, hp⟩
      exact ⟨by simpa only [v, Nat.not_lt_zero, false_and, exists_false, ↓reduceIte] using hv, hp⟩
  refine hzero.seq_le le_rfl fun m' hfr ⟨hv, hp⟩ => ?_
  have hnext : ∀ i < n, v (i + 1) = Function.update (v i) (2 * (i * n + i)) (M.lit 1) := by
    intro i _
    funext q
    by_cases hq : q = 2 * (i * n + i)
    · subst q
      simp only [v, Function.update_self]
      exact if_pos ⟨i, by omega, rfl⟩
    · rw [Function.update_of_ne hq]
      dsimp only [v]
      have hequiv : (∃ j < i + 1, q = 2 * (j * n + j)) ↔
          ∃ j < i, q = 2 * (j * n + j) := by
        constructor
        · rintro ⟨j, hj, hqj⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjlt | rfl
          · exact ⟨j, hjlt, hqj⟩
          · exact (hq hqj).elim
        · rintro ⟨j, hj, hqj⟩
          exact ⟨j, by omega, hqj⟩
      simp only [hequiv]
  refine (writes_patch rfl v (fun i => 2 * (i * n + i)) (fun _ => M.lit 1) hv
    (fun i hi => by nlinarith) hnext fun i hi m'' hfr' _ hpos => ?_).mono le_rfl ?_
  · have hz : off + 2 * (i * n + i) < m''.store.len b := by
      rw [hfr'.len_eq, hfr.len_eq]
      nlinarith
    refine wp_call_const (hI (.lit 1)) rfl rfl rfl trivial hz ?_
    exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
      Store.get_upd_self hz _, hpos⟩
  · intro m'' _ ⟨hv', hp'⟩
    exact ⟨hv', hp'.trans hp⟩

/-- The complete initialized word vector is the column-major matrix with literal one on the
real diagonal and literal zero in every other real or imaginary component. -/
theorem holdsEntries_of_holdsVec {K : Type} {M : Machine K} {s : Store K} {n b off : ℕ}
    (h : s.HoldsVec b off (2 * (n * n))
      (fun q => if ∃ j < n, q = 2 * (j * n + j) then M.lit 1 else M.lit 0)) :
    s.HoldsEntries (EntryCodec.pair K) ⟨b, off, n, n, n⟩
      (fun i j => (if i = j then M.lit 1 else M.lit 0, M.lit 0)) := by
  intro i hi j hj z
  change i < n at hi
  change j < n at hj
  have hidx := Idx.add_lt_mul hj hi
  fin_cases z
  · have hequiv : (∃ t < n, 2 * (j * n + i) = 2 * (t * n + t)) ↔ i = j := by
      constructor
      · rintro ⟨t, ht, htq⟩
        have hq : j * n + i = t * n + t := by omega
        have hjt : j = t := by
          have hd := congrArg (fun q => q / n) hq
          simpa only [Idx.div_add hi, Idx.div_add ht] using hd
        subst t
        omega
      · intro hij
        exact ⟨j, hj, by rw [hij]⟩
    change s.get b (off + 2 * (j * n + i) + 0) =
      some (if i = j then M.lit 1 else M.lit 0)
    have hp := h (2 * (j * n + i)) (by nlinarith)
    simpa only [Nat.add_zero, hequiv] using hp
  · have hnexists : ¬ ∃ t < n, 2 * (j * n + i) + 1 = 2 * (t * n + t) := by
      rintro ⟨t, -, ht⟩
      omega
    change s.get b (off + 2 * (j * n + i) + 1) = some (M.lit 0)
    have hp := h (2 * (j * n + i) + 1) (by nlinarith)
    simpa only [Nat.add_assoc, if_neg hnexists] using hp

/-- Identity writes one zero literal per word and one one literal per diagonal entry. -/
theorem stmtCost_identity (n y : ℕ) :
    stmtCost (identity (Op := Op) (Tst := Tst)).body [n, y] =
      (2 * (n * n)) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • Count.one (Has.inj (ScalarOp.lit 1)) [] := by
  simp [identity, stmtCost, useCost]

/-- Identity needs only the larger literal implementation workspace, with no allocated buffer. -/
theorem stmtPeak_identity_le (W : Op → List ℕ → ℕ) (n y : ℕ) :
    stmtPeak W (identity (Op := Op) (Tst := Tst)).body [n, y] ≤
      max (W (Has.inj (ScalarOp.lit 0)) []) (W (Has.inj (ScalarOp.lit 1)) []) := by
  simp only [identity, stmtPeak]
  exact max_le (Finset.sup_le fun _ _ => le_max_left _ _)
    (Finset.sup_le fun _ _ => le_max_right _ _)

end NLAlib.Ops.PairMatrix
