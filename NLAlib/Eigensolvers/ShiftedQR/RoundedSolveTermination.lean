/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward

/-!
# Termination contracts of the routines of the rounded deflation worklist

The termination-only side of the worklist's routines: a decoupler and a Schur leaf that terminate
from every stored matrix, with no unit roundoff, no Hessenberg input and no spectrum assumed. What
makes a run succeed is index safety (every bounded index read is within its bound, because every
index word is an exact natural literal), the room of the buffers and the total scalar operations.
The worklist's termination is `NLAlib.ShiftedQR.solveRoundedWith_terminates`.

## Main definitions

* `NLAlib.ShiftedQR.TerminatingDecouplerRoutine`: a decoupler that terminates from every stored
  matrix, writes only the matrix, the flag and its log, and leaves them stored.
* `NLAlib.ShiftedQR.CompletingLeafRoutine`: a Schur leaf that terminates from every stored
  matrix, writes only its block and accumulator, and leaves both stored (no rounding model).
* `NLAlib.ShiftedQR.TerminatingLeafRoutine`: the same with the accumulator near a unitary.

## Main results

* `NLAlib.ShiftedQR.bottomScan_terminates`: the bottom-$k$ scan on any matrix.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- **A terminating decoupling routine with a cap dimension and a log**: for a decoupler with
the interface `[n, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`, from any matrix of order
$n + 1 \ge k + 1$, $n \le n_{\max}$, stored in place, with the log in a buffer of its own, and on
every tape, the run is total, writes
only the matrix, the flag and the log, and leaves a stored matrix, a stored flag and the `ns`
slots of the log closed with planes below $n$ (so that the log can be replayed). -/
def TerminatingDecouplerRoutine (nmax k F T : ℕ) (ps : List ℝ) (ns w : ℕ) (D : Stmt O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {w₀ q f lg : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → n ≤ nmax → HoldsMatrix w₀ H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps → μ.Live [w₀, q, w₀, f, lg] →
    w₀.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w₀.1 →
    f.2 + 1 ≤ μ.store.len f.1 → lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1 →
    (∀ b ∈ [w₀, q, f], b.1 ≠ lg.1) →
    Fp.Apart [w₀, f, lg] [2 * ((n + 1) * (n + 1)), 1, ns * (1 + 5 * w)] →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) →
    Writes .total I tape D (Env.frame [n + 1, k, ps.length, F, T, ns, w] [w₀, q, w₀, f, lg])
      (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w₀ H' μ'.store) ∧
        ∃ L : List (Option (List GivensEntry)), L.length = ns ∧
          (∀ e ∈ slotEntries w L, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L [] μ'.store) μ

/-- **A completing Schur leaf routine with parameter words and a cap**: from any matrix of order
$d \le k_{\max}$ stored at `w` (no structure assumed), the words `ps` stored, and on every tape,
the run is total, writes only the block and its accumulator, and leaves both stored. Nothing is
claimed of the values: no rounding model is needed. The interface is
`[d, np, T] (Bk, P) → (Bk, Ub)`; the strengthening with an accumulator near a unitary is
`NLAlib.ShiftedQR.TerminatingLeafRoutine`. -/
def CompletingLeafRoutine (kmax : ℕ) (ps : List ℝ) (T : ℕ) (L : Stmt O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [w, p, ub] → ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Writes .total I tape L (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ' => ∃ Tb Ub : Matrix (Fin d) (Fin d) ℂ, HoldsMatrix w Tb μ'.store ∧
        HoldsMatrix ub Ub μ'.store) μ

/-- **A terminating Schur leaf routine with parameter words and a cap**: a completing leaf
routine (`NLAlib.ShiftedQR.CompletingLeafRoutine`) whose stored accumulator is moreover within
$\varepsilon_L$ of an exact unitary. The interface is `[d, np, T] (Bk, P) → (Bk, Ub)`. -/
def TerminatingLeafRoutine (εL : ℝ) (kmax : ℕ) (ps : List ℝ) (T : ℕ) (L : Stmt O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [w, p, ub] → ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Writes .total I tape L (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ' => ∃ Tb Ub V : Matrix (Fin d) (Fin d) ℂ, HoldsMatrix w Tb μ'.store ∧
        HoldsMatrix ub Ub μ'.store ∧ HasOrthonormalCols V ∧ specNorm (Ub - V) ≤ εL) μ

/-- A terminating leaf routine completes. -/
theorem TerminatingLeafRoutine.completing {εL : ℝ} {kmax : ℕ} {ps : List ℝ} {T : ℕ}
    {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutine εL kmax ps T L I) :
    CompletingLeafRoutine kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, _, hTb, hUb, _⟩ =>
      ⟨Tb, Ub, hTb, hUb⟩

/-- A terminating leaf routine on orders at most $k_{\max}$ terminates on smaller orders. -/
theorem TerminatingLeafRoutine.mono_kmax {εL : ℝ} {kmax kmax' : ℕ} {ps : List ℝ} {T : ℕ}
    {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutine εL kmax ps T L I)
    (hk : kmax' ≤ kmax) : TerminatingLeafRoutine εL kmax' ps T L I :=
  fun B hd hB hp hl hroom hwo hpo => h B (hd.trans hk) hB hp hl hroom hwo hpo

/-- A completing leaf routine on orders at most $k_{\max}$ completes on smaller orders. -/
theorem CompletingLeafRoutine.mono_kmax {kmax kmax' : ℕ} {ps : List ℝ} {T : ℕ}
    {L : Stmt O Q} {I : Interp O Q ℝ} (h : CompletingLeafRoutine kmax ps T L I)
    (hk : kmax' ≤ kmax) : CompletingLeafRoutine kmax' ps T L I :=
  fun B hd hB hp hl hroom hwo hpo => h B (hd.trans hk) hB hp hl hroom hwo hpo

/-- **A Schur leaf routine with its accumulator near a unitary if `P`**: a completing leaf
routine (`NLAlib.ShiftedQR.CompletingLeafRoutine`) whose stored accumulator is within
$\varepsilon_L$ of an exact unitary when the proposition `P` holds. At `P` false it is a
completing leaf routine, at `P` true a terminating one
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`). -/
def TerminatingLeafRoutineIf (P : Prop) (εL : ℝ) (kmax : ℕ) (ps : List ℝ) (T : ℕ) (L : Stmt O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [w, p, ub] → ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d))) →
    Writes .total I tape L (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ' => ∃ Tb Ub : Matrix (Fin d) (Fin d) ℂ, HoldsMatrix w Tb μ'.store ∧
        HoldsMatrix ub Ub μ'.store ∧
        (P → ∃ V : Matrix (Fin d) (Fin d) ℂ, HasOrthonormalCols V ∧ specNorm (Ub - V) ≤ εL)) μ

/-- A terminating leaf routine keeps its accumulator near a unitary under any condition. -/
theorem TerminatingLeafRoutine.terminatingLeafRoutineIf {εL : ℝ} {kmax : ℕ} {ps : List ℝ}
    {T : ℕ} {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutine εL kmax ps T L I)
    (P : Prop) : TerminatingLeafRoutineIf P εL kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, V, hTb, hUb, hV, hb⟩ =>
      ⟨Tb, Ub, hTb, hUb, fun _ => ⟨V, hV, hb⟩⟩

/-- A completing leaf routine claims nothing of its accumulator under a false condition. -/
theorem CompletingLeafRoutine.terminatingLeafRoutineIf {kmax : ℕ} {ps : List ℝ} {T : ℕ}
    {L : Stmt O Q} {I : Interp O Q ℝ} (h : CompletingLeafRoutine kmax ps T L I) (εL : ℝ) :
    TerminatingLeafRoutineIf False εL kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, hTb, hUb⟩ =>
      ⟨Tb, Ub, hTb, hUb, False.elim⟩

/-- A leaf routine with its accumulator near a unitary if `P` completes. -/
theorem TerminatingLeafRoutineIf.completing {P : Prop} {εL : ℝ} {kmax : ℕ} {ps : List ℝ}
    {T : ℕ} {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutineIf P εL kmax ps T L I) :
    CompletingLeafRoutine kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, hTb, hUb, _⟩ =>
      ⟨Tb, Ub, hTb, hUb⟩

/-- A leaf routine with its accumulator near a unitary if `P`, where `P` holds, terminates
with that accumulator bound. -/
theorem TerminatingLeafRoutineIf.terminating {P : Prop} {εL : ℝ} {kmax : ℕ} {ps : List ℝ}
    {T : ℕ} {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutineIf P εL kmax ps T L I)
    (hP : P) : TerminatingLeafRoutine εL kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, hTb, hUb, hV⟩ =>
      ⟨Tb, Ub, (hV hP).choose, hTb, hUb, (hV hP).choose_spec⟩

/-- A weaker condition: if `P'` implies `P`, a routine with its accumulator near a unitary if `P`
has it if `P'`. -/
theorem TerminatingLeafRoutineIf.mono {P P' : Prop} {εL : ℝ} {kmax : ℕ} {ps : List ℝ} {T : ℕ}
    {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutineIf P εL kmax ps T L I)
    (hP : P' → P) : TerminatingLeafRoutineIf P' εL kmax ps T L I :=
  fun B hd hB hp hl hroom hwo hpo =>
    (h B hd hB hp hl hroom hwo hpo).mono le_rfl fun _ _ ⟨Tb, Ub, hTb, hUb, hV⟩ =>
      ⟨Tb, Ub, hTb, hUb, fun hP' => hV (hP hP')⟩

/-- A leaf routine with its accumulator near a unitary if `P` on orders at most $k_{\max}$ has
it on smaller orders. -/
theorem TerminatingLeafRoutineIf.mono_kmax {P : Prop} {εL : ℝ} {kmax kmax' : ℕ} {ps : List ℝ}
    {T : ℕ} {L : Stmt O Q} {I : Interp O Q ℝ} (h : TerminatingLeafRoutineIf P εL kmax ps T L I)
    (hk : kmax' ≤ kmax) : TerminatingLeafRoutineIf P εL kmax' ps T L I :=
  fun B hd hB hp hl hroom hwo hpo => h B (hd.trans hk) hB hp hl hroom hwo hpo

section Leaf

variable [Has EigenvalueKernelOp O]

end Leaf

section Scan

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The registers of `bottomScan` on any matrix: the flag is $1$ with a subdiagonal index
$i < n$ stored, or $0$ with some index word stored. -/
def BottomScanStored (n : ℕ) (r : ℕ × ℕ) (st : Store ℝ) : Prop :=
  (st.get r.1 (r.2 + 3) = some 1 ∧ ∃ i : Fin n, st.get r.1 (r.2 + 4) = some (i : ℝ)) ∨
    (st.get r.1 (r.2 + 3) = some 0 ∧ ∃ x, st.get r.1 (r.2 + 4) = some x)

/-- The rounded bottom-$k$ scan terminates on any matrix: on a machine whose natural
literals up to $n + 1$ are exact, for any $(n+1) \times (n+1)$ matrix stored at `a`, $k \le n$
and any threshold word, `bottomScan` writes only its five registers and leaves the flag $1$ with
a subdiagonal index $i < n$, or the flag $0$ with an index word
(`NLAlib.ShiftedQR.BottomScanStored`). -/
theorem bottomScan_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1))
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n)
    {a t r : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hH : HoldsMatrix a H m.store) (ht : m.store.get t.1 t.2 = some thr)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)) (Env.frame [n + 1, k] [a, t, r])
      (Store.inBlock r.1 r.2 5) (fun m' => m'.pos = m.pos ∧ BottomScanStored n r m'.store) m := by
  have hzero : M.lit ((0 : ℕ) : ℚ) = (0 : ℝ) := by simpa using hNat 0 (Nat.zero_le _)
  unfold bottomScan
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hFlag⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIndex⟩
  have hFlag₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hFlag
  simp only [hzero] at hFlag₂ hIndex
  have hfr := (hfr₁.trans' hfr₂).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 5)
  have hH₂ := hH.of_eqOff hfr hA
  have ht₂ := hfr.keep (Store.readsOnly_get _ _ _) hT ht
  have hl₂ := hl.congr hfr.length_eq
  have hroom₂ : r.2 + 5 ≤ m₂.store.len r.1 := by rw [hfr.len_eq]; exact hroom
  refine (writes_loop rfl (fun _ => Store.inBlock r.1 r.2 5) (fun _ _ => le_rfl)
    (fun _ m' => m'.pos = m₂.pos ∧ BottomScanStored n r m'.store)
    ⟨rfl, Or.inr ⟨hFlag₂, ⟨0, hIndex⟩⟩⟩ ?_).mono le_rfl ?_
  · intro j hj m' hfr' ⟨hp', hs⟩
    obtain ⟨flag, hflag⟩ : ∃ x, m'.store.get r.1 (r.2 + 3) = some x := by
      rcases hs with ⟨h1, -⟩ | ⟨h0, -⟩
      exacts [⟨_, h1⟩, ⟨_, h0⟩]
    obtain ⟨index, hindex⟩ : ∃ x, m'.store.get r.1 (r.2 + 4) = some x := by
      rcases hs with ⟨-, i, hi⟩ | ⟨-, hx⟩
      exacts [⟨_, hi⟩, hx]
    have hw := scanRound_writes_word (τ := τ) (k := n + 1 - 1 - k + j) hS hL hC
      (hNat.mono n.le_succ)
      (by omega) (hH₂.of_eqOff hfr' hA) (hfr'.keep (Store.readsOnly_get _ _ _) hT ht₂) hflag
      hindex (hl₂.congr hfr'.length_eq) (by rw [hfr'.len_eq]; exact hroom₂) hA hT
    refine (hw.in_frame rfl rfl (hl₂.congr hfr'.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hp'', hF, hI⟩
    refine ⟨hp''.trans hp', ?_⟩
    split_ifs at hF hI
    · exact Or.inl ⟨hF, ⟨n + 1 - 1 - k + j, by omega⟩, hI⟩
    · rcases hs with ⟨h1, i, hi⟩ | ⟨h0, -⟩
      · rw [h1, Option.some.injEq] at hflag
        rw [hi, Option.some.injEq] at hindex
        exact Or.inl ⟨hflag ▸ hF, i, hindex ▸ hI⟩
      · rw [h0, Option.some.injEq] at hflag
        exact Or.inr ⟨hflag ▸ hF, _, hI⟩
  · intro m' _ ⟨hp', hs⟩
    exact ⟨hp'.trans (hp₂.trans hp₁), hs⟩

end Scan

end NLAlib.ShiftedQR
