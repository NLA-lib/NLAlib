/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward

/-!
# Termination of the rounded deflation worklist

The termination-only counterpart of `NLAlib.ShiftedQR.solveRounded_backward`: on every tape
and from every stored matrix, the rounded worklist runs to completion when its decoupler and its
leaf do. Nothing numerical is assumed: no unit roundoff, no Hessenberg input, no spectrum. What
makes the run succeed is index safety (every bounded index read is within its bound, because
every index word is an exact natural literal), the room of the stack (the active ranges have
positive sizes summing to at most the order), and the total scalar operations.

## Main definitions

* `NLAlib.ShiftedQR.TerminatingDecoupler`: a decoupler that terminates from every stored
  matrix, writes only the matrix and the flag, and leaves both stored.
* `NLAlib.ShiftedQR.TerminatingLeaf`: a leaf routine that terminates from every stored matrix
  and writes only its output.

## Main results

* `NLAlib.ShiftedQR.bottomScan_terminates`: the bottom-$k$ scan on any matrix.
* `NLAlib.ShiftedQR.IsRandomSmallEig.terminatingLeaf`: the `SmallEig` leaf terminates.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- **A terminating decoupler** for orders up to $n_{\max} + 1$, with the bottom width `k`, the
iteration cap `F` and the parameter words `ps`: from any matrix of order $n + 1 \ge k + 1$,
$n \le n_{\max}$, stored in place (no structure
assumed) and on every tape, the run is total, writes only the matrix and the one-word flag, and
leaves a stored matrix and a stored flag. The geometry is that of
`NLAlib.ShiftedQR.RoundedDecouplingContract`. The interface is `[n, k, np, F] (W, P) → (W, Fl)`.
-/
def TerminatingDecoupler (nmax k F : ℕ) (ps : List ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {w q f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → n ≤ nmax → HoldsMatrix w H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps → μ.Live [w, q, w, f] →
    w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) →
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length, F] [w, q, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ

/-- **A terminating leaf routine**: from any matrix of order $d$ stored at `w` (no structure
assumed) and on every tape, the run is total, writes only its $2d$ output words, the output
disjoint from the input, and leaves them stored. The interface is `[d] (B) → (Ev)`. -/
def TerminatingLeaf (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w o : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    HoldsMatrix w B μ.store → μ.Live [w, o] → o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape L.body (Env.frame [d] [w, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) μ

/-- **A terminating decoupling routine with a cap dimension**:
`NLAlib.ShiftedQR.TerminatingDecoupler` for a decoupler with the interface
`[n, k, np, F, T] (W, P) → (W, Fl)`: from any matrix of order $n + 1 \ge k + 1$,
$n \le n_{\max}$, stored in place and on every tape, the run is total, writes only the matrix and
the flag, and leaves a stored matrix and a stored flag. -/
def TerminatingDecouplerRoutine (nmax k F T : ℕ) (ps : List ℝ) (D : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {w q f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → n ≤ nmax → HoldsMatrix w H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps → μ.Live [w, q, w, f] →
    w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) →
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length, F, T] [w, q, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ

/-- **A terminating leaf routine with parameter words and a cap**: from any matrix of order
$d \le k_{\max}$ stored at `w` (no structure assumed), the words `ps` stored, and on every tape,
the run is total, writes only its $2d$ output words and leaves them stored. The interface is
`[d, np, T] (B, P) → (Ev)`. -/
def TerminatingLeafRoutine (kmax : ℕ) (ps : List ℝ) (T : ℕ) (L : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p o : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [w, p, o] → o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Fp.Disj (Store.inBlock p.1 p.2 ps.length) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape L.body (Env.frame [d, ps.length, T] [w, p, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) μ

/-- A terminating decoupler, lifted by `NLAlib.ShiftedQR.liftDecoupler`, is a terminating
decoupling routine for every cap. -/
theorem TerminatingDecoupler.terminatingDecouplerRoutine {nmax k F : ℕ} {ps : List ℝ}
    {D : Impl O Q} {I : Interp O Q ℝ} (h : TerminatingDecoupler nmax k F ps D I) (T : ℕ) :
    TerminatingDecouplerRoutine nmax k F T ps (liftDecoupler D) I := by
  intro n w q f tape μ H hk hn hH hq hl hw hf hwf hqwf
  unfold liftDecoupler
  exact (h H hk hn hH hq hl hw hf hwf hqwf).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by simpa [Mem.Live] using hl)

/-- A terminating leaf, lifted by `NLAlib.ShiftedQR.liftLeaf`, is a terminating leaf routine for
every order bound, parameter words and cap. -/
theorem TerminatingLeaf.terminatingLeafRoutine {L : Impl O Q} {I : Interp O Q ℝ}
    (h : TerminatingLeaf L I) (kmax : ℕ) (ps : List ℝ) (T : ℕ) :
    TerminatingLeafRoutine kmax ps T (liftLeaf L) I := by
  intro d w p o tape μ B _ hB _ hl hroom hwo _
  unfold liftLeaf
  exact (h B hB (hl.mono (by simp)) hroom hwo).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (hl.mono (by simp))

/-- The leaf routine of a terminating small-eigenvalue routine with the word count $12$ and the
words `qs` (none, or $12$; `NLAlib.ShiftedQR.TerminatingSmallEigAt`) terminates, with any words
`ps₀` before `qs`. -/
theorem TerminatingSmallEigAt.terminatingLeafRoutine {kmax T : ℕ} {qs ps₀ : List ℝ}
    {SE : Impl O Q} {I : Interp O Q ℝ} (h : TerminatingSmallEigAt kmax 12 T qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12) :
    TerminatingLeafRoutine kmax (ps₀ ++ qs) T (seLeaf SE) I := by
  intro d w p o tape μ B hd hB hp hl hroom hwo hpo
  obtain ⟨hq, hsub⟩ := Store.readBlock_tail_twelve hq12 hp
  unfold seLeaf
  refine (h (q := (p.1, p.2 + ((ps₀ ++ qs).length - 12))) tape μ B hd hB hq
    (by simpa [Mem.Live] using hl) hroom hwo
    (hpo.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)).in_frame ?_ ?_ ?_
  · simp
  · simp [Operand.evalList, Operand.eval]
  · simpa [Mem.Live] using hl

/-- The leaf routine of a terminating small-eigenvalue routine with $12$ words `qs` terminates,
with any words `ps₀` before `qs`. -/
theorem TerminatingSmallEig.terminatingLeafRoutine {kmax T : ℕ} {qs ps₀ : List ℝ}
    {SE : Impl O Q} {I : Interp O Q ℝ} (h : TerminatingSmallEig kmax T qs SE I)
    (hqs : qs.length = 12) : TerminatingLeafRoutine kmax (ps₀ ++ qs) T (seLeaf SE) I :=
  TerminatingSmallEigAt.terminatingLeafRoutine (hqs ▸ h.at) (Or.inr hqs)

section Leaf

variable [Has EigenvalueKernelOp O]

/-- The `SmallEig` leaf terminates: a randomized small-eigenvalue kernel
(`NLAlib.ShiftedQR.IsRandomSmallEig`) always succeeds on live, readable operands with room, at
every input and on every tape, so the leaf routine that calls it is a terminating leaf. -/
theorem IsRandomSmallEig.terminatingLeaf {law : ℕ → MeasureTheory.Measure ℝ} {s : ℕ}
    {β φ : ℝ} {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) :
    TerminatingLeaf (smallEigLeaf (O := O) (Q := Q)) I := by
  obtain ⟨W, Bad, -, -, hI⟩ := h
  intro d w o tape μ B hH hl hroom _
  unfold smallEigLeaf
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  exact (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) fun _ _ h => by
    obtain ⟨-, -, ys, -, hys, -⟩ := h
    obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hys
    exact ⟨y, hy⟩

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
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [a, t, r])
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
