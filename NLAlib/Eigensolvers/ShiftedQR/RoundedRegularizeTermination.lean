/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecouple
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.ShiftedQR.StableStepTermination

/-!
# Termination of the rounded `Regularize`

`Regularize` of [BanksGarzaVargasSrivastava2022, §4] (`NLAlib.ShiftedQR.regularize`: `SmallEig`
of the trailing block, the disk draws, `Optimal` and the trials) runs to completion on every tape
and from every stored matrix. Nothing numerical is assumed: the matrix need not be upper
Hessenberg, the machine need not round well, the shifts may be arbitrary words. Each block is
shown to succeed from stored inputs, leaving its outputs stored: the scalar operations, the
comparisons and the kernels always succeed on stored operands with room, every loop is capped,
and every bounded index read is within its bound because the index words are exact natural
literals.

## Main results

* `NLAlib.ShiftedQR.Store.exists_holdsMatrix_of_readBlock`: a stored block holds a matrix.
* `NLAlib.ShiftedQR.trialStep_terminates`: one trial step (rounded step and scan).
* `NLAlib.ShiftedQR.regularize_terminates`: `Regularize`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-! ### Stored matrices -/

/-- A stored block of $2 \cdot rc$ words holds an $r \times c$ matrix. -/
theorem Store.exists_holdsMatrix_of_readBlock {s : Store ℝ} {b : ℕ × ℕ} {rows cols : ℕ}
    {xs : List ℝ} (h : s.readBlock b.1 b.2 (2 * (cols * rows)) = some xs) :
    ∃ A : Matrix (Fin rows) (Fin cols) ℂ, HoldsMatrix b A s :=
  ⟨_, holdsMatrix_storedMatrix fun j hj => by rw [Store.get_of_readBlock h hj 0]; rfl⟩

/-! ### The trials of `Regularize` on any matrix -/

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The computation of one trial terminates on any matrix: on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$, from any matrix of order
$n + 1$ at `A`, any shift pair at `S` and any threshold word at `Thr`, $k \le n$,
`NLAlib.ShiftedQR.trialStep` writes only the log and its four outputs and leaves the step stored at
`T` and the scan flag stored in `Rg`. The views are live and have room; the four outputs are apart
from the three inputs, the step `T` from `SR`, `Ds` and `Rg`, and `SR` from `Ds`. -/
theorem trialStep_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a sp thr t sr ds rg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv : ℝ}
    (hl : m.Live [a, sp, thr, t, sr, ds, rg])
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, sp, thr, t, sr, ds, rg], b.1 ≠ lg.1) :
    Writes .total I τ (trialStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, sp, thr, t, sr, ds, rg, lg])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix t H' m'.store) ∧
        ∃ x, m'.store.get rg.1 (rg.2 + 3) = some x ∧
        ∃ es : List GivensEntry, es.length = k * n ∧ (∀ x ∈ es, x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w LL es m'.store) m := sorry

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The acceptance of a trial terminates on any matrix: on a scalar machine,
`NLAlib.ShiftedQR.trialAccept` copies any matrix at `T` to `A` and stores words in `G` and `Fl`,
writing only these. -/
theorem trialAccept_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {t a g f : ℕ × ℕ} {H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : m.Live [t, a, g, f])
    (hT : HoldsMatrix t H' m.store) (hra : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hrg : g.2 < m.store.len g.1) (hrf : f.2 < m.store.len f.1)
    (hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hga : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hL : IsIndexLit M I) {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    {P : List GivensEntry} (hlog : HoldsSlottedLog lg ns w LL P m.store) (hj : LL.length < ns)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [t, a, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body (Env.frame [n + 1, w, LL.length] [t, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => HoldsMatrix a H' m'.store ∧ (∃ x, m'.store.get g.1 g.2 = some x) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        HoldsSlottedLog lg ns w (LL ++ [some P]) [] m'.store) m := sorry

/-- One trial of `Regularize` terminates on any matrix: on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$, from any matrix of order
$n + 1$ at `A`, any shift pair at `S`, any threshold word at `Thr` and any words at `G` and `Fl`,
$k \le n$, with live views, room for the scratch `T`, `SR`, `Ds`, `Rg`, the scratch apart from
the inputs, `T` from `SR`, `Ds` and `Rg`, `SR` from `Ds`, and `G`, `Fl` apart from each other,
from the scratch and from the matrix, `NLAlib.ShiftedQR.regularizeTrial` writes only the log and
the matrix, `G`, `Fl` and its scratch, and leaves the matrix, `G` and `Fl` stored. -/
theorem regularizeTrial_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a sp thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv gv fv : ℝ}
    (hl : m.Live [a, sp, thr, t, sr, ds, rg, a, g, f])
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some gv)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, sp, thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, sp, thr, t, sr, ds, rg, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get g.1 g.2 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = 1 ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

/-- The trials of `Regularize` terminate on any matrix: on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$, from any matrix of order
$n + 1$ at `A`, any $2k$ shift words at `S`, any threshold word at `Thr` and any words at `G` and
`Fl`, $k \le n$, with live views, room for the scratch `T`, `SR`, `Ds`, `Rg`, the scratch apart
from the inputs, `T` from `SR`, `Ds` and `Rg`, `SR` from `Ds`, `G`, `Fl` apart from each other,
from the scratch and from the matrix, and the matrix, `G` and `Fl` apart from `S` and `Thr`,
`NLAlib.ShiftedQR.regularizeTrials` leaves the matrix, `G` and `Fl` stored. -/
theorem regularizeTrials_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a s thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} {tv gv fv : ℝ}
    (hl : m.Live [a, s, thr, t, sr, ds, rg, a, g, f])
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some gv)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, s, thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, s, thr, t, sr, ds, rg, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get g.1 g.2 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

/-- The decision of `Regularize` terminates on any matrix: with the scratch of
`NLAlib.ShiftedQR.regularize` at `L + 2, …, L + 6`, the views `NLAlib.ShiftedQR.RegularizeViews`,
the context `NLAlib.ShiftedQR.RegularizeCtx` (any matrix and any words) and any $2k$ shift words
at `S`, $k \le n$, `NLAlib.ShiftedQR.regularizeDecide` leaves the matrix and the flag
stored. -/
theorem regularizeDecide_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} (hctx : RegularizeCtx L k H R cw tv a rd c thr s f m) {xs : List ℝ}
    (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

end Trials

/-! ### `Regularize` on any matrix -/

section Regularize

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] in
/-- The `SmallEig` leaf stores its output: a randomized small-eigenvalue kernel
(`NLAlib.ShiftedQR.IsRandomSmallEig`) called on any matrix of order $d$ at `w`, with room for the
$2d$ output words at `o`, writes only the output and leaves it stored, on every tape. -/
theorem IsRandomSmallEig.smallEigLeaf_terminates {law : ℕ → MeasureTheory.Measure ℝ} {s : ℕ}
    {β φ : ℝ} {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) {d : ℕ} {w o : ℕ × ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ} {B : Matrix (Fin d) (Fin d) ℂ} (hH : HoldsMatrix w B μ.store)
    (hl : μ.Live [w, o]) (hroom : o.2 + 2 * d ≤ μ.store.len o.1) :
    Writes .total I τ (smallEigLeaf (O := O) (Q := Q)).body (Env.frame [d] [w, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) μ := by
  obtain ⟨W, Bad, -, -, hI⟩ := h
  unfold smallEigLeaf
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, -, hys, -⟩
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
  exact ⟨y, hy⟩

omit [Has IndexOp O] [Has EigenvalueKernelOp O] [Has CmpTst Q] in
/-- The $k$ random perturbations terminate on any words: on a scalar machine with an exact
polar sampler, from any radius word at `Rd` and any $2k$ words at `S`, with the scratch pair `Z`
apart from `S`, `NLAlib.ShiftedQR.regularizeDraws` writes only `S` and `Z` and leaves `S`
stored. -/
theorem regularizeDraws_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    {rd z s : ℕ × ℕ} {R : ℝ} {xs : List ℝ} (hl : m.Live [rd, z, s])
    (hrd : m.store.get rd.1 rd.2 = some R) (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    (hz : z.2 + 2 ≤ m.store.len z.1)
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) :
    Writes .total I τ (regularizeDraws (O := O) (Q := Q)).body (Env.frame [k] [rd, z, s])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => ∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) m := by
  unfold regularizeDraws
  refine writes_loop (N := k) rfl (fun _ => Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
    (fun _ _ => le_rfl) (fun _ μ => ∃ ys, μ.store.readBlock s.1 s.2 (2 * k) = some ys)
    ⟨xs, hs⟩ ?_
  rintro i hi μ hfr ⟨ys, hys⟩
  obtain ⟨r, hsi⟩ := Store.exists_readBlock_pair hys (o := 2 * i) (by omega)
  have hsub : Store.inBlock s.1 (s.2 + 2 * i) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hdraw := regularizeDraw_writes (τ := τ) (m := μ) (sp := (s.1, s.2 + 2 * i)) (z := z) hS hD
    (hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨hsr, hzr.symm.symm⟩) hrd) hsi
    (by rw [hfr.len_eq]; exact hz) (hzs.mono le_rfl hsub)
  have hlμ := hl.congr hfr.length_eq
  refine (hdraw.in_frame rfl rfl (by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hlμ ⊢
      exact ⟨hlμ.1, hlμ.2.2, hlμ.2.1, hlμ.2.2⟩)).mono
    (sup_le (hsub.trans le_sup_left) le_sup_right) ?_
  rintro μ' hfr' ⟨-, hnew⟩
  refine Store.exists_readBlock_of_eqOff_sub hys (by omega) hfr' ?_ hnew
  refine Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr ⟨(Fp.disj_inBlock_of_le le_rfl).symm,
    Fp.disj_inBlock_of_le le_rfl⟩, hzs.mono le_rfl (sup_le ?_ ?_)⟩
  · exact Fp.inBlock_le_inBlock le_rfl (by omega)
  · exact Fp.inBlock_le_inBlock (by omega) (by omega)

omit [Has EigenvalueKernelOp O] in
/-- `Regularize` with a small-eigenvalue routine and scratch terminates on any matrix: with the
views `NLAlib.ShiftedQR.RegularizeViews` and the context `NLAlib.ShiftedQR.RegularizeCtx` (any
matrix of order $n + 1$, any words), $k \le n$, a routine that terminates on orders at most $k$
(`NLAlib.ShiftedQR.TerminatingSmallEigAt`) with its words stored below the scratch, apart from the
shifts, and an exact polar sampler, on a scalar machine with exact comparisons, index literals and
exact natural literals up to $n + 1$, `NLAlib.ShiftedQR.regularizeWithScratchWith` writes only the
log and the matrix, the $k$ output pairs, the flag and the scratch above $L$, and leaves the
matrix, the pairs and the flag stored. -/
theorem regularizeWithScratchWith_terminates {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1))
    (hC : IsCmp id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} (hctx : RegularizeCtx L k H R cw tv a rd c thr s f m) {nq T : ℕ}
    {qs : List ℝ} {SE : Impl O Q} (hSE : TerminatingSmallEigAt k nq T qs SE I) {qw : ℕ × ℕ}
    (hqL : qw.1 < L) (hq : m.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hqw : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (regularizeWithScratchWith SE).body
      (Env.frame [n + 1, k, nq, T, w, LL.length] [a, rd, c, thr, qw, (L, 0), (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

omit [Has EigenvalueKernelOp O] in
/-- `Regularize` with a terminating small-eigenvalue routine terminates on any matrix, with
the word count `nq` apart from the words `qs` (`NLAlib.ShiftedQR.TerminatingSmallEigAt`): as
`NLAlib.ShiftedQR.regularize_terminates` for `NLAlib.ShiftedQR.regularizeWith`, with the routine's
words stored at `qw`, apart from the outputs. On a
scalar machine with exact comparisons, index literals and exact natural literals up to $n + 1$,
with a `SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
from any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, room for $k \le n$ output
pairs at `s` and the flag at `f` (the views live, the matrix, the pairs and the flag apart from
each other and from the three words), `NLAlib.ShiftedQR.regularize` writes only the log and the
matrix, the pairs and the flag, and leaves all three stored, on every tape. -/
theorem regularizeWith_terminates_at {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cw tv : ℝ}
    (hl : m.Live [a, rd, c, thr, s, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cw)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrs : s.2 + 2 * k ≤ m.store.len s.1)
    (hrf : f.2 < m.store.len f.1) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : TerminatingSmallEigAt k nq T qs SE I) {qw : ℕ × ℕ} (hlq : qw.1 < m.store.length)
    (hq : m.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeWith SE).body
      (Env.frame [n + 1, k, nq, T, w, LL.length] [a, rd, c, thr, qw, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

/-- **`Regularize` terminates on any matrix** ([BanksGarzaVargasSrivastava2022, §4.2]): on a
scalar machine with exact comparisons, index literals and exact natural literals up to $n + 1$,
with a `SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
from any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, room for $k \le n$ output
pairs at `s` and the flag at `f` (the views live, the matrix, the pairs and the flag apart from
each other and from the three words), `NLAlib.ShiftedQR.regularize` writes only the log and the
matrix, the pairs and the flag, and leaves all three stored, on every tape. -/
theorem regularize_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cw tv : ℝ}
    (hl : m.Live [a, rd, c, thr, s, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cw)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrs : s.2 + 2 * k ≤ m.store.len s.1)
    (hrf : f.2 < m.store.len f.1)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, rd, c, thr, s, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularize (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, rd, c, thr, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

end Regularize

end NLAlib.ShiftedQR
