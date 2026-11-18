/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularizeTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedFindTermination
public import NLAlib.Eigensolvers.ShiftedQR.StableStepTermination

/-!
# Termination of the rounded step $\mathrm{Sh}_{k,B}$

$\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, §5] (`NLAlib.ShiftedQR.shStep`: `Find`,
the comparison test, `Exc` and its trials) runs to completion on every tape and from every stored
matrix, with no numerical hypothesis: each block succeeds from stored inputs with room and leaves
its outputs stored, every loop is capped and the index words are exact natural literals.

## Main definitions

* `NLAlib.ShiftedQR.ShRoom`: the room of the step's scratch words.

## Main results

* `NLAlib.ShiftedQR.shTrial_terminates`, `NLAlib.ShiftedQR.shExc_terminates`: one trial and `Exc`.
* `NLAlib.ShiftedQR.shStep_terminates`: $\mathrm{Sh}_{k,B}$.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-! ### `Sh` on any matrix -/

section Sh

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q] {n : ℕ}

/-- The room `NLAlib.ShiftedQR.shStep` has with its twelve scratch buffers at `L, …, L + 11`:
the flag has room, the store has $L + 12$ buffers and the scratch buffers have their lengths
(the tail of `NLAlib.ShiftedQR.ShCtx`). -/
def ShRoom (L n k : ℕ) (ε : ℝ) (f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  f.2 < m.store.len f.1 ∧ m.store.length = L + 12 ∧
    m.store.len L = 2 ∧ m.store.len (L + 1) = 1 ∧ m.store.len (L + 2) = 1 ∧
    m.store.len (L + 3) = 1 ∧ m.store.len (L + 4) = 1 ∧
    m.store.len (L + 5) = 2 * ((n + 1) * (n + 1)) ∧ m.store.len (L + 6) = 2 * k ∧
    m.store.len (L + 7) = 2 * k ∧ m.store.len (L + 8) = 5 ∧ m.store.len (L + 9) = 1 ∧
    m.store.len (L + 10) = 2 * (excNet ε).length ∧ m.store.len (L + 11) = 1

/-- The room of `Sh` is kept by every write. -/
theorem ShRoom.of_eqOff {L k : ℕ} {ε : ℝ} {f : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : ShRoom L n k ε f m) (hfr : m.store.EqOff F m'.store) : ShRoom L n k ε f m' := by
  unfold ShRoom at h ⊢
  simpa only [hfr.len_eq, hfr.length_eq] using h

/-- The context of `Sh` has its room. -/
theorem ShCtx.shRoom {L k : ℕ} {ε : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} {m : Mem ℝ}
    (h : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) : ShRoom L n k ε f m :=
  h.2.2.2.2.2.2.2.2

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The potential test of `Sh` terminates on any matrix: with the views
`NLAlib.ShiftedQR.ShViews` and the room `NLAlib.ShiftedQR.ShRoom`, from any step at `T`, any
matrix at `A` and stored words at `Pt`, `Gw` and `Fl`, $k \le n$,
`NLAlib.ShiftedQR.shPotentialAccept` leaves the matrix, `Gw` and `Fl` stored. -/
theorem shPotentialAccept_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkn : k ≤ n) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    (hr : ShRoom L n k ε f m) {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {pv gv fv : ℝ}
    (hT : HoldsMatrix (L + 5, 0) H' m.store) (hA : HoldsMatrix a H m.store)
    (hpt : m.store.get (L + 2) 0 = some pv) (hg : m.store.get (L + 11) 0 = some gv)
    (hf : m.store.get f.1 f.2 = some fv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    {P : List GivensEntry} (hlog : HoldsSlottedLog lg ns w LL P m.store)
        (hj : LL.length + 1 ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shPotentialAccept (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, w, LL.length]
          [(L + 2, 0), (L + 5, 0), (L + 9, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock (L + 9) 0 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ 1 ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- One trial of `Sh` terminates on any matrix: with the views and the room of `Sh`, from
any matrix at `A`, any shift pair in the scratch buffer `L + 10`, stored threshold words at
`Thr` and `Pt` and stored words at `Gw` and `Fl`, $k \le n$, on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$,
`NLAlib.ShiftedQR.shTrial` leaves the matrix, `Gw` and `Fl` stored. -/
theorem shTrial_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ}
    {m : Mem ℝ} {L k q o : ℕ} (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) (hr : ShRoom L n k ε f m)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv pv gv fv : ℝ}
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock (L + 10) o 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hpt : m.store.get (L + 2) 0 = some pv)
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + 1 ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, w, LL.length]
          [a, (L + 10, o), thr, (L + 2, 0), (L + 5, 0), (L + 6, 0),
        (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ 1 ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The trials of `Sh` terminate on any matrix: with the views and the room of `Sh`, from
any matrix at `A`, any $2n_0$ words in the scratch buffer `L + 10` ($n_0$ the size of the net),
stored threshold words at `Thr` and `Pt` and stored words at `Gw` and `Fl`, $k \le n$, on a
scalar machine with exact comparisons, index literals and exact natural literals up to $n + 1$,
`NLAlib.ShiftedQR.shTrials` leaves the matrix, `Gw` and `Fl` stored. -/
theorem shTrials_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ}
    {m : Mem ℝ} {L k q : ℕ} (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) (hr : ShRoom L n k ε f m)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} {tv pv gv fv : ℝ}
    (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock (L + 10) 0 (2 * (excNet ε).length) = some xs)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hpt : m.store.get (L + 2) 0 = some pv)
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + (excNet ε).length ≤ ns)
        (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length]
          [a, (L + 10, 0), thr, (L + 2, 0), (L + 5, 0),
        (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (excNet ε).length ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has IdxTst Q] in
/-- The exceptional branch of `Sh` terminates on any matrix: with the views of `Sh`, the
context `NLAlib.ShiftedQR.ShCtx` (any matrix, shifts and words), a stored pair at `Z = L` and a
stored word at `Rt = L + 1`, $1 \le k \le n$, on a scalar machine with exact comparisons, index
literals, exact natural literals up to $n + 1$ and an exact polar sampler,
`NLAlib.ShiftedQR.shExc` leaves the matrix, `Gw` and `Fl` stored. -/
theorem shExc_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) {z : ℂ} {p : ℝ}
    (hZ : m.store.readBlock L 0 2 = some [z.re, z.im]) (hRt : m.store.get (L + 1) 0 = some p)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + (excNet ε).length ≤ ns)
        (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shExc (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length]
          [a, (L, 0), wr, ww, wp, g, thr, (L + 1, 0),
        (L + 2, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), (L + 10, 0), a,
        (L + 11, 0), f, lg])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock (L + 2) 0 1 ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 10) 0 (2 * (excNet ε).length) ⊔
          (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
            Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
              Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
              Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1))) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (excNet ε).length ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has IdxTst Q] in
/-- The decision of `Sh` terminates on any matrix: with the views and the context of `Sh`, a
stored pair at `Z`, stored words at `Rt`, `P0`, `P1` and a stored step at `T`, $1 \le k \le n$,
`NLAlib.ShiftedQR.shDecide` (accept the computed step, or the exceptional branch) leaves the
matrix and the flag stored. -/
theorem shDecide_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) {z : ℂ} {p p0 p1 : ℝ}
    (hZ : m.store.readBlock L 0 2 = some [z.re, z.im]) (hRt : m.store.get (L + 1) 0 = some p)
    (hP0 : m.store.get (L + 3) 0 = some p0) (hP1 : m.store.get (L + 4) 0 = some p1)
    (hT : HoldsMatrix (L + 5, 0) H' m.store)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store)
        (hj : LL.length + (1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length]
          [a, (L, 0), wr, ww, wp, g, thr, (L + 1, 0),
        (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0),
        (L + 9, 0), (L + 10, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The `comptau` test of `Sh` terminates on any matrix: with the views and the room of `Sh`,
from any matrix at `A`, any pair at `Z = L` and a stored word at `Cg`, $k \le n$, on a scalar
machine with exact comparisons and the literal $0$ exact, `NLAlib.ShiftedQR.shTestStep` leaves
the step at `T = L + 5` and the words at `P0 = L + 3`, `P1 = L + 4` stored. -/
theorem shTestStep_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k : ℕ} (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    (hr : ShRoom L n k ε f m) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {z : ℂ} {cg : ℝ}
    (hA : HoldsMatrix a H m.store) (hZ : m.store.readBlock L 0 2 = some [z.re, z.im])
    (hcg : m.store.get wg.1 wg.2 = some cg)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + 1 ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shTestStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length]
          [a, (L, 0), wg, (L + 5, 0), (L + 6, 0), (L + 3, 0), (L + 4, 0), lg])
      (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
        Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix (L + 5, 0) H' m'.store) ∧ (∃ x, m'.store.get (L + 3) 0 = some x) ∧
        ∃ x, m'.store.get (L + 4) 0 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ 1 ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has DiskSampleOp O] in
/-- The start of `Sh` terminates on any matrix: from the context `NLAlib.ShiftedQR.ShCtx` (any
matrix, shifts and words), $k = 2^q \le n$, on a scalar machine with exact comparisons, index
literals, index conversion and exact natural literals up to $n + 1$, the potential, `Find` and
the `comptau` test (`NLAlib.ShiftedQR.shPrefix`) keep the context and leave the pair `Z`, the
words `Rt`, `P0`, `P1` and the step `T` stored. -/
theorem shPrefix_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + 1 ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shPrefix (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, w, LL.length]
          [a, s, wg, (L, 0), (L + 1, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0),
        (L + 6, 0), lg])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock L 0 2 ⊔
        (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
          Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m' ∧
        (∃ z : ℂ, m'.store.readBlock L 0 2 = some [z.re, z.im]) ∧
        (∃ x, m'.store.get (L + 1) 0 = some x) ∧ (∃ x, m'.store.get (L + 3) 0 = some x) ∧
        (∃ x, m'.store.get (L + 4) 0 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix (L + 5, 0) H' m'.store ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ 1 ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

/-- `Sh` with scratch terminates on any matrix: from the views and the context of `Sh` (any
matrix, shifts and words), $1 \le k = 2^q \le n$, on a scalar machine with exact comparisons,
index literals, index conversion, exact natural literals up to $n + 1$ and an exact polar
sampler, `NLAlib.ShiftedQR.shStepWithScratch` leaves the matrix and the flag stored. -/
theorem shStepWithScratch_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ}
    {L k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store)
        (hj : LL.length + (1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (shStepWithScratch (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, s, wg, wr, ww, wp, g, thr, (L, 0),
        (L + 1, 0), (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0),
        (L + 8, 0), (L + 9, 0), (L + 10, 0), (L + 11, 0), a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

/-- **`Sh` terminates on any matrix** ([BanksGarzaVargasSrivastava2022, Lemma 5.4]): on a scalar
machine with exact comparisons, index literals, index conversion, exact natural literals up to
$n + 1$ and an exact polar sampler, for $k = 2^q \le n$, from any matrix of order $n + 1$ at `a`,
any $2k$ shift words at `s`, any words at `wg`, `wr`, `ww`, `wp`, `thr`, the net words of
`NLAlib.ShiftedQR.excNet ε` at `g` and room for the flag, all views live, the matrix and the
flag apart from each other and from the input words, `NLAlib.ShiftedQR.shStep` writes only the
matrix and the flag and leaves both stored, on every tape. -/
theorem shStep_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ}
    {k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} {cg cr cw cp tv : ℝ}
    (hl : m.Live [a, s, wg, wr, ww, wp, g, thr, f]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    (hwg : m.store.get wg.1 wg.2 = some cg) (hwr : m.store.get wr.1 wr.2 = some cr)
    (hww : m.store.get ww.1 ww.2 = some cw) (hwp : m.store.get wp.1 wp.2 = some cp)
    (hg : m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im]))
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrf : f.2 < m.store.len f.1)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store)
        (hj : LL.length + (1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) :
    Writes .total I τ (shStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, s, wg, wr, ww, wp, g, thr, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

end Sh

end NLAlib.ShiftedQR
