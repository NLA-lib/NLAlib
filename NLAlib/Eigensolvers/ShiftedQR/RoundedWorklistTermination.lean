/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward

/-!
# The rounded deflation worklist always terminates

The termination-only counterpart of `NLAlib.ShiftedQR.solveRounded_backward`: on every tape and
from every stored matrix, `NLAlib.ShiftedQR.solveRounded` runs to completion when its decoupler
and its leaf do (`NLAlib.ShiftedQR.TerminatingDecoupler`, `NLAlib.ShiftedQR.TerminatingLeaf`).
The proof follows the backward-error proof round by round with a value-free state: the views keep
their geometry, every word read is stored, and the stack holds nonempty ranges inside the order
whose sizes sum to at most the order, which leaves room for the two pushes of a split. The fuel
of the loop makes the run finite.

## Main definitions

* `NLAlib.ShiftedQR.RangesFit`: nonempty ranges inside the order, of total size at most it.
* `NLAlib.ShiftedQR.RoundedStoredState`: the value-free state between two rounds.

## Main results

* `NLAlib.ShiftedQR.roundedWorklistRound_terminates`: one round keeps the value-free state.
* `NLAlib.ShiftedQR.solveRounded_terminates`: the rounded worklist terminates.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- The ranges $(lo_j, d_j)$ fit in the order $N$: each has $d_j \ge 1$ and $lo_j + d_j \le N$,
and $\sum_j d_j \le N$. -/
def RangesFit (N : ℕ) (rs : List (ℕ × ℕ)) : Prop :=
  (∀ r ∈ rs, 1 ≤ r.2 ∧ r.1 + r.2 ≤ N) ∧ (rs.map Prod.snd).sum ≤ N

/-- If the ranges $(lo, d) :: rs$ fit in the order $N$ (each nonempty and inside, sizes summing
to at most $N$), then the number of ranges of $rs$ plus $d$ is at most $N$. -/
theorem RangesFit.length_add_le {N lo d : ℕ} {rs : List (ℕ × ℕ)}
    (h : RangesFit N ((lo, d) :: rs)) : rs.length + d ≤ N := by
  have hl := List.length_le_sum_of_one_le (rs.map Prod.snd) (by
    intro i hi
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
    exact (h.1 r (List.mem_cons_of_mem _ hr)).1)
  have hs := h.2
  simp only [List.length_map, List.map_cons, List.sum_cons] at hl hs
  omega

/-- If the ranges $x :: rs$ fit in the order $N$, so do the ranges $rs$. -/
theorem RangesFit.of_cons {N : ℕ} {x : ℕ × ℕ} {rs : List (ℕ × ℕ)} (h : RangesFit N (x :: rs)) :
    RangesFit N rs := by
  refine ⟨fun r hr => h.1 r (List.mem_cons_of_mem _ hr), ?_⟩
  have hs := h.2
  simp only [List.map_cons, List.sum_cons] at hs
  omega

/-- If the ranges $rs$ followed by $x$ fit in the order $N$, so do the ranges $x :: rs$. -/
theorem RangesFit.cons_of_concat {N : ℕ} {x : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    (h : RangesFit N (rs ++ [x])) : RangesFit N (x :: rs) := by
  refine ⟨fun r hr => h.1 r ?_, ?_⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    exacts [List.mem_append_right _ (List.mem_singleton_self _), List.mem_append_left _ hr]
  · have hs := h.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hs ⊢
    omega

/-- If the ranges $(lo, d) :: rs$ fit in the order $N$ and $i + 1 < d$, then so do the ranges
$rs$ followed by the two children $(lo + i + 1, d - i - 1)$ and $(lo, i + 1)$ of the split. -/
theorem RangesFit.split {N lo d i : ℕ} {rs : List (ℕ × ℕ)} (h : RangesFit N ((lo, d) :: rs))
    (hi : i + 1 < d) : RangesFit N (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) := by
  have h0 := h.1 (lo, d) List.mem_cons_self
  dsimp only at h0
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact h.1 r (List.mem_cons_of_mem _ hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega
  · have hs := h.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hs ⊢
    omega

/-- The part of `NLAlib.ShiftedQR.RoundedStoredState` that a round changes: the failure word is
stored, some matrix of order $n + 1$ is stored at `a`, and the stack at `st` holds ranges that
fit in the order $n + 1$ (`NLAlib.ShiftedQR.RangesFit`). -/
def RoundedStoredCore (n : ℕ) (a st f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  (∃ x, μ.store.get f.1 f.2 = some x) ∧
    (∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A μ.store) ∧
    ∃ rs, StackHolds st rs μ.store ∧ RangesFit (n + 1) rs

/-- **The value-free state of the rounded worklist** of order $n + 1$ with the parameter words
`ps`: the eight views keep the geometry of `NLAlib.ShiftedQR.RoundedGeometry`, the threshold word
is stored, the parameter words are `ps`, the failure word is stored, some matrix is stored at `a`,
and the stack holds ranges that fit in the order (`NLAlib.ShiftedQR.RangesFit`). -/
def RoundedStoredState (n : ℕ) (ps : List ℝ) (a t p st out w r f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  RoundedGeometry (n + 1) ps.length a t p st out w r f μ ∧ (∃ x, μ.store.get t.1 t.2 = some x) ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧ RoundedStoredCore n a st f μ

/-- From the geometry of the rounded worklist with the threshold and parameter words stored at
`μ`, a write inside the round footprint to `μ'` keeps them, so the core
`NLAlib.ShiftedQR.RoundedStoredCore` at `μ'` gives the full value-free state at `μ'`. -/
theorem RoundedStoredState.of_core {n : ℕ} {ps : List ℝ} {a t p st out w r f : ℕ × ℕ}
    {μ μ' : Mem ℝ} {F : Fp} (h : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (ht : ∃ x, μ.store.get t.1 t.2 = some x)
    (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfr : μ.store.EqOff F μ'.store) (hF : F ≤ roundedWorklistFp (n + 1) a st out w r f)
    (hcore : RoundedStoredCore n a st f μ') :
    RoundedStoredState n ps a t p st out w r f μ' := by
  have hd := h.disj_params.mono hF le_rfl
  obtain ⟨x, hx⟩ := ht
  exact ⟨h.of_eqOff hfr, ⟨x, hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_left) hx⟩,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hd.mono le_rfl le_sup_right) hp, hcore⟩

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The abort keeps the value-free core: on a machine whose natural literals up to $n + 1$
are exact, from the geometry of the rounded worklist of order $n + 1$ with some matrix stored at
`a`, `roundedAbort` writes the failure word and the stack count and leaves the core
`NLAlib.ShiftedQR.RoundedStoredCore` (an empty stack). -/
theorem roundedAbort_writes_core {M : Machine ℝ} {I : Interp O Q ℝ} (hL : IsIndexLit M I) {n : ℕ}
    (hN : IsExactNatLit id M (n + 1)) {np : ℕ} {τ : Tape ℝ} {m : Mem ℝ}
    {a t p st out w r f : ℕ × ℕ} (hG : RoundedGeometry (n + 1) np a t p st out w r f m)
    (hA : ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A m.store) :
    Writes .total I τ (roundedAbort (O := O) (Q := Q)).body (Env.frame [] [st, f])
      (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 1) (RoundedStoredCore n a st f) m := by
  obtain ⟨A, hA⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hFA, hFS, -, -, hAS, -, -, -⟩ := hG.disj_round
  refine (roundedAbort_writes hL hN (by omega) (by have := hG.room.2.2.2.1; omega)
    (by have := hG.room.2.2.2.2.2.2.2.1; omega) (hFS.mono le_rfl (by fp_sub))).mono le_rfl ?_
  rintro m' hfr ⟨h1, h0⟩
  exact ⟨⟨1, h1⟩, ⟨A, hA.of_eqOff hfr
      (Fp.disj_sup_left.mpr ⟨hFA, hAS.symm.mono (by fp_sub) le_rfl⟩)⟩,
    [], ⟨by simpa using h0, fun _ h => absurd h (by simp)⟩, by simp [RangesFit]⟩

/-- The large branch after the decoupling call terminates: on a scalar machine whose natural
literals up to $n + 1$ are exact, with exact `toNat` and comparisons, from the geometry of the
rounded worklist of order $n + 1$ with a threshold word, any failure word $x$, a matrix stored at
`a`, any matrix $\mathbf{H}'$ of order $d + 1 \ge k + 1$ in the work matrix, and a stack whose
ranges after the popped $(lo, d + 1)$ fit in the order (`NLAlib.ShiftedQR.RangesFit`), the rest of
`NLAlib.ShiftedQR.roundedProcessLarge` (abort, or scan and split or abort) runs to completion and
leaves the core `NLAlib.ShiftedQR.RoundedStoredCore`. -/
theorem roundedLargeRest_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q) {tape : Tape ℝ} {μ₁ : Mem ℝ}
    {lo d : ℕ} {a t p st out w r f : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {x thr : ℝ} (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ₁)
    (ht : μ₁.store.get t.1 t.2 = some thr) (hf : μ₁.store.get f.1 f.2 = some x)
    (hA : HoldsMatrix a A μ₁.store) (hW : HoldsMatrix w H' μ₁.store)
    (hSt : StackHolds st rs μ₁.store) (hfit : RangesFit (n + 1) ((lo, d + 1) :: rs))
    (hk : k ≤ d) :
    Writes .total I tape (roundedLargeRest D)
      (Env.frame [n + 1, k, ps.length, F, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f) (RoundedStoredCore n a st f) μ₁ := by
  have hfit0 := hfit.1 _ List.mem_cons_self
  have hlen := hfit.length_add_le
  dsimp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWw : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  obtain ⟨hWA, -, -, -, -, -, hRA, hRT, hRS, -, hRF, hRW, hFA, hFS, -, -, hAS, -, -, -⟩ :=
    hG.disj_round
  have hlSF : μ₁.Live [st, f] := hG.live_of_subset (by simp)
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hf) ?_
  by_cases hx : 0 < x
  · rw [if_pos (by simpa using hx)]
    exact ((roundedAbort_writes_core hL hNat hG ⟨A, hA⟩).in_frame rfl rfl hlSF).mono
      (by fp_sub [roundedWorklistFp]) fun _ _ h => h
  rw [if_neg (by simpa using hx)]
  have hlS : μ₁.Live [w, t, r] := hG.live_of_subset (by simp)
  have hb := bottomScan_terminates (τ := tape) (n := d) (k := k) hS hL (hNat.mono (by omega)) hC
    hk hW ht hlS hG.room.2.2.2.2.2.2.1 (hRW.mono le_rfl hWw) hRT
  refine (hb.in_frame rfl rfl hlS).seq_le (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hscan⟩
  have hG₂ := hG.of_eqOff hfr₂
  have hA₂ := hA.of_eqOff hfr₂ hRA
  rcases hscan with ⟨hR1, i, hRi⟩ | ⟨hR0, -⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR1) ?_
    rw [if_pos (by simp)]
    have hi := i.isLt
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hRi rfl (by omega) ?_
    have hlASW : μ₂.Live [a, st, w] := hG₂.live_of_subset (by simp)
    have hsplit := writeAndSplit_writes_mem (O := O) (Q := Q) (τ := tape) (i := (i : ℕ)) hS hL
      hQ hNat hlASW hA₂ (hW.of_eqOff hfr₂ (hRW.mono le_rfl hWw))
      (hSt.of_eqOff hfr₂ (hRS.mono le_rfl (by fp_sub))) hfit0.2 (by omega) (by omega)
      hG₂.room.1 hG₂.room.2.2.2.1 (hWA.mono hWw le_rfl) hAS
    refine (hsplit.in_frame rfl rfl hlASW).mono (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₃ hfr₃ ⟨-, hA₃, hSt₃⟩
    exact ⟨⟨x, (hfr₂.trans' hfr₃).keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨hRF, Fp.disj_sup_left.mpr ⟨hFA.symm, hFS.symm⟩⟩) hf⟩, ⟨_, hA₃⟩,
      _, hSt₃, hfit.split (by omega)⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR0) ?_
    rw [if_neg (by simp)]
    exact ((roundedAbort_writes_core hL hNat hG₂ ⟨A, hA₂⟩).in_frame rfl rfl
      (hG₂.live_of_subset (by simp))).mono (by fp_sub [roundedWorklistFp]) fun _ _ h => h

/-- The large branch terminates: on a scalar machine whose natural literals up to $n + 1$
are exact, with exact `toNat` and comparisons and a terminating decoupler
(`NLAlib.ShiftedQR.TerminatingDecoupler`) of bottom width $k \le d$, from the geometry of the
rounded worklist of order $n + 1$ with the threshold and parameter words stored, any failure
word, a matrix $\mathbf{A}$ stored at `a` whose block on $(lo, d + 1)$ is in the work matrix, and
a stack whose ranges after $(lo, d + 1)$ fit in the order, `NLAlib.ShiftedQR.roundedProcessLarge`
runs to completion and leaves the core `NLAlib.ShiftedQR.RoundedStoredCore`. -/
theorem roundedLarge_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q)
    (hD : TerminatingDecoupler n k F ps D I) {tape : Tape ℝ} {μ : Mem ℝ}
    {lo d : ℕ} {a t p st out w r f : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix w (subBlock A (lo, d + 1)) μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d + 1) :: rs))
    (hk : k ≤ d) :
    Writes .total I tape (roundedProcessLarge D).body
      (Env.frame [n + 1, k, ps.length, F, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f) (RoundedStoredCore n a st f) μ := by
  have hfit0 := hfit.1 _ List.mem_cons_self
  have hlen := hfit.length_add_le
  dsimp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWw : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  obtain ⟨hWA, hWT, hWP, hWS, -, hWF, -, -, -, -, -, -, hFA, hFS, -, hFT, -, -, -, hPF⟩ :=
    hG.disj_round
  have hlD : μ.Live [w, p, w, f] := hG.live_of_subset (by simp)
  have hw := hD (tape := tape) (subBlock A (lo, d + 1)) hk (by omega) hW hp hlD
    (by have := hG.room.2.2.2.2.2.1; omega) hG.room.2.2.2.2.2.2.2.1 (hWF.mono hWw le_rfl)
    (Fp.disj_sup_right.mpr ⟨hWP.symm.mono le_rfl hWw, hPF⟩)
  unfold roundedProcessLarge
  refine hw.frame_seq_le rfl rfl hlD (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨⟨x, hf₁⟩, H', hW₁⟩
  have hDfp : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 :=
    sup_le_sup_right hWw _
  exact roundedLargeRest_terminates hS hL hNat hQ hC D (hG.of_eqOff hfr₁)
    (hfr₁.keep (Store.readsOnly_get _ _ _)
      ((Fp.disj_sup_left.mpr ⟨hWT, hFT⟩).mono hDfp le_rfl) ht) hf₁
    (hA.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWA, hFA⟩).mono hDfp le_rfl)) hW₁
    (hSt.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWS, hFS⟩).mono hDfp (by fp_sub))) hfit hk

/-- Processing a popped range terminates: on a scalar machine whose natural literals up to
$n + 1$ are exact, with exact `toNat` and comparisons, a terminating decoupler
(`NLAlib.ShiftedQR.TerminatingDecoupler`) of bottom width $k$ and a terminating leaf
(`NLAlib.ShiftedQR.TerminatingLeaf`), from the geometry of
the rounded worklist of order $n + 1$ with the threshold and parameter words and the failure word
stored, a matrix $\mathbf{A}$ stored at `a`, and a stack whose ranges after the popped $(lo, d)$
fit in the order, `NLAlib.ShiftedQR.roundedProcessRange` runs to completion and leaves the core
`NLAlib.ShiftedQR.RoundedStoredCore`. -/
theorem roundedRange_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q)
    (hD : TerminatingDecoupler n k F ps D I) (L : Impl O Q) (hLeaf : TerminatingLeaf L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {lo d : ℕ} {a t p st out w r f : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr x : ℝ}
    (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hf : μ.store.get f.1 f.2 = some x) (hA : HoldsMatrix a A μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d) :: rs)) :
    Writes .total I tape (roundedProcessRange D L).body
      (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f) (RoundedStoredCore n a st f) μ := by
  have hfit0 := hfit.1 _ List.mem_cons_self
  have hlen := hfit.length_add_le
  dsimp only at hfit0
  have hd : d ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWfp : Store.inBlock w.1 w.2 (2 * (d * d)) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  obtain ⟨hWA, hWT, hWP, hWS, hWO, hWF, -, -, -, -, -, -, -, -, hFO, -, -, hAO, hSO, -⟩ :=
    hG.disj_round
  have hlAW : μ.Live [a, w] := hG.live_of_subset (by simp)
  unfold roundedProcessRange
  refine (copyToWork_writes (τ := tape) (lo := lo) (d := d) hS hlAW hA hfit0.2
    (by have := hG.room.2.2.2.2.2.1; omega) (hWA.symm.mono le_rfl hWfp)).frame_seq_le rfl rfl
    hlAW (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hW₁⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hWF.mono hWfp le_rfl) hf
  have hA₁ := hA.of_eqOff hfr₁ (hWA.mono hWfp le_rfl)
  have hSt₁ := hSt.of_eqOff hfr₁ (hWS.mono hWfp (by fp_sub))
  by_cases hs : d ≤ k
  · refine (writes_ifPos (P := RoundedStoredCore n a st f) (n := k + 1 - d) rfl ?_).seq_le
      le_rfl ?_
    · rw [if_pos (by omega)]
      have hl : μ₁.Live [w, (out.1, out.2 + 2 * lo)] := by
        simpa [Mem.Live] using And.intro (hG₁.live w (by simp)) (hG₁.live out (by simp))
      have hOfp : Store.inBlock out.1 (out.2 + 2 * lo) (2 * d) ≤
          Store.inBlock out.1 out.2 (2 * (n + 1)) := by fp_sub
      refine ((hLeaf (subBlock A (lo, d)) hW₁ hl
        (by dsimp only; have := hG₁.room.2.2.2.2.1; omega)
        (hWO.mono hWfp hOfp)).in_frame rfl rfl hl).mono (by fp_sub [roundedWorklistFp]) ?_
      rintro μ₂ hfr₂ -
      exact ⟨⟨x, hfr₂.keep (Store.readsOnly_get _ _ _) (hFO.symm.mono hOfp le_rfl) hf₁⟩,
        ⟨A, hA₁.of_eqOff hfr₂ (hAO.symm.mono hOfp le_rfl)⟩, rs,
        hSt₁.of_eqOff hfr₂ (hSO.symm.mono hOfp (by fp_sub)), hfit.of_cons⟩
    · intro μ₂ _ hpost
      refine writes_ifPos (n := d - k) rfl ?_
      rw [if_neg (by omega)]
      exact hpost
  · refine (writes_ifPos (F := ⊥) (P := fun μ₂ => μ₂ = μ₁) (n := k + 1 - d) rfl
      (by rw [if_neg (by omega)])).seq_le bot_le ?_
    rintro μ₂ - rfl
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine writes_ifPos (n := d' + 1 - k) rfl ?_
    rw [if_pos (by omega)]
    exact (roundedLarge_terminates hS hL hNat hQ hC D hD hG₁
      (hfr₁.keep (Store.readsOnly_get _ _ _) (hWT.mono hWfp le_rfl) ht)
      (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hWP.mono hWfp le_rfl) hp) hA₁ hW₁ hSt₁
      hfit (by omega)).in_frame rfl rfl hG₁.live

/-- One round keeps the value-free state: on a scalar machine whose natural literals up to
$n + 1$ are exact, with exact `toNat` and comparisons, a terminating decoupler
(`NLAlib.ShiftedQR.TerminatingDecoupler`) and a terminating leaf
(`NLAlib.ShiftedQR.TerminatingLeaf`), from the value-free state
`NLAlib.ShiftedQR.RoundedStoredState` of order $n + 1$ with a positive stack count, the round
`NLAlib.ShiftedQR.roundedWorklistRound` runs to completion and reaches the value-free state. -/
theorem roundedWorklistRound_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q)
    (hD : TerminatingDecoupler n k F ps D I) (L : Impl O Q) (hLeaf : TerminatingLeaf L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p st out w r f : ℕ × ℕ} {cnt : ℕ}
    (h : RoundedStoredState n ps a t p st out w r f μ)
    (hcount : μ.store.get st.1 st.2 = some (cnt : ℝ)) (hpos : 0 < cnt) :
    Writes .total I tape (roundedWorklistRound D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (RoundedStoredState n ps a t p st out w r f) μ := by
  obtain ⟨hG, ⟨thr, ht⟩, hp, ⟨x, hf⟩, ⟨A, hA⟩, rs, hSt, hfit⟩ := h
  refine Writes.mono (P := RoundedStoredCore n a st f) ?_ le_rfl
    (fun μ' hfr hcore => RoundedStoredState.of_core hG ⟨thr, ht⟩ hp hfr le_rfl hcore)
  obtain rfl | ⟨rs', ⟨lo, d⟩, rfl⟩ := List.eq_nil_or_concat rs
  · have hc0 : (cnt : ℝ) = 0 := Option.some.inj (hcount.symm.trans (by simpa using hSt.1))
    exact absurd (by exact_mod_cast hc0 : cnt = 0) (by omega)
  rw [List.concat_eq_append] at hfit hSt
  have hfit' := hfit.cons_of_concat
  have hfit0 := hfit'.1 _ List.mem_cons_self
  have hlen := hfit'.length_add_le
  dsimp only at hfit0
  have hRS : Fp.Disj (Store.inBlock r.1 r.2 2) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    (by simpa using hG.disj 6 3 (by simp) : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono (by fp_sub) le_rfl
  have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
  unfold roundedWorklistRound
  refine (rangePop_writes_of_isExactNatLit (τ := tape) hS hL hQ hNat hSt (by omega)
    (by simpa only [Nat.add_assoc] using hG.room.2.2.2.1)
    (by have := hG.room.2.2.2.2.2.2.1; omega) hlSR hRS).frame_seq_le rfl rfl hlSR
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hSt₁, hRange⟩
  have hpop : Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2 ≤
      roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
  have hpar := hG.disj_params.mono hpop le_rfl
  have hpd {X : Fp} (h1 : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) X)
      (h2 : Fp.Disj (Store.inBlock r.1 r.2 5) X) :
      Fp.Disj (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2) X :=
    Fp.disj_sup_left.mpr ⟨h1.mono (by fp_sub) le_rfl, h2.mono (by fp_sub) le_rfl⟩
  have hLo : μ₁.store.get r.1 r.2 = some (lo : ℝ) := by
    simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
  have hSize : μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ) := by
    simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hLo rfl (by omega) ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hSize rfl (by omega) ?_
  have hG₁ := hG.of_eqOff hfr₁
  exact (roundedRange_terminates hS hL hNat hQ hC D hD L hLeaf hG₁
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hpar.mono le_rfl le_sup_left) ht)
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hpar.mono le_rfl le_sup_right) hp)
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hpd (by simpa using hG.disj 3 7 (by simp))
      (by simpa using hG.disj 6 7 (by simp))) hf)
    (hA.of_eqOff hfr₁ (hpd (by simpa using hG.disj 3 0 (by simp))
      (by simpa using hG.disj 6 0 (by simp)))) hSt₁ hfit').in_frame rfl rfl hG₁.live

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of the capped loop terminates: on a machine whose natural literals up to
$n + 1$ are exact, with exact comparisons, from the value-free state
`NLAlib.ShiftedQR.RoundedStoredState` of order $n + 1$, the exit of
`NLAlib.ShiftedQR.roundedWorklist` (abort on a positive stack count, else skip) runs to
completion, at any round `i`. -/
theorem roundedWorklistExit_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    {k F : ℕ} {ps : List ℝ} {tape : Tape ℝ} {μ : Mem ℝ} {a t p st out w r f : ℕ × ℕ} (i : ℕ)
    (h : RoundedStoredState n ps a t p st out w r f μ) :
    Writes .total I tape (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 3, off := IExp.var 7 }]
        (Stmt.frame [] [{ buf := 3, off := IExp.var 7 }, { buf := 7, off := IExp.var 11 }]
          (roundedAbort (O := O) (Q := Q)).body) Stmt.skip)
      ((Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f]).pushIdx i)
      (roundedWorklistFp (n + 1) a st out w r f) (fun _ => True) μ := by
  obtain ⟨hG, -, -, -, hA, rs, hSt, -⟩ := h
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) hSt.1) ?_
  by_cases hpos : 0 < rs.length
  · rw [if_pos (by simpa using hpos)]
    exact ((roundedAbort_writes_core hL hNat hG hA).in_frame rfl rfl
      (hG.live_of_subset (by simp))).mono (by fp_sub [roundedWorklistFp]) fun _ _ _ => trivial
  · rw [if_neg (by simpa using hpos)]
    exact (Writes.skip trivial).mono bot_le fun _ _ h => h

/-- The capped loop of the rounded worklist terminates: on a scalar machine whose natural
literals up to $n + 1$ are exact, with exact `toNat` and comparisons, a terminating decoupler
(`NLAlib.ShiftedQR.TerminatingDecoupler`) and a terminating leaf
(`NLAlib.ShiftedQR.TerminatingLeaf`), from the geometry of the rounded worklist of order $n + 1$
(`NLAlib.ShiftedQR.RoundedGeometry`) with any matrix $\mathbf{H}$ stored at `a`, the threshold
word stored and the parameter words `ps`, `NLAlib.ShiftedQR.roundedWorklist` runs to completion
within the round footprint. -/
theorem roundedWorklist_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q)
    (hD : TerminatingDecoupler n k F ps D I) (L : Impl O Q) (hLeaf : TerminatingLeaf L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p st out w r f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (hA : HoldsMatrix a H μ.store) (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (roundedWorklist D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f) (fun _ => True) μ := by
  obtain ⟨hFA, hFS⟩ : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧ Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    ⟨by simpa using hG.disj 7 0 (by simp), by simpa using hG.disj 7 3 (by simp)⟩
  have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 3 0 (by simp)
  unfold roundedWorklist
  refine (writes_indexLit hL rfl rfl (by have := hG.room.2.2.2.2.2.2.2.1; dsimp only; omega)).seq_le
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hF₁⟩
  have hlS : μ₁.Live [st] := (hG.of_eqOff hfr₁).live_of_subset (by simp)
  have hw := stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := tape) hL hQ hNat
    (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
    (by simpa only [Nat.add_assoc] using (hG.of_eqOff hfr₁).room.2.2.2.1)
  refine hw.frame_seq_le rfl rfl hlS (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hSt₂⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  have h01 : Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 (1 + 2 * (n + 1)) ≤
      roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
  have hS0 : RoundedStoredState n ps a t p st out w r f μ₂ :=
    RoundedStoredState.of_core hG ⟨thr, ht⟩ hp hfr₁₂ h01
      ⟨⟨_, hfr₂.keep (Store.readsOnly_get _ _ _) hFS.symm hF₁⟩,
        ⟨H, hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩)⟩, [(0, n + 1)], hSt₂,
        by simp [RangesFit]⟩
  refine (writes_whileFuel (N := 2 * (n + 1)) rfl
    (fun _ => roundedWorklistFp (n + 1) a st out w r f) (fun _ _ => le_rfl)
    (roundedWorklistFp (n + 1) a st out w r f)
    (fun _ => RoundedStoredState n ps a t p st out w r f) (fun _ => True) hS0 ?_
    (fun _ _ hS' => roundedWorklistExit_terminates hL hNat hC _ hS')).mono (by simp)
    fun _ _ h => h
  intro i _ μ' _ hS'
  obtain ⟨rs, hSt, -⟩ := hS'.2.2.2.2.2
  rw [Interp.testAt_eq rfl rfl, hC.test_isPos hSt.1]
  refine Mode.holds_some ?_
  by_cases hpos : 0 < rs.length
  · rw [if_pos (by simpa using hpos)]
    exact (roundedWorklistRound_terminates hS hL hNat hQ hC D hD L hLeaf hS' hSt.1
      hpos).in_frame rfl rfl hS'.1.live
  · rw [if_neg (by simpa using hpos)]
    exact roundedWorklistExit_terminates hL hNat hC i hS'

/-- The rounded deflation worklist terminates: on a scalar machine whose natural literals up
to $n + 1$ are exact (the stack, the flags and the indices are such literals), with exact `toNat`
and comparisons, let the decoupler `D` terminate with the bottom width $k$, the iteration cap $F$
and the parameter words `ps` (`NLAlib.ShiftedQR.TerminatingDecoupler`) and the leaf routine `L`
terminate (`NLAlib.ShiftedQR.TerminatingLeaf`). Then for any matrix $\mathbf{H}$ of order
$n + 1$ stored at `a` (no structure assumed), any threshold word and on every tape,
`solveRounded D L` runs to completion and writes only the matrix, the output and the failure
word. The views are live, have room and are pairwise apart. Nothing numerical is assumed. -/
theorem solveRounded_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) {k F : ℕ} {ps : List ℝ} (D : Impl O Q)
    (hD : TerminatingDecoupler n k F ps D I) (L : Impl O Q) (hLeaf : TerminatingLeaf L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p out f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (solveRounded D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun _ => True) μ := by
  unfold solveRounded
  refine writes_allocs_preserving_post
    (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0), .const 5])
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 5]) rfl (fun _ _ => trivial) ?_
  intro s hs hlens hBelow
  have hG := roundedGeometry_allocated (np := ps.length) hl hr ha hs hlens hBelow
  have hw := roundedWorklist_terminates hS hL hNat hQ hC D hD L hLeaf (tape := tape) hG
    (hA.of_below hBelow (hl a (by simp))) (hBelow.get_of (hl t (by simp)) ht)
    ((hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp)
  exact (hw.in_frame rfl rfl hG.live).mono (by fp_sub [roundedWorklistFp]) fun _ _ h => h

end Theorems

end NLAlib.ShiftedQR
