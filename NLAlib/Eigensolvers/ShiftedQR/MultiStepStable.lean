/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.StableStep

/-!
# The rounded multishift QR step as a stable chain

The degree $k$ rounded step `NLAlib.ShiftedQR.multiStepStable` repeats the rounded single-shift step
`NLAlib.ShiftedQR.stepWithDiagInPlace` in place with the $k$ shifts of a stored list, all its
rotations recorded in one slot of the log. By the single steps it is a chain of backward-stable
steps (`NLAlib.ShiftedQR.IsStableQRChainBy`) by the unitary of its log.

## Main results

* `NLAlib.ShiftedQR.multiStepStable_isStableQRChainBy`: the degree $k$ step is a stable chain by
  the unitary of its log; `NLAlib.ShiftedQR.multiStepStable_isStableQRChain` without it.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix
variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- The words of entry `j` of a list of complex numbers stored as interleaved pairs. -/
private theorem take_drop_flatMap_pair (ss : List ℂ) {j : ℕ} (hj : j < ss.length) :
    ((ss.flatMap fun z => [z.re, z.im]).drop (2 * j)).take 2 = [ss[j].re, ss[j].im] := by
  induction ss generalizing j with
  | nil => simp at hj
  | cons z zs ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatMap_cons, show 2 * (j + 1) = 2 + 2 * j by ring, ← List.drop_drop]
      simpa using ih (by simpa using hj)

/-- **The degree $k$ rounded step is a stable chain by its recorded unitary** (the setting of
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): on a machine with the standard model at
$\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and the shifts $s_1, \dots, s_k$ stored as $2k$ words, the program
`multiStepStable` appends $kn$ entries (planes below $n$) to the pending slot $j$ of the log
(empty before, `P = []`), stores in place an $\widehat{\mathbf{H}}'$, and in `Ds` the last diagonal
entries of triangular factors $\widehat{\mathbf{R}}_1, \dots, \widehat{\mathbf{R}}_k$, such that
the steps form a backward-stable chain with relative error $x = 300(n+1)^2\boldsymbol{u}$ by the
exact unitary `givensLog (n + 1) es` of the entries. The matrix, the shifts, the diagonal outputs
and the log are pairwise disjoint views. -/
theorem multiStepStable_isStableQRChainBy {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s ds lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns)
    (hw : ss.length * n ≤ w)
    (hl : m.Live [a, s, ds, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) =
      some (ss.flatMap fun z => [z.re, z.im]))
    (hd : ds.2 + 2 * ss.length ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock ds.1 ds.2 (2 * ss.length))) :
    Writes .total I τ multiStepStable.body
      (Env.frame [n + 1, ss.length, w, L.length] [a, s, a, ds, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ds.1 ds.2 (2 * ss.length) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = ss.length * n ∧
        (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L es m'.store ∧
        ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
          IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H ss H' Rs (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
          m'.store.readBlock ds.1 ds.2 (2 * ss.length) =
            some (Rs.flatMap fun R =>
              [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im])) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ ds.1 < m.store.length ∧
      lg.1 < m.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨hp, es, hes, hpl, hlog', H', Rs, hc, hH', hA', hD'⟩ => ⟨hp, es, hes, hpl,
      hlog'.of_below hBelow hlive.2.2.2, H', Rs, hc, hH', hA'.of_below hBelow hlive.1,
      hBelow.readBlock_of hlive.2.2.1 hD'⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by simpa [t] using hlens 0 (by simp)
  have hne : ∀ {b o k : ℕ} {b' o' k' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') := fun h => Fp.disj_inBlock_of_ne h
  have htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)) := hne (by dsimp [t]; omega)
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * ss.length) ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))
  have hFs : Fp.Disj F (Store.inBlock s.1 s.2 (2 * ss.length)) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has,
      hne (by dsimp [t]; omega)⟩, hsd.symm⟩,
      (hlgd.mono le_rfl (le_sup_right.trans le_sup_left))⟩
  refine (writes_loop (m := ⟨store, m.pos⟩) (n := .var 1) (N := ss.length) rfl (fun _ => F)
    (fun _ _ => le_rfl)
    (fun j μ => μ.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = j * n ∧
      (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L es μ.store ∧
      ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (ss.take j) H' Rs (givensLog (n + 1) es) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' μ.store ∧
        μ.store.readBlock ds.1 ds.2 (2 * j) = some (Rs.flatMap fun R =>
          [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]))
    ⟨rfl, [], by simp, by simp, hlog.of_below hBelow hlive.2.2.2, H, [],
      by simpa using IsStableQRChainBy.nil (x := 300 * (n + 1) ^ 2 * u) H, hH,
      hA.of_below hBelow hlive.1, by simp⟩ ?_).mono
    (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (Fp.inBlock_le_sup_above le_rfl)) (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      (le_sup_right.trans le_sup_left)) ?_
  · intro j hjk μ hfr ⟨hp, es, hes, hpl, hlogj, Hj, Rs, hc, hHj, hAj, hDj⟩
    have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hFs
      ((hBelow.readBlock hlive.2.1 _ _).trans hs)
    have hsj : μ.store.readBlock s.1 (s.2 + 2 * j) 2 = some [ss[j].re, ss[j].im] := by
      rw [Store.readBlock_sub hsμ (by omega), take_drop_flatMap_pair ss hjk]
    have hdg : Store.inBlock ds.1 (ds.2 + 2 * j) 2 ≤ Store.inBlock ds.1 ds.2 (2 * ss.length) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hsg : Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * ss.length) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hpre : Store.inBlock ds.1 ds.2 (2 * j) ≤ Store.inBlock ds.1 ds.2 (2 * ss.length) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hlμ : μ.Live [a, (s.1, s.2 + 2 * j), t, a, (ds.1, ds.2 + 2 * j), lg] := by
      simp [Mem.Live, hfr.length_eq, t, hlen]; omega
    have hwj : es.length + n ≤ w := by rw [hes]; nlinarith [Nat.mul_le_mul_right n hjk]
    have hstep := stepWithDiagInPlace_isStableQRStep (τ := τ) (m := μ) (t := t)
      (s := (s.1, s.2 + 2 * j)) (dg := (ds.1, ds.2 + 2 * j)) (P := es) hS hM hu hCmp hL hNat
      hHj hnu hn hlogj hj hwj (hlμ.mono (by simp)) hAj hsj
      (by rw [hfr.len_eq]; dsimp [t]; simpa only [Nat.zero_add] using ht.ge)
      (by dsimp only; rw [hfr.len_eq, (hBelow ds.1 hlive.2.2.1).1]; omega)
      (hne (by dsimp [t]; omega)) (hne (by dsimp [t]; omega)) (htd.mono le_rfl hdg)
      (had.mono le_rfl hdg)
      (Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr
        ⟨hlgd.mono le_rfl (le_sup_left.trans le_sup_left),
          hlgd.mono le_rfl (hsg.trans (le_sup_right.trans le_sup_left))⟩,
        hne (by dsimp [t]; omega)⟩, hlgd.mono le_rfl (hdg.trans le_sup_right)⟩)
    refine (hstep.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, hes]) rfl hlμ).mono
      (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        ((hdg.trans le_sup_right).trans le_sup_left)) le_sup_right) ?_
    intro μ' hfr' ⟨hp', es', hes', hpl', hlog', H', R, hR, hA', hD'⟩
    have hDj' := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨had.mono le_rfl hpre,
        htd.mono le_rfl hpre⟩, (Fp.disj_inBlock_of_le le_rfl).symm⟩,
        hlgd.mono le_rfl (hpre.trans le_sup_right)⟩) hDj
    refine ⟨hp'.trans hp, es ++ es', by rw [List.length_append, hes, hes']; ring, ?_, hlog', H',
      Rs ++ [R], ?_, hR.1, hA', ?_⟩
    · exact fun e he => (List.mem_append.mp he).elim (hpl e) (hpl' e)
    · rw [List.take_add_one, List.getElem?_eq_getElem hjk, Option.toList_some, givensLog_append]
      exact hc.snoc hR
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, List.flatMap_append]
      exact Store.readBlock_add hDj' hD'
  · intro μ _ ⟨hp, es, hes, hpl, hlog', H', Rs, hc, hH', hA', hD'⟩
    exact ⟨hp, es, hes, hpl, hlog', H', Rs, by simpa using hc, hH', hA', hD'⟩

/-- **The degree $k$ rounded step is a stable chain** (the setting of
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): `NLAlib.ShiftedQR.multiStepStable_isStableQRChainBy`
without the unitary. -/
theorem multiStepStable_isStableQRChain {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s ds lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns)
    (hw : ss.length * n ≤ w)
    (hl : m.Live [a, s, ds, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) =
      some (ss.flatMap fun z => [z.re, z.im]))
    (hd : ds.2 + 2 * ss.length ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock ds.1 ds.2 (2 * ss.length))) :
    Writes .total I τ multiStepStable.body
      (Env.frame [n + 1, ss.length, w, L.length] [a, s, a, ds, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ds.1 ds.2 (2 * ss.length) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H ss H' Rs ∧ IsUpperHessenberg H' ∧
          HoldsMatrix a H' m'.store ∧
          m'.store.readBlock ds.1 ds.2 (2 * ss.length) =
            some (Rs.flatMap fun R =>
              [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im])) m := by
  refine (multiStepStable_isStableQRChainBy hS hM hu hCmp hL hNat hH hnu hn hlog hj hw hl hA hs hd
    has had hsd hlgd).mono le_rfl ?_
  rintro m' - ⟨hp, es, -, -, -, H', Rs, hc, hH', hA', hD⟩
  exact ⟨hp, H', Rs, hc.isStableQRChain, hH', hA', hD⟩

end NLAlib.ShiftedQR
