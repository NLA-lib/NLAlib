/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.StableStep

/-!
# Termination of the rounded shifted QR step

The rounded single-shift step `NLAlib.ShiftedQR.stepWithDiagInPlace` and the degree $k$ step
`NLAlib.ShiftedQR.multiStepStable` terminate on every matrix and every shift words, leaving their
outputs stored, with no numerical hypothesis on the machine (only the scalar and comparison
contracts). The stored-word lemmas read complex numbers from blocks of interleaved real words.

## Main results

* `NLAlib.ShiftedQR.exists_flatMap_pair_eq`, `NLAlib.ShiftedQR.Store.exists_readBlock_flatMap_pair`,
  `NLAlib.ShiftedQR.Store.exists_readBlock_pair`,
  `NLAlib.ShiftedQR.Store.exists_readBlock_of_eqOff_sub`: stored words as complex numbers.
* `NLAlib.ShiftedQR.sweep_terminates`: the Givens sweep terminates on any matrices.
* `NLAlib.ShiftedQR.stepWithDiagInPlace_terminates`, `NLAlib.ShiftedQR.multiStepStable_terminates`:
  the single and degree $k$ steps terminate on any matrix.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-! ### Stored words -/

/-- A list of $2k$ words is the interleaved pair list of $k$ complex numbers. -/
theorem exists_flatMap_pair_eq {xs : List ℝ} {k : ℕ} (h : xs.length = 2 * k) :
    ∃ zs : List ℂ, zs.length = k ∧ (zs.flatMap fun z => [z.re, z.im]) = xs := by
  induction k generalizing xs with
  | zero => exact ⟨[], rfl, (List.length_eq_zero_iff.mp (by simpa using h)).symm⟩
  | succ k ih =>
    match xs, h with
    | x :: y :: ys, h =>
      obtain ⟨zs, hzs, hflat⟩ := ih (xs := ys) (by simp at h; omega)
      exact ⟨⟨x, y⟩ :: zs, by simp [hzs], by simp [hflat]⟩

/-- A stored block of $2k$ words holds $k$ complex numbers as interleaved pairs. -/
theorem Store.exists_readBlock_flatMap_pair {s : Store ℝ} {b off k : ℕ} {xs : List ℝ}
    (h : s.readBlock b off (2 * k) = some xs) :
    ∃ zs : List ℂ, zs.length = k ∧
      s.readBlock b off (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]) := by
  obtain ⟨zs, hzs, hflat⟩ := exists_flatMap_pair_eq (Store.length_of_readBlock h)
  exact ⟨zs, hzs, by rw [hzs, hflat, h]⟩

/-- Two stored words inside a stored block are the parts of one complex number. -/
theorem Store.exists_readBlock_pair {s : Store ℝ} {b off N o : ℕ} {xs : List ℝ}
    (h : s.readBlock b off N = some xs) (ho : o + 2 ≤ N) :
    ∃ z : ℂ, s.readBlock b (off + o) 2 = some [z.re, z.im] := by
  have hsub := Store.readBlock_sub h ho
  obtain ⟨zs, hzs, hflat⟩ := exists_flatMap_pair_eq (k := 1) (Store.length_of_readBlock hsub)
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hzs
  exact ⟨z, by rw [hsub, ← hflat]; simp⟩

/-- A stored block stays stored when a sub-block is rewritten with stored words and a write
apart from the rest of the block. -/
theorem Store.exists_readBlock_of_eqOff_sub {s s' : Store ℝ} {b off N o l : ℕ} {xs ys : List ℝ}
    {F : Fp} (h : s.readBlock b off N = some xs) (hol : o + l ≤ N) (hfr : s.EqOff F s')
    (hF : Fp.Disj F (Store.inBlock b off o ⊔ Store.inBlock b (off + o + l) (N - (o + l))))
    (hnew : s'.readBlock b (off + o) l = some ys) : ∃ zs, s'.readBlock b off N = some zs := by
  have hpre := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hF.mono le_rfl le_sup_left)
    (Store.readBlock_sub (o := 0) (n := o) h (by omega))
  have hsub := Store.readBlock_sub (o := o + l) (n := N - (o + l)) h (by omega)
  rw [← Nat.add_assoc] at hsub
  have hsuf := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hF.mono le_rfl le_sup_right) hsub
  have h1 := Store.readBlock_add hpre hnew
  rw [Nat.add_assoc] at hsuf
  have h2 := Store.readBlock_add h1 hsuf
  rw [show o + l + (N - (o + l)) = N by omega] at h2
  exact ⟨_, h2⟩

/-! ### The rounded step on any matrix -/

section Termination

/-- The sweep terminates on any matrices: on a scalar machine with exact comparisons, from
any working matrix at `w` and output at `z` of order $n + 1$, the $n$ rounds of the Givens sweep
write only the two matrices and the coefficient words and leave both matrices stored. -/
theorem sweep_terminates {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hCmp : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w z cf : ℕ × ℕ}
    {W₀ Z₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hW : HoldsMatrix w W₀ m.store)
    (hZ : HoldsMatrix z Z₀ m.store) (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hl : m.Live [w, z, cf, w, z]) :
    Writes .total I τ sweep.body (Env.frame [n + 1] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧ ∃ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, True ∧
        HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store) m := by
  unfold sweep
  refine writes_loop (N := n) rfl (fun _ => _) (fun _ _ => le_rfl)
    (fun _ m' => m'.pos = m.pos ∧ ∃ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, True ∧
      HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store)
    ⟨rfl, W₀, Z₀, trivial, hW, hZ⟩ ?_
  rintro k hk m' hfr ⟨hp, W, Z, -, hW', hZ'⟩
  have hround := round_writes_word (τ := τ) (m := m') (n := n + 1) (k := k) hS hCmp
    (by omega)
    (cv := (roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).1)
    (sv := (roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).2) rfl hW' hZ'
    (by rw [hfr.len_eq]; exact hc) hwz hwc hzc
  refine (hround.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro m'' _ ⟨hp', hW'', hZ''⟩
  exact ⟨hp'.trans hp, _, _, trivial, hW'', hZ''⟩

variable [Has IndexOp Op]

/-- One rounded step in place terminates on any matrix: on a scalar machine with exact
comparisons and the literal $0$ exact, from any matrix of order $n + 1$ at `a` and any shift
pair at `s`, `stepWithDiagInPlace` writes only the matrix, the scratch matrix `t`, the
diagonal pair `dg` and the log, leaves the matrix and the pair stored, and appends $n$ entries
with planes below $n$ to the pending slot of the log. The scratch matrix is disjoint from the
matrix, the shift and the pair; the matrix is disjoint from the pair; the log from all of them. -/
theorem stepWithDiagInPlace_terminates {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t dg lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns) (hw : P.length + n ≤ w)
    (hl : m.Live [a, s, t, dg, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hst : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 2 ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiagInPlace.body
      (Env.frame [n + 1, w, L.length, P.length] [a, s, t, a, dg, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a H' m'.store) ∧ (∃ z : ℂ, m'.store.readBlock dg.1 dg.2 2 = some [z.re, z.im]) ∧
        ∃ es : List GivensEntry, es.length = n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w L (P ++ es) m'.store)
      m := by
  have hlen := Store.le_len_of_readBlock hA (by positivity)
  have hstep := stepWithDiag_writes_of_inv (τ := τ) (Inv := fun _ _ _ _ => True) hS hzero hCmp
    hL hNat hn hlog hj hw hl hA hs ht hd hat hst htd hlgd (fun _ _ _ _ _ _ => trivial) trivial
  refine hstep.frame_seq_le rfl rfl hl
    (sup_le (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right) ?_
  rintro m₁ hfr ⟨hp, es, hes, hpl, hlog₁, W, Z, -, hT, hD⟩
  have hcopy := copyMatrix_writes (τ := τ) hS hT (by rw [hfr.len_eq]; exact hlen) hat.symm
  refine (hcopy.in_frame rfl rfl ((hl.congr hfr.length_eq).mono (by simp))).mono
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_
  intro m₂ hfr₂ ⟨hp₂, hA₂⟩
  exact ⟨hp₂.trans hp, ⟨_, hA₂⟩, ⟨_, hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) had hD⟩, es,
    hes, hpl, hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
      (hlgd.mono le_rfl (le_sup_left.trans (le_sup_left.trans le_sup_left))).symm hlog₁⟩

/-- The degree $k$ rounded step terminates on any matrix: on a scalar machine with exact
comparisons and the literal $0$ exact, from any matrix of order $n + 1$ at `a` and any $2k$
shift words at `s`, `multiStepStable` writes only the matrix, the $2k$ diagonal words `ds` and
the log, leaves both stored, and fills the pending slot $j$ of the log with $kn$ entries with planes
below $n$. The matrix, the shifts, the diagonal words and the log are pairwise disjoint views. -/
theorem multiStepStable_terminates {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s ds lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns) (hw : k * n ≤ w)
    (hl : m.Live [a, s, ds, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    (hd : ds.2 + 2 * k ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k))) :
    Writes .total I τ multiStepStable.body (Env.frame [n + 1, k, w, L.length] [a, s, a, ds, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a H' m'.store) ∧ (∃ ys, m'.store.readBlock ds.1 ds.2 (2 * k) = some ys) ∧
        ∃ es : List GivensEntry, es.length = k * n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w L es m'.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ ds.1 < m.store.length ∧
      lg.1 < m.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨hp, ⟨H', hA'⟩, ⟨ys, hD'⟩, es, hes, hpl, hlog'⟩ => ⟨hp,
      ⟨H', hA'.of_below hBelow hlive.1⟩, ⟨ys, hBelow.readBlock_of hlive.2.2.1 hD'⟩, es, hes, hpl,
      hlog'.of_below hBelow hlive.2.2.2⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by simpa [t] using hlens 0 (by simp)
  have hne : ∀ {b o k : ℕ} {b' o' k' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') := fun h => Fp.disj_inBlock_of_ne h
  have htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)) := hne (by dsimp [t]; omega)
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))
  have hFs : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k)) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has,
      hne (by dsimp [t]; omega)⟩, hsd.symm⟩, hlgd.mono le_rfl (le_sup_right.trans le_sup_left)⟩
  refine (writes_loop (m := ⟨store, m.pos⟩) (n := .var 1) (N := k) rfl (fun _ => F)
    (fun _ _ => le_rfl)
    (fun j μ => μ.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix a H' μ.store) ∧ (∃ ys, μ.store.readBlock ds.1 ds.2 (2 * j) = some ys) ∧
      ∃ es : List GivensEntry, es.length = j * n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w L es μ.store)
    ⟨rfl, ⟨H, hA.of_below hBelow hlive.1⟩, ⟨[], by simp⟩, [], by simp, by simp,
      hlog.of_below hBelow hlive.2.2.2⟩ ?_).mono
    (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (Fp.inBlock_le_sup_above le_rfl)) (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      (le_sup_right.trans le_sup_left)) fun _ _ h => h
  intro j hjk μ hfr ⟨hp, ⟨Hj, hAj⟩, ⟨ys, hDj⟩, es, hes, hpl, hlogj⟩
  have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hFs
    ((hBelow.readBlock hlive.2.1 _ _).trans hs)
  obtain ⟨z, hsj⟩ := Store.exists_readBlock_pair hsμ (o := 2 * j) (by omega)
  have hdg : Store.inBlock ds.1 (ds.2 + 2 * j) 2 ≤ Store.inBlock ds.1 ds.2 (2 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hsg : Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hpre : Store.inBlock ds.1 ds.2 (2 * j) ≤ Store.inBlock ds.1 ds.2 (2 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hlμ : μ.Live [a, (s.1, s.2 + 2 * j), t, a, (ds.1, ds.2 + 2 * j), lg] := by
    simp [Mem.Live, hfr.length_eq, t, hlen]; omega
  have hwj : es.length + n ≤ w := by rw [hes]; nlinarith [Nat.mul_le_mul_right n hjk]
  have hstep := stepWithDiagInPlace_terminates (τ := τ) (m := μ) (t := t) (H := Hj)
    (s := (s.1, s.2 + 2 * j)) (dg := (ds.1, ds.2 + 2 * j)) (P := es) hS hzero hCmp hL hNat hn
    hlogj hj hwj (hlμ.mono (by simp)) hAj hsj
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
  intro μ' hfr' ⟨hp', hA', ⟨v, hD'⟩, es', hes', hpl', hlog'⟩
  have hDj' := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨had.mono le_rfl hpre,
      htd.mono le_rfl hpre⟩, (Fp.disj_inBlock_of_le le_rfl).symm⟩,
      hlgd.mono le_rfl (hpre.trans le_sup_right)⟩) hDj
  refine ⟨hp'.trans hp, hA', ⟨ys ++ [v.re, v.im], ?_⟩, es ++ es',
    by rw [List.length_append, hes, hes']; ring,
    fun e he => (List.mem_append.mp he).elim (hpl e) (hpl' e), hlog'⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  exact Store.readBlock_add hDj' hD'

end Termination

end NLAlib.ShiftedQR
