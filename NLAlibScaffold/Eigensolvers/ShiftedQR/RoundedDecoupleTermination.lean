/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedDecouple
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedSolveTermination

/-!
# Termination of the rounded decoupling loop

The termination-only counterpart of the decoupler's contract: `NLAlib.ShiftedQR.roundedDecouple`
(the loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] with `Regularize` and
$\mathrm{Sh}_{k,B}$) runs to completion on every tape and from every stored matrix. Nothing
numerical is assumed: the matrix need not be upper Hessenberg, the machine need not round
well, the shifts may be garbage. Each block is shown to succeed from stored inputs, leaving its
outputs stored: the scalar operations, the comparisons and the kernels always succeed on stored
operands with room, every loop is capped, and every bounded index read is within its bound
because the index words are exact natural literals.

## Main results

* `NLAlib.ShiftedQR.multiStepStable_terminates`: the degree $k$ rounded step.
* `NLAlib.ShiftedQR.regularize_terminates`: `Regularize`.
* `NLAlib.ShiftedQR.shStep_terminates`: $\mathrm{Sh}_{k,B}$.
* `NLAlib.ShiftedQR.roundedDecouple_terminatingDecoupler`: the decoupler is a
  `NLAlib.ShiftedQR.TerminatingDecoupler`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

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

/-- A stored block of $2 \cdot rc$ words holds an $r \times c$ matrix. -/
theorem Store.exists_holdsMatrix_of_readBlock {s : Store ℝ} {b : ℕ × ℕ} {rows cols : ℕ}
    {xs : List ℝ} (h : s.readBlock b.1 b.2 (2 * (cols * rows)) = some xs) :
    ∃ A : Matrix (Fin rows) (Fin cols) ℂ, HoldsMatrix b A s :=
  ⟨_, holdsMatrix_storedMatrix fun j hj => by rw [Store.get_of_readBlock h hj 0]; rfl⟩

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

section Step

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- **The sweep terminates on any matrices**: on a scalar machine with exact comparisons, from
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
    (cv := (coefficientWords M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).1)
    (sv := (coefficientWords M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).2) rfl hW' hZ'
    (by rw [hfr.len_eq]; exact hc) hwz hwc hzc
  refine (hround.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro m'' _ ⟨hp', hW'', hZ''⟩
  exact ⟨hp'.trans hp, _, _, trivial, hW'', hZ''⟩

/-- **One rounded step in place terminates on any matrix**: on a scalar machine with exact
comparisons and the literal $0$ exact, from any matrix of order $n + 1$ at `a` and any shift
pair at `s`, `stepWithDiagInPlace` writes only the matrix, the scratch matrix `t` and the
diagonal pair `dg`, and leaves the matrix and the pair stored. The scratch matrix is disjoint
from the matrix, the shift and the pair; the matrix is disjoint from the pair. -/
theorem stepWithDiagInPlace_terminates {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t dg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, t, dg]) (hA : HoldsMatrix a H m.store)
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
      (Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiagInPlace.body (Env.frame [n + 1] [a, s, t, a, dg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a H' m'.store) ∧ ∃ z : ℂ, m'.store.readBlock dg.1 dg.2 2 = some [z.re, z.im])
      m := by
  have hlen := Store.le_len_of_readBlock hA (by positivity)
  have hstep := stepWithDiag_writes_of_sweep (τ := τ) (P := fun _ _ => True) hS hzero hl hA hs
    ht hd hat hst htd fun m₁ w cf hW hZ hc hwz hwc hzc hl₁ =>
      sweep_terminates hS hCmp hW hZ hc hwz hwc hzc hl₁
  refine hstep.frame_seq_le rfl rfl hl (sup_le (le_sup_right.trans le_sup_left) le_sup_right) ?_
  rintro m₁ hfr ⟨hp, W, Z, -, hT, hD⟩
  have hcopy := copyMatrix_writes (τ := τ) hS hT (by rw [hfr.len_eq]; exact hlen) hat.symm
  refine (hcopy.in_frame rfl rfl ((hl.congr hfr.length_eq).mono (by simp))).mono
    (le_sup_left.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hA₂⟩
  exact ⟨hp₂.trans hp, ⟨_, hA₂⟩, _, hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) had hD⟩

/-- **The degree $k$ rounded step terminates on any matrix**: on a scalar machine with exact
comparisons and the literal $0$ exact, from any matrix of order $n + 1$ at `a` and any $2k$
shift words at `s`, `multiStepStable` writes only the matrix and the $2k$ diagonal words `ds`
and leaves both stored. The matrix, the shifts and the diagonal words are pairwise disjoint
views. -/
theorem multiStepStable_terminates {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s ds : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ}
    (hl : m.Live [a, s, ds]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs)
    (hd : ds.2 + 2 * k ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k))) :
    Writes .total I τ multiStepStable.body (Env.frame [n + 1, k] [a, s, a, ds])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * k))
      (fun m' => m'.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a H' m'.store) ∧ ∃ ys, m'.store.readBlock ds.1 ds.2 (2 * k) = some ys) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ ds.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨hp, ⟨H', hA'⟩, ys, hD'⟩ => ⟨hp, ⟨H', hA'.of_below hBelow hlive.1⟩, ys,
      hBelow.readBlock_of hlive.2.2 hD'⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by simpa [t] using hlens 0 (by simp)
  have hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)) := Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)) := Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * k)
  have hFs : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k)) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has, hts⟩, hsd.symm⟩
  refine (writes_loop (m := ⟨store, m.pos⟩) (n := .var 1) (N := k) rfl (fun _ => F)
    (fun _ _ => le_rfl)
    (fun j μ => μ.pos = m.pos ∧ (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix a H' μ.store) ∧ ∃ ys, μ.store.readBlock ds.1 ds.2 (2 * j) = some ys)
    ⟨rfl, ⟨H, hA.of_below hBelow hlive.1⟩, [], by simp⟩ ?_).mono
    (sup_le (sup_le (le_sup_left.trans le_sup_left) (Fp.inBlock_le_sup_above le_rfl))
      (le_sup_right.trans le_sup_left)) fun _ _ h => h
  intro j hj μ hfr ⟨hp, ⟨Hj, hAj⟩, ys, hDj⟩
  have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hFs
    ((hBelow.readBlock hlive.2.1 _ _).trans hs)
  obtain ⟨z, hsj⟩ := Store.exists_readBlock_pair hsμ (o := 2 * j) (by omega)
  have hdg : Store.inBlock ds.1 (ds.2 + 2 * j) 2 ≤ Store.inBlock ds.1 ds.2 (2 * k) :=
    fun b i hi => ⟨hi.1, by have := hi.2.1; omega, by have := hi.2.2; omega⟩
  have hpre : Store.inBlock ds.1 ds.2 (2 * j) ≤ Store.inBlock ds.1 ds.2 (2 * k) :=
    fun b i hi => ⟨hi.1, hi.2.1, by have := hi.2.2; omega⟩
  have hlμ : μ.Live [a, (s.1, s.2 + 2 * j), t, a, (ds.1, ds.2 + 2 * j)] := by
    simp [Mem.Live, hfr.length_eq, t, hlen]; omega
  have hstep := stepWithDiagInPlace_terminates (τ := τ) (m := μ) (t := t)
    (s := (s.1, s.2 + 2 * j)) (dg := (ds.1, ds.2 + 2 * j)) hS hzero hCmp
    (hlμ.mono (by simp)) hAj hsj
    (by rw [hfr.len_eq]; dsimp [t]; simpa only [Nat.zero_add] using ht.ge)
    (by rw [hfr.len_eq, (hBelow ds.1 hlive.2.2).1]; dsimp only; omega)
    hta.symm (Fp.disj_inBlock_of_ne (by dsimp [t]; omega))
    (htd.mono le_rfl hdg) (had.mono le_rfl hdg)
  refine (hstep.in_frame rfl rfl hlμ).mono
    (sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (hdg.trans le_sup_right)) ?_
  intro μ' hfr' ⟨hp', hA', w, hD'⟩
  have hDj' := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨had.mono le_rfl hpre,
      htd.mono le_rfl hpre⟩, (Fp.disj_inBlock_of_le le_rfl).symm⟩) hDj
  refine ⟨hp'.trans hp, hA', ys ++ [w.re, w.im], ?_⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  exact Store.readBlock_add hDj' hD'

end Step

/-! ### The trials of `Regularize` on any matrix -/

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The computation of one trial terminates on any matrix**: on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$, from any matrix of order
$n + 1$ at `A`, any shift pair at `S` and any threshold word at `Thr`, $k \le n$,
`NLAlib.ShiftedQR.trialStep` writes only its four outputs and leaves the step stored at `T` and
the scan flag stored in `Rg`. The views are live; the four outputs are apart from the inputs and
from each other as in `NLAlib.ShiftedQR.trialStep_writes`. -/
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
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ (trialStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, sp, thr, t, sr, ds, rg])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix t H' m'.store) ∧
        ∃ x, m'.store.get rg.1 (rg.2 + 3) = some x) m := by
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (Nat.zero_le _)
  unfold trialStep
  refine (copyMatrix_writes (τ := τ) hS hA hrt (hW.symm.mono (by fp_sub) (by fp_sub))).frame_seq_le
    rfl rfl (hl.mono (by simp)) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hT₁⟩
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hs
  have hthr₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr
  have hrep := replicatePair_writes (τ := τ) (sr := sr) hS hs₁ (by rw [hfr₁.len_eq]; exact hrsr)
    (hW.symm.mono (by fp_sub) (by fp_sub))
  refine hrep.frame_seq_le rfl rfl ((hl.congr hfr₁.length_eq).mono (by simp)) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSR₂⟩
  rw [List.length_replicate] at hSR₂
  have hT₂ := hT₁.of_eqOff hfr₂ hts.symm
  have hthr₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr₁
  have hl₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by rw [hfr₂.len_eq, hfr₁.len_eq]
  have hL₂ : m₂.store.length = m.store.length := by rw [hfr₂.length_eq, hfr₁.length_eq]
  have hms := multiStepStable_terminates (τ := τ) (m := m₂) (a := t) (s := sr) (ds := ds)
    hS hzero hC ((hl.congr hL₂).mono (by simp)) hT₂ hSR₂
    (by rw [hl₂]; exact hrds) hts htd hsd
  refine hms.frame_seq_le rfl rfl ((hl.congr hL₂).mono (by simp)) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, ⟨H', hT₃⟩, -⟩
  have hthr₃ := hfr₃.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨hW.mono (by fp_sub) (by fp_sub), hW.mono (by fp_sub) (by fp_sub)⟩)
    hthr₂
  have hL₃ : m₃.store.length = m.store.length := by rw [hfr₃.length_eq, hL₂]
  have hb := bottomScan_terminates (τ := τ) (m := m₃) (a := t) (t := thr) (r := rg) hS hL hNat hC
    hk hT₃ hthr₃ ((hl.congr hL₃).mono (by simp))
    (by rw [hfr₃.len_eq, hl₂]; exact hrrg) hrg (hW.mono (by fp_sub) (by fp_sub))
  refine (hb.in_frame rfl rfl ((hl.congr hL₃).mono (by simp))).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hscan⟩
  refine ⟨⟨H', hT₃.of_eqOff hfr₄ hrg⟩, ?_⟩
  rcases hscan with ⟨h1, -⟩ | ⟨h0, -⟩
  exacts [⟨_, h1⟩, ⟨_, h0⟩]

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **The acceptance of a trial terminates on any matrix**: on a scalar machine,
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
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1)) :
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body (Env.frame [n + 1] [t, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1)
      (fun m' => HoldsMatrix a H' m'.store ∧ (∃ x, m'.store.get g.1 g.2 = some x) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  unfold trialAccept
  refine (copyMatrix_writes (τ := τ) hS hT hra hta).frame_seq_le rfl rfl
    (hl.mono (by simp)) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hA₁⟩
  refine (writes_call_const (hS (.lit 0)) (z := g) rfl trivial
    (by rw [hfr₁.len_eq]; exact hrg)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hG₂⟩
  refine (writes_call_const (hS (.lit 1)) (z := f) rfl trivial
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, hF₃⟩
  exact ⟨(hA₁.of_eqOff hfr₂ (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₃
    (hga.mono (by fp_sub) le_rfl), ⟨_, hfr₃.keep (Store.readsOnly_get _ _ _) hgf.symm hG₂⟩,
    ⟨_, hF₃⟩⟩

/-- **One trial of `Regularize` terminates on any matrix**: under the hypotheses of
`NLAlib.ShiftedQR.trialStep_terminates` with stored words at `G` and `Fl` apart from the rest,
`NLAlib.ShiftedQR.regularizeTrial` writes only the matrix, `G`, `Fl` and its scratch, and leaves
the matrix, `G` and `Fl` stored. -/
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
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1)) :
    Writes .total I τ (regularizeTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, sp, thr, t, sr, ds, rg, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get g.1 g.2 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  unfold regularizeTrial
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hg) ?_
  by_cases hgp : 0 < gv
  · rw [show decide (0 < id gv) = true by simpa using hgp, if_pos rfl]
    have hstep := trialStep_terminates (τ := τ) hS hL hNat hC hk (hl.mono (by simp)) hA hs hthr
      hrt hrsr hrds hrrg hW hts htd hsd hrg
    refine hstep.frame_seq_le rfl rfl (hl.mono (by simp)) le_sup_right ?_
    rintro m₁ hfr₁ ⟨⟨H', hT₁⟩, x, hR⟩
    have hA₁ := hA.of_eqOff hfr₁ (hW.mono le_rfl (by fp_sub))
    have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGF.symm.mono (by fp_sub) (by fp_sub)) hg
    have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGF.symm.mono (by fp_sub) (by fp_sub)) hf
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR) ?_
    split_ifs
    · have hacc := trialAccept_terminates (τ := τ) (a := a) (g := g) (f := f) hS
        ((hl.congr hfr₁.length_eq).mono (by simp)) hT₁
        (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hg)
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hf)
        (hW.mono (by fp_sub) (by fp_sub)) (hGF.mono le_rfl (by fp_sub)) hgf
      refine (hacc.in_frame rfl rfl ((hl.congr hfr₁.length_eq).mono (by simp))).mono
        (by fp_sub) ?_
      rintro m₂ - ⟨hA₂, hG₂, hF₂⟩
      exact ⟨⟨_, hA₂⟩, hG₂, hF₂⟩
    · exact (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hg₁⟩, ⟨_, hf₁⟩⟩).mono bot_le fun _ _ h => h
  · rw [show decide (0 < id gv) = false by simpa using hgp, if_neg (by simp)]
    exact (Writes.skip ⟨⟨_, hA⟩, ⟨_, hg⟩, ⟨_, hf⟩⟩).mono bot_le fun _ _ h => h

/-- **The trials of `Regularize` terminate on any matrix**: under the hypotheses of
`NLAlib.ShiftedQR.regularizeTrial_terminates` with any $2k$ shift words at `S`, apart from the
matrix, `G` and `Fl`, `NLAlib.ShiftedQR.regularizeTrials` leaves the matrix, `G` and `Fl`
stored. -/
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
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1)) :
    Writes .total I τ (regularizeTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, thr, t, sr, ds, rg, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get g.1 g.2 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
    Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5)
  have hFS : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_left.mpr ⟨hAS, hW.mono le_rfl (by fp_sub)⟩
  unfold regularizeTrials
  refine writes_loop (N := k) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun _ μ => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' μ.store) ∧
      (∃ x, μ.store.get g.1 g.2 = some x) ∧ ∃ x, μ.store.get f.1 f.2 = some x)
    ⟨⟨H, hA⟩, ⟨_, hg⟩, ⟨_, hf⟩⟩ ?_
  rintro j hj μ hfr ⟨⟨Hμ, hAμ⟩, ⟨gμ, hgμ⟩, ⟨fμ, hfμ⟩⟩
  have hl' : ∀ b, μ.store.len b = m.store.len b := fun b => hfr.len_eq b
  have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFS.mono le_rfl le_sup_left) hs
  obtain ⟨z, hsj⟩ := Store.exists_readBlock_pair hsμ (o := 2 * j) (by omega)
  have hthrμ := hfr.keep (Store.readsOnly_get _ _ _) (hFS.mono le_rfl le_sup_right) hthr
  have hpair : Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hlμ : μ.Live [a, (s.1, s.2 + 2 * j), thr, t, sr, ds, rg, a, g, f] := by
    have := hl.congr hfr.length_eq
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at this ⊢
    tauto
  have htr := regularizeTrial_terminates (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hL hNat hC hk
    hlμ hAμ hsj hthrμ hgμ hfμ (by rw [hl']; exact hrt) (by rw [hl']; exact hrsr)
    (by rw [hl']; exact hrds) (by rw [hl']; exact hrrg)
    (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left hpair _) _)) hts htd hsd hrg hGF hgf
  exact (htr.in_frame rfl rfl hlμ).mono le_rfl fun _ _ h => h

/-- **The decision of `Regularize` terminates on any matrix**: with the scratch of
`NLAlib.ShiftedQR.regularize` at `L + 2, …, L + 6`, the views `NLAlib.ShiftedQR.RegularizeViews`,
the context `NLAlib.ShiftedQR.RegularizeCtx` (any matrix and any words) and any $2k$ shift words
at `S`, $k \le n$, `NLAlib.ShiftedQR.regularizeDecide` leaves the matrix and the flag
stored. -/
theorem regularizeDecide_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} (hctx : RegularizeCtx L k H R cw tv a rd c thr s f m) {xs : List ℝ}
    (hs : m.store.readBlock s.1 s.2 (2 * k) = some xs) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv
  obtain ⟨hA, -, hc, hthr, -, hrf, hlen, -, -, h2, h3, h4, h5, h6⟩ := hctx
  obtain ⟨zs, hzs, hsS⟩ := Store.exists_readBlock_flatMap_pair hs
  have hopt := optimalTest_writes_word (τ := τ) (ss := zs) (a := a) (s := s) (c := c)
    (f := (L + 2, 0)) hS hC (by omega) hA hsS hc (by simp [h2])
    (by simp [Mem.Live, hlen]; omega)
    (by
      rw [hzs]
      exact Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨by disjoint, by disjoint⟩,
        by disjoint⟩)
  rw [hzs] at hopt
  simp only at hopt
  unfold regularizeDecide
  refine hopt.frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hb⟩
  have hA₁ := hA.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne (by omega))
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (L + 2, 0)) hb) ?_
  split_ifs
  · refine (writes_call_const (hS (.lit 0)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    exact ⟨⟨_, hA₁.of_eqOff hfr₂ haf.symm⟩, ⟨_, hF₂⟩⟩
  refine (writes_call_const (hS (.lit 2)) (z := f) rfl trivial
    (by rw [hfr₁.len_eq]; exact hrf)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hF₂⟩
  refine (writes_call_const (hS (.lit 1)) (z := (L + 2, 0)) rfl trivial
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; simp [h2])).seq_le (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, hG₃⟩
  have hfr := (hfr₁.trans' hfr₂).trans' hfr₃
  have hl : ∀ b, m₃.store.len b = m.store.len b := fun b => by
    rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
  have hG : ∀ {z : ℕ × ℕ} {l : ℕ}, z.1 < L →
      Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock z.1 z.2 l) →
      Fp.Disj (Store.inBlock (L + 2) 0 1 ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock (L + 2, 0).1 (L + 2, 0).2 1) (Store.inBlock z.1 z.2 l) := fun hz hfz =>
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (by omega), hfz⟩,
      Fp.disj_inBlock_of_ne (by dsimp only; omega)⟩
  have hs₃ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hG hsl hsf.symm) hs
  have hthr₃ := hfr.keep (Store.readsOnly_get _ _ _)
    (hG htl (hio.mono (by fp_sub) (by fp_sub))) hthr
  have hA₃ := hA.of_eqOff hfr (hG ha haf.symm)
  have hF₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hF₂
  have hL₃ : m₃.store.length = L + 7 := by rw [hfr.length_eq, hlen]
  have htr := regularizeTrials_terminates (τ := τ) (a := a) (s := s) (thr := thr)
    (t := (L + 3, 0)) (sr := (L + 4, 0)) (ds := (L + 5, 0)) (rg := (L + 6, 0))
    (g := (L + 2, 0)) (f := f) hS hL hNat hC hk (by simp [Mem.Live, hL₃]; omega) hA₃ hs₃ hthr₃ hG₃ hF₃
    (by simp [hl, h3]) (by simp [hl, h4]) (by simp [hl, h5]) (by simp [hl, h6])
    (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr
      ⟨has, hio.mono (by fp_sub) (by fp_sub)⟩, by disjoint⟩, Fp.disj_sup_right.mpr
      ⟨hsf.symm, hio.mono (by fp_sub) (by fp_sub)⟩⟩)
  refine (htr.in_frame rfl rfl (by simp [Mem.Live, hL₃]; omega)).mono (by fp_sub) ?_
  rintro m₄ - ⟨hA₄, -, hF₄⟩
  exact ⟨hA₄, hF₄⟩

end Trials

/-! ### `Regularize` on any matrix -/

section Regularize

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] in
/-- **The `SmallEig` leaf stores its output**: a randomized small-eigenvalue kernel
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
/-- **The $k$ random perturbations terminate on any words**: on a scalar machine with an exact
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

end Regularize

end NLAlib.ShiftedQR
