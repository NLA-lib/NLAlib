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

* `NLAlib.ShiftedQR.trialStep_terminates`: one trial step (rounded step and scan).
* `NLAlib.ShiftedQR.regularize_terminates`: `Regularize`.
* `NLAlib.ShiftedQR.shStep_terminates`: $\mathrm{Sh}_{k,B}$.
* `NLAlib.ShiftedQR.roundedDecouple_terminatingDecoupler`: the decoupler is a
  `NLAlib.ShiftedQR.TerminatingDecoupler`.
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
  split_ifs
  · have hstep := trialStep_terminates (τ := τ) hS hL hNat hC hk (hl.mono (by simp)) hA hs hthr
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
  · exact (Writes.skip ⟨⟨_, hA⟩, ⟨_, hg⟩, ⟨_, hf⟩⟩).mono bot_le fun _ _ h => h

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
    (g := (L + 2, 0)) (f := f) hS hL hNat hC hk (by simp [Mem.Live, hL₃]; omega) hA₃ hs₃ hthr₃
    hG₃ hF₃
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

/-- **`Regularize` with scratch terminates on any matrix**: with the views
`NLAlib.ShiftedQR.RegularizeViews` and the context `NLAlib.ShiftedQR.RegularizeCtx` (any matrix of
order $n + 1$, any words), $k \le n$, a `SmallEig` kernel meeting
`NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler, on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$,
`NLAlib.ShiftedQR.regularizeWithScratch` writes only the matrix, the $k$ output pairs, the flag
and the scratch above $L$, and leaves the matrix, the pairs and the flag stored. -/
theorem regularizeWithScratch_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} (hctx : RegularizeCtx L k H R cw tv a rd c thr s f m) :
    Writes .total I τ (regularizeWithScratch (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, rd, c, thr, (L, 0), (L + 1, 0), (L + 2, 0), (L + 3, 0),
        (L + 4, 0), (L + 5, 0), (L + 6, 0), a, s, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv'
  obtain ⟨hA, hR, -, -, hrs, -, hlen, h0, h1, -⟩ := id hctx
  have hIn : ∀ {F : Fp} {μ μ' : Mem ℝ}, Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
      ⊔ Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) →
      RegularizeCtx L k H R cw tv a rd c thr s f μ → μ.store.EqOff F μ'.store →
      RegularizeCtx L k H R cw tv a rd c thr s f μ' := fun hF h hfr => h.of_eqOff hfr hF
  have hsIn : Fp.Disj (Store.inBlock s.1 s.2 (2 * k))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock rd.1 rd.2 1 ⊔
        Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨has.symm,
      hio.mono (by fp_sub) (by fp_sub)⟩, hio.mono (by fp_sub) (by fp_sub)⟩,
      hio.mono (by fp_sub) (by fp_sub)⟩
  unfold regularizeWithScratch
  refine (copyToWork_writes (τ := τ) (w := (L, 0)) (lo := n + 1 - k) (d := k) hS
    (by simp [Mem.Live, hlen]; omega) hA (by omega) (by simp [h0]) (by disjoint)).frame_seq_le
    rfl rfl (by simp [Mem.Live, hlen]; omega) (Fp.inBlock_le_sup_above le_rfl) ?_
  rintro m₁ hfr₁ ⟨-, hB⟩
  have hc₁ := hIn (by disjoint) hctx hfr₁
  have hL₁ : m₁.store.length = L + 7 := by rw [hfr₁.length_eq, hlen]
  refine (hSE.smallEigLeaf_terminates (τ := τ) (w := (L, 0)) (o := s) hB
    (by simp [Mem.Live, hL₁]; omega) (by dsimp only; rw [hfr₁.len_eq]; exact hrs)).frame_seq_le
    rfl rfl (by simp [Mem.Live, hL₁]; omega) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨xs, hS₂⟩
  have hc₂ := hIn hsIn hc₁ hfr₂
  have hL₂ : m₂.store.length = L + 7 := by rw [hfr₂.length_eq, hL₁]
  obtain ⟨-, hrd₂, -⟩ := id hc₂
  obtain ⟨R', hR'⟩ : ∃ x, m₂.store.get rd.1 rd.2 = some x := ⟨_, hrd₂⟩
  refine (regularizeDraws_terminates (τ := τ) (z := (L + 1, 0)) hS hD
    (by simp [Mem.Live, hL₂]; omega) hR' hS₂
    (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; simp [h1]) (by disjoint) (by disjoint)
    (hio.mono (by fp_sub) (by fp_sub))).frame_seq_le rfl rfl (by simp [Mem.Live, hL₂]; omega)
    (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨ys, hS₃⟩
  have hc₃ := hIn (Fp.disj_sup_left.mpr ⟨hsIn, by disjoint⟩) hc₂ hfr₃
  refine (regularizeDecide_terminates (τ := τ) hS hL hNat hC hk hv hc₃ hS₃).in_frame rfl rfl
    (by simp [Mem.Live, hc₃.2.2.2.2.2.2.1]; omega) |>.mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨hA₄, hF₄⟩
  refine ⟨hA₄, ⟨_, hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) ?_ hS₃⟩, hF₄⟩
  exact Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has, by disjoint⟩,
    hsf.symm⟩, by disjoint⟩

/-- **`Regularize` terminates on any matrix** ([BanksGarzaVargasSrivastava2022, §4.2]): on a
scalar machine with exact comparisons, index literals and exact natural literals up to $n + 1$,
with a `SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
from any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, room for $k \le n$ output
pairs at `s` and the flag at `f` (the views live and apart as in
`NLAlib.ShiftedQR.regularize_pwrites`), `NLAlib.ShiftedQR.regularize` writes only the matrix, the
pairs and the flag, and leaves all three stored, on every tape. -/
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
    (hrf : f.2 < m.store.len f.1) :
    Writes .total I τ (regularize (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, rd, c, thr, a, s, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have e : (regularize (O := O) (Q := Q)).body = Stmt.allocs [.const 2 * (.var 1 * .var 1),
      .const 2, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 1, .const 2 * .var 1,
      .const 5] (.frame [.var 0, .var 1] [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
        ⟨7, .const 0⟩, ⟨8, .const 0⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩, ⟨11, .const 0⟩,
        ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨0, .var 2⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩]
        (regularizeWithScratch (O := O) (Q := Q)).body) := rfl
  have hlv : a.1 < m.store.length ∧ rd.1 < m.store.length ∧ c.1 < m.store.length ∧
      thr.1 < m.store.length ∧ s.1 < m.store.length ∧ f.1 < m.store.length := by
    simpa [Mem.Live] using hl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlv
  rw [e]
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨⟨H', hA'⟩, ⟨ys, hS'⟩, ⟨x, hF'⟩⟩ => ⟨⟨H', hA'.of_below hBelow h1⟩,
      ⟨ys, hBelow.readBlock_of h5 hS'⟩, ⟨x, hBelow.get_of h6 hF'⟩⟩) ?_
  intro s₁ hlen hlens hBelow
  have hl7 := fun i (hi : i < 7) => hlens i (by simpa using hi)
  have hctx : RegularizeCtx m.store.length k H R cw tv a rd c thr s f ⟨s₁, m.pos⟩ := by
    refine ⟨hA.of_below hBelow h1, hBelow.get_of h2 hrd, hBelow.get_of h3 hc,
      hBelow.get_of h4 hthr, by rw [(hBelow s.1 h5).1]; exact hrs,
      by rw [(hBelow f.1 h6).1]; exact hrf, by simpa using hlen, ?_⟩
    simpa using ⟨hl7 0 (by norm_num), hl7 1 (by norm_num), hl7 2 (by norm_num),
      hl7 3 (by norm_num), hl7 4 (by norm_num), hl7 5 (by norm_num), hl7 6 (by norm_num)⟩
  refine ((regularizeWithScratch_terminates hS hL hNat hC hSE hD hk
    ⟨⟨h1, h2, h3, h4, h5, h6⟩, has, haf, hsf, hio⟩ hctx).in_frame rfl rfl ?_).mono
    (by fp_sub) fun _ _ h => h
  simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hctx.2.2.2.2.2.2.1]
  omega

end Regularize

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

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **The potential test of `Sh` terminates on any matrix**: with the views
`NLAlib.ShiftedQR.ShViews` and the room `NLAlib.ShiftedQR.ShRoom`, from any step at `T`, any
matrix at `A` and stored words at `Pt`, `Gw` and `Fl`, $k \le n$,
`NLAlib.ShiftedQR.shPotentialAccept` leaves the matrix, `Gw` and `Fl` stored. -/
theorem shPotentialAccept_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkn : k ≤ n) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    (hr : ShRoom L n k ε f m) {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {pv gv fv : ℝ}
    (hT : HoldsMatrix (L + 5, 0) H' m.store) (hA : HoldsMatrix a H m.store)
    (hpt : m.store.get (L + 2) 0 = some pv) (hg : m.store.get (L + 11) 0 = some gv)
    (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shPotentialAccept (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q] [(L + 2, 0), (L + 5, 0), (L + 9, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock (L + 9) 0 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, haf, -⟩ := hv
  obtain ⟨hrf, hlen, -, -, -, -, -, h5, -, -, -, h9, -, h11⟩ := hr
  unfold shPotentialAccept
  refine (roundedPotential_writes_word (τ := τ) (q := q) hS hkn hT (p := (L + 9, 0))
    (by simp [h9]) (by disjoint)).frame_seq_le rfl rfl (by simp [Mem.Live, hlen])
    le_sup_right ?_
  rintro m₁ hfr₁ ⟨-, hP⟩
  have hpt₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hpt
  have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hg
  have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hf
  have hT₁ := hT.of_eqOff hfr₁ (by disjoint)
  have hA₁ := hA.of_eqOff hfr₁ (by disjoint)
  refine writes_ite rfl rfl (hC.test_lt (d := []) hP hpt₁) ?_
  split_ifs
  · have hacc := trialAccept_terminates (τ := τ) (a := a) (g := (L + 11, 0)) (f := f) hS
      (by simp [Mem.Live, hfr₁.length_eq, hlen]; omega) hT₁
      (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
      (by rw [hfr₁.len_eq]; simp [h11]) (by rw [hfr₁.len_eq]; exact hrf) (by disjoint)
      (Fp.disj_sup_left.mpr ⟨by disjoint, haf.symm⟩) (by disjoint)
    refine (hacc.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hlen]; omega)).mono
      (by fp_sub) ?_
    rintro m₂ - ⟨hA₂, hG₂, hF₂⟩
    exact ⟨⟨_, hA₂⟩, hG₂, hF₂⟩
  · exact (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hg₁⟩, ⟨_, hf₁⟩⟩).mono bot_le fun _ _ h => h

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **One trial of `Sh` terminates on any matrix**: with the views and the room of `Sh`, from
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
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q] [a, (L + 10, o), thr, (L + 2, 0), (L + 5, 0), (L + 6, 0),
        (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, haf, -⟩ := hv'
  obtain ⟨hrf, hlen, -, -, -, -, -, h5, h6, h7, h8, -, -, h11⟩ := id hr
  unfold shTrial
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (L + 11, 0)) hg) ?_
  split_ifs
  · have hstep := trialStep_terminates (τ := τ) (a := a) (sp := (L + 10, o)) (thr := thr)
      (t := (L + 5, 0)) (sr := (L + 6, 0)) (ds := (L + 7, 0)) (rg := (L + 8, 0)) hS hL hNat hC
      hkn (by simp [Mem.Live, hlen]; omega) hA hs hthr (by simp [h5]) (by simp [h6])
      (by simp [h7]) (by simp [h8]) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
      (by disjoint)
    refine hstep.frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
    rintro m₁ hfr₁ ⟨⟨H', hT₁⟩, x, hR⟩
    have hA₁ := hA.of_eqOff hfr₁ (by disjoint)
    have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hg
    have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hf
    have hpt₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hpt
    have hr₁ := hr.of_eqOff hfr₁
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := ((L + 8, 0).1, (L + 8, 0).2 + 3))
      hR) ?_
    split_ifs
    · have hacc := trialAccept_terminates (τ := τ) (a := a) (g := (L + 11, 0)) (f := f) hS
        (by simp [Mem.Live, hfr₁.length_eq, hlen]; omega) hT₁
        (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
        (by rw [hfr₁.len_eq]; simp [h11]) (by rw [hfr₁.len_eq]; exact hrf) (by disjoint)
        (Fp.disj_sup_left.mpr ⟨by disjoint, haf.symm⟩) (by disjoint)
      refine (hacc.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hlen]; omega)).mono
        (by fp_sub) ?_
      rintro m₂ - ⟨hA₂, hG₂, hF₂⟩
      exact ⟨⟨_, hA₂⟩, hG₂, hF₂⟩
    · refine ((shPotentialAccept_terminates (τ := τ) (q := q) hS hC hkn hv hr₁ hT₁ hA₁ hpt₁ hg₁
        hf₁).in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hlen]; omega)).mono
        (by fp_sub) fun _ _ h => h
  · exact (Writes.skip ⟨⟨_, hA⟩, ⟨_, hg⟩, ⟨_, hf⟩⟩).mono bot_le fun _ _ h => h

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **The trials of `Sh` terminate on any matrix**: under the hypotheses of
`NLAlib.ShiftedQR.shTrial_terminates` with any $2n_0$ words in the scratch buffer `L + 10`
($n_0$ the size of the net), `NLAlib.ShiftedQR.shTrials` leaves the matrix, `Gw` and `Fl`
stored. -/
theorem shTrials_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ}
    {m : Mem ℝ} {L k q : ℕ} (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) (hr : ShRoom L n k ε f m)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} {tv pv gv fv : ℝ}
    (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock (L + 10) 0 (2 * (excNet ε).length) = some xs)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hpt : m.store.get (L + 2) 0 = some pv)
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length] [a, (L + 10, 0), thr, (L + 2, 0), (L + 5, 0),
        (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, haf, hio⟩ := hv'
  obtain ⟨-, hlen, -⟩ := id hr
  unfold shTrials
  refine writes_loop rfl (fun _ => _) (fun _ _ => le_rfl)
    (fun _ μ => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' μ.store) ∧
      (∃ x, μ.store.get (L + 11) 0 = some x) ∧ ∃ x, μ.store.get f.1 f.2 = some x)
    ⟨⟨H, hA⟩, ⟨_, hg⟩, ⟨_, hf⟩⟩ ?_
  rintro j hj μ hfr ⟨⟨Hμ, hAμ⟩, ⟨gμ, hgμ⟩, ⟨fμ, hfμ⟩⟩
  have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs
  obtain ⟨z, hsj⟩ := Store.exists_readBlock_pair hsμ (o := 2 * j) (by omega)
  have hthrμ := hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
    ⟨Fp.disj_sup_left.mpr ⟨hio.mono le_sup_left (by fp_sub), by disjoint⟩,
      hio.mono le_sup_right (by fp_sub)⟩, by disjoint⟩) hthr
  have hptμ := hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hpt
  have hlμ : μ.store.length = L + 12 := by rw [hfr.length_eq, hlen]
  exact ((shTrial_terminates (τ := τ) (q := q) (o := 0 + 2 * j) hS hL hNat hC hkn hv
    (hr.of_eqOff hfr) hAμ hsj hthrμ hptμ hgμ hfμ).in_frame rfl rfl
    (by simp [Mem.Live, hlμ]; omega)).mono le_rfl fun _ _ h => h

/-- **The exceptional branch of `Sh` terminates on any matrix**: with the views of `Sh`, the
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
    (hZ : m.store.readBlock L 0 2 = some [z.re, z.im]) (hRt : m.store.get (L + 1) 0 = some p) :
    Writes .total I τ (shExc (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length] [a, (L, 0), wr, ww, wp, g, thr, (L + 1, 0),
        (L + 2, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), (L + 10, 0), a,
        (L + 11, 0), f])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock (L + 2) 0 1 ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 10) 0 (2 * (excNet ε).length) ⊔
          (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
            Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
              Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
              Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1))))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ x, m'.store.get (L + 11) 0 = some x) ∧ ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, haf, hio⟩ := hv'
  obtain ⟨hA, -, -, hcr, hcw, hcp, hG, hthr, hrf, hlen, -, h1, h2, -, -, -, -, -, -, -, h10,
    h11⟩ := id hctx
  have hfI := hio.mono le_sup_right le_rfl
  unfold shExc
  refine (shExcInit_writes (τ := τ) (rt := (L + 1, 0)) (pt := (L + 2, 0))
    (gw := (L + 11, 0)) (f := f) hS (hNat.mono (by omega)) hcr hcp hRt (by simp [h2])
    (by simp [h11]) hrf (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
      ⟨Fp.disj_sup_right.mpr ⟨hfI.mono le_rfl (by fp_sub), by disjoint⟩, by disjoint⟩,
        by disjoint⟩) (by disjoint) (by disjoint)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen]; omega) le_sup_left ?_
  rintro m₁ hfr₁ ⟨-, hR₁, hP₁, hG₁, hF₁⟩
  have hfo : Fp.Disj (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock (L + 2) 0 1 ⊔
      Store.inBlock (L + 11) 0 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔
        Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_left.mpr ⟨by disjoint, (Fp.disj_sup_right.mpr ⟨haf.symm, hfI⟩).mono le_rfl
      (by fp_sub)⟩
  have hc₁ := hctx.of_eqOff hfr₁ hfo
  have hZ₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hZ
  have hzr := Store.get_of_readBlock hZ₁ (j := 0) (by norm_num) 0
  have hzi := Store.get_of_readBlock hZ₁ (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hzr hzi
  have hL₁ : m₁.store.length = L + 12 := by rw [hfr₁.length_eq, hlen]
  refine (excShifts_writes_word (τ := τ) (c := (L, 0)) (rt := (L + 1, 0)) (cw := ww) (g := g)
    (ss := (L + 10, 0)) (r := z) hS hD hzr (by simpa using hzi) hR₁ hc₁.2.2.2.2.1
    hc₁.2.2.2.2.2.2.1 (by rw [hfr₁.len_eq]; simp [h10]) (by simp [Mem.Live, hL₁]; omega)
    (by disjoint) (by disjoint)).frame_seq_le rfl rfl (by simp [Mem.Live, hL₁]; omega)
    (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSs⟩
  have hc₂ := hc₁.of_eqOff hfr₂ (by disjoint)
  have hL₂ : m₂.store.length = L + 12 := by rw [hfr₂.length_eq, hL₁]
  refine ((shTrials_terminates (τ := τ) (q := q) hS hL hNat hC hkn hv hc₂.shRoom hc₂.1 hSs
    hc₂.2.2.2.2.2.2.2.1 (hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hP₁)
    (hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hG₁)
    (hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hF₁)).in_frame rfl rfl
    (by simp [Mem.Live, hL₂]; omega)).mono (by fp_sub) fun _ _ h => h

/-- **The decision of `Sh` terminates on any matrix**: with the views and the context of `Sh`, a
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
    (hT : HoldsMatrix (L + 5, 0) H' m.store) :
    Writes .total I τ (shDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length] [a, (L, 0), wr, ww, wp, g, thr, (L + 1, 0),
        (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0),
        (L + 9, 0), (L + 10, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, haf, hio⟩ := hv'
  obtain ⟨hA, -, -, -, -, -, -, -, hrf, hlen, -, -, -, -, -, -, -, -, -, -, -, h11⟩ := id hctx
  unfold shDecide
  refine writes_ite rfl rfl (hC.test_lt (d := []) hP0 hP1) ?_
  split_ifs
  · refine ((trialAccept_terminates (τ := τ) (a := a) (g := (L + 11, 0)) (f := f) hS
      (by simp [Mem.Live, hlen]; omega) hT (Store.le_len_of_readBlock hA (by positivity))
      (by simp [h11]) hrf (by disjoint) (Fp.disj_sup_left.mpr ⟨by disjoint, haf.symm⟩)
      (by disjoint)).in_frame rfl rfl (by simp [Mem.Live, hlen]; omega)).mono ?_ ?_
    · fp_sub
    · rintro m' - ⟨hA', -, hF'⟩
      exact ⟨⟨_, hA'⟩, hF'⟩
  · refine ((shExc_terminates (τ := τ) (q := q) hS hL hNat hC hD hk0 hkn hv hctx hZ hRt).in_frame
      rfl rfl (by simp [Mem.Live, hlen]; omega)).mono ?_ ?_
    · fp_sub
    · rintro m' - ⟨hA', -, hF'⟩
      exact ⟨hA', hF'⟩

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **The `comptau` test of `Sh` terminates on any matrix**: with the views and the room of `Sh`,
from any matrix at `A`, any pair at `Z = L` and a stored word at `Cg`, $k \le n$, on a scalar
machine with exact comparisons and the literal $0$ exact, `NLAlib.ShiftedQR.shTestStep` leaves
the step at `T = L + 5` and the words at `P0 = L + 3`, `P1 = L + 4` stored. -/
theorem shTestStep_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k : ℕ} (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    (hr : ShRoom L n k ε f m) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {z : ℂ} {cg : ℝ}
    (hA : HoldsMatrix a H m.store) (hZ : m.store.readBlock L 0 2 = some [z.re, z.im])
    (hcg : m.store.get wg.1 wg.2 = some cg) :
    Writes .total I τ (shTestStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, (L, 0), wg, (L + 5, 0), (L + 6, 0), (L + 3, 0), (L + 4, 0)])
      (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
        Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix (L + 5, 0) H' m'.store) ∧ (∃ x, m'.store.get (L + 3) 0 = some x) ∧
        ∃ x, m'.store.get (L + 4) 0 = some x) m := by
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, -, -⟩ := hv
  obtain ⟨-, hlen, -, -, -, h3, h4, h5, h6, -⟩ := hr
  unfold shTestStep
  refine (copyMatrix_writes (τ := τ) (b := (L + 5, 0)) hS hA (by simp [h5])
    (by disjoint)).frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hT₁⟩
  have hrep := replicatePair_writes (τ := τ) (k := k) (sp := (L, 0)) (sr := (L + 6, 0)) hS
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hZ)
    (by rw [hfr₁.len_eq]; simp [h6]) (by disjoint)
  rw [List.length_replicate] at hrep
  refine hrep.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hlen]) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSR⟩
  have hL₂ : m₂.store.length = L + 12 := by rw [hfr₂.length_eq, hfr₁.length_eq, hlen]
  refine (stepComptau_terminates (τ := τ) (a := (L + 5, 0)) (s := (L + 6, 0))
    (p := (L + 3, 0)) hS hzero hC (by simp [Mem.Live, hL₂]) (hT₁.of_eqOff hfr₂ (by disjoint)) hSR
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; simp [h3]) (by disjoint) (by disjoint)).frame_seq_le
    rfl rfl (by simp [Mem.Live, hL₂]) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨⟨H', hT₃⟩, x, hP₃⟩
  have hL₃ : m₃.store.length = L + 12 := by rw [hfr₃.length_eq, hL₂]
  have hfr := (hfr₁.trans' hfr₂).trans' hfr₃
  refine (shThreshold_writes (τ := τ) (p := (L + 4, 0)) hS hkn (hA.of_eqOff hfr (by disjoint))
    (hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hcg)
    (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; simp [h4]) (by disjoint)
    (by disjoint)).in_frame rfl rfl (by simp [Mem.Live, hL₃]; omega) |>.mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hP₄⟩
  exact ⟨⟨H', hT₃.of_eqOff hfr₄ (by disjoint)⟩,
    ⟨x, hfr₄.keep (Store.readsOnly_get _ _ _) (by disjoint) hP₃⟩, ⟨_, hP₄⟩⟩

omit [Has DiskSampleOp O] in
/-- **The start of `Sh` terminates on any matrix**: from the context `NLAlib.ShiftedQR.ShCtx` (any
matrix, shifts and words), $k = 2^q \le n$, on a scalar machine with exact comparisons, index
literals, index conversion and exact natural literals up to $n + 1$, the potential, `Find` and
the `comptau` test (`NLAlib.ShiftedQR.shPrefix`) keep the context and leave the pair `Z`, the
words `Rt`, `P0`, `P1` and the step `T` stored. -/
theorem shPrefix_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (shPrefix (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k] [a, s, wg, (L, 0), (L + 1, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0),
        (L + 6, 0)])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock L 0 2 ⊔
        (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
          Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1))
      (fun m' => ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m' ∧
        (∃ z : ℂ, m'.store.readBlock L 0 2 = some [z.re, z.im]) ∧
        (∃ x, m'.store.get (L + 1) 0 = some x) ∧ (∃ x, m'.store.get (L + 3) 0 = some x) ∧
        (∃ x, m'.store.get (L + 4) 0 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix (L + 5, 0) H' m'.store) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, -, -⟩ := hv'
  obtain ⟨hA, hss, hcg, -, -, -, -, -, -, hlen, h0, h1, -⟩ := id hctx
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (Nat.zero_le _)
  unfold shPrefix
  refine (roundedPotential_writes_word (τ := τ) (q := q) (p := (L + 1, 0)) hS hkn hA
    (by simp [h1]) (by disjoint)).frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega)
    (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hR₁⟩
  have hc₁ := hctx.of_eqOff hfr₁ (by disjoint)
  have hL₁ : m₁.store.length = L + 12 := by rw [hfr₁.length_eq, hlen]
  refine (findRounded_terminates (τ := τ) (m := q) (z := (L, 0)) hS hL hC hQ
    (comptauHalf_terminatingHalfTau hS hzero hC n k) (hNat.mono (by omega)) hkq hc₁.1 hc₁.2.1
    (by simp [Mem.Live, hL₁]; omega) (by disjoint)
    (by rw [hfr₁.len_eq]; simp [h0])).frame_seq_le rfl rfl (by simp [Mem.Live, hL₁]; omega)
    (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨z, hZ₂⟩
  have hc₂ := hc₁.of_eqOff hfr₂ (by disjoint)
  have hL₂ : m₂.store.length = L + 12 := by rw [hfr₂.length_eq, hL₁]
  refine (shTestStep_terminates (τ := τ) hS hzero hC hkn hv hc₂.shRoom hc₂.1 hZ₂
    hc₂.2.2.1).in_frame rfl rfl (by simp [Mem.Live, hL₂]; omega) |>.mono (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨hT₃, hP0, hP1⟩
  exact ⟨hc₂.of_eqOff hfr₃ (by disjoint),
    ⟨z, hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hZ₂⟩,
    ⟨_, hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint)
      (hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hR₁)⟩, hP0, hP1, hT₃⟩

/-- **`Sh` with scratch terminates on any matrix**: from the views and the context of `Sh` (any
matrix, shifts and words), $1 \le k = 2^q \le n$, on a scalar machine with exact comparisons,
index literals, index conversion, exact natural literals up to $n + 1$ and an exact polar
sampler, `NLAlib.ShiftedQR.shStepWithScratch` leaves the matrix and the flag stored. -/
theorem shStepWithScratch_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ} {m : Mem ℝ}
    {L k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (shStepWithScratch (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, (L, 0),
        (L + 1, 0), (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0),
        (L + 8, 0), (L + 9, 0), (L + 10, 0), (L + 11, 0), a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have hv' := hv
  obtain ⟨⟨ha, hsl, hwg, hwr, hww, hwp, hgl, hthl, hfl⟩, -, -⟩ := hv'
  have hlen := hctx.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 < k := hkq ▸ Nat.two_pow_pos q
  unfold shStepWithScratch
  refine (shPrefix_terminates (τ := τ) hS hL hNat hC hQ hkq hkn hv hctx).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨hc₁, ⟨z, hZ⟩, ⟨p, hRt⟩, ⟨p0, hP0⟩, ⟨p1, hP1⟩, H', hT⟩
  exact ((shDecide_terminates (τ := τ) (q := q) hS hL hNat hC hD hk0 hkn hv hc₁ hZ hRt hP0 hP1
    hT).in_frame rfl rfl (by simp [Mem.Live, hc₁.2.2.2.2.2.2.2.2.2.1]; omega)).mono
    (by fp_sub) fun _ _ h => h

/-- **`Sh` terminates on any matrix** ([BanksGarzaVargasSrivastava2022, Lemma 5.4]): on a scalar
machine with exact comparisons, index literals, index conversion, exact natural literals up to
$n + 1$ and an exact polar sampler, for $k = 2^q \le n$, from any matrix of order $n + 1$ at `a`,
any $2k$ shift words at `s`, any words at `wg`, `wr`, `ww`, `wp`, `thr`, the net words of
`NLAlib.ShiftedQR.excNet ε` at `g` and room for the flag, the views live and apart as in
`NLAlib.ShiftedQR.shStep_pwrites`, `NLAlib.ShiftedQR.shStep` writes only the matrix and the flag
and leaves both stored, on every tape. -/
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
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrf : f.2 < m.store.len f.1) :
    Writes .total I τ (shStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have e : (shStep (O := O) (Q := Q)).body = Stmt.allocs [.const 2, .const 1, .const 1,
      .const 1, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 2, .const 2 * .var 2,
      .const 5, .const 1, .const 2 * .var 3, .const 1]
      (.frame [.var 0, .var 1, .var 2, .var 3] [⟨0, .var 4⟩, ⟨1, .var 5⟩, ⟨2, .var 6⟩,
        ⟨3, .var 7⟩, ⟨4, .var 8⟩, ⟨5, .var 9⟩, ⟨6, .var 10⟩, ⟨7, .var 11⟩, ⟨10, .const 0⟩,
        ⟨11, .const 0⟩, ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
        ⟨16, .const 0⟩, ⟨17, .const 0⟩, ⟨18, .const 0⟩, ⟨19, .const 0⟩, ⟨20, .const 0⟩,
        ⟨21, .const 0⟩, ⟨0, .var 4⟩, ⟨9, .var 13⟩]
        (shStepWithScratch (O := O) (Q := Q)).body) := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : a.1 < m.store.length ∧ s.1 < m.store.length ∧
      wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
      wp.1 < m.store.length ∧ g.1 < m.store.length ∧ thr.1 < m.store.length ∧
      f.1 < m.store.length := by simpa [Mem.Live] using hl
  obtain ⟨ss, hssk, hss⟩ := Store.exists_readBlock_flatMap_pair hs
  rw [hssk] at hss
  rw [e]
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨⟨H', hA'⟩, ⟨x, hF'⟩⟩ => ⟨⟨H', hA'.of_below hBelow h1⟩,
      ⟨x, hBelow.get_of h9 hF'⟩⟩) ?_
  intro s₁ hlen hlens hBelow
  have hl12 := fun i (hi : i < 12) => hlens i (by simpa using hi)
  have hctx : ShCtx m.store.length k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f
      ⟨s₁, m.pos⟩ := by
    refine ⟨hA.of_below hBelow h1, hBelow.readBlock_of h2 hss, hBelow.get_of h3 hwg,
      hBelow.get_of h4 hwr, hBelow.get_of h5 hww, hBelow.get_of h6 hwp,
      hBelow.readBlock_of h7 hg, hBelow.get_of h8 hthr, by rw [(hBelow f.1 h9).1]; exact hrf,
      by simpa using hlen, ?_⟩
    simpa using ⟨hl12 0 (by norm_num), hl12 1 (by norm_num), hl12 2 (by norm_num),
      hl12 3 (by norm_num), hl12 4 (by norm_num), hl12 5 (by norm_num), hl12 6 (by norm_num),
      hl12 7 (by norm_num), hl12 8 (by norm_num), hl12 9 (by norm_num), hl12 10 (by norm_num),
      hl12 11 (by norm_num)⟩
  refine ((shStepWithScratch_terminates hS hL hNat hC hQ hD hkq hkn
    ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, haf, hio⟩ hctx).in_frame rfl rfl ?_).mono
    (by fp_sub) fun _ _ h => h
  simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hctx.2.2.2.2.2.2.2.2.2.1]
  omega

end Sh

/-! ### The decoupling loop on any matrix -/

section Decouple

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] {n : ℕ}

/-- **One iteration terminates on any matrix**: on a scalar machine with exact comparisons,
index literals, index conversion and exact natural literals up to $n + 1$, a `SmallEig` kernel
meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler, for $k = 2^q \le n$, from
any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, `wg`, `wr`, `ww`, `wp`, the
net words of `NLAlib.ShiftedQR.excNet ε` at `g` and room for the flag, the matrix and the flag
apart from each other and from the inputs, `NLAlib.ShiftedQR.shIteration` (`Regularize`, then
`Sh`) writes only the matrix and the flag and leaves both stored, on every tape. -/
theorem shIteration_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ}
    {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cv tv cg cr cw cp : ℝ}
    (hl : m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cv)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hwg : m.store.get wg.1 wg.2 = some cg)
    (hwr : m.store.get wr.1 wr.2 = some cr) (hww : m.store.get ww.1 ww.2 = some cw)
    (hwp : m.store.get wp.1 wp.2 = some cp)
    (hg : m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im])) (hrf : f.2 < m.store.len f.1) :
    Writes .total I τ (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, rd, c, thr, wg, wr, ww, wp, g, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ : a.1 < m.store.length ∧
      rd.1 < m.store.length ∧ c.1 < m.store.length ∧ thr.1 < m.store.length ∧
      wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
      wp.1 < m.store.length ∧ g.1 < m.store.length ∧ f.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 2] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * k]) rfl
    (fun hBelow ⟨⟨H', hA'⟩, x, hF'⟩ => ⟨⟨H', hA'.of_below hBelow h1⟩,
      x, hBelow.get_of h10 hF'⟩) ?_
  intro store hlen hlens hBelow
  set L := m.store.length
  have hsl : store.len L = 2 * k := by simpa using hlens 0 (by simp)
  have hLs : store.length = L + 1 := by simpa using hlen
  have hS0 : ∀ {z : ℕ × ℕ} {l : ℕ}, z.1 < L →
      Fp.Disj (Store.inBlock L 0 (2 * k)) (Store.inBlock z.1 z.2 l) :=
    fun hz => Fp.disj_inBlock_of_ne (by omega)
  have hfI : Fp.Disj (Store.inBlock f.1 f.2 1) _ := hio.mono le_sup_right le_rfl
  have hAI : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) _ :=
    hio.mono le_sup_left le_rfl
  refine Writes.in_frame (Writes.mono (F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock L 0 (2 * k) ⊔ Store.inBlock f.1 f.2 1) ?_ (by fp_sub) fun _ _ h => h) rfl rfl
    (by simp [Mem.Live, hLs]; omega)
  unfold shIterationWithScratch
  refine (regularize_terminates (τ := τ) (s := (L, 0)) hS hL hNat hC hSE hD hkn
    (hS0 h1).symm haf (hS0 h10)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hAI.mono le_rfl (by fp_sub),
      Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hS0 h2, hS0 h3⟩, hS0 h4⟩⟩,
      hfI.mono le_rfl (by fp_sub)⟩)
    (by simp [Mem.Live, hLs]; omega) (hA.of_below hBelow h1) (hBelow.get_of h2 hrd)
    (hBelow.get_of h3 hc) (hBelow.get_of h4 hthr) (by simp [hsl])
    (by rw [(hBelow f.1 h10).1]; exact hrf)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hLs]; omega) le_rfl ?_
  rintro m₁ hfr₁ ⟨⟨H₁, hA₁⟩, ⟨xs, hS₁⟩, ⟨x, hF₁⟩⟩
  have hk : ∀ {z : ℕ × ℕ} {v : ℝ}, z.1 < L → Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock z.1 z.2 1) → Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 1) → m.store.get z.1 z.2 = some v →
      m₁.store.get z.1 z.2 = some v := fun hz hf ha hv =>
    hfr₁.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
      ⟨ha, hS0 hz⟩, hf⟩) (hBelow.get_of hz hv)
  refine writes_ite rfl rfl (hC.test_isZero (d := []) (x := f) hF₁) ?_
  split_ifs
  · refine ((shStep_terminates (τ := τ) (s := (L, 0)) hS hL hNat hC hQ hD hkq hkn haf
      (Fp.disj_sup_right.mpr ⟨?_, hio⟩ |>.mono le_rfl (by fp_sub))
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega) hA₁ hS₁
      (hk h5 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwg)
      (hk h6 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwr)
      (hk h7 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hww)
      (hk h8 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwp)
      (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
        ⟨hAI.mono le_rfl (by fp_sub), hS0 h9⟩, hfI.mono le_rfl (by fp_sub)⟩)
        (hBelow.readBlock_of h9 hg))
      (hk h4 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hthr)
      (by rw [hfr₁.len_eq, (hBelow f.1 h10).1]; exact hrf)).in_frame rfl rfl
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega)).mono (by fp_sub) fun _ _ h => h
    exact Fp.disj_sup_left.mpr ⟨(hS0 h1).symm, (hS0 h10).symm⟩
  · exact (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hF₁⟩⟩).mono bot_le fun _ _ h => h

omit [Has EigenvalueKernelOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The scan of the decoupling loop on any matrix keeps the loop's operands and stores the scan
flag. -/
theorem roundedDecoupleScan_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ}
    {μ : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {w q f : ℕ × ℕ} {ps : List ℝ} (hps0 : 0 < ps.length)
    (hctx : DecoupleLoopCtx n L w q f ps μ) (hW : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix w H μ.store) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [w, q, (L, 0)])
      (Store.inBlock L 0 5)
      (fun μ' => DecoupleLoopCtx n L w q f ps μ' ∧
        (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) ∧
        ∃ x, μ'.store.get L 3 = some x) μ := by
  obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hctx
  obtain ⟨H, hH⟩ := hW
  have hRW : Fp.Disj (Store.inBlock (L, 0).1 (L, 0).2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) := Fp.disj_inBlock_of_ne (by simp; omega)
  have ht := Store.get_of_readBlock hp hps0 0
  rw [Nat.add_zero] at ht
  refine (bottomScan_terminates (τ := τ) hS hL hNat hC hk hH ht (hl.mono (by simp))
    (by simpa using hrL) hRW (Fp.disj_inBlock_of_ne (by simp; omega))).mono le_rfl ?_
  rintro μ' hfr ⟨-, hscan⟩
  refine ⟨hctx.of_eqOff (by simp) hfr, ⟨H, hH.of_eqOff hfr hRW⟩, ?_⟩
  rcases hscan with ⟨h1, -⟩ | ⟨h0, -⟩
  exacts [⟨_, by simpa using h1⟩, ⟨_, by simpa using h0⟩]

omit [Has ScalarOp O] [Has EigenvalueKernelOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The exit of the decoupling loop on any scan flag stores the flag and keeps the matrix. -/
theorem roundedDecoupleExit_terminates {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} {w p f : ℕ × ℕ}
    {ps : List ℝ} (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hW : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H μ.store) {x : ℝ}
    (hx : μ.store.get L 3 = some x) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ := by
  obtain ⟨H, hW⟩ := hW
  have hrf := hctx.2.2.2.2.2.2.1
  have hWF := hctx.2.2.2.2.2.2.2.2.1
  unfold roundedDecoupleExit
  refine writes_ite (a := [(L, 3)]) rfl rfl (hC.test_isPos hx) ?_
  split_ifs <;>
  · refine (writes_indexLit hL rfl rfl (by omega)).mono le_rfl ?_
    rintro μ' hfr ⟨-, hF⟩
    exact ⟨⟨_, hF⟩, H, hW.of_eqOff hfr hWF.symm⟩

/-- **The decoupling loop terminates on any matrix**: under the hypotheses of
`NLAlib.ShiftedQR.shIteration_terminates` on the parameter words `ps` (the words of
`NLAlib.ShiftedQR.roundedDecoupleParams`: ten words, then the net), from the operands of the loop
`NLAlib.ShiftedQR.DecoupleLoopCtx` and any matrix, `NLAlib.ShiftedQR.roundedDecoupleLoop` writes
only the matrix, the flag and its registers and leaves the matrix and the flag stored. -/
theorem roundedDecoupleLoop_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {μ : Mem ℝ} {k q F L : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ} {w p f : ℕ × ℕ}
    {ps : List ℝ} (hlen : ps.length = 10 + 2 * (excNet ε).length)
    (hnet : ps.drop 10 = (excNet ε).flatMap fun z => [z.re, z.im])
    (hctx : DecoupleLoopCtx n L w p f ps μ) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : HoldsMatrix w H μ.store) :
    Writes .total I τ (roundedDecoupleLoop (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, ps.length, F, q, (excNet ε).length] [w, p, (L, 0), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ := by
  have hps0 : 0 < ps.length := by omega
  set Inv : ℕ → Mem ℝ → Prop := fun _ μ' => DecoupleLoopCtx n L w p f ps μ' ∧
    (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) ∧
    ∃ x, μ'.store.get L 3 = some x
  unfold roundedDecoupleLoop
  refine (roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hctx ⟨H, hW⟩).frame_seq_le
    rfl rfl (hctx.2.2.2.1.mono (by simp)) (by fp_sub) ?_
  rintro μ₁ - hinv₁
  refine (writes_whileFuel (N := F) rfl (fun _ => Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))
    ⊔ Store.inBlock f.1 f.2 1 ⊔ Store.inBlock L 0 5) (fun _ _ => le_rfl)
    (Store.inBlock f.1 f.2 1) Inv _ hinv₁ ?_ ?_).mono (by fp_sub) fun _ _ h => h
  · rintro i - μ' - ⟨hc, hW', x, hx⟩
    refine ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero hx), ?_⟩
    dsimp only
    split_ifs
    · obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hc
      obtain ⟨H', hW'⟩ := hW'
      have hget : ∀ j < 10, μ'.store.get p.1 (p.2 + j) = some (ps.getD j 0) :=
        fun j hj => Store.get_of_readBlock hp (by omega) 0
      have hnet' : μ'.store.readBlock p.1 (p.2 + 10) (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) := by
        rw [Store.readBlock_sub hp (by omega), hnet, List.take_of_length_le]
        simp [List.length_flatMap]
        omega
      have hPd : ∀ j < 10, Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock f.1 f.2 1) (Store.inBlock p.1 (p.2 + j) 1) := fun j hj =>
        hPWF.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))
      have hit := shIteration_terminates (τ := τ) (ε := ε) (a := w) (rd := (p.1, p.2 + 1))
        (c := (p.1, p.2 + 2)) (thr := (p.1, p.2 + 3)) (wg := (p.1, p.2 + 4))
        (wr := (p.1, p.2 + 5)) (ww := (p.1, p.2 + 6)) (wp := (p.1, p.2 + 7))
        (g := (p.1, p.2 + 10)) (f := f) hS hL hNat hC hQ hSE hD hkq hkn hWF
        (by
          refine hPWF.symm.mono le_rfl ?_
          refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_)
            ?_ <;> exact Fp.inBlock_le_inBlock (by dsimp only; omega) (by dsimp only; omega))
        (by have := hl; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto)
        hW' (hget 1 (by omega)) (hget 2 (by omega)) (hget 3 (by omega)) (hget 4 (by omega))
        (hget 5 (by omega)) (hget 6 (by omega)) (hget 7 (by omega)) hnet' (by omega)
      refine hit.frame_seq_le rfl rfl (by
        have := hl; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto) (by fp_sub) ?_
      rintro μ₂ hfr₂ ⟨hW₂, -⟩
      have hc₂ := hc.of_eqOff (by fp_sub) hfr₂
      refine ((roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hc₂
        hW₂).in_frame rfl rfl (hc₂.2.2.2.1.mono (by simp))).mono (by fp_sub) fun _ _ h => h
    · exact (roundedDecoupleExit_terminates hL hC hc hW' hx).in_frame rfl rfl
        (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto)
  · rintro μ' - ⟨hc, hW', x, hx⟩
    exact (roundedDecoupleExit_terminates hL hC hc hW' hx).in_frame rfl rfl
      (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at this ⊢; tauto)

/-- **The rounded decoupling loop terminates on every tape and every matrix**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], termination only): on a scalar machine with exact
comparisons, index literals, index conversion and exact natural literals up to $n_{\max} + 1$, a
`SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
`NLAlib.ShiftedQR.roundedDecouple` with the parameter words
`NLAlib.ShiftedQR.roundedDecoupleParams` and $k = 2^q$ is a
`NLAlib.ShiftedQR.TerminatingDecoupler` for orders up to $n_{\max} + 1$, with any iteration cap
$F$. No numerical hypothesis is needed: the loop is capped, every operation succeeds on stored
operands, and the two index words $q \le k$ and $|\mathrm{net}| \le n_p$ are exact. -/
theorem roundedDecouple_terminatingDecoupler {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I)
    {k q F : ℕ} (hkq : k = 2 ^ q) (tL R tv γ B α ε : ℝ) :
    TerminatingDecoupler nmax k F (roundedDecoupleParams tL R tv γ B α ε k q)
      (roundedDecouple (O := O) (Q := Q)) I := by
  intro n w p f tape μ H hk hn hW hp hl hrw hrf hWF hPWF
  set ps := roundedDecoupleParams tL R tv γ B α ε k q with hps
  have hlen : ps.length = 10 + 2 * (excNet ε).length := length_roundedDecoupleParams ..
  have hnet : ps.drop 10 = (excNet ε).flatMap fun z => [z.re, z.im] := by
    simp [ps, roundedDecoupleParams]
  have hqk : q ≤ k := hkq ▸ (Nat.lt_two_pow_self).le
  have hNat' : IsExactNatLit id M (n + 1) := hNat.mono (by omega)
  have h1 : w.1 < μ.store.length := hl w (by simp)
  have h2 : p.1 < μ.store.length := hl p (by simp)
  have h3 : f.1 < μ.store.length := hl f (by simp)
  unfold roundedDecouple
  change Writes .total I tape (Stmt.allocs [.const 5] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [5]) rfl
    (fun hBelow ⟨⟨x, hF'⟩, H', hW'⟩ => ⟨⟨x, hBelow.get_of h3 hF'⟩, H', hW'.of_below hBelow h1⟩) ?_
  intro s₁ hlen' hlens hBelow
  set L := μ.store.length
  have hl0 := hlens 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hlen'
  have hctx : DecoupleLoopCtx n L w p f ps ⟨s₁, μ.pos⟩ := by
    refine ⟨h1, h2, h3, ?_, hBelow.readBlock_of h2 hp, by rw [(hBelow w.1 h1).1]; exact hrw,
      by rw [(hBelow f.1 h3).1]; exact hrf, by simpa using hl0.ge, hWF, hPWF⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hlen']
    omega
  have hget : ∀ j < 10, s₁.get p.1 (p.2 + j) = some (ps.getD j 0) :=
    fun j hj => Store.get_of_readBlock hctx.2.2.2.2.1 (by omega) 0
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 8 (by omega)) (by simp [ps,
    roundedDecoupleParams]) hqk ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by simp [ps,
    roundedDecoupleParams]) (show (excNet ε).length ≤ ps.length by omega) ?_
  refine ((roundedDecoupleLoop_terminates (τ := tape) (F := F) hS hL hNat' hC hQ hSE hD hkq hk hlen
    hnet hctx (hW.of_below hBelow h1)).in_frame rfl rfl ?_).mono ?_ fun _ _ h => h
  · exact hctx.2.2.2.1.mono (by simp)
  · exact sup_le le_sup_left (fun b i h => Or.inr (show L ≤ b from h.1 ▸ le_rfl))

end Decouple

end NLAlib.ShiftedQR
