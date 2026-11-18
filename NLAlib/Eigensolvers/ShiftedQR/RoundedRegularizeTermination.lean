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
          HoldsSlottedLog lg ns w LL es m'.store) m := by
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (Nat.zero_le _)
  have hD : ∀ b ∈ [a, sp, thr, t, sr, ds, rg], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hl' : m.Live [a, sp, thr, t, sr, ds, rg, lg] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlgl ⊢
    tauto
  unfold trialStep
  refine (copyMatrix_writes (τ := τ) hS hA hrt (hW.symm.mono (by fp_sub) (by fp_sub))).frame_seq_le
    rfl rfl (hl.mono (by simp)) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hT₁⟩
  have hlog₁ := hfr₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hD t (by simp) _ _ _ _)
    hlog
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hs
  have hthr₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr
  have hrep := replicatePair_writes (τ := τ) (sr := sr) hS hs₁ (by rw [hfr₁.len_eq]; exact hrsr)
    (hW.symm.mono (by fp_sub) (by fp_sub))
  refine hrep.frame_seq_le rfl rfl ((hl.congr hfr₁.length_eq).mono (by simp)) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSR₂⟩
  rw [List.length_replicate] at hSR₂
  have hT₂ := hT₁.of_eqOff hfr₂ hts.symm
  have hlog₂ := hfr₂.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
    (hD sr (by simp) _ _ _ _) hlog₁
  have hthr₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr₁
  have hl₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by rw [hfr₂.len_eq, hfr₁.len_eq]
  have hL₂ : m₂.store.length = m.store.length := by rw [hfr₂.length_eq, hfr₁.length_eq]
  have hms := multiStepStable_terminates (τ := τ) (m := m₂) (a := t) (s := sr) (ds := ds)
    hS hzero hC hL hNat (Nat.le_succ n) hlog₂ hj hw ((hl'.congr hL₂).mono (by simp)) hT₂ hSR₂
    (by rw [hl₂]; exact hrds) hts htd hsd
    (Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨(hD t (by simp) _ _ _ _).symm,
      (hD sr (by simp) _ _ _ _).symm⟩, (hD ds (by simp) _ _ _ _).symm⟩)
  refine hms.frame_seq_le rfl rfl ((hl'.congr hL₂).mono (by simp)) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, ⟨H', hT₃⟩, -, es, hes, hpl, hlog₃⟩
  have hthr₃ := hfr₃.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hW.mono (by fp_sub) (by fp_sub),
      hW.mono (by fp_sub) (by fp_sub)⟩, (hD thr (by simp) _ _ _ _).symm⟩) hthr₂
  have hL₃ : m₃.store.length = m.store.length := by rw [hfr₃.length_eq, hL₂]
  have hb := bottomScan_terminates (τ := τ) (m := m₃) (a := t) (t := thr) (r := rg) hS hL hNat hC
    hk hT₃ hthr₃ ((hl.congr hL₃).mono (by simp))
    (by rw [hfr₃.len_eq, hl₂]; exact hrrg) hrg (hW.mono (by fp_sub) (by fp_sub))
  refine (hb.in_frame rfl rfl ((hl.congr hL₃).mono (by simp))).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hscan⟩
  have hlog₄ := hfr₄.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
    (hD rg (by simp) _ _ _ _) hlog₃
  refine ⟨⟨H', hT₃.of_eqOff hfr₄ hrg⟩, ?_⟩
  rcases hscan with ⟨h1, -⟩ | ⟨h0, -⟩
  exacts [⟨_, h1, es, hes, hpl, hlog₄⟩, ⟨_, h0, es, hes, hpl, hlog₄⟩]

omit [Has CmpTst Q] in
/-- The acceptance of a trial terminates on any matrix: on a scalar machine,
`NLAlib.ShiftedQR.trialAccept` copies any matrix at `T` to `A` and stores words in `G` and `Fl`,
writing only these. -/
theorem trialAccept_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hNat : IsExactNatLit id M 1)
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
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body
        (Env.frame [n + 1, w, LL.length] [t, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => HoldsMatrix a H' m'.store ∧ (∃ x, m'.store.get g.1 g.2 = some x) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        HoldsSlottedLog lg ns w (LL ++ [some P]) [] m'.store) m := by
  have hD : ∀ b ∈ [t, a, g, f], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  unfold trialAccept
  refine (copyMatrix_writes (τ := τ) hS hT hra hta).frame_seq_le rfl rfl
    (hl.mono (by simp)) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hA₁⟩
  refine (writes_call_const (hS (.lit 0)) (z := g) rfl trivial
    (by rw [hfr₁.len_eq]; exact hrg)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hG₂⟩
  refine (writes_call_const (hS (.lit 1)) (z := f) rfl trivial
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrf)).seq_le (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, hF₃⟩
  have hlog₃ : HoldsSlottedLog lg ns w LL P m₃.store :=
    hfr₃.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hD f (by simp) _ _ _ _)
      (hfr₂.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hD g (by simp) _ _ _ _)
        (hfr₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hD a (by simp) _ _ _ _) hlog))
  have hL₃ : m₃.store.length = m.store.length := by
    rw [hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq]
  refine ((slottedLogValidate_writes_of_exactNat (τ := τ) hL hNat hlog₃ hj).in_frame
    rfl rfl (by simp [Mem.Live, hL₃, hlgL])).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hlog₄⟩
  exact ⟨((hA₁.of_eqOff hfr₂ (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₃
    (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₄ (hD a (by simp) _ _ _ _).symm,
    ⟨_, hfr₄.keep (Store.readsOnly_get _ _ _) (hD g (by simp) _ _ _ _).symm
      (hfr₃.keep (Store.readsOnly_get _ _ _) hgf.symm hG₂)⟩,
    _, hfr₄.keep (Store.readsOnly_get _ _ _) (hD f (by simp) _ _ _ _).symm hF₃, hlog₄⟩

/-- One trial of `Regularize` terminates on any matrix: on a scalar machine with exact
comparisons, index literals and exact natural literals up to $n + 1$, from any matrix of order
$n + 1$ at `A`, any shift pair at `S`, any threshold word at `Thr` and any words at `G` and `Fl`,
$k \le n$, with live views, room for the scratch `T`, `SR`, `Ds`, `Rg`, the scratch apart from
the inputs, `T` from `SR`, `Ds` and `Rg`, `SR` from `Ds`, and `G`, `Fl` apart from each other,
from the scratch and from the matrix, `NLAlib.ShiftedQR.regularizeTrial` writes only the log and
the matrix, `G`, `Fl` and its scratch, and leaves the matrix, `G` and `Fl` stored. -/
theorem regularizeTrial_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk0 : 0 < k) (hk : k ≤ n) {a sp thr t sr ds rg g f : ℕ × ℕ}
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
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  have hD : ∀ b ∈ [a, sp, thr, t, sr, ds, rg, g, f], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  have hl' : m.Live [a, sp, thr, t, sr, ds, rg, lg] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlgl ⊢
    tauto
  have hl'' : m.Live [a, sp, thr, t, sr, ds, rg, a, g, f, lg] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlgl ⊢
    tauto
  have hrej : HoldsSlottedLog lg ns w (LL ++ [none]) [] m.store := hlog.reject hj
  unfold regularizeTrial
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hg) ?_
  split_ifs
  · have hstep := trialStep_terminates (τ := τ) hS hL hNat hC hk (hl.mono (by simp)) hA hs hthr
      hrt hrsr hrds hrrg hW hts htd hsd hrg hlog hj hw hlgl
      (fun b hb => hlgb b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h | h | h | h <;> simp [h]))
    refine hstep.frame_seq_le rfl rfl hl' (by fp_sub) ?_
    rintro m₁ hfr₁ ⟨⟨H', hT₁⟩, x, hR, es, hes, hpl, hlog₁⟩
    have hA₁ := hA.of_eqOff hfr₁ (Fp.disj_sup_left.mpr
      ⟨hW.mono le_rfl (by fp_sub), (hD a (by simp) _ _ _ _).symm⟩)
    have hGFl : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
        Store.inBlock rg.1 rg.2 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
        (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1) :=
      Fp.disj_sup_left.mpr ⟨hGF.symm.mono (by fp_sub) le_rfl, Fp.disj_sup_right.mpr
        ⟨(hD g (by simp) _ _ _ _).symm, (hD f (by simp) _ _ _ _).symm⟩⟩
    have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGFl.mono le_rfl le_sup_left) hg
    have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGFl.mono le_rfl le_sup_right) hf
    have hlgl₁ : m₁.Live [lg] := by simpa [Mem.Live, hfr₁.length_eq] using hlgL
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR) ?_
    split_ifs
    · have hacc := trialAccept_terminates (τ := τ) (a := a) (g := g) (f := f) hS
        (hNat.mono (by omega)) ((hl.congr hfr₁.length_eq).mono (by simp)) hT₁
        (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hg)
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hf)
        (hW.mono (by fp_sub) (by fp_sub)) (hGF.mono le_rfl (by fp_sub)) hgf hL hlog₁ hj hlgl₁
        (fun b hb => hlgb b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h <;> simp [h]))
      refine (hacc.in_frame rfl rfl ((hl''.congr hfr₁.length_eq).mono (by simp))).mono
        (by fp_sub) ?_
      rintro m₂ - ⟨hA₂, hG₂, x, hF₂, hlog₂⟩
      exact ⟨⟨_, hA₂⟩, hG₂, x, hF₂, [some es], rfl,
        slotEntries_singleton_some w es ▸ forall_mem_padEntries (by omega) hpl, hlog₂⟩
    · exact (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hg₁⟩, _, hf₁, [none], rfl, by simp [slotEntries],
        hlog₁.reject hj⟩).mono bot_le fun _ _ h => h
  · exact (Writes.skip ⟨⟨_, hA⟩, ⟨_, hg⟩, _, hf, [none], rfl, by simp [slotEntries], hrej⟩).mono
      bot_le fun _ _ h => h

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
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
    Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))
  have hFS : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hAS, hW.mono le_rfl (by fp_sub)⟩,
      Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne (hlgb s (by simp)).symm,
        Fp.disj_inBlock_of_ne (hlgb thr (by simp)).symm⟩⟩
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  unfold regularizeTrials
  refine writes_loop (N := k) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun j μ => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' μ.store) ∧
      (∃ x, μ.store.get g.1 g.2 = some x) ∧ ∃ x, μ.store.get f.1 f.2 = some x ∧
      ∃ Ls : List (Option (List GivensEntry)), Ls.length = j ∧
        (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w (LL ++ Ls) [] μ.store)
    ⟨⟨H, hA⟩, ⟨_, hg⟩, _, hf, [], rfl, by simp [slotEntries], by simpa using hlog⟩ ?_
  rintro j hj μ hfr ⟨⟨Hμ, hAμ⟩, ⟨gμ, hgμ⟩, fμ, hfμ, Ls, hLs, hpl, hlogμ⟩
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
  have hlgμ : μ.Live [lg] := by simpa [Mem.Live, hfr.length_eq] using hlgL
  have htr := regularizeTrial_terminates (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hL hNat hC
    (by omega) hk hlμ hAμ hsj hthrμ hgμ hfμ (by rw [hl']; exact hrt) (by rw [hl']; exact hrsr)
    (by rw [hl']; exact hrds) (by rw [hl']; exact hrrg)
    (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left hpair _) _)) hts htd hsd hrg hGF hgf
    hlogμ (by simp; omega) hw hlgμ
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact hlgb s (by simp) | exact hlgb _ (by simp))
  rw [show (LL ++ Ls).length = LL.length + j by simp [hLs]] at htr
  have hlμ' : μ.Live [a, (s.1, s.2 + 2 * j), thr, t, sr, ds, rg, a, g, f, lg] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hlμ hlgμ ⊢
    tauto
  refine (htr.in_frame rfl rfl hlμ').mono le_rfl ?_
  rintro μ' - ⟨hA', hg', x, hf', Ls', hLs', hpl', hlog'⟩
  refine ⟨hA', hg', x, hf', Ls ++ Ls', by simp [hLs, hLs'], ?_, by rwa [← List.append_assoc]⟩
  rw [slotEntries_append]
  intro e he
  rcases List.mem_append.mp he with he | he
  exacts [hpl e he, hpl' e he]

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
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L)
    (hlgv : ∀ b ∈ [a, rd, c, thr, s, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length]
          [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv
  obtain ⟨hA, -, hc, hthr, -, hrf, hlen, -, -, h2, h3, h4, h5, h6⟩ := hctx
  have hlgM : ∀ {i o m o' m'}, L ≤ i →
      Fp.Disj (Store.inBlock i o m) (Store.inBlock lg.1 o' m') :=
    fun hi => Fp.disj_inBlock_of_ne (by omega)
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
  have hlog₁ := hfr₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hlgM (by omega)) hlog
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (L + 2, 0)) hb) ?_
  split_ifs
  · refine (writes_call_const (hS (.lit 0)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    refine ⟨⟨_, hA₁.of_eqOff hfr₂ haf.symm⟩, _, hF₂, List.replicate k none, by simp,
      by simp [slotEntries_replicate_none], ?_⟩
    exact (hfr₂.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
      (Fp.disj_inBlock_of_ne (hlgv f (by simp))) hlog₁).reject_replicate hj
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
  have hlog₃ := hfr₃.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hlgM (by omega))
    (hfr₂.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
      (Fp.disj_inBlock_of_ne (hlgv f (by simp))) hlog₁)
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
      ⟨hsf.symm, hio.mono (by fp_sub) (by fp_sub)⟩⟩) hlog₃ hj hw
    (hlgl.congr hfr.length_eq)
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (dsimp only; omega) | exact hlgv _ (by simp))
  refine (htr.in_frame rfl rfl (by simp [Mem.Live, hL₃]; omega)).mono (by fp_sub) ?_
  rintro m₄ - ⟨hA₄, -, hF₄⟩
  exact ⟨hA₄, hF₄⟩

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
    (hlgl : m.Live [lg]) (hlgL : lg.1 < L)
    (hlgv : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
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
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
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
  have hlgM : ∀ {i o m o' m'}, L ≤ i →
      Fp.Disj (Store.inBlock i o m) (Store.inBlock lg.1 o' m') :=
    fun hi => Fp.disj_inBlock_of_ne (by omega)
  have hslg : Fp.Disj (Store.inBlock s.1 s.2 (2 * k))
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) :=
    Fp.disj_inBlock_of_ne (hlgv s (by simp))
  unfold regularizeWithScratchWith
  refine (copyToWork_writes (τ := τ) (w := (L, 0)) (lo := n + 1 - k) (d := k) hS
    (by simp [Mem.Live, hlen]; omega) hA (by omega) (by simp [h0]) (by disjoint)).frame_seq_le
    rfl rfl (by simp [Mem.Live, hlen]; omega) (le_sup_of_le_left (Fp.inBlock_le_sup_above le_rfl))
    ?_
  rintro m₁ hfr₁ ⟨-, hB⟩
  have hc₁ := hIn (by disjoint) hctx hfr₁
  have hlog₁ := hfr₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hlgM le_rfl) hlog
  have hL₁ : m₁.store.length = L + 7 := by rw [hfr₁.length_eq, hlen]
  have hq₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_inBlock_of_ne (by omega)) hq
  refine (hSE (w := (L, 0)) (q := qw) (o := s) τ m₁ _ le_rfl hB hq₁
    (by simp [Mem.Live, hL₁]; omega) (by rw [hfr₁.len_eq]; exact hrs)
    (by disjoint) hqw.symm).frame_seq_le
    rfl rfl (by simp [Mem.Live, hL₁]; omega) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨xs, hS₂⟩
  have hc₂ := hIn hsIn hc₁ hfr₂
  have hlog₂ := hfr₂.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) hslg hlog₁
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
  have hlog₃ := hfr₃.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨hslg, hlgM (by omega)⟩) hlog₂
  refine (regularizeDecide_terminates (τ := τ) hS hL hNat hC hk hv hc₃ hS₃ hlog₃ hj hw
    (hlgl.congr ((hfr₁.trans' hfr₂).trans' hfr₃).length_eq) hlgL
    (fun b hb => hlgv b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h | h | h <;> simp [h]))).in_frame rfl rfl
    (by simp [Mem.Live, hc₃.2.2.2.2.2.2.1]; omega) |>.mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨hA₄, hF₄⟩
  refine ⟨hA₄, ⟨_, hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) ?_ hS₃⟩, hF₄⟩
  exact Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
    ⟨has, by disjoint⟩, hsf.symm⟩, by disjoint⟩, hslg.symm⟩

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
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  have e : (regularizeWith SE).body = Stmt.allocs [.const 2 * (.var 1 * .var 1),
      .const 2, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 1, .const 2 * .var 1,
      .const 5] (.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5] [⟨0, .var 6⟩,
        ⟨1, .var 7⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩, ⟨4, .var 10⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩,
        ⟨11, .const 0⟩, ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
        ⟨0, .var 6⟩, ⟨6, .var 12⟩, ⟨7, .var 13⟩, ⟨8, .var 14⟩]
        (regularizeWithScratchWith SE).body) := rfl
  have hlv : a.1 < m.store.length ∧ rd.1 < m.store.length ∧ c.1 < m.store.length ∧
      thr.1 < m.store.length ∧ s.1 < m.store.length ∧ f.1 < m.store.length := by
    simpa [Mem.Live] using hl
  have hlgl' : lg.1 < m.store.length := hlgl lg (by simp)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlv
  rw [e]
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨⟨H', hA'⟩, ⟨ys, hS'⟩, ⟨x, hF', Ls, hLs, hpl, hlog'⟩⟩ =>
      ⟨⟨H', hA'.of_below hBelow h1⟩, ⟨ys, hBelow.readBlock_of h5 hS'⟩,
        ⟨x, hBelow.get_of h6 hF', Ls, hLs, hpl,
          hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
            (fun b i g => by rw [g.1]; exact hlgl') hlog'⟩⟩) ?_
  intro s₁ hlen hlens hBelow
  have hl7 := fun i (hi : i < 7) => hlens i (by simpa using hi)
  have hctx : RegularizeCtx m.store.length k H R cw tv a rd c thr s f ⟨s₁, m.pos⟩ := by
    refine ⟨hA.of_below hBelow h1, hBelow.get_of h2 hrd, hBelow.get_of h3 hc,
      hBelow.get_of h4 hthr, by rw [(hBelow s.1 h5).1]; exact hrs,
      by rw [(hBelow f.1 h6).1]; exact hrf, by simpa using hlen, ?_⟩
    simpa using ⟨hl7 0 (by norm_num), hl7 1 (by norm_num), hl7 2 (by norm_num),
      hl7 3 (by norm_num), hl7 4 (by norm_num), hl7 5 (by norm_num), hl7 6 (by norm_num)⟩
  have hlog₁ : HoldsSlottedLog lg ns w LL [] s₁ :=
    hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
      (fun b i g => by rw [g.1]; exact hlgl') hlog
  refine ((regularizeWithScratchWith_terminates hS hL hNat hC hD hk
    ⟨⟨h1, h2, h3, h4, h5, h6⟩, has, haf, hsf, hio⟩ hctx hSE hlq
    ((hBelow.readBlock hlq qw.2 qs.length).trans hq) (hqw.mono (by fp_sub) le_rfl) hlog₁ hj hw
    (by simp [Mem.Live, hctx.2.2.2.2.2.2.1]; omega) hlgl' hlgb).in_frame
    rfl rfl ?_).mono
    (by fp_sub) fun _ _ h => h
  simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hctx.2.2.2.2.2.2.1]
  omega

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
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  unfold regularize
  have hl' : m.Live [a, rd, c, thr, rd, a, s, f, lg] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlgl ⊢
    tauto
  exact (regularizeWith_terminates_at hS hL hNat hC hD hk has haf hsf hio hl hA hrd hc hthr hrs hrf
    (hSE.terminatingSmallEigAt k 0 0 []) (qw := rd) (hl rd (by simp)) (by simp)
    (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega) hlog hj hw hlgl
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hlgb _ (by simp))).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) hl'

end Regularize

end NLAlib.ShiftedQR
