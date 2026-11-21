/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Decouple

/-!
# Termination of the last-eigenvalue decoupling

The decoupling loop of `NLAlib.SmallEig.decoupleLast` runs to completion on every tape and from
every stored matrix: each round is a recorded rounded step, a validation of its slot and a scan, all
of which complete on any scalar machine whose index literals and natural literals up to the order
are exact, and the loop is capped.

## Main results

* `NLAlib.SmallEig.decoupleLast_terminates`: the decoupling completes on every tape.
-/

@[expose] public section

open scoped Matrix
namespace NLAlib.SmallEig

open Ops ShiftedQR

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- One round of `NLAlib.SmallEig.decoupleLast` on any matrix: a step recorded in the pending slot,
the validation of the slot and a scan keep the operands and close one more slot. -/
private theorem decoupleLast_round_terminates {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp id I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 2)) {ζ : ℂ} {τ : Tape ℝ} {ρ : Env} {μ : Mem ℝ} {L i : ℕ}
    {h lam qw f lg : ℕ × ℕ} {t : ℝ} {ns w : ℕ} {LL Ls : List (Option (List GivensEntry))}
    {dsM dsV dsS : List IExp} {asM asV asS : List Operand}
    (hdM : IExp.evalList ρ.idx dsM = some [n + 2, 1, w, LL.length + i])
    (haM : Operand.evalList ρ asM = some [h, lam, h, (L + 1, 0), lg])
    (hdV : IExp.evalList ρ.idx dsV = some [w, LL.length + i])
    (haV : Operand.evalList ρ asV = some [lg])
    (hdS : IExp.evalList ρ.idx dsS = some [n + 2, 1])
    (haS : Operand.evalList ρ asS = some [h, (qw.1, qw.2 + 7), (L, 0)])
    (hlgL : lg.1 < L) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1)
    (hc : DecoupleLastCtx n L h lam qw f ζ t μ.store) {H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (hW : HoldsMatrix h H' μ.store) (hLs : Ls.length = i)
    (hpl : ∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 2)
    (hlg : HoldsSlottedLog lg ns w (LL ++ Ls) [] μ.store) (hj : LL.length + i < ns)
    (hw : n + 1 ≤ w) :
    Writes .total I τ
      (.seq (.frame dsM asM (multiStepStable (Op := O) (Tst := Q)))
        (.seq (.frame dsV asV (slottedLogValidate (O := O) (Q := Q)))
          (.frame dsS asS (bottomScan (O := O) (Q := Q))))) ρ
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock L 0 5 ⊔
        Store.inBlock (L + 1) 0 2 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => DecoupleLastCtx n L h lam qw f ζ t μ'.store ∧
        (∃ H'' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, HoldsMatrix h H'' μ'.store) ∧
        (∃ x, μ'.store.get L 3 = some x) ∧
        ∃ Ls' : List (Option (List GivensEntry)), Ls'.length = i + 1 ∧
          (∀ e ∈ slotEntries w Ls', e.1 + 1 < n + 2) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls') [] μ'.store) μ := by
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hlen := hc.1
  have hhL : h.1 < L := hc.2.1
  have hlamL : lam.1 < L := hc.2.2.1
  have hqL : qw.1 < L := hc.2.2.2.1
  have hgh : h.1 ≠ lg.1 := hlgb h (by simp)
  have hgl : lam.1 ≠ lg.1 := hlgb lam (by simp)
  have hgq : qw.1 ≠ lg.1 := hlgb qw (by simp)
  have hdc := hc.2.2.2.2.2.2.2.2.2.2
  have hRH : ∀ {o k : ℕ}, Fp.Disj (Store.inBlock L o k)
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) := Fp.disj_inBlock_of_ne (by omega)
  have hDL : ∀ {b o k : ℕ}, b ≠ lam.1 → b ≠ qw.1 →
      Fp.Disj (Store.inBlock b o k)
        (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock qw.1 (qw.2 + 7) 1) :=
    fun h1 h2 => Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne h1, Fp.disj_inBlock_of_ne h2⟩
  have hlgD := hDL (b := lg.1) (o := lg.2) (k := ns * (1 + 5 * w)) (Ne.symm hgl) (Ne.symm hgq)
  have hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock h.1 h.2 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
        Store.inBlock lam.1 lam.2 (2 * 1) ⊔ Store.inBlock (L + 1) 0 (2 * 1)) :=
    Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm hgh),
      Fp.disj_inBlock_of_ne (Ne.symm hgl)⟩, Fp.disj_inBlock_of_ne (by omega)⟩
  refine (multiStepStable_terminates (k := 1) (τ := τ) (a := h) (s := lam) (ds := (L + 1, 0))
    (n := n + 1) hS hzero hC hL hNat (by omega) hlg (by simp; omega) (by omega)
    (by simp [Mem.Live, hlen]; omega) hW (by simpa using hc.2.2.2.2.2.1)
    (by simp [hc.2.2.2.2.2.2.2.2.1]) (hdc.mono le_rfl (le_sup_left.trans le_sup_left))
    (Fp.disj_inBlock_of_ne (by omega)) (Fp.disj_inBlock_of_ne (by omega)) hlgd).frame_seq_le
    (by rw [List.length_append, hLs]; exact hdM) haM (by simp [Mem.Live, hlen]; omega)
    (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right) ?_
  rintro μ₁ hf₁ ⟨-, ⟨H'', hW''⟩, -, es, hes, hpl', hlg₁⟩
  have hc₁ := hc.of_eqOff_of_disj (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
    ⟨hdc.mono le_rfl le_sup_left, hDL (by omega) (by omega)⟩, hlgD⟩) hf₁
  refine ((slottedLogValidate_writes_of_exactNat hL (hNat.mono (by omega)) hlg₁
    (by simp; omega)).in_frame (by rw [List.length_append, hLs]; exact hdV) haV
    (by simp [Mem.Live, hc₁.1]; omega)).seq_le le_sup_right ?_
  rintro μ₂ hf₂ ⟨-, hlg₂⟩
  have hc₂ := hc₁.of_eqOff_of_disj hlgD hf₂
  have hW₂ := hW''.of_eqOff hf₂ (Fp.disj_inBlock_of_ne (Ne.symm hgh))
  refine ((bottomScan_terminates_decoupleLastCtx hS hL hNat hC hc₂ hW₂).in_frame hdS haS
    (by simp [Mem.Live, hc₂.1]; omega)).mono
    ((le_sup_right.trans le_sup_left).trans le_sup_left) ?_
  rintro μ₃ hf₃ hs₃
  refine ⟨hc₂.of_eqOff (le_sup_right.trans le_sup_left) hf₃, ⟨H'', hW₂.of_eqOff hf₃ hRH⟩, hs₃,
    Ls ++ [some es], by simp [hLs], planes_slotEntries_append_some (by omega) hpl hpl', ?_⟩
  rw [← List.append_assoc]
  exact hf₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_inBlock_of_ne (by omega)) hlg₂

omit [Has IdxTst Q] in
/-- `NLAlib.SmallEig.decoupleLast` terminates on every tape: from `NLAlib.SmallEig.DecoupleInput`
with any matrix of order $n + 2$ and at least eight words, on a scalar machine with index
literals, exact natural literals up to $n + 2$ and exact comparisons, it writes only
the matrix and the flag and stores both. -/
theorem decoupleLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {n m₂ : ℕ}
    (hNat : IsExactNatLit id M (n + 2)) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) {τ : Tape ℝ} {μ : Mem ℝ} {h lam qw f : ℕ × ℕ}
    (hin : DecoupleInput H ζ qs h lam qw f μ)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + m₂ ≤ ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [n + 2, m₂, w, LL.length] [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => (∃ H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, HoldsMatrix h H' μ'.store) ∧
        ∃ x, μ'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length ≤ m₂ ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 2) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store) μ := by
  obtain ⟨hl, ⟨hhr, -, -, hfr, -⟩, ⟨dH, -, -, -⟩, hHs, hlam, hqw⟩ := hin
  simp only [Fp.blocks_cons, Fp.blocks_nil] at dH
  have hh1 : h.1 < μ.store.length := hl h (by simp)
  have hl1 : lam.1 < μ.store.length := hl lam (by simp)
  have hq1 : qw.1 < μ.store.length := hl qw (by simp)
  have hf1 : f.1 < μ.store.length := hl f (by simp)
  have hlg1 : lg.1 < μ.store.length := hlgl lg (by simp)
  have hlgf : f.1 ≠ lg.1 := hlgb f (by simp)
  unfold decoupleLast
  change Writes .total I τ (Stmt.allocs [.const 5, .const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [5, 2]) rfl
    (fun hBelow ⟨⟨H', hW⟩, x, hx, Ls, hLs, hpl, hlg⟩ => ⟨⟨H', hW.of_below hBelow hh1⟩, x,
      hBelow.get_of hf1 hx, Ls, hLs, hpl, hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlg1) hlg⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  set G := Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock L 0 5 ⊔
    Store.inBlock (L + 1) 0 2 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) with hG
  have hc₁ : DecoupleLastCtx n L h lam qw f ζ (qs.getD 7 0) s₁ :=
    ⟨by omega, hh1, hl1, hq1, hf1, hBelow.readBlock_of hl1 hlam,
      hBelow.get_of hq1 (Store.get_of_readBlock hqw (by omega) 0),
      by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      by rw [(hBelow f.1 hf1).1]; omega, dH.mono le_rfl (by fp_sub)⟩
  have hRH : ∀ {o k : ℕ}, Fp.Disj (Store.inBlock L o k)
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) := Fp.disj_inBlock_of_ne (by omega)
  set Inv : ℕ → Mem ℝ → Prop := fun i μ' => DecoupleLastCtx n L h lam qw f ζ (qs.getD 7 0)
    μ'.store ∧ (∃ H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, HoldsMatrix h H' μ'.store) ∧
      (∃ x, μ'.store.get L 3 = some x) ∧ ∃ Ls : List (Option (List GivensEntry)),
        Ls.length = i ∧ (∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 2) ∧
        HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store with hInv
  have hR3 : Store.inBlock L 0 5 ≤ Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔
      Store.inBlock L 0 5 ⊔ Store.inBlock (L + 1) 0 2 := le_sup_right.trans le_sup_left
  have hlog₁ : HoldsSlottedLog lg ns w LL [] s₁ :=
    hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
      (fun b i g => by rw [g.1]; exact hlg1) hlog
  refine (bottomScan_terminates_decoupleLastCtx (τ := τ) (μ := ⟨s₁, μ.pos⟩) hS hL hNat hC
    hc₁ (hHs.of_below hBelow hh1)).frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega)
    (fun b i hb => Or.inr (hb.1 ▸ le_rfl)) ?_
  rintro μ₁ hfr₁ ⟨x₁, hx₁⟩
  have hlogμ₁ : HoldsSlottedLog lg ns w LL [] μ₁.store :=
    hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hlog₁
  have hexit : ∀ i ≤ m₂, ∀ μ' : Mem ℝ, Inv i μ' → Writes .total I τ
      (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ'' => (∃ H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, HoldsMatrix h H' μ''.store) ∧
        ∃ x, μ''.store.get f.1 f.2 = some x ∧ ∃ Ls : List (Option (List GivensEntry)),
          Ls.length ≤ m₂ ∧ (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 2) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) [] μ''.store) μ' := by
    rintro i hi μ' ⟨hc', ⟨H', hW⟩, ⟨x, hx⟩, Ls, hLs, hpl, hlg⟩
    refine (roundedDecoupleExit_writes_word (r := (L, 0)) hL hC (by simpa using hx)
      hc'.2.2.2.2.2.2.2.2.2.1).mono le_rfl ?_
    rintro μ'' hfr ⟨y, hy⟩
    exact ⟨⟨H', hW.of_eqOff hfr (hc'.2.2.2.2.2.2.2.2.2.2.mono le_rfl le_sup_right).symm⟩, y, hy,
      Ls, hLs ▸ hi, hpl,
      hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hlgf) hlg⟩
  refine (writes_whileFuel (N := m₂) rfl (fun _ => G) (fun _ _ => le_rfl)
    (Store.inBlock f.1 f.2 1) Inv _ ⟨hc₁.of_eqOff hR3 hfr₁,
      ⟨H, (hHs.of_below hBelow hh1).of_eqOff hfr₁ hRH⟩, ⟨x₁, hx₁⟩, [], rfl, by simp [slotEntries],
      by rw [List.append_nil]; exact hlogμ₁⟩ ?_ ?_).mono ?_ (fun _ _ h => h)
  · rintro i hi μ' - ⟨hc', ⟨H', hW⟩, ⟨v, hv⟩, Ls, hLs, hpl, hlg⟩
    refine ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero hv), ?_⟩
    dsimp only
    split_ifs with hz
    · exact decoupleLast_round_terminates hS hL hC hNat rfl rfl rfl rfl rfl rfl hlg1 hlgb hc' hW
        hLs hpl hlg (by omega) hw
    · exact (hexit i hi.le μ' ⟨hc', ⟨H', hW⟩, ⟨v, hv⟩, Ls, hLs, hpl, hlg⟩).in_frame rfl rfl
        (by simp [Mem.Live, hc'.1]; omega)
  · rintro μ' - hI
    exact (hexit m₂ le_rfl μ' hI).in_frame rfl rfl (by simp [Mem.Live, hI.1.1]; omega)
  · exact sup_le (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (fun b i hb => Or.inr (hb.1 ▸ le_rfl))) (fun b i hb => Or.inr (hb.1 ▸ Nat.le_succ L)))
      (le_sup_right.trans le_sup_left)) (le_sup_right.trans (le_sup_left.trans le_sup_left))

end Theorems

end NLAlib.SmallEig
