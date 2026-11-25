/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledAlg
public import NLAlib.Matrix.Factorizations.LU.ScaledPrefix
public import NLAlib.Matrix.Factorizations.LU.ScaledStepCorrect

/-!
# The actual stored fixed-scale LU loop

Every selected row comes from the actual ratio scan and is recorded as an exact natural
literal. Original row scales follow the same exchanges as the residual and committed lower
rows. The existing weighted Gaussian-prefix theorem proves the final factorization even for
singular matrices and zero original rows.

## Main results

* `NLAlib.LU.scaledLoop_meets`: full actual fixed-scale pivot loop.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The actual factors start at literal zero and the actual scale words are original row
norms. The output factors/history satisfy the canonical fixed-scale specification. -/
def scaledLoopSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] tape t (packed, ls, us) → (packed', ls', us', hs) requires
    ls = List.replicate (n * n) (M.lit 0) ∧ us = List.replicate (n * n) (M.lit 0) ∧
      ∀ i : Fin n, dec (vec ((packed.drop (n * n)).take n) i.val) =
        ‖decodeMatrix dec n n (packed.take (n * n)) i‖
  ensures (factorScaledSpec dec).post [n] t [packed.take (n * n)] [ls', us', hs]

private theorem scaledLoop_initial {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {n : ℕ} {packed : List K} {R L U H : ℕ × ℕ} {s : Store K}
    (hr : s.readBlock R.1 R.2 (n * n + n) = some packed)
    (hl : s.readBlock L.1 L.2 (n * n) = some (List.replicate (n * n) (M.lit 0)))
    (hu : s.readBlock U.1 U.2 (n * n) = some (List.replicate (n * n) (M.lit 0)))
    (hscale : ∀ i : Fin n, dec (vec ((packed.drop (n * n)).take n) i.val) =
      ‖decodeMatrix dec n n (packed.take (n * n)) i‖) :
    IsScaledFactorPrefix dec (decodeMatrix dec n n (packed.take (n * n))) 0
      R L U (R.1, R.2 + n * n) H s := by
  have hr₀ : s.readBlock R.1 R.2 (n * n) = some (packed.take (n * n)) := by
    simpa only [Nat.add_zero, List.drop_zero] using
      Store.readBlock_sub hr (o := 0) (n := n * n) (by omega)
  exact IsScaledFactorPrefix.initial (IsFactorPrefix.initial hM hr₀ hl hu)
    (Store.readBlock_sub hr (o := n * n) (n := n) (by omega)) hscale

private theorem scaledLoop_read_state {dec : K → ℝ} {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {p : Fin n → Fin n} {R L U : ℕ × ℕ} {s : Store K}
    (hf : IsFactorPrefix dec (A.submatrix (luPivotPermutation p k) id) k R L U s)
    (hS : ∀ i : Fin n, ∃ w, s.get R.1 (R.2 + n * n + i.val) = some w ∧
      dec w = ‖A (luPivotPermutation p k i)‖) :
    ∃ rr ss ls us : List K,
      s.readBlock R.1 R.2 (n * n + n) = some (rr ++ ss) ∧
      s.readBlock L.1 L.2 (n * n) = some ls ∧
      s.readBlock U.1 U.2 (n * n) = some us ∧ rr.length = n * n ∧ ss.length = n ∧
      (∀ i j : Fin n, decodeMatrix dec n n rr i j =
        gaussState (A.submatrix (luPivotPermutation p k) id) k i j) ∧
      (∀ i j : Fin n, decodeMatrix dec n n ls i j = if j.val < k then
        luLower (A.submatrix (luPivotPermutation p k) id) i j else 0) ∧
      (∀ i j : Fin n, decodeMatrix dec n n us i j = if i.val < k then
        luUpper (A.submatrix (luPivotPermutation p k) id) i j else 0) ∧
      (∀ i : Fin n, dec (vec ss i.val) = ‖A (luPivotPermutation p k i)‖) := by
  obtain ⟨rr, ls, us, hr, hl, hu, hres, hlo, hup⟩ := hf.read_blocks
  obtain ⟨ss, hs, hscale⟩ := read_scaledPrefix_scales
    (A := A) (p := p) (k := k) (S := (R.1, R.2 + n * n)) hS
  exact ⟨rr, ss, ls, us, Store.readBlock_add hr hs, hl, hu,
    Store.length_of_readBlock hr, Store.length_of_readBlock hs, hres, hlo, hup, hscale⟩

/-- Every scaled pivot is obtained from an executed scan and recorded in the actual log.
The completed weighted prefix proves canonical LU for all matrices, including singular ones. -/
theorem scaledLoop_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (scaledLoop (Op := Op) (Tst := Tst)).Meets I (scaledLoopSpec M dec) := by
  routine_intro [n] (R, L, U, H, selected) reads (packed, ls, us)
  obtain ⟨rfl, rfl, hscale⟩ := hpre
  have hstart := scaledLoop_initial (H := H) hM hpacked hls hus hscale
  loop_inv (fun _ => Fp.blocks [R, L, U, H, selected]
    [n * n + n, n * n, n * n, n, 1])
    (fun k μ => μ.pos = m.pos ∧
      IsScaledFactorPrefix dec (decodeMatrix dec n n (packed.take (n * n))) k
        R L U (R.1, R.2 + n * n) H μ.store)
    with k hk m₁ hfr hP
  case round =>
    obtain ⟨hp, p, hpr, hf, hH, hS, hweighted⟩ := hP
    obtain ⟨rr, ss, ls₁, us₁, hr₁, hl₁, hu₁, hrrlen, hsslen, hres, hlo, hup, hsd⟩ :=
      scaledLoop_read_state hf hS
    have htake : (rr ++ ss).take (n * n) = rr := by rw [← hrrlen, List.take_left]
    have hdrop : ((rr ++ ss).drop (n * n)).take n = ss := by
      rw [← hrrlen, List.drop_left, ← hsslen, List.take_length]
    call (scaledStep_meets (bound := n) hI hcmp hlit hQ hM) [n, k]
      (R, L, U, (H.1, H.2 + k), selected)
      as m₂ hfr₂ hpos₂ (packed₂, ls₂, us₂, hs) hstep
    case' hpre =>
      change (scaledChoiceSpec dec n).pre [n, k] (τ.shift m₁.pos)
        [(rr ++ ss).take (n * n), ((rr ++ ss).drop (n * n)).take n]
      rw [htake, hdrop]
      exact scaledChoice_pre_of_prefix ⟨k, hk⟩ le_rfl hres hsd
    obtain ⟨rw, hrw, rfl⟩ := Store.readBlock_one_eq_some.mp hhs
    obtain ⟨r, hkr, hdr, hselected, hnext⟩ := scaledStepSpec_prefix hM
      (decodeMatrix dec n n (packed.take (n * n))) p ⟨k, hk⟩ hstep
      (by simpa only [htake] using hres) hlo hup (by simpa only [hdrop] using hsd)
    have hr₂ : m₂.store.readBlock R.1 R.2 (n * n) = some (packed₂.take (n * n)) := by
      simpa only [Nat.add_zero, List.drop_zero] using
        Store.readBlock_sub hpacked₂ (o := 0) (n := n * n) (by omega)
    have hs₂ := Store.readBlock_sub hpacked₂ (o := n * n) (n := n) (by omega)
    have hHkeep := hfr₂.keep (Store.readsOnly_indexPrefix_committed dec p k H)
      (by clear * - hRH hLH hUH hHselected; disjoint) hH
    refine ⟨hpos₂.trans hp, ?_⟩
    apply IsScaledFactorPrefix.update _ p ⟨k, hk⟩ r hkr hpr
      (IsFactorPrefix.of_reads hr₂ hls₂ hus₂ hnext.1 hnext.2.1 hnext.2.2.1)
      hHkeep hrw hdr _ hweighted hselected
    intro i
    refine ⟨vec ((packed₂.drop (n * n)).take n) i.val,
      Store.get_of_readBlock hs₂ i.isLt default, ?_⟩
    simpa only [luPivotPermutation_update, Equiv.trans_apply] using hnext.2.2.2 i
  case exit =>
    rintro m₁ _ ⟨hp, hstate⟩
    obtain ⟨ls', us', hs, hl', hu', hh', hout⟩ := hstate.read_outputs (τ.shift m.pos)
    obtain ⟨p, _, hf, _, hS, _⟩ := hstate
    obtain ⟨rr, ss, _, _, hr, _⟩ := scaledLoop_read_state hf hS
    exact ⟨hp, [rr ++ ss, ls', us', hs], Mem.readBlocks_of_cons hr
      (Mem.readBlocks_of_cons hl' (Mem.readBlocks_of_cons hu'
        (Mem.readBlocks_of_cons hh' rfl))), hout⟩

end NLAlib.LU
