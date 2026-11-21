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

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
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
    (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shPotentialAccept (O := O) (Q := Q))
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
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shTrial (O := O) (Q := Q))
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
    (hg : m.store.get (L + 11) 0 = some gv) (hf : m.store.get f.1 f.2 = some fv) :
    Writes .total I τ (shTrials (O := O) (Q := Q))
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
    (hZ : m.store.readBlock L 0 2 = some [z.re, z.im]) (hRt : m.store.get (L + 1) 0 = some p) :
    Writes .total I τ (shExc (O := O) (Q := Q))
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
    (hT : HoldsMatrix (L + 5, 0) H' m.store) :
    Writes .total I τ (shDecide (O := O) (Q := Q))
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
/-- The `comptau` test of `Sh` terminates on any matrix: with the views and the room of `Sh`,
from any matrix at `A`, any pair at `Z = L` and a stored word at `Cg`, $k \le n$, on a scalar
machine with exact comparisons and the literal $0$ exact, `NLAlib.ShiftedQR.shTestStep` leaves
the step at `T = L + 5` and the words at `P0 = L + 3`, `P1 = L + 4` stored. -/
theorem shTestStep_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k : ℕ} (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    (hr : ShRoom L n k ε f m) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {z : ℂ} {cg : ℝ}
    (hA : HoldsMatrix a H m.store) (hZ : m.store.readBlock L 0 2 = some [z.re, z.im])
    (hcg : m.store.get wg.1 wg.2 = some cg) :
    Writes .total I τ (shTestStep (O := O) (Q := Q))
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
  rintro m₃ hfr₃ ⟨-, ⟨H', hT₃⟩, x, hP₃⟩
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
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (shPrefix (O := O) (Q := Q))
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
    (hctx : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (shStepWithScratch (O := O) (Q := Q))
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
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrf : f.2 < m.store.len f.1) :
    Writes .total I τ (shStep (O := O) (Q := Q))
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  have e : (shStep (O := O) (Q := Q)) = Stmt.allocs [.const 2, .const 1, .const 1,
      .const 1, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 2, .const 2 * .var 2,
      .const 5, .const 1, .const 2 * .var 3, .const 1]
      (.frame [.var 0, .var 1, .var 2, .var 3] [⟨0, .var 4⟩, ⟨1, .var 5⟩, ⟨2, .var 6⟩,
        ⟨3, .var 7⟩, ⟨4, .var 8⟩, ⟨5, .var 9⟩, ⟨6, .var 10⟩, ⟨7, .var 11⟩, ⟨10, .const 0⟩,
        ⟨11, .const 0⟩, ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
        ⟨16, .const 0⟩, ⟨17, .const 0⟩, ⟨18, .const 0⟩, ⟨19, .const 0⟩, ⟨20, .const 0⟩,
        ⟨21, .const 0⟩, ⟨0, .var 4⟩, ⟨9, .var 13⟩]
        (shStepWithScratch (O := O) (Q := Q))) := rfl
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

end NLAlib.ShiftedQR
