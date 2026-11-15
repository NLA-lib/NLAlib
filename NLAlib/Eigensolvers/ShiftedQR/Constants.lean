/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.StorageNorm
public import NLAlib.Ops.Blas.Power
public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Logic.ScalarOutput
public import NLAlib.Ops.Logic.SpatialScalar

/-!
# Actual scalar initialization of shifted QR parameters

The raw input parameters are stored as conditioning bound, optimality, promising factor,
contraction, and relative deflation tolerance. The program computes the absolute tolerance
from the actual matrix component words before the matrix changes. Persistent parameters are
stored as absolute tolerance, conditioning bound, optimality, promising factor, contraction.
Per-block constants are the squared absolute tolerance and the contraction to power twice the
degree. Norms, powers, copies, and arithmetic all expand to their actual scalar syntax.

## Main results

* `NLAlib.ShiftedQR.initializeParameters`: matrix-dependent persistent parameter initialization.
* `NLAlib.ShiftedQR.iterationConstants`: squared tolerance and contraction power for one block.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Compute the raw matrix norm, form the absolute tolerance, and copy four retained parameters.
Raw parameter words have order `[B,θ,α,γ,δ]`; output words have order `[τ,B,θ,α,γ]`. -/
def initializeParametersWithScratch : Impl Op Tst := opsImpl% [n] (H, Raw, T) → (Params) {
  run matrixNorm.body [n, n] (H, T);
  call (Has.inj ScalarOp.mul) [] (Raw[4], T) → (Params);
  run (unaryMap (Has.inj ScalarOp.copy)).body [4] (Raw, Params[1])
}

/-- Compute persistent parameters with one scoped intermediate norm word. -/
def initializeParameters : Impl Op Tst := opsImpl% [n] (H, Raw) → (Params) {
  let T ← alloc 1;
  run initializeParametersWithScratch.body [n] (H, Raw, T, Params)
}

/-- The three scalar calls before the sequential contraction power. -/
def iterationPrefix : List (ScalarIns ScalarOp) :=
  [⟨.mul, [⟨0, .var 1⟩, ⟨0, .var 1⟩], ⟨2, .var 3⟩⟩,
   ⟨.lit 1, [], ⟨1, .var 2⟩⟩,
   ⟨.sub, [⟨1, .var 2⟩, ⟨0, .var 1 + .const 4⟩], ⟨1, .var 2⟩⟩]

/-- Compute squared tolerance and contraction power using one caller-owned base word. -/
def iterationConstantsWithScratch : Impl Op Tst :=
  ⟨1, 2, 2, .seq (.scalarBlock (iterationPrefix.map ScalarIns.lift))
    (.frame [.const 2 * .var 0] [⟨1, .var 2⟩, ⟨3, .var 4⟩] scalarPower.body)⟩

/-- Compute the two per-block constants with one scoped arithmetic scratch word. -/
def iterationConstants : Impl Op Tst := opsImpl% [k] (Params) → (Threshold, Power) {
  let T ← alloc 1;
  run iterationConstantsWithScratch.body [k] (Params, T, Threshold, Power)
}

private theorem iterationPrefix_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {p t a b : ℕ × ℕ} {tol gamma : ℝ}
    (htp : t.1 ≠ p.1) (hta : t.1 ≠ a.1) (hga : (p.1, p.2 + 4) ≠ a)
    (hTol : m.store.get p.1 p.2 = some tol)
    (hGamma : m.store.get p.1 (p.2 + 4) = some gamma)
    (ht : t.2 < m.store.len t.1) (ha : a.2 < m.store.len a.1) :
    Writes .total I τ (.scalarBlock (iterationPrefix.map ScalarIns.lift))
      (Env.frame [k] [p, t, a, b]) (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock a.1 a.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get a.1 a.2 = some (tol ^ 2) ∧
        μ.store.get t.1 t.2 = some (1 - gamma)) m := by
  let ws := [(a, M.mul tol tol), (t, M.lit 1), (t, M.sub (M.lit 1) gamma)]
  have hev : ScalarIns.evalBlock M.eval (Env.frame [k] [p, t, a, b]) iterationPrefix
      m.store.cellFn = some ws := by
    have hpt := Ne.symm htp
    rcases p with ⟨pb, po⟩
    rcases t with ⟨tb, toff⟩
    rcases a with ⟨ab, ao⟩
    rcases b with ⟨bb, bo⟩
    have hupd (g : ℕ × ℕ → Option ℝ) (u w : ℕ × ℕ) (v : Option ℝ) :
        Function.update g u v w = if w = u then v else g w := Function.update_apply ..
    have hpair := @Prod.mk.injEq ℕ ℕ
    dsimp only [iterationPrefix, ws, Env.frame, Store.cellFn]
    repeat' first
    | rw [ScalarIns.evalBlock.eq_def]
      simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, Option.map_some, false_and,
        if_true, if_false, *]
  have hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  refine (writes_machineScalarBlock (τ := τ) hS hev hroom).mono ?_ ?_
  · intro q i hi
    simp only [ws, List.map_cons, List.map_nil, Fp.cells, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h <;> obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    have ha' := get_updCells (m := m) (ws₁ := [])
      (ws₂ := [(t, M.lit 1), (t, M.sub (M.lit 1) gamma)]) (z := a) (v := M.mul tol tol)
      ha (by simp [show a ≠ t from fun h => hta (congrArg Prod.fst h).symm])
    have ht' := get_updCells (m := m) (ws₁ := [(a, M.mul tol tol), (t, M.lit 1)])
      (ws₂ := []) (z := t) (v := M.sub (M.lit 1) gamma) ht (by simp)
    have hone : M.lit 1 = 1 := by simpa using hE.lit 1
    have hmul : M.mul tol tol = tol ^ 2 := by simpa only [id_eq, pow_two] using hE.mul tol tol
    have hsub : M.sub (M.lit 1) gamma = 1 - gamma := by
      simpa only [id_eq, hone] using hE.sub (M.lit 1) gamma
    exact ⟨rfl, by simpa only [ws, hmul, List.nil_append] using ha',
      by simpa only [ws, hsub, List.cons_append, List.nil_append] using ht'⟩

/-- Actual scalar arithmetic computes the squared absolute tolerance and the contraction
factor to power twice the degree. The two output words may share an arena but are disjoint. -/
theorem iterationConstantsWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {p t a b : ℕ × ℕ} {tol B theta alpha gamma : ℝ}
    (hP : m.store.readBlock p.1 p.2 5 = some [tol, B, theta, alpha, gamma])
    (htp : t.1 ≠ p.1) (hta : t.1 ≠ a.1) (htb : t.1 ≠ b.1)
    (hPout : Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock a.1 a.2 1 ⊔ Store.inBlock b.1 b.2 1))
    (hab : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock b.1 b.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1)
    (ha : a.2 + 1 ≤ m.store.len a.1) (hb : b.2 + 1 ≤ m.store.len b.1) :
    Writes .total I τ iterationConstantsWithScratch.body (Env.frame [k] [p, t, a, b])
      (Store.inBlock t.1 t.2 1 ⊔ Fp.blocks [a, b] [1, 1])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [a, b] [1, 1] =
        some [[tol ^ 2], [(1 - gamma) ^ (2 * k)]]) m := by
  have hTol : m.store.get p.1 p.2 = some tol := by
    simpa using Store.get_of_readBlock hP (j := 0) (by omega) (0 : ℝ)
  have hGamma : m.store.get p.1 (p.2 + 4) = some gamma := by
    simpa using Store.get_of_readBlock hP (j := 4) (by omega) (0 : ℝ)
  have hga : (p.1, p.2 + 4) ≠ a := by
    simpa only [Nat.add_zero, Prod.eta] using
      (hPout.mono le_rfl le_sup_left).ne_offsets (i := 4) (j := 0) (by omega) (by omega)
  have hpl := Store.lt_length_of_get hTol
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  have hal := Store.lt_length_of_lt_len (show a.2 < m.store.len a.1 by omega)
  have hbl := Store.lt_length_of_lt_len (show b.2 < m.store.len b.1 by omega)
  have hp := iterationPrefix_writes (b := b) (k := k) (τ := τ) hS hE htp hta hga hTol hGamma
    (by omega) (by omega)
  refine hp.seq_le (by fp_sub) ?_
  intro μ hfr ⟨hpos, hThresh, hBase⟩
  have hpow := (writes_scalarPower_exact (τ := τ) (n := 2 * k) hS hE hBase
    (by rw [hfr.len_eq]; omega) (Fp.disj_inBlock_of_ne htb)).keep
    (Store.readsOnly_get a.1 a.2 (tol ^ 2)) hab.symm hThresh
  refine (hpow.in_frame rfl rfl (by simp [Mem.Live, hfr.length_eq]; omega)).mono
    (by fp_sub) ?_
  intro μ' _ ⟨⟨hp', hPower⟩, hThreshold⟩
  refine ⟨hp'.trans hpos, ?_⟩
  simp [Mem.readBlocks, Store.readBlock_succ, hPower, hThreshold]

/-- Scoped per-block initialization releases its base word and retains only the two requested
constants. The persistent parameter block is protected from both outputs. -/
theorem iterationConstants_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {p a b : ℕ × ℕ} {tol B theta alpha gamma : ℝ}
    (hP : m.store.readBlock p.1 p.2 5 = some [tol, B, theta, alpha, gamma])
    (hPout : Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock a.1 a.2 1 ⊔ Store.inBlock b.1 b.2 1))
    (hab : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock b.1 b.2 1))
    (ha : a.2 + 1 ≤ m.store.len a.1) (hb : b.2 + 1 ≤ m.store.len b.1) :
    Writes .total I τ iterationConstants.body (Env.frame [k] [p, a, b])
      (Fp.blocks [a, b] [1, 1])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [a, b] [1, 1] =
        some [[tol ^ 2], [(1 - gamma) ^ (2 * k)]]) m := by
  have hpl := Store.lt_length_of_get
    (Store.get_of_readBlock hP (j := 0) (by omega) (0 : ℝ))
  have hal := Store.lt_length_of_lt_len (show a.2 < m.store.len a.1 by omega)
  have hbl := Store.lt_length_of_lt_len (show b.2 < m.store.len b.1 by omega)
  apply writes_allocs_readBlocks (lens := [.const 1]) (ns := [1]) rfl
    (by simp [Mem.Live]; omega)
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : t.2 + 1 ≤ store.len t.1 := by simpa [t] using (hlens 0 (by simp)).ge
  have hbody := iterationConstantsWithScratch_writes (k := k) (τ := τ) (m := ⟨store, m.pos⟩)
    hS hE (hBelow.readBlock_of hpl hP) (by dsimp [t]; omega) (by dsimp [t]; omega)
    (by dsimp [t]; omega) hPout hab ht
    (by rw [(hBelow a.1 hal).1]; exact ha) (by rw [(hBelow b.1 hbl).1]; exact hb)
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le (Fp.inBlock_le_sup_above (by dsimp [t]; omega)) le_sup_left)
    (fun _ _ hp => hp)


/-- The actual matrix component norm supplies the absolute tolerance before the four retained
raw parameters are copied. Persistent words are tolerance followed by those raw parameters. -/
theorem initializeParametersWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a raw t p : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    {B theta alpha gamma delta : ℝ}
    (hl : m.Live [a, raw, t, p]) (hH : HoldsMatrix a H m.store)
    (hRaw : m.store.readBlock raw.1 raw.2 5 = some [B, theta, alpha, gamma, delta])
    (hta : t.1 ≠ a.1) (htr : t.1 ≠ raw.1)
    (hRawP : Fp.Disj (Store.inBlock raw.1 raw.2 5) (Store.inBlock p.1 p.2 5))
    (ht : t.2 + 1 ≤ m.store.len t.1) (hP : p.2 + 5 ≤ m.store.len p.1) :
    Writes .total I τ initializeParametersWithScratch.body (Env.frame [n] [a, raw, t, p])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock p.1 p.2 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock p.1 p.2 5 =
        some [delta * frobNorm H, B, theta, alpha, gamma]) m := by
  have hlive : a.1 < m.store.length ∧ raw.1 < m.store.length ∧
      t.1 < m.store.length ∧ p.1 < m.store.length := by simpa [Mem.Live] using hl
  have hDelta : m.store.get raw.1 (raw.2 + 4) = some delta := by
    simpa using Store.get_of_readBlock hRaw (j := 4) (by omega) (0 : ℝ)
  have hRaw4 : m.store.readBlock raw.1 raw.2 4 = some [B, theta, alpha, gamma] := by
    simpa using Store.readBlock_sub hRaw (o := 0) (n := 4) (by omega)
  have hn := matrixNorm_writes (τ := τ) (H := H) hS hE
    (by simp [Mem.Live]; omega) hH (by omega) hta.symm
  refine hn.frame_seq_le rfl rfl (by simp [Mem.Live]; omega) le_sup_left ?_
  intro μ hfr ⟨hp, hNorm⟩
  have hd := hfr.keep (Store.readsOnly_get raw.1 (raw.2 + 4) delta)
    (Fp.disj_inBlock_of_ne htr) hDelta
  have hr4 := hfr.keep (Store.readsOnly_readBlock raw.1 raw.2 4 [B, theta, alpha, gamma])
    (Fp.disj_inBlock_of_ne htr) hRaw4
  have hsep : Fp.Disj (Store.inBlock p.1 p.2 1) (Store.inBlock raw.1 raw.2 4) :=
    hRawP.symm.mono (Fp.inBlock_le_inBlock le_rfl (by omega))
      (Fp.inBlock_le_inBlock le_rfl (by omega))
  refine ((writes_call_bin (hS .mul) (x := (raw.1, raw.2 + 4)) (y := t) (z := p)
    rfl rfl trivial hd hNorm rfl (fun _ =>
      ⟨by simp [Mem.Live, hfr.length_eq]; omega, by rw [hfr.len_eq]; omega⟩)).keep
    (Store.readsOnly_readBlock raw.1 raw.2 4 [B, theta, alpha, gamma]) hsep hr4).seq_le
    (by fp_sub) ?_
  intro μ₁ hfr₁ ⟨⟨hp₁, hTau⟩, hRaw₁⟩
  have hcopySep : Fp.Disj (Store.inBlock raw.1 raw.2 4)
      (Store.inBlock p.1 (p.2 + 1) 4) :=
    hRawP.mono (Fp.inBlock_le_inBlock le_rfl (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))
  have htail : Fp.Disj (Store.inBlock p.1 (p.2 + 1) 4) (Store.inBlock p.1 p.2 1) := by
    intro b i hhi hlo
    dsimp only [Store.inBlock] at hhi hlo
    omega
  have hcopy := (writes_unaryMap_of_disj_or_eq (md := .total) (m := μ₁) (τ := τ)
    (x := raw) (y := (p.1, p.2 + 1))
    (n := 4) (f := id) (hS .copy)
    (Or.inl hcopySep) hRaw₁ (by rw [hfr₁.len_eq, hfr.len_eq]; omega)).keep
    (Store.readsOnly_get p.1 p.2 (M.mul delta (frobNorm H))) htail hTau
  refine (hcopy.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hfr.length_eq]; omega)).mono
    (by fp_sub) ?_
  intro μ₂ _ ⟨⟨hp₂, hParams⟩, hTau₂⟩
  have hm : M.mul delta (frobNorm H) = delta * frobNorm H := hE.mul delta (frobNorm H)
  refine ⟨hp₂.trans (hp₁.trans hp), ?_⟩
  rw [Store.readBlock_succ, hTau₂, Option.bind_some, hParams]
  simp only [hm, List.map_id, Option.map_some]

/-- Scoped initialization computes the absolute tolerance from the still-raw matrix and
releases its intermediate norm word. Persistent output words have order `[τ,B,θ,α,γ]`. -/
theorem initializeParameters_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a raw p : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    {B theta alpha gamma delta : ℝ}
    (hl : m.Live [a, raw, p]) (hH : HoldsMatrix a H m.store)
    (hRaw : m.store.readBlock raw.1 raw.2 5 = some [B, theta, alpha, gamma, delta])
    (hRawP : Fp.Disj (Store.inBlock raw.1 raw.2 5) (Store.inBlock p.1 p.2 5))
    (hP : p.2 + 5 ≤ m.store.len p.1) :
    Writes .total I τ initializeParameters.body (Env.frame [n] [a, raw, p])
      (Store.inBlock p.1 p.2 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock p.1 p.2 5 =
        some [delta * frobNorm H, B, theta, alpha, gamma]) m := by
  have hlive : a.1 < m.store.length ∧ raw.1 < m.store.length ∧ p.1 < m.store.length := by
    simpa [Mem.Live] using hl
  apply writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl hlive.2.2
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : t.2 + 1 ≤ store.len t.1 := by simpa [t] using (hlens 0 (by simp)).ge
  have hbody := initializeParametersWithScratch_writes (τ := τ) (m := ⟨store, m.pos⟩)
    hS hE (by simp [Mem.Live, t, hlen]; omega) (hH.of_below hBelow hlive.1)
    (hBelow.readBlock_of hlive.2.1 hRaw) (by dsimp [t]; omega) (by dsimp [t]; omega)
    hRawP ht (by rw [(hBelow p.1 hlive.2.2).1]; exact hP)
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le (Fp.inBlock_le_sup_above (by dsimp [t]; omega)) le_sup_left)
    (fun _ _ hp => hp)


end NLAlib.ShiftedQR
