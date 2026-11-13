/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.KernelCall
public import NLAlib.Matrix.Computation.Deflation
public import NLAlib.Matrix.Computation.DeflationProgramTree
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Computation.PairKernels.Hermitian

/-!
# The deflation program computes `deflate`

The refinement of the program `NLAlib.deflateProg` to the shallow `NLAlib.deflate`. Under any
interpretation whose kernels `mm` and `qr` are routines on interleaved pairs, **every successful run
computes exactly `NLAlib.deflate` on the machine of the semantics, the routines and the tape**
(`NLAlib.Computation.ScalarSem.toFloatMachine` with the normal sampler
`NLAlib.Computation.ScalarSem.tapeNormal` of the stored Gaussian tape from the run's tape position,
and the sample matrix `NLAlib.Computation.tapeIndexMatrix` of the positions); under the standard
model with every value in range and exact literals up to $2$ the run always succeeds; for a tape
rounding independent of the position, the same output is `NLAlib.deflate` on the machine with the
sampler `NLAlib.Computation.ScalarSem.gaussianNormal` and the ideal complex Gaussian sample
`NLAlib.Computation.tapeComplexMatrix`. The counts are `NLAlib.deflateCount`.

## Main results

* `NLAlib.holds_of_exec_forRange_drawMul`: the drawn test matrix.
* `NLAlib.holds_of_exec_deflateProg`, `NLAlib.exists_exec_deflateProg`: the refinement (partial
  equality, success) for the builder from any state.
* `NLAlib.deflate_tapeNormal_eq_deflate_gaussianNormal`: the tape sampler as a sampler of ideal
  complex Gaussians.
* `NLAlib.deflateProg.toStmt_compiled`, `NLAlib.deflateProg.holds_of_exec_compiled`,
  `NLAlib.deflateProg.exists_exec_compiled`, `NLAlib.deflateProg.cnt_le_of_exec_compiled`: the
  registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K}

/-- One word of the draw loop of `NLAlib.deflateProg`: a successful run of the Gaussian draw into
the cell `k` of `G`, then its product with the stored $\sqrt{1/2}$ in the cell `s` outside `G`,
writes the draw, then the product, and advances the Gaussian position by one. -/
private theorem exists_of_exec_draw_mul {p : P} {G k : ℕ} {s : Cell ℕ ℕ} (hsG : s.buf ≠ G)
    {t₁ t₂ : St P K C} (hsc : t₁.store.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p))
    (hr : exec I (.seq (.instr (.draw p .gaussian ⟨G, IExp.var k⟩)) (.seq
      (.instr (.bin p .mul ⟨G, IExp.var k⟩ ⟨G, IExp.var k⟩ s)) .skip)) t₁ = some t₂) :
    ∃ (s' s'' : Store P K) (v : K),
      t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) = some s' ∧
      I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian)) (I.sem.sqrtHalf p) = some v ∧
      s'.write p G k v = some s'' ∧ t₂.store = s'' ∧
      t₂.pos = Function.update t₁.pos .gaussian (t₁.pos .gaussian + 1) := by
  obtain ⟨s', hw⟩ : ∃ s', t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) = some s' := by
    cases hw : t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) with
    | none => simp [exec_seq, exec_instr, Instr.run, hw, IExp.eval] at hr
    | some s' => exact ⟨s', rfl⟩
  have hsc' : s'.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p) := by
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hsG)]; exact hsc
  obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian))
      (I.sem.sqrtHalf p) = some v := by
    cases hb : I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian)) (I.sem.sqrtHalf p) with
    | none => simp [exec_seq, exec_instr, Instr.run, hw, hsc', hb, IExp.eval,
        Store.read_of_write_eq_some hw] at hr
    | some v => exact ⟨v, rfl⟩
  obtain ⟨s'', hw2⟩ : ∃ s'', s'.write p G k v = some s'' := by
    cases hw2 : s'.write p G k v with
    | none => simp [exec_seq, exec_instr, Instr.run, hw, hsc', hv, hw2, IExp.eval,
        Store.read_of_write_eq_some hw] at hr
    | some s'' => exact ⟨s'', rfl⟩
  rw [exec_seq_instr_draw (dst := (⟨G, IExp.var k⟩ : Cell ℕ ℕ)) I hw,
    exec_seq_instr_bin (dst := (⟨G, IExp.var k⟩ : Cell ℕ ℕ)) (x := (⟨G, IExp.var k⟩ : Cell ℕ ℕ))
      (y := s) I (Store.read_of_write_eq_some hw) hsc' hv hw2, exec_skip] at hr
  cases hr
  exact ⟨s', s'', v, hw, hv, hw2, rfl, rfl⟩

/-- The draw loop stores the tape sampler's matrix: a successful run of the draw loop of
`NLAlib.deflateProg` (each of the $2n^2$ words of the block at `G` a Gaussian draw times the
stored $\sqrt{1/2}$ in the cell `s`, outside `G`) ends with the block at `G` holding the
$n \times n$ matrix whose entry $k = i + nj$ is sample $k$ of
`NLAlib.Computation.ScalarSem.tapeNormal` on the tape of Gaussian draws from the current
position, the Gaussian position advanced by $2n^2$, and every cell outside the block unchanged.
No printed source. -/
theorem holds_of_exec_forRange_drawMul (p : P) (n : ℕ) {G : ℕ} {s : Cell ℕ ℕ}
    {st st' : St P K C} (hs : st.store.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p))
    (hsG : s.buf ≠ G)
    (h : exec I (forRange (ι := ι) (2 * (.const n * .const n)) fun w => do
      ins (.draw p .gaussian ⟨G, .var w⟩)
      ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)).run st = some st') :
    pairLayout.Holds st'.store p G 0 ((tapeIndexMatrix n).map
        (I.sem.tapeNormal p fun i => I.tape .gaussian (st.pos .gaussian + i))) ∧
      st'.pos = Function.update st.pos .gaussian (st.pos .gaussian + 2 * (n * n)) ∧
      (∀ q b i, b ≠ G → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape := by
  have key : (forRange (ι := ι) (2 * (IExp.const n * IExp.const n)) fun w => do
      ins (.draw p .gaussian ⟨G, .var w⟩)
      ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)).run = .seq
      (.loop (2 * (IExp.const n * IExp.const n)) fun w => .seq
        (.instr (.draw p .gaussian ⟨G, .var w⟩)) (.seq
          (.instr (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)) .skip)) .skip := rfl
  rw [key, exec_seq_skip] at h
  -- the loop keeps the drawn products below $k$, the other cells, the shape and the position
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k t =>
      (∀ w < k, t.store.read p G w = some ((I.sem.bin p .mul
        (I.tape .gaussian (st.pos .gaussian + w)) (I.sem.sqrtHalf p)).getD default)) ∧
      (∀ q b i, b ≠ G → t.store.read q b i = st.store.read q b i) ∧
      t.store.shape = st.store.shape ∧
      t.pos = Function.update st.pos .gaussian (st.pos .gaussian + k)) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun q b i _ => rfl, rfl, ?_⟩
    simp
  · intro k hk t₁ t₂ ⟨hW, hOUT, hsh, hpos⟩ hr
    have hsc : t₁.store.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p) := by
      rw [hOUT p s.buf s.idx.eval hsG]; exact hs
    have hpk : t₁.pos .gaussian = st.pos .gaussian + k := by rw [hpos]; simp
    obtain ⟨s', s'', v, hw, hv, hw2, hs2, hp2⟩ := exists_of_exec_draw_mul hsG hsc hr
    refine ⟨fun w hw' => ?_, fun q b i hb => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge w k with hlt | hge
      · rw [hs2, Store.read_of_write_eq_some_of_ne hw2 (Or.inr (show w ≠ k by omega)),
          Store.read_of_write_eq_some_of_ne hw (Or.inr (show w ≠ k by omega))]
        exact hW w hlt
      · have hwk : w = k := by omega
        subst hwk
        rw [hpk] at hv
        rw [hs2, Store.read_of_write_eq_some hw2]
        simp [hv]
    · rw [hs2, Store.read_of_write_eq_some_of_ne hw2 (Or.inl hb),
        Store.read_of_write_eq_some_of_ne hw (Or.inl hb), hOUT q b i hb]
    · rw [hs2, Store.shape_of_write_eq_some hw2, Store.shape_of_write_eq_some hw, hsh]
    · rw [hp2, hpos]
      simp [Function.update_idem, add_assoc]
  obtain ⟨hW, hOUT, hsh, hpos⟩ := inv
  refine ⟨fun i j (t : Fin 2) => ?_, hpos, fun q b i hb => hOUT q b i hb, hsh⟩
  have hij : (i : ℕ) + n * (j : ℕ) < n * n := by
    have e := Nat.mul_le_mul_left n (show (j : ℕ) + 1 ≤ n from j.isLt)
    rw [Nat.mul_add, Nat.mul_one] at e
    have := i.isLt
    omega
  have hn2 : (2 * (IExp.const n * IExp.const n)).eval = 2 * (n * n) := rfl
  have hw := hW (2 * ((i : ℕ) + n * (j : ℕ)) + t) (by have := t.isLt; omega)
  fin_cases t
  · simpa [pairLayout, tapeIndexMatrix, ScalarSem.tapeNormal, Matrix.map_apply,
      Matrix.of_apply] using hw
  · simpa [pairLayout, tapeIndexMatrix, ScalarSem.tapeNormal, Matrix.map_apply,
      Matrix.of_apply] using hw

omit [Inhabited K] in
private theorem dfH_zcopy_congr (p : P) {m₁ m₂ n₁ n₂ : IExp ℕ} (hm : m₁.eval = m₂.eval)
    (hn : n₁.eval = n₂.eval) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) (st : St P K C) :
    exec I (zcopy (ι := ι) p m₁ n₁ X xo Y yo).run st =
      exec I (zcopy (ι := ι) p m₂ n₂ X xo Y yo).run st := by
  change exec I (.seq (.named "zcopy" _ (.seq (.loop (2 * (m₁ * n₁)) _) .skip)) .skip) st =
    exec I (.seq (.named "zcopy" _ (.seq (.loop (2 * (m₂ * n₂)) _) .skip)) .skip) st
  rw [exec_seq_skip, exec_seq_skip, exec_named, exec_named, exec_seq_skip, exec_seq_skip,
    exec_loop, exec_loop]
  simp only [IExp.eval_mul, IExp.eval_ofNat, hm, hn]

omit [Inhabited K] in
private theorem dfH_zzero_congr (p : P) {m₁ m₂ n₁ n₂ : IExp ℕ} (hm : m₁.eval = m₂.eval)
    (hn : n₁.eval = n₂.eval) (Y : ℕ) (yo : IExp ℕ) (st : St P K C) :
    exec I (zzero (ι := ι) p m₁ n₁ Y yo).run st = exec I (zzero (ι := ι) p m₂ n₂ Y yo).run st := by
  change exec I (.seq (.named "zzero" _ (.seq (.loop (2 * (m₁ * n₁)) _) .skip)) .skip) st =
    exec I (.seq (.named "zzero" _ (.seq (.loop (2 * (m₂ * n₂)) _) .skip)) .skip) st
  rw [exec_seq_skip, exec_seq_skip, exec_named, exec_named, exec_seq_skip, exec_seq_skip,
    exec_loop, exec_loop]
  simp only [IExp.eval_mul, IExp.eval_ofNat, hm, hn]

/-- The product and the factorization of `NLAlib.deflateProg`: the product $\mathbf{P}\mathbf{G}$
into the block at `Yb`, then its factorization into the blocks at `Qf`, `Rf`, end with the block at
`Qf` holding the factor $\mathbf{Q}$ of `qrR (mmR P₀ Gm)`, every cell outside the three blocks
unchanged and the same store shape. -/
private theorem holds_of_exec_kcall_mm_qr {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n : ℕ) {Pm G Yb Qf Rf : ℕ} {po : IExp ℕ} {s σ₁ σ₂ : St P K C}
    {P₀ Gm : Matrix (Fin n) (Fin n) (K × K)}
    (hP : pairLayout.Holds s.store p Pm po.eval P₀) (hG : pairLayout.Holds s.store p G 0 Gm)
    (h1 : Yb ≠ Pm ∨ n = 0) (h2 : Yb ≠ G) (h3 : Qf ≠ Yb) (h4 : Rf ≠ Yb) (h5 : Qf ≠ Rf)
    (hσ₁ : exec I (stmt (ι := ι) (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)]
      [(Yb, 0)])).run s = some σ₁)
    (hσ₂ : exec I (stmt (ι := ι) (.kcall qr p [.const n, .const n] [(Yb, 0)]
      [(Qf, 0), (Rf, 0)])).run σ₁ = some σ₂) :
    pairLayout.Holds σ₂.store p Qf 0 (qrR (mmR P₀ Gm)).1 ∧
      (∀ q b i, b ≠ Yb → b ≠ Qf → b ≠ Rf → σ₂.store.read q b i = s.store.read q b i) ∧
      σ₂.store.shape = s.store.shape ∧ σ₂.pos = s.pos := by
  have hca : blockDisjoint (Yb, 0, n * n * 2) (Pm, po.eval, n * n * 2) = true := by
    rcases h1 with h1 | rfl <;> simp [blockDisjoint, *]
  change exec I (.seq (.kcall mm p _ _ _) .skip) s = some σ₁ at hσ₁
  rw [exec_seq_skip, exec_kcall] at hσ₁
  obtain ⟨s₁, hs₁, rfl⟩ := Option.map_eq_some_iff.mp hσ₁
  have hk₁ : I.kcallStore mm p [n, n, n] [(Pm, po.eval), (G, 0)] [(Yb, 0)] s.store = some s₁ := by
    simpa using hs₁
  obtain ⟨hY, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hP hG hca
    (by simp [blockDisjoint, h2]) hk₁
  change exec I (.seq (.kcall qr p _ _ _) .skip) _ = some σ₂ at hσ₂
  rw [exec_seq_skip, exec_kcall] at hσ₂
  obtain ⟨s₂, hs₂, rfl⟩ := Option.map_eq_some_iff.mp hσ₂
  have hk₂ : I.kcallStore qr p [n, n] [(Yb, 0)] [(Qf, 0), (Rf, 0)] s₁ = some s₂ := by
    simpa using hs₂
  obtain ⟨hQm, -, hfr₂⟩ := hqr.holds_of_kcallStore_eq_some pairLayout.get_put p hY
    (by simp [blockDisjoint, h5]) (by simp [blockDisjoint, h3]) (by simp [blockDisjoint, h4]) hk₂
  refine ⟨hQm, fun q b i hbY hbQ hbR => ?_, (Interp.shape_of_kcallStore_eq_some hk₂).trans
    (Interp.shape_of_kcallStore_eq_some hk₁), rfl⟩
  exact (hfr₂ _ _ _ (by simp [blockDisjoint, hbQ]) (by simp [blockDisjoint, hbR])).trans
    (hfr₁ _ _ _ (by simp [blockDisjoint, hbY]))

/-- The kernel calls and the output copies of `NLAlib.deflateProg`. -/
private theorem holds_kcalls_deflateProg {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n r : ℕ) {Pm Q G Yb Qf Rf : ℕ} {po qo : IExp ℕ} {s s' : St P K C}
    {P₀ Gm : Matrix (Fin n) (Fin n) (K × K)}
    (hP : pairLayout.Holds s.store p Pm po.eval P₀) (hG : pairLayout.Holds s.store p G 0 Gm)
    (hne : (Yb ≠ Pm ∨ n = 0) ∧ Yb ≠ G ∧ Qf ≠ Yb ∧ Rf ≠ Yb ∧ Qf ≠ Rf ∧ Q ≠ Qf)
    (h : exec I (do
      stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
      stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
      zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
      zzero p (.const n) (.const r - .const n) Q
        (qo + 2 * (.const n * (.const r - (.const r - .const n)))) :
        Builder P ι ℕ ℕ Unit).run s = some s') :
    pairLayout.Holds s'.store p Q qo.eval (Matrix.of fun i (j : Fin r) =>
        if hj : (j : ℕ) < n then (qrR (mmR P₀ Gm)).1 i ⟨j, hj⟩ else
          ((I.sem.lit p 0).getD default, (I.sem.lit p 0).getD default)) ∧
      (∀ q b i, b ≠ Yb → b ≠ Qf → b ≠ Rf →
        blockDisjoint (b, i, 1) (Q, qo.eval, 2 * (n * r)) = true →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  rw [exec_run_bind I (b := stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)]
    [(Yb, 0)])) (fun _ => rfl)] at h
  obtain ⟨σ₁, hσ₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_run_bind I (b := stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)]))
    (fun _ => rfl)] at h
  obtain ⟨σ₂, hσ₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hQm, hfr₂, hsh₂, hpos₂⟩ :=
    holds_of_exec_kcall_mm_qr hmm hqr p n hP hG h1 h2 h3 h4 h5 hσ₁ hσ₂
  -- the copy of the first columns
  have hm : r - (r - n) ≤ n ∧ r - (r - n) ≤ r := ⟨by omega, by omega⟩
  have hnr : n * (r - (r - n)) + n * (r - n) = n * r := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.sub_le r n)]
  rw [exec_run_bind I (b := zcopy (ι := ι) p (.const n) (.const r - (.const r - .const n)) Qf 0 Q
    qo) (fun _ => rfl)] at h
  obtain ⟨σ₃, hσ₃, h⟩ := Option.bind_eq_some_iff.mp h
  rw [dfH_zcopy_congr p (m₁ := .const n) (n₁ := .const r - (.const r - .const n))
    (m₂ := .const n) (n₂ := .const (r - (r - n))) rfl rfl] at hσ₃
  have hA : pairLayout.Holds σ₂.store p Qf (IExp.eval 0)
      (Matrix.of fun i (j : Fin (r - (r - n))) => (qrR (mmR P₀ Gm)).1 i ⟨j, by omega⟩) :=
    fun i j t => hQm i ⟨j, by omega⟩ t
  have hXY : blockDisjoint (Q, qo.eval, 2 * (n * (r - (r - n)))) (Qf, IExp.eval 0,
      2 * (n * (r - (r - n)))) = true := by simp [blockDisjoint, h6]
  obtain ⟨hC, hfr₃, hsh₃, hpos₃⟩ := holds_of_exec_zcopy p n (r - (r - n)) hA hXY hσ₃
  -- the zero columns
  rw [dfH_zzero_congr p (m₁ := .const n) (n₁ := .const r - .const n) (m₂ := .const n)
    (n₂ := .const (r - n)) rfl rfl] at h
  obtain ⟨hZ, hfr₄, hsh₄, hpos₄⟩ := holds_of_exec_zzero (toNat := fun _ => 0) (mmR := mmR)
    (qrR := qrR) (unif := fun k (_ : Unit) => k) (normal := fun (_ : Unit) => ((default : K),
      (default : K))) p n (r - n) h
  have hyo : (qo + 2 * (IExp.const n * (IExp.const r - (IExp.const r - IExp.const n)))).eval =
      qo.eval + 2 * (n * (r - (r - n))) := by
    simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_sub, IExp.eval_const, IExp.eval_ofNat]
  rw [hyo] at hZ hfr₄
  refine ⟨fun i j t => ?_, fun q b i hbY hbQ hbR hb => ?_, ?_, hpos₄.trans (hpos₃.trans hpos₂)⟩
  · obtain ⟨t, ht⟩ := t
    change t < 2 at ht
    change s'.store.read p Q (qo.eval + (2 * (i.1 + n * j.1) + t)) = _
    have hj := Nat.mul_le_mul_left n (show j.1 + 1 ≤ r from j.2)
    rw [Nat.mul_succ] at hj
    have hi := i.2
    by_cases hjn : (j : ℕ) < n
    · have hjm : (j : ℕ) < r - (r - n) := by omega
      have hjm' := Nat.mul_le_mul_left n (show j.1 + 1 ≤ r - (r - n) by omega)
      rw [Nat.mul_succ] at hjm'
      rw [hfr₄ _ _ _ (by
        simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
        omega)]
      have := hC i ⟨j, hjm⟩ ⟨t, ht⟩
      simp only [Matrix.of_apply] at this ⊢
      rw [dif_pos hjn]
      exact this
    · have hrn : r - (r - n) = n := by omega
      have hj' : (j : ℕ) - n < r - n := by omega
      have e : n * ((j : ℕ) - n) + n * n = n * j := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      have := hZ i ⟨j - n, hj'⟩ (⟨t, ht⟩ : Fin 2)
      change s'.store.read p Q (qo.eval + 2 * (n * (r - (r - n))) +
        (2 * (i.1 + n * (j.1 - n)) + t)) = _ at this
      rw [hrn] at this
      simp only [Matrix.of_apply, dif_neg hjn]
      have e2 : qo.eval + 2 * (n * n) + (2 * (i.1 + n * (j.1 - n)) + t) =
          qo.eval + (2 * (i.1 + n * j.1) + t) := by omega
      rw [e2] at this
      rw [this]
      rcases t with _ | _ | t
      · rfl
      · rfl
      · omega
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
    have hd : ∀ {o l : ℕ}, (b ≠ Q ∨ i + 1 ≤ o ∨ o + l ≤ i) →
        blockDisjoint (b, i, 1) (Q, o, l) = true := fun h => by
      simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      omega
    rw [hfr₄ _ _ _ (hd (by omega)), hfr₃ _ _ _ (hd (by omega)), hfr₂ _ _ _ hbY hbQ hbR]
  · exact hsh₄.trans (hsh₃.trans hsh₂)

/-- The body of `NLAlib.deflateProg` inside its allocations. -/
private theorem holds_body_deflateProg {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n r : ℕ) {Pm Q t G Yb Qf Rf : ℕ} {po qo : IExp ℕ} {s s' : St P K C}
    {P₀ : Matrix (Fin n) (Fin n) (K × K)} (hP : pairLayout.Holds s.store p Pm po.eval P₀)
    (hPm : n = 0 ∨ (t ≠ Pm ∧ G ≠ Pm ∧ Yb ≠ Pm))
    (hne : t ≠ G ∧ Yb ≠ G ∧ Qf ≠ Yb ∧ Rf ≠ Yb ∧ Qf ≠ Rf ∧ Q ≠ Qf)
    (h : exec I (do
      ins (.lit p ⟨t, 0⟩ 1)
      ins (.litIdx p ⟨t, 1⟩ 2)
      ins (.bin p .div ⟨t, 0⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      ins (.un p .sqrt ⟨t, 0⟩ ⟨t, 0⟩)
      forRange (2 * (.const n * .const n)) fun w => do
        ins (.draw p .gaussian ⟨G, .var w⟩)
        ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)
      stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
      stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
      zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
      zzero p (.const n) (.const r - .const n) Q
        (qo + 2 * (.const n * (.const r - (.const r - .const n)))) :
        Builder P ι ℕ ℕ Unit).run s = some s') :
    pairLayout.Holds s'.store p Q qo.eval
        (deflate (I.sem.toFloatMachine p toNat mmR qrR unif
          (I.sem.tapeNormal p fun i => I.tape .gaussian (s.pos .gaussian + i))) r P₀
          (tapeIndexMatrix n)) ∧
      (∀ q b i, b ≠ t → b ≠ G → b ≠ Yb → b ≠ Qf → b ≠ Rf →
        blockDisjoint (b, i, 1) (Q, qo.eval, 2 * (n * r)) = true →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧
      s'.pos = Function.update s.pos .gaussian (s.pos .gaussian + 2 * (n * n)) := by
  obtain ⟨htG, hrest⟩ := hne
  change exec I (.seq (.instr (.lit p ⟨t, 0⟩ 1)) (.seq (.instr (.litIdx p ⟨t, 1⟩ 2))
    (.seq (.instr (.bin p .div ⟨t, 0⟩ ⟨t, 0⟩ ⟨t, 1⟩)) (.seq (.instr (.un p .sqrt ⟨t, 0⟩ ⟨t, 0⟩))
    (Builder.run do
      forRange (2 * (.const n * .const n)) fun w => do
        ins (ι := ι) (.draw p .gaussian ⟨G, .var w⟩)
        ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)
      stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
      stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
      zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
      zzero p (.const n) (.const r - .const n) Q
        (qo + 2 * (.const n * (.const r - (.const r - .const n))))))))) s = some s' at h
  -- the four instructions
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v₁, hv₁, s₁, hw₁, rfl⟩, rfl⟩, h⟩ := h
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨z₂, hz₂, s₂, hw₂, rfl⟩, rfl⟩, h⟩ := h
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v₃, hv₃, s₃, hw₃, rfl⟩, rfl⟩, h⟩ := h
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a', ha', v₄, hv₄, s₄, hw₄, rfl⟩, rfl⟩, h⟩ := h
  change s.store.write p t 0 v₁ = some s₁ at hw₁
  change s₁.write p t 1 z₂ = some s₂ at hw₂
  change s₂.read p t 0 = some a at ha
  change s₂.read p t 1 = some c at hc
  change s₂.write p t 0 v₃ = some s₃ at hw₃
  change s₃.read p t 0 = some a' at ha'
  change s₃.write p t 0 v₄ = some s₄ at hw₄
  rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by norm_num)),
    Store.read_of_write_eq_some hw₁, Option.some_inj] at ha
  rw [Store.read_of_write_eq_some hw₂, Option.some_inj] at hc
  rw [Store.read_of_write_eq_some hw₃, Option.some_inj] at ha'
  subst ha hc ha'
  have hz₂' : I.sem.lit p 2 = some z₂ := by simpa using hz₂
  have hsq : v₄ = I.sem.sqrtHalf p := by simp [ScalarSem.sqrtHalf, hv₁, hz₂', hv₃, hv₄]
  have hfr₄ : ∀ q b i, b ≠ t → s₄.read q b i = s.store.read q b i := fun q b i h => by
    rw [Store.read_of_write_eq_some_of_ne hw₄ (Or.inl h), Store.read_of_write_eq_some_of_ne hw₃
      (Or.inl h), Store.read_of_write_eq_some_of_ne hw₂ (Or.inl h),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inl h)]
  have hsh₄ : s₄.shape = s.store.shape := by
    rw [Store.shape_of_write_eq_some hw₄, Store.shape_of_write_eq_some hw₃,
      Store.shape_of_write_eq_some hw₂, Store.shape_of_write_eq_some hw₁]
  -- the draws
  rw [exec_run_bind I (b := forRange (ι := ι) (2 * (.const n * .const n)) fun w => do
    ins (.draw p .gaussian ⟨G, .var w⟩)
    ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)) (fun _ => rfl)] at h
  obtain ⟨σ₅, h₅, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hGm, hpos₅, hfr₅, hsh₅⟩ := holds_of_exec_forRange_drawMul (I := I) (ι := ι) p n
    (s := ⟨t, 0⟩) (st := { s with store := s₄, cnt := _ })
    (hsq ▸ Store.read_of_write_eq_some hw₄) htG h₅
  -- the kernel calls and the copies
  obtain ⟨hQ, hfr, hsh, hpos⟩ := holds_kcalls_deflateProg hmm hqr p n r (P₀ := P₀) (s := σ₅)
    (by
      rcases hPm with rfl | ⟨h1, h2, -⟩
      · exact fun i => i.elim0
      intro i j k
      rw [hfr₅ p Pm _ h2.symm]
      change s₄.read p Pm _ = _
      rw [hfr₄ _ _ _ h1.symm]
      exact hP i j k) hGm ⟨hPm.elim Or.inr fun h => Or.inl h.2.2, hrest⟩ h
  refine ⟨hQ, fun q b i hbt hbG hbY hbQ hbR hb => ?_, hsh.trans (hsh₅.trans hsh₄),
    hpos.trans hpos₅⟩
  rw [hfr q b i hbY hbQ hbR hb, hfr₅ q b i hbG]
  exact hfr₄ q b i hbt

/-- The refinement of the deflation program, partial equality: if kernels `mm` and `qr` of
`I` are the routines `mmR` and `qrR` on interleaved pairs, a successful run of
`NLAlib.deflateProg` at size $n$ and rank $r$, from a state whose block at `Pm` holds the stored
$n \times n$ matrix $\mathbf{P}$, with the output block at `Q` of $2nr$ words (in an existing
buffer at tag `p`, so not one of the program's scratch buffers) disjoint from it,
ends with the output block holding
$$\mathsf{deflate}(\mathbf{P}, r)$$
computed by `NLAlib.deflate` on the machine `M` of the semantics at `p` with product `mmR`, QR
`qrR` and the tape sampler `NLAlib.Computation.ScalarSem.tapeNormal` of the Gaussian tape from the
run's position (for every choice of the machine's other black boxes), with the sample
`NLAlib.Computation.tapeIndexMatrix n`; every cell outside the output block is unchanged, the
store shape too, and the Gaussian position is advanced by $2n^2$. No printed source. -/
theorem holds_of_exec_deflateProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n r : ℕ) {Pm Q : ℕ} {po qo : IExp ℕ}
    {st st' : St P K C} {P₀ : Matrix (Fin n) (Fin n) (K × K)}
    (hP : pairLayout.Holds st.store p Pm po.eval P₀)
    (hQP : blockDisjoint (Q, qo.eval, 2 * (n * r)) (Pm, po.eval, 2 * (n * n)) = true)
    (hQ : ∃ len, st.store.shape[Q]? = some (p, len) ∧ qo.eval + 2 * (n * r) ≤ len)
    (h : exec I (deflateProg p mm qr (.const n) (.const r) Pm po Q qo).run st = some st') :
    pairLayout.Holds st'.store p Q qo.eval
        (deflate (I.sem.toFloatMachine p toNat mmR qrR unif
          (I.sem.tapeNormal p fun i => I.tape .gaussian (st.pos .gaussian + i))) r P₀
          (tapeIndexMatrix n)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Q, qo.eval, 2 * (n * r)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos .gaussian (st.pos .gaussian + 2 * (n * n)) := by
  obtain ⟨len, hQs, -⟩ := hQ
  have hQS : Q < st.store.size := by
    rw [← Store.size_shape]
    exact (Array.getElem?_eq_some_iff.mp hQs).1
  have hprog : (deflateProg p mm qr (.const n) (.const r) Pm po Q qo).run =
      .seq (.alloc p 2 fun t => .alloc p (2 * (.const n * .const n)) fun G =>
        .alloc p (2 * (.const n * .const n)) fun Yb =>
        .alloc p (2 * (.const n * .const n)) fun Qf =>
        .alloc p (2 * (.const n * .const n)) fun Rf => (do
          ins (.lit p ⟨t, 0⟩ 1)
          ins (.litIdx p ⟨t, 1⟩ 2)
          ins (.bin p .div ⟨t, 0⟩ ⟨t, 0⟩ ⟨t, 1⟩)
          ins (.un p .sqrt ⟨t, 0⟩ ⟨t, 0⟩)
          forRange (2 * (.const n * .const n)) fun w => do
            ins (.draw p .gaussian ⟨G, .var w⟩)
            ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)
          stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
          stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
          zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
          zzero p (.const n) (.const r - .const n) Q
            (qo + 2 * (.const n * (.const r - (.const r - .const n)))) :
            Builder P ι ℕ ℕ Unit).run) .skip := rfl
  rw [hprog, exec_seq_skip, exec_alloc] at h
  obtain ⟨st₁, h₁, e₁⟩ := Option.map_eq_some_iff.mp h
  clear h
  rw [exec_alloc] at h₁
  obtain ⟨st₂, h₂, e₂⟩ := Option.map_eq_some_iff.mp h₁
  clear h₁
  rw [exec_alloc] at h₂
  obtain ⟨st₃, h₃, e₃⟩ := Option.map_eq_some_iff.mp h₂
  clear h₂
  rw [exec_alloc] at h₃
  obtain ⟨st₄, h₄, e₄⟩ := Option.map_eq_some_iff.mp h₃
  clear h₃
  rw [exec_alloc] at h₄
  obtain ⟨st₅, h₅, e₅⟩ := Option.map_eq_some_iff.mp h₄
  clear h₄
  subst e₁ e₂ e₃ e₄ e₅
  have hPm : n = 0 ∨ Pm < st.store.size := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr (Store.lt_size_of_read_eq_some (hP ⟨0, h⟩ ⟨0, h⟩ (0 : Fin 2)))
  obtain ⟨hQ', hfr', hsh', hpos'⟩ := holds_body_deflateProg (toNat := toNat) (unif := unif)
    hmm hqr p n r (P₀ := P₀) (h := h₅) (by
      rcases hPm with rfl | hPm
      · exact fun i => i.elim0
      intro i j k
      dsimp only
      repeat rw [Store.read_push_of_lt
        (by first | omega | (simp only [Array.size_push]; omega))]
      exact hP i j k)
    (by
      rcases hPm with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [Array.size_push]; omega))
    (by simp only [Array.size_push]; omega)
  have hsz : st₅.store.size = st.store.size + 5 := by
    rw [Store.size_eq_of_shape_eq hsh']; simp
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size → Store.read (Array.pop (Array.pop
      (Array.pop (Array.pop (Array.pop st₅.store))))) q b i = st₅.store.read q b i := by
    intro q b i hb
    repeat rw [Store.read_pop_of_lt (by first | omega | (simp only [Array.size_pop]; omega))]
  refine ⟨hQ'.of_forall_read_eq fun i _ _ => hpop hQS, fun q b' i hb' => ?_, ?_, hpos'⟩
  · rcases Nat.lt_or_ge b' st.store.size with hb'' | hb''
    · rw [hpop hb'', hfr' q b' i (by omega) (by simp only [Array.size_push]; omega)
        (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
        (by simp only [Array.size_push]; omega) hb']
      repeat rw [Store.read_push_of_lt
        (by first | omega | (simp only [Array.size_push]; omega))]
    · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le hb'']
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop st₅.store))))) = _
    rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, Store.shape_pop, Store.shape_pop, hsh']
    simp [Store.shape]

private theorem exists_exec_kcalls_deflateProg {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n r : ℕ) {Pm Q G Yb Qf Rf : ℕ} {po qo : IExp ℕ} {s : St P K C}
    {P₀ Gm : Matrix (Fin n) (Fin n) (K × K)}
    (hP : pairLayout.Holds s.store p Pm po.eval P₀) (hG : pairLayout.Holds s.store p G 0 Gm)
    (hYb : s.store.shape[Yb]? = some (p, 2 * (n * n)))
    (hQf : s.store.shape[Qf]? = some (p, 2 * (n * n)))
    (hRf : s.store.shape[Rf]? = some (p, 2 * (n * n)))
    (hQ : ∃ len, s.store.shape[Q]? = some (p, len) ∧ qo.eval + 2 * (n * r) ≤ len)
    (hne : (Yb ≠ Pm ∨ n = 0) ∧ Yb ≠ G ∧ Qf ≠ Yb ∧ Rf ≠ Yb ∧ Qf ≠ Rf ∧ Q ≠ Qf) :
    ∃ s', exec I (do
      stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
      stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
      zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
      zzero p (.const n) (.const r - .const n) Q
        (qo + 2 * (.const n * (.const r - (.const r - .const n)))) :
        Builder P ι ℕ ℕ Unit).run s = some s' := by
  obtain ⟨len, hQs, hle⟩ := hQ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  have hsz : ∀ (A : Matrix (Fin n) (Fin n) (K × K)) {st : Store P K} {b : ℕ},
      st.shape[b]? = some (p, 2 * (n * n)) → ∃ st', st.writeBlock p b 0 (pairLayout.toArray A) =
        some st' := fun A st b hb => Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi =>
    ⟨_, hb, by simp only [EntryLayout.size_toArray, pairLayout] at hi; linarith⟩
  have hca : blockDisjoint (Yb, 0, n * n * 2) (Pm, po.eval,
      n * n * 2) = true := by rcases h1 with h1 | rfl <;> simp [blockDisjoint, *]
  have hcb : blockDisjoint (Yb, 0, n * n * 2) (G, 0,
      n * n * 2) = true := by simp [blockDisjoint, h2]
  obtain ⟨s₁, hs₁⟩ := hsz (mmR (pairLayout.toMatrix n n (pairLayout.toArray P₀))
    (pairLayout.toMatrix n n (pairLayout.toArray Gm))) hYb
  have hk₁ : I.kcallStore mm p [n, n, n] [(Pm, po.eval), (G, 0)] [(Yb, 0)] s.store = some s₁ :=
    (hmm.kcallStore_eq p ((pairLayout.holds_iff_readBlock_eq_some _ _ _ _ _).mp hP)
      ((pairLayout.holds_iff_readBlock_eq_some _ _ _ _ _).mp hG) hca hcb).trans hs₁
  have hY := (hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hP hG hca hcb hk₁).1
  have hd₁ : blockDisjoint (Qf, 0, n * n * 2) (Rf, 0,
      n * n * 2) = true := by simp [blockDisjoint, h5]
  have hd₂ : blockDisjoint (Qf, 0, n * n * 2) (Yb, 0,
      n * n * 2) = true := by simp [blockDisjoint, h3]
  have hd₃ : blockDisjoint (Rf, 0, n * n * 2) (Yb, 0,
      n * n * 2) = true := by simp [blockDisjoint, h4]
  have hsh₁ := Store.shape_of_writeBlock_eq_some hs₁
  obtain ⟨s₂, hs₂⟩ := hsz (qrR (pairLayout.toMatrix n n (pairLayout.toArray (mmR P₀ Gm)))).1
    (b := Qf) (by rw [hsh₁]; exact hQf)
  have hsh₂ := Store.shape_of_writeBlock_eq_some hs₂
  obtain ⟨s₃, hs₃⟩ := hsz (qrR (pairLayout.toMatrix n n (pairLayout.toArray (mmR P₀ Gm)))).2
    (b := Rf) (by rw [hsh₂, hsh₁]; exact hRf)
  have hk₂ : I.kcallStore qr p [n, n] [(Yb, 0)] [(Qf, 0), (Rf, 0)] s₁ = some s₃ :=
    (hqr.kcallStore_eq p ((pairLayout.holds_iff_readBlock_eq_some _ _ _ _ _).mp hY) hd₁ hd₂
      hd₃).trans (by rw [hs₂, Option.bind_some, hs₃])
  have hQm := (hqr.holds_of_kcallStore_eq_some pairLayout.get_put p hY hd₁ hd₂ hd₃ hk₂).1
  have hsh₃ := (Store.shape_of_writeBlock_eq_some hs₃).trans (hsh₂.trans hsh₁)
  have hm : r - (r - n) ≤ n ∧ r - (r - n) ≤ r := ⟨by omega, by omega⟩
  have hnr : n * (r - (r - n)) + n * (r - n) = n * r := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.sub_le r n)]
  change ∃ s', exec I (.seq (.kcall mm p _ _ _) (.seq (.kcall qr p _ _ _)
    (.seq (.named _ _ (.seq (.loop _ _) .skip)) (.seq (.named _ _ (.seq (.loop _ _) .skip))
    .skip)))) s = some s'
  rw [exec_seq, exec_kcall, show I.kcallStore mm p ([IExp.const n, IExp.const n,
    IExp.const n].map IExp.eval) ([(Pm, po), (G, (0 : IExp ℕ))].map fun x => (x.1, x.2.eval))
    ([(Yb, (0 : IExp ℕ))].map fun x => (x.1, x.2.eval)) s.store = some s₁ from hk₁,
    Option.map_some, Option.bind_some, exec_seq, exec_kcall, show I.kcallStore qr p
    ([IExp.const n, IExp.const n].map IExp.eval) ([(Yb, (0 : IExp ℕ))].map fun x =>
    (x.1, x.2.eval)) ([(Qf, (0 : IExp ℕ)), (Rf, 0)].map fun x => (x.1, x.2.eval)) s₁ = some s₃
    from hk₂, Option.map_some, Option.bind_some, exec_seq, exec_named, exec_seq_skip]
  have hA : pairLayout.Holds s₃ p Qf (IExp.eval 0)
      (Matrix.of fun i (j : Fin (r - (r - n))) => (qrR (mmR P₀ Gm)).1 i ⟨j, by omega⟩) :=
    fun i j t => hQm i ⟨j, by omega⟩ t
  have hXY : blockDisjoint (Q, qo.eval, 2 * (n * (r - (r - n)))) (Qf, IExp.eval 0,
      2 * (n * (r - (r - n)))) = true := by simp [blockDisjoint, h6]
  obtain ⟨s₄, h₄⟩ := exists_exec_zcopy (I := I) (ι := ι) p n (r - (r - n)) (yo := qo)
    (st := { s with store := s₃, cnt := _ }) hA hXY ⟨len, by rw [hsh₃]; exact hQs, by nlinarith⟩
  have hsh₄ := (holds_of_exec_zcopy p n (r - (r - n)) hA hXY h₄).2.2.1
  change exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) _ = some s₄ at h₄
  rw [exec_seq_skip, exec_named, exec_seq_skip, exec_loop] at h₄
  rw [exec_loop, show IExp.eval (2 * (IExp.const n * (IExp.const r - (IExp.const r -
    IExp.const n))) : IExp ℕ) = IExp.eval (2 * (IExp.const n * IExp.const (r - (r - n))))
    from rfl, h₄, Option.bind_some,
    exec_seq_skip, exec_named, exec_seq_skip]
  obtain ⟨s₅, h₅⟩ := exists_exec_zzero (I := I) (ι := ι) p n (r - n) (Y := Q)
    (yo := qo + 2 * (.const n * (.const r - (.const r - .const n)))) (st := s₄) hsem
    ⟨len, by rw [hsh₄, hsh₃]; exact hQs, by
      simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_sub, IExp.eval_const, IExp.eval_ofNat]
      omega⟩
  change exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) _ = some s₅ at h₅
  rw [exec_seq_skip, exec_named, exec_seq_skip, exec_loop] at h₅
  rw [exec_loop, show IExp.eval (2 * (IExp.const n * (IExp.const r - IExp.const n)) : IExp ℕ) =
    IExp.eval (2 * (IExp.const n * IExp.const (r - n))) from rfl, h₅]
  exact ⟨s₅, rfl⟩

omit [Inhabited K] in
private theorem exists_exec_drawMul_deflateProg {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {t G : ℕ} {v : K}
    {s : St P K C} (ht : s.store.read p t 0 = some v)
    (hG : s.store.shape[G]? = some (p, 2 * (n * n))) (htG : t ≠ G) :
    ∃ s', exec I (.loop (2 * (.const n * .const n)) fun w => (do
      ins (ι := ι) (.draw p .gaussian ⟨G, .var w⟩)
      ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩) : Builder P ι ℕ ℕ Unit).run) s =
        some s' := by
  refine (exists_exec_loop_eq_some_of_forall I (fun _ s' => s'.store.shape = s.store.shape ∧
    s'.store.read p t 0 = some v) ⟨rfl, ht⟩ ?_).imp fun _ h => h.1
  intro w hw s₀ ⟨hsh, hr⟩
  have hw' : w < 2 * (n * n) := hw
  have hG₀ : s₀.store.shape[G]? = some (p, 2 * (n * n)) := hsh ▸ hG
  obtain ⟨s₁, hw₁⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (I.tape .gaussian (s₀.pos .gaussian)) hG₀ hw'
  obtain ⟨z, hz⟩ := hsem.bin_ok p .mul (I.tape .gaussian (s₀.pos .gaussian)) v trivial
    (by simp) trivial
  obtain ⟨s₂, hw₂⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    (by rw [Store.shape_of_write_eq_some hw₁]; exact hG₀) hw'
  change ∃ s', exec I (.seq (.instr (.draw p .gaussian _)) (.seq (.instr (.bin p .mul _ _ _))
    .skip)) s₀ = some s' ∧ _
  rw [exec_seq_instr_draw I hw₁, exec_seq_instr_bin I (Store.read_of_write_eq_some hw₁)
    ((Store.read_of_write_eq_some_of_ne hw₁ (Or.inl htG)).trans hr) hz hw₂, exec_skip]
  exact ⟨_, rfl, (Store.shape_of_write_eq_some hw₂).trans
    ((Store.shape_of_write_eq_some hw₁).trans hsh), (Store.read_of_write_eq_some_of_ne hw₂
    (Or.inl htG)).trans ((Store.read_of_write_eq_some_of_ne hw₁ (Or.inl htG)).trans hr)⟩

private theorem exists_exec_body_deflateProg {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 2) (p : P) (hu : u p ≤ 1) (n r : ℕ)
    {Pm Q t G Yb Qf Rf : ℕ} {po qo : IExp ℕ} {s : St P K C}
    {P₀ : Matrix (Fin n) (Fin n) (K × K)} (hP : pairLayout.Holds s.store p Pm po.eval P₀)
    (ht : s.store.shape[t]? = some (p, 2)) (hG : s.store.shape[G]? = some (p, 2 * (n * n)))
    (hYb : s.store.shape[Yb]? = some (p, 2 * (n * n)))
    (hQf : s.store.shape[Qf]? = some (p, 2 * (n * n)))
    (hRf : s.store.shape[Rf]? = some (p, 2 * (n * n)))
    (hQ : ∃ len, s.store.shape[Q]? = some (p, len) ∧ qo.eval + 2 * (n * r) ≤ len)
    (hPm : n = 0 ∨ (t ≠ Pm ∧ G ≠ Pm ∧ Yb ≠ Pm))
    (hne : t ≠ G ∧ Yb ≠ G ∧ Qf ≠ Yb ∧ Rf ≠ Yb ∧ Qf ≠ Rf ∧ Q ≠ Qf) :
    ∃ s', exec I (do
      ins (.lit p ⟨t, 0⟩ 1)
      ins (.litIdx p ⟨t, 1⟩ 2)
      ins (.bin p .div ⟨t, 0⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      ins (.un p .sqrt ⟨t, 0⟩ ⟨t, 0⟩)
      forRange (2 * (.const n * .const n)) fun w => do
        ins (.draw p .gaussian ⟨G, .var w⟩)
        ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)
      stmt (.kcall mm p [.const n, .const n, .const n] [(Pm, po), (G, 0)] [(Yb, 0)])
      stmt (.kcall qr p [.const n, .const n] [(Yb, 0)] [(Qf, 0), (Rf, 0)])
      zcopy p (.const n) (.const r - (.const r - .const n)) Qf 0 Q qo
      zzero p (.const n) (.const r - .const n) Q
        (qo + 2 * (.const n * (.const r - (.const r - .const n)))) :
        Builder P ι ℕ ℕ Unit).run s = some s' := by
  obtain ⟨htG, hrest⟩ := hne
  obtain ⟨v₁, hv₁⟩ := hsem.lit_ok p 1 trivial
  obtain ⟨z₂, hz₂, hd₂⟩ := hlit p 2 le_rfl
  obtain ⟨δ₁, hδ₁, hdv₁⟩ := hsem.lit_err p 1 v₁ hv₁
  obtain ⟨v₃, hv₃⟩ := hsem.bin_ok p .div v₁ z₂ trivial (fun _ => by rw [hd₂]; norm_num) trivial
  obtain ⟨δ₃, hδ₃, hdv₃⟩ := hsem.bin_err p .div v₁ z₂ v₃ trivial hv₃
  have hpos : 0 ≤ dec p v₃ := by
    have := abs_le.mp (hδ₁.trans hu)
    have := abs_le.mp (hδ₃.trans hu)
    rw [hdv₃, hdv₁, hd₂]
    simp only [BinOp.realOp, Rat.cast_one, one_mul, Nat.cast_ofNat]
    exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (by linarith)
  obtain ⟨v₄, hv₄⟩ := hsem.sqrt_ok p v₃ hpos
  have hw : ∀ {st : Store P K} (i : ℕ) (v : K), st.shape = s.store.shape → i < 2 →
      ∃ st', st.write p t i v = some st' := fun i v hsh hi =>
    Store.exists_write_eq_some_of_getElem?_shape v (hsh ▸ ht) hi
  obtain ⟨s₁, hw₁⟩ := hw 0 v₁ rfl (by norm_num)
  have hsh₁ := Store.shape_of_write_eq_some hw₁
  obtain ⟨s₂, hw₂⟩ := hw 1 z₂ hsh₁ (by norm_num)
  have hsh₂ := (Store.shape_of_write_eq_some hw₂).trans hsh₁
  obtain ⟨s₃, hw₃⟩ := hw 0 v₃ hsh₂ (by norm_num)
  have hsh₃ := (Store.shape_of_write_eq_some hw₃).trans hsh₂
  obtain ⟨s₄, hw₄⟩ := hw 0 v₄ hsh₃ (by norm_num)
  have hsh₄ := (Store.shape_of_write_eq_some hw₄).trans hsh₃
  change ∃ s', exec I (.seq (.instr (.lit p _ 1)) (.seq (.instr (.litIdx p _ 2))
    (.seq (.instr (.bin p .div _ _ _)) (.seq (.instr (.un p .sqrt _ _))
    (.seq (.loop _ _) _))))) s = some s'
  rw [exec_seq_instr_lit I hv₁ hw₁, exec_seq_instr_litIdx I hz₂ hw₂,
    exec_seq_instr_bin I ((Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by norm_num))).trans
      (Store.read_of_write_eq_some hw₁)) (Store.read_of_write_eq_some hw₂) hv₃ hw₃,
    exec_seq_instr_un I (Store.read_of_write_eq_some hw₃) hv₄ hw₄]
  obtain ⟨s₅, h₅⟩ := exists_exec_drawMul_deflateProg (I := I) (ι := ι) hsem p n
    (s := { s with store := s₄, cnt := _ }) (Store.read_of_write_eq_some hw₄)
    (by rw [hsh₄]; exact hG) htG
  rw [exec_seq, h₅, Option.bind_some]
  have hz₂' : I.sem.lit p 2 = some z₂ := by simpa using hz₂
  have hsq : v₄ = I.sem.sqrtHalf p := by simp [ScalarSem.sqrtHalf, hv₁, hz₂', hv₃, hv₄]
  obtain ⟨hGm, -, hfr, hsh₅⟩ := holds_of_exec_forRange_drawMul (I := I) (ι := ι) p n
    (s := ⟨t, 0⟩) (st := { s with store := s₄, cnt := _ }) (hsq ▸ Store.read_of_write_eq_some hw₄)
    htG (by change exec I (.seq (.loop _ _) .skip) _ = _; rw [exec_seq_skip]; exact h₅)
  have hsh₅' : s₅.store.shape = s.store.shape := hsh₅.trans hsh₄
  refine exists_exec_kcalls_deflateProg hmm hqr hsem p n r (P₀ := P₀) ?_ hGm (hsh₅' ▸ hYb)
    (hsh₅' ▸ hQf)
    (hsh₅' ▸ hRf) (hsh₅' ▸ hQ) ⟨hPm.elim Or.inr fun h => Or.inl h.2.2, hrest⟩
  rcases hPm with rfl | ⟨h1, h2, -⟩
  · exact fun i => i.elim0
  intro i j k
  rw [hfr p Pm _ h2.symm]
  dsimp only
  rw [Store.read_of_write_eq_some_of_ne hw₄ (Or.inl h1.symm),
    Store.read_of_write_eq_some_of_ne hw₃ (Or.inl h1.symm),
    Store.read_of_write_eq_some_of_ne hw₂ (Or.inl h1.symm),
    Store.read_of_write_eq_some_of_ne hw₁ (Or.inl h1.symm)]
  exact hP i j k

/-- The refinement of the deflation program, success: under the standard model at $u$ with
every value in range, $u(p) \le 1$ and exact literals up to $2$, if kernels `mm` and `qr` of `I`
are routines on interleaved pairs, the input block at `Pm` holds a stored matrix and the output
block at `Q` (tag `p`, $2nr$ words, disjoint from it) exists, the run of `NLAlib.deflateProg`
succeeds. No printed source. -/
theorem exists_exec_deflateProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p ≤ 1) (n r : ℕ) {Pm Q : ℕ} {po qo : IExp ℕ} {st : St P K C}
    {P₀ : Matrix (Fin n) (Fin n) (K × K)} (hP : pairLayout.Holds st.store p Pm po.eval P₀)
    (hQP : blockDisjoint (Q, qo.eval, 2 * (n * r)) (Pm, po.eval, 2 * (n * n)) = true)
    (hQ : ∃ len, st.store.shape[Q]? = some (p, len) ∧ qo.eval + 2 * (n * r) ≤ len) :
    ∃ st', exec I (deflateProg p mm qr (.const n) (.const r) Pm po Q qo).run st = some st' := by
  have hmap : ∀ {α β : Type} {o : Option α} {f : α → β}, (∃ x, o = some x) →
      ∃ y, o.map f = some y := fun {_ _ _ f} ⟨x, hx⟩ => ⟨f x, by rw [hx]; rfl⟩
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  apply hmap
  change ∃ st', exec I (.alloc p _ _) _ = some st'
  rw [exec_alloc]; apply hmap
  change ∃ st', exec I (.alloc p _ _) _ = some st'
  rw [exec_alloc]; apply hmap
  change ∃ st', exec I (.alloc p _ _) _ = some st'
  rw [exec_alloc]; apply hmap
  change ∃ st', exec I (.alloc p _ _) _ = some st'
  rw [exec_alloc]; apply hmap
  obtain ⟨len, hQs, hle⟩ := hQ
  have hQS : Q < st.store.size := by
    rw [← Store.size_shape]
    exact (Array.getElem?_eq_some_iff.mp hQs).1
  have hPm : n = 0 ∨ Pm < st.store.size := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr (Store.lt_size_of_read_eq_some (hP ⟨0, h⟩ ⟨0, h⟩ (0 : Fin 2)))
  refine exists_exec_body_deflateProg hmm hqr hsem hlit p hu n r (P₀ := P₀) ?_ ?_ ?_ ?_ ?_ ?_
    ⟨len, ?_, hle⟩ ?_ ?_
  · rcases hPm with rfl | hPm
    · exact fun i => i.elim0
    intro i j k
    dsimp only
    repeat rw [Store.read_push_of_lt
      (by first | omega | (simp only [Array.size_push]; omega))]
    exact hP i j k
  iterate 5
    · repeat rw [Store.getElem?_shape_push_of_lt _
        (by first | omega | (simp only [Array.size_push]; omega))]
      exact Store.getElem?_shape_push_size _ _ _
  · dsimp only
    repeat rw [Store.getElem?_shape_push_of_lt _
      (by first | omega | (simp only [Array.size_push]; omega))]
    exact hQs
  · rcases hPm with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [Array.size_push]; omega)
  · simp only [Array.size_push]; omega

omit [DecidableEq P] [AddMonoid C] in
/-- The tape sampler is a sampler of ideal complex Gaussians: for a rounding $\rho$ of real
draws and an ideal real tape $\xi$, deflation on the machine whose normal sampler is the tape
sampler of the stored tape $\rho \circ \xi$, with the sample of positions
`NLAlib.Computation.tapeIndexMatrix n`, equals deflation on the same machine with the sampler
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$ and the ideal complex Gaussian sample
`NLAlib.Computation.tapeComplexMatrix ξ n`. No printed source. -/
theorem deflate_tapeNormal_eq_deflate_gaussianNormal (sem : ScalarSem P K) (p : P)
    (ρ : ℝ → K) (ξ : ℕ → ℝ) (n r : ℕ) (P₀ : Matrix (Fin n) (Fin n) (K × K)) :
    deflate (sem.toFloatMachine p toNat mmR qrR unif (sem.tapeNormal p fun i => ρ (ξ i))) r P₀
        (tapeIndexMatrix n) =
      deflate (sem.toFloatMachine p toNat mmR qrR unif (sem.gaussianNormal p ρ)) r P₀
        (tapeComplexMatrix ξ n) := by
  have hsq : (√2 : ℝ) ≠ 0 := by positivity
  have hcancel : ∀ x : ℝ, √2 * (x / √2) = x := fun x => by field_simp
  have hmat : (tapeIndexMatrix n).map
      (sem.toFloatMachine p toNat mmR qrR unif (sem.tapeNormal p fun i => ρ (ξ i))).normal =
      (tapeComplexMatrix ξ n).map
      (sem.toFloatMachine p toNat mmR qrR unif (sem.gaussianNormal p ρ)).normal := by
    ext i j <;>
    simp only [Matrix.map_apply, tapeIndexMatrix, tapeComplexMatrix, Matrix.of_apply,
      ScalarSem.toFloatMachine, ScalarSem.tapeNormal, ScalarSem.gaussianNormal, hcancel]
  unfold deflate
  rw [hmat]
  rfl

/-! ### The registered tree -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The registered tree instantiates to the builder: at the sizes $N$ and $(r)$ the tree
`NLAlib.deflateProg.compiled` is `NLAlib.deflateProg` on the declared buffers $0$, $1$ from
offset $0$. No printed source. -/
theorem deflateProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 1 → ℕ) :
    (deflateProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 1) (b := 2) (fun _ _ N n h =>
        (deflateProg p mm qr N (n 0) (h 0) 0 (h 1) 0).run) N n := by
  rfl

/-- The registered tree computes `deflate`: if kernels `mm` and `qr` of `I` are the routines
`mmR` and `qrR` on interleaved pairs, a successful run of `NLAlib.deflateProg.compiled` at the
sizes $N$ and $(r)$ from the initial state with the stored $\mathbf{P}$ and $2Nr$ empty cells as
declared buffers ends with declared buffer $1$ holding $\mathsf{deflate}(\mathbf{P}, r)$ on the
machine with the tape sampler of the Gaussian tape from position $0$. No printed source. -/
theorem deflateProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (N r : ℕ)
    (P₀ : Matrix (Fin N) (Fin N) (K × K)) {st' : St P K C}
    (h : (deflateProg.compiled p mm qr).exec I N ![r]
      (inputState p [(pairLayout.toArray P₀).map some, Array.replicate (2 * (N * r)) none]) =
        some st') :
    pairLayout.Holds st'.store p 1 0
      (deflate (I.sem.toFloatMachine p toNat mmR qrR unif
        (I.sem.tapeNormal p (I.tape .gaussian))) r P₀ (tapeIndexMatrix N)) := by
  rw [Prog.exec_eq_exec_toStmt, deflateProg.toStmt_compiled] at h
  simpa [inputState] using (holds_of_exec_deflateProg (toNat := toNat) (unif := unif) hmm hqr p N
    r (Pm := 0) (Q := 1) (po := 0) (qo := 0) (pairLayout.holds_inputState p (k := 0) rfl)
    (by simp [blockDisjoint])
    ⟨2 * (N * r), by simp [inputState, Store.getElem?_shape], by simp⟩ h).1

/-- The registered tree always succeeds under the standard model at $u$ with every value in
range, $u(p) \le 1$ and exact literals up to $2$, if kernels `mm` and `qr` of `I` are routines on
interleaved pairs, from the initial state of `NLAlib.deflateProg.holds_of_exec_compiled`. No
printed source. -/
theorem deflateProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p ≤ 1) (N r : ℕ) (P₀ : Matrix (Fin N) (Fin N) (K × K)) :
    ∃ st' : St P K C, (deflateProg.compiled p mm qr).exec I N ![r]
      (inputState p [(pairLayout.toArray P₀).map some, Array.replicate (2 * (N * r)) none]) =
        some st' := by
  rw [Prog.exec_eq_exec_toStmt, deflateProg.toStmt_compiled]
  exact exists_exec_deflateProg hmm hqr hsem hlit p hu N r (Pm := 0) (Q := 1) (po := 0) (qo := 0)
    (pairLayout.holds_inputState p (k := 0) rfl) (by simp [blockDisjoint])
    ⟨2 * (N * r), by simp [inputState, Store.getElem?_shape], by simp⟩

omit [Inhabited K] in
/-- The counts and the memory of the registered tree: under the standard charge (one per
operation), every successful run of `NLAlib.deflateProg.compiled` at the sizes $N$ and $(r)$ adds
at most `NLAlib.deflateCount p mm qr N r` to the counts and raises the peak memory at tag `p` by
at most the $8N^2 + 2$ scratch cells above the current memory (by nothing at any other tag). No
printed source. -/
theorem deflateProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : IsUnitCharge I) (p : P) (N r : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (deflateProg.compiled p mm qr).exec I N ![r] st = some st') :
    st'.cnt ≤ st.cnt + deflateCount p mm qr N r ∧
      ∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + if q = p then 8 * (N * N) + 2 else 0) := by
  have hb := (deflateProg.compiled p mm qr).bounds_staticCost_of_exec_eq_some I N ![r] h
  have hcharge : I.charge = fun k => Finsupp.single k 1 := hc.charge_eq
  have hb' := hb.mono (b := ⟨deflateCount p mm qr N r,
    fun q => if q = p then 8 * (N * N) + 2 else 0, _⟩) ?_ ?_ le_rfl
  · exact ⟨hb'.count, hb'.peak⟩
  · rw [hcharge]
    intro k
    change (FStmt.staticCost (fun k => Finsupp.single k 1) I.width
      (deflateProg.compiled (ι := ι) p mm qr) (Fin.cons N ![r])).count k ≤ _
    change (StaticCost.seq _ _).count k ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step,
      StaticCost.zero, StaticCost.sequence_count_apply, Instr.kind, Instr.subst, IExp.evalIn,
      Finsupp.add_apply, List.map_const', List.sum_replicate, List.length_range,
      Finsupp.zero_apply]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
      Matrix.Fin.cons_vecCons, Matrix.cons_val_fin_one, Fin.val_eq_zero, Fin.mk_one, add_zero,
      zero_add, smul_eq_mul, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, deflateCount, Nat.sub_sub_eq_min]
    simp only [IExp.evalIn, Matrix.cons_val_zero, Finsupp.add_apply]
    classical
    cases k <;> simp only [Finsupp.single_apply, OpKind.bin.injEq, OpKind.un.injEq,
      OpKind.lit.injEq, OpKind.draw.injEq, OpKind.copy.injEq, OpKind.kcall.injEq, reduceCtorEq,
      ite_false, mul_zero, add_zero, zero_add, le_refl]
    all_goals split_ifs <;> linarith
  · intro q
    change (FStmt.staticCost I.charge I.width
      (deflateProg.compiled (ι := ι) p mm qr) (Fin.cons N ![r])).cells q ≤ _
    change (StaticCost.seq _ _).cells q ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step,
      StaticCost.zero, IExp.evalIn, Instr.kind, Instr.subst]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero,
      Matrix.Fin.cons_vecCons, StaticCost.sequence_cells_mk, List.range_eq_nil, max_self,
      add_zero, Nat.max_zero, ite_self]
    split_ifs <;> omega

end NLAlib
