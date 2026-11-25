/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotScan

/-!
# Division-free scaled pivot scans

`argmaxScaledAbs` compares absolute values relative to nonnegative stored row scales. Zero
scales are guarded explicitly: the policy gives zero score to a zero numerator and scale.
The exact policy theorem assumes zero-scale compatibility. Equal scores retain the first
index. Product comparisons are certified under exact arithmetic; rounded products do not
in general preserve exact ratio comparisons.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.argmaxScaledAbs`: scan relative magnitudes without scalar division.

## Main results

* `NLAlib.Computation.exec_argmaxScaledAbs`: exact first ratio maximum and singleton write frame.
* `NLAlib.Computation.executionComposable_argmaxScaledAbs`: composition with following code.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Select the first largest absolute-value-to-scale ratio in a nonempty vector using exact
cross-product comparisons. The six workspace cells hold zero, incumbent magnitude and scale,
candidate magnitude, and two products. A zero candidate scale is skipped; a zero incumbent
scale is replaced only by a positive candidate magnitude. Thus compatible zero scales have
score zero, and no scalar division instruction is executed. [Higham2002, §9.3]. -/
def argmaxScaledAbs {P ι VB VI : Type} (tag : P) (n : IExp VI) (x : VB) (xo : IExp VI)
    (scales : VB) (so : IExp VI) (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 6
  scope do
    ins (.lit tag ⟨scratch, 0⟩ 0)
    copyAbs tag ⟨scratch, 1⟩ ⟨x, xo⟩ ⟨scratch, 0⟩
    ins (.copy tag ⟨scratch, 2⟩ ⟨scales, so⟩)
    ins (.litIdx tag index 0)
  forRange n fun k => do
    copyAbs tag ⟨scratch, 3⟩ ⟨x, xo + IExp.var k⟩ ⟨scratch, 0⟩
    ifThenElse tag .eq ⟨scales, so + IExp.var k⟩ ⟨scratch, 0⟩ (pure ()) (do
      ifThenElse tag .eq ⟨scratch, 2⟩ ⟨scratch, 0⟩
        (ifThenElse tag .lt ⟨scratch, 0⟩ ⟨scratch, 3⟩ (do
          ins (.copy tag ⟨scratch, 1⟩ ⟨scratch, 3⟩)
          ins (.copy tag ⟨scratch, 2⟩ ⟨scales, so + IExp.var k⟩)
          ins (.litIdx tag index (.var k))) (pure ()))
        (do
          scope do
            ins (.bin tag .mul ⟨scratch, 4⟩ ⟨scratch, 1⟩ ⟨scales, so + IExp.var k⟩)
            ins (.bin tag .mul ⟨scratch, 5⟩ ⟨scratch, 3⟩ ⟨scratch, 2⟩)
          ifThenElse tag .lt ⟨scratch, 4⟩ ⟨scratch, 5⟩ (do
            ins (.copy tag ⟨scratch, 1⟩ ⟨scratch, 3⟩)
            ins (.copy tag ⟨scratch, 2⟩ ⟨scales, so + IExp.var k⟩)
            ins (.litIdx tag index (.var k))) (pure ())))

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The scoped scaled pivot scan composes with every following builder. -/
theorem executionComposable_argmaxScaledAbs (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (scales : ℕ) (so : IExp ℕ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (argmaxScaledAbs tag n x xo scales so index) :=
  executionComposable_single I (fun _ => rfl)

private def scaledAccept {P ι VB VI : Type} (tag : P) (scratch : VB)
    (scale index : Cell VB VI) (k : IExp VI) : Builder P ι VB VI Unit := do
  ins (.copy tag ⟨scratch, 1⟩ ⟨scratch, 3⟩)
  ins (.copy tag ⟨scratch, 2⟩ scale)
  ins (.litIdx tag index k)

private def ScanFrame (_tag : P) (initial : Store P K) (scratch : ℕ)
    (index : Cell ℕ ℕ) (s : Store P K) : Prop :=
  s.shape = initial.shape ∧ ∀ q b j, b ≠ scratch →
    (b ≠ index.buf ∨ j ≠ index.idx.eval) → s.read q b j = initial.read q b j

private theorem ScanFrame.refl (tag : P) (s : Store P K) (scratch : ℕ)
    (index : Cell ℕ ℕ) : ScanFrame tag s scratch index s :=
  ⟨rfl, fun _ _ _ _ _ => rfl⟩

private theorem ScanFrame.trans {tag : P} {initial mid last : Store P K} {scratch : ℕ}
    {index : Cell ℕ ℕ} (h₁ : ScanFrame tag initial scratch index mid)
    (h₂ : ScanFrame tag mid scratch index last) : ScanFrame tag initial scratch index last :=
  ⟨h₂.1.trans h₁.1, fun q b j hb hi => (h₂.2 q b j hb hi).trans (h₁.2 q b j hb hi)⟩

private theorem ScanFrame.scratch_write {tag : P} {initial s last : Store P K}
    {scratch j : ℕ} {index : Cell ℕ ℕ} {w : K}
    (h : ScanFrame tag initial scratch index s) (hw : s.write tag scratch j w = some last) :
    ScanFrame tag initial scratch index last :=
  ⟨(Store.shape_of_write_eq_some hw).trans h.1, fun q b i hb hi =>
    (Store.read_of_write_eq_some_of_ne hw (Or.inl hb)).trans (h.2 q b i hb hi)⟩

private theorem ScanFrame.index_write {tag : P} {initial s last : Store P K}
    {scratch : ℕ} {index : Cell ℕ ℕ} {w : K}
    (h : ScanFrame tag initial scratch index s)
    (hw : s.write tag index.buf index.idx.eval w = some last) :
    ScanFrame tag initial scratch index last :=
  ⟨(Store.shape_of_write_eq_some hw).trans h.1, fun q b i hb hi =>
    (Store.read_of_write_eq_some_of_ne hw hi).trans (h.2 q b i hb hi)⟩

private theorem exec_scaledAccept (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (scale index : Cell ℕ ℕ)
    (k : IExp ℕ) (c t : ℝ) (hc : st.store.read tag scratch 3 = some c)
    (ht : st.store.read tag scale.buf scale.idx.eval = some t)
    (hsh : st.store.shape[scratch]? = some (tag, 6))
    (hi : Writable st.store tag index.buf index.idx.eval 1)
    (hsi : scratch ≠ index.buf) (hst : scratch ≠ scale.buf) :
    ∃ out, exec I (scaledAccept tag scratch scale index k).run st = some out ∧
      ScanFrame tag st.store scratch index out.store ∧
      out.store.read tag scratch 1 = some c ∧
      out.store.read tag scratch 2 = some t ∧
      out.store.read tag index.buf index.idx.eval = some (k.eval : ℝ) ∧
      out.store.read tag scratch 0 = st.store.read tag scratch 0 := by
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape c hsh (by omega : 1 < 6)
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape t
    ((Store.shape_of_write_eq_some hs₁).symm ▸ hsh) (by omega : 2 < 6)
  obtain ⟨len, hlen, hlt⟩ := hi 0 (by omega)
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape (k.eval : ℝ)
    (((Store.shape_of_write_eq_some hs₂).trans (Store.shape_of_write_eq_some hs₁)).symm ▸ hlen)
    (by simpa using hlt)
  let out : St P ℝ C := { st with
    store := s₃
    cnt := ((st.cnt + I.charge (.copy tag)) + I.charge (.copy tag)) + I.charge (.lit tag) }
  have ht₁ : s₁.read tag scale.buf scale.idx.eval = some t :=
    (Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hst.symm)).trans ht
  refine ⟨out, ?_, ((ScanFrame.refl tag st.store scratch index).scratch_write hs₁
      |>.scratch_write hs₂).index_write hs₃, ?_, ?_, Store.read_of_write_eq_some hs₃, ?_⟩
  · change exec I (.seq (.instr (.copy tag ⟨scratch, 1⟩ ⟨scratch, 3⟩)) _) st = some out
    rw [exec_seq_instr_copy I hc hs₁]
    change exec I (.seq (.instr (.copy tag ⟨scratch, 2⟩ scale)) _) _ = some out
    rw [exec_seq_instr_copy I ht₁ hs₂]
    change exec I (.seq (.instr (.litIdx tag index k)) .skip) _ = some out
    rw [exec_seq_instr_litIdx I (by simp [hI, exactSem]) hs₃, exec_skip]
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by omega : 1 ≠ 2))]
    exact Store.read_of_write_eq_some hs₁
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsi)]
    exact Store.read_of_write_eq_some hs₂
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by omega : 0 ≠ 2)),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inr (by omega : 0 ≠ 1))]

private theorem exec_test (I : Interp P ι ℝ C) (tag : P) (st : St P ℝ C)
    (op : CmpOp) (x y : Cell ℕ ℕ) (a b : ℝ) (r : Bool)
    (hx : st.store.read tag x.buf x.idx.eval = some a)
    (hy : st.store.read tag y.buf y.idx.eval = some b)
    (hc : I.sem.cmp tag op a b = some r) (t e : Stmt P ι ℕ ℕ)
    (Q : Store P ℝ → Prop)
    (hb : ∀ σ : St P ℝ C, σ.store = st.store →
      ∃ out, exec I (if r then t else e) σ = some out ∧ Q out.store) :
    ∃ out, exec I (.seq (.ite tag op x y t e) .skip) st = some out ∧ Q out.store := by
  let σ : St P ℝ C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  obtain ⟨out, hr, hq⟩ := hb σ rfl
  refine ⟨out, ?_, hq⟩
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hx, hy, hc, Option.bind_some, Option.map_some]
  cases r <;> exact hr

private def scaledProducts {P ι VB VI : Type} (tag : P) (scratch : VB)
    (scale : Cell VB VI) : Builder P ι VB VI Unit := scope do
  ins (.bin tag .mul ⟨scratch, 4⟩ ⟨scratch, 1⟩ scale)
  ins (.bin tag .mul ⟨scratch, 5⟩ ⟨scratch, 3⟩ ⟨scratch, 2⟩)

private theorem exec_scaledProducts (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (scale : Cell ℕ ℕ) (b s c t : ℝ)
    (hb : st.store.read tag scratch 1 = some b)
    (hs : st.store.read tag scratch 2 = some s)
    (hc : st.store.read tag scratch 3 = some c)
    (ht : st.store.read tag scale.buf scale.idx.eval = some t)
    (hsh : st.store.shape[scratch]? = some (tag, 6)) :
    ∃ out, exec I (scaledProducts tag scratch scale).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag scratch 4 = some (b * t) ∧
      out.store.read tag scratch 5 = some (c * s) ∧
      ∀ q buf j, (buf ≠ scratch ∨ j ≠ 4 ∧ j ≠ 5) →
        out.store.read q buf j = st.store.read q buf j := by
  obtain ⟨s₁, hw₁, hr₁, hshape₁, hread₁, -⟩ := exec_scalar_bin I tag st .mul
    ⟨scratch, 4⟩ ⟨scratch, 1⟩ scale b t (b * t) hb ht (by simp [hI, exactSem])
    ⟨6, hsh, by norm_num [IExp.eval]⟩
  let σ : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.bin tag .mul) }
  have hc₁ : s₁.read tag scratch 3 = some c :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 3 ≠ 4))).trans hc
  have hs₁ : s₁.read tag scratch 2 = some s :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 2 ≠ 4))).trans hs
  obtain ⟨s₂, hw₂, hr₂, hshape₂, hread₂, -⟩ := exec_scalar_bin I tag σ .mul
    ⟨scratch, 5⟩ ⟨scratch, 3⟩ ⟨scratch, 2⟩ c s (c * s) hc₁ hs₁
    (by simp [hI, exactSem]) ⟨6, hshape₁ ▸ hsh, by norm_num [IExp.eval]⟩
  refine ⟨{ σ with store := s₂, cnt := σ.cnt + I.charge (.bin tag .mul) }, ?_,
    hshape₂.trans hshape₁, ?_, hread₂, ?_⟩
  · change exec I (.seq
      (.seq (.instr (.bin tag .mul ⟨scratch, 4⟩ ⟨scratch, 1⟩ scale)) _) .skip) st = _
    rw [exec_seq_skip]
    rw [exec_seq_instr_bin I hb ht (by simp [hI, exactSem]) hw₁]
    exact hr₂
  · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega : 4 ≠ 5))]
    exact hread₁
  · intro q buf j hj
    rw [Store.read_of_write_eq_some_of_ne hw₂ (hj.imp id And.right),
      Store.read_of_write_eq_some_of_ne hw₁ (hj.imp id And.left)]

private theorem exec_scaledFinish (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (scale index : Cell ℕ ℕ)
    (k : IExp ℕ) (b s c t iw : ℝ)
    (hb : st.store.read tag scratch 1 = some b)
    (hs : st.store.read tag scratch 2 = some s)
    (hc : st.store.read tag scratch 3 = some c)
    (ht : st.store.read tag scale.buf scale.idx.eval = some t)
    (hidx : st.store.read tag index.buf index.idx.eval = some iw)
    (hsh : st.store.shape[scratch]? = some (tag, 6))
    (hsi : scratch ≠ index.buf) (hst : scratch ≠ scale.buf)
    (take : Prop) [Decidable take] :
    ∃ out, exec I (if take then (scaledAccept tag scratch scale index k).run else .skip)
      st = some out ∧ ScanFrame tag st.store scratch index out.store ∧
      out.store.read tag scratch 1 = some (if take then c else b) ∧
      out.store.read tag scratch 2 = some (if take then t else s) ∧
      out.store.read tag index.buf index.idx.eval = some (if take then (k.eval : ℝ) else iw) ∧
      out.store.read tag scratch 0 = st.store.read tag scratch 0 := by
  by_cases htake : take
  · obtain ⟨out, hr, hf, h₁, h₂, h₃, h₀⟩ := exec_scaledAccept I hI tag st scratch scale index
      k c t hc ht hsh (by
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        obtain ⟨len, hlen, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some hidx
        exact ⟨len, hlen, by simpa using hlt⟩) hsi hst
    exact ⟨out, by simpa only [htake, ↓reduceIte] using hr,
      hf, by simpa only [htake, ↓reduceIte] using h₁,
      by simpa only [htake, ↓reduceIte] using h₂,
      by simpa only [htake, ↓reduceIte] using h₃, h₀⟩
  · exact ⟨st, by simpa only [htake, ↓reduceIte] using exec_skip I st,
      ScanFrame.refl tag st.store scratch index, by simpa only [htake, ↓reduceIte] using hb,
      by simpa only [htake, ↓reduceIte] using hs,
      by simpa only [htake, ↓reduceIte] using hidx, rfl⟩

private def scaledDecision {P ι VB VI : Type} (tag : P) (scratch : VB)
    (scale index : Cell VB VI) (k : IExp VI) : Builder P ι VB VI Unit :=
  ifThenElse tag .eq scale ⟨scratch, 0⟩ (pure ()) (do
    ifThenElse tag .eq ⟨scratch, 2⟩ ⟨scratch, 0⟩
      (ifThenElse tag .lt ⟨scratch, 0⟩ ⟨scratch, 3⟩
        (scaledAccept tag scratch scale index k) (pure ()))
      (do
        scaledProducts tag scratch scale
        ifThenElse tag .lt ⟨scratch, 4⟩ ⟨scratch, 5⟩
          (scaledAccept tag scratch scale index k) (pure ())))

private theorem exec_scaledFinish_of_frame (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (base : Store P ℝ) (scratch : ℕ) (scale index : Cell ℕ ℕ)
    (k : IExp ℕ) (b s c t iw : ℝ)
    (hsh : base.shape[scratch]? = some (tag, 6))
    (hsi : scratch ≠ index.buf) (hst : scratch ≠ scale.buf)
    (σ : St P ℝ C) (hf : ScanFrame tag base scratch index σ.store)
    (h₁ : σ.store.read tag scratch 1 = some b)
    (h₂ : σ.store.read tag scratch 2 = some s)
    (h₃ : σ.store.read tag scratch 3 = some c)
    (h₄ : σ.store.read tag scale.buf scale.idx.eval = some t)
    (h₅ : σ.store.read tag index.buf index.idx.eval = some iw)
    (h₀ : σ.store.read tag scratch 0 = some 0)
    (take : Prop) [Decidable take] (he : take ↔ b / s < c / t) :
    ∃ out, exec I (if take then (scaledAccept tag scratch scale index k).run else .skip)
      σ = some out ∧ ScanFrame tag base scratch index out.store ∧
      out.store.read tag scratch 1 = some (if b / s < c / t then c else b) ∧
      out.store.read tag scratch 2 = some (if b / s < c / t then t else s) ∧
      out.store.read tag index.buf index.idx.eval =
        some (if b / s < c / t then (k.eval : ℝ) else iw) ∧
      out.store.read tag scratch 0 = some 0 := by
  obtain ⟨out, hr, hframe, hr₁, hr₂, hr₃, hr₀⟩ := exec_scaledFinish I hI tag σ scratch
    scale index k b s c t iw h₁ h₂ h₃ h₄ h₅ (hf.1 ▸ hsh) hsi hst take
  refine ⟨out, hr, hf.trans hframe, ?_, ?_, ?_, hr₀.trans h₀⟩
  · simpa only [he] using hr₁
  · simpa only [he] using hr₂
  · simpa only [he] using hr₃

private theorem exec_scaledDecision (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (scale index : Cell ℕ ℕ)
    (k : IExp ℕ) (b s c t iw : ℝ)
    (hb : st.store.read tag scratch 1 = some b)
    (hs : st.store.read tag scratch 2 = some s)
    (hc : st.store.read tag scratch 3 = some c)
    (ht : st.store.read tag scale.buf scale.idx.eval = some t)
    (hidx : st.store.read tag index.buf index.idx.eval = some iw)
    (hz : st.store.read tag scratch 0 = some 0)
    (hsh : st.store.shape[scratch]? = some (tag, 6))
    (hsi : scratch ≠ index.buf) (hst : scratch ≠ scale.buf)
    (hb0 : 0 ≤ b) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hbs : s = 0 → b = 0) (hct : t = 0 → c = 0) :
    ∃ out, exec I (scaledDecision tag scratch scale index k).run st = some out ∧
      ScanFrame tag st.store scratch index out.store ∧
      out.store.read tag scratch 1 = some (if b / s < c / t then c else b) ∧
      out.store.read tag scratch 2 = some (if b / s < c / t then t else s) ∧
      out.store.read tag index.buf index.idx.eval =
        some (if b / s < c / t then (k.eval : ℝ) else iw) ∧
      out.store.read tag scratch 0 = some 0 := by
  classical
  let Q : Store P ℝ → Prop := fun out =>
    ScanFrame tag st.store scratch index out ∧
    out.read tag scratch 1 = some (if b / s < c / t then c else b) ∧
    out.read tag scratch 2 = some (if b / s < c / t then t else s) ∧
    out.read tag index.buf index.idx.eval = some (if b / s < c / t then (k.eval : ℝ) else iw) ∧
    out.read tag scratch 0 = some 0
  let finish := exec_scaledFinish_of_frame I hI tag st.store scratch scale index k b s c t iw
    hsh hsi hst
  change ∃ out, exec I (.seq (.ite tag .eq scale ⟨scratch, 0⟩ .skip _) .skip) st = some out ∧ _
  apply exec_test I tag st .eq scale ⟨scratch, 0⟩ t 0 (decide (t = 0)) ht hz
    (by simp [hI, exactSem]) _ _ Q
  intro σ hσ
  have hf : ScanFrame tag st.store scratch index σ.store := hσ ▸ ScanFrame.refl _ _ _ _
  by_cases htzero : t = 0
  · simp only [htzero, decide_true, ↓reduceIte]
    have he : False ↔ b / s < c / t := by
      rw [htzero, hct htzero, zero_div]
      exact iff_of_false (fun h => h) (not_lt_of_ge (div_nonneg hb0 hs0))
    simpa only [Bool.false_eq_true, ↓reduceIte] using finish σ hf (hσ ▸ hb) (hσ ▸ hs)
      (hσ ▸ hc) (hσ ▸ ht) (hσ ▸ hidx) (hσ ▸ hz) False he
  · simp only [htzero, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply exec_test I tag σ .eq ⟨scratch, 2⟩ ⟨scratch, 0⟩ s 0 (decide (s = 0))
      (hσ ▸ hs) (hσ ▸ hz) (by simp [hI, exactSem]) _ _ Q
    intro τ hτ
    have hτ' : τ.store = st.store := hτ.trans hσ
    have hfτ : ScanFrame tag st.store scratch index τ.store := hτ' ▸ ScanFrame.refl _ _ _ _
    by_cases hszero : s = 0
    · simp only [hszero, decide_true, ↓reduceIte]
      apply exec_test I tag τ .lt ⟨scratch, 0⟩ ⟨scratch, 3⟩ 0 c (decide (0 < c))
        (hτ' ▸ hz) (hτ' ▸ hc) (by simp [hI, exactSem])
        (scaledAccept tag scratch scale index k).run .skip Q
      intro υ hυ
      have hυ' : υ.store = st.store := hυ.trans hτ'
      have he : 0 < c ↔ b / s < c / t := by
        rw [hszero, hbs hszero, zero_div]
        exact (div_pos_iff_of_pos_right (lt_of_le_of_ne ht0 (Ne.symm htzero))).symm
      simpa only [decide_eq_true_eq] using finish υ (hυ' ▸ ScanFrame.refl _ _ _ _)
        (hυ' ▸ hb) (hυ' ▸ hs) (hυ' ▸ hc) (hυ' ▸ ht) (hυ' ▸ hidx) (hυ' ▸ hz) (0 < c) he
    · simp only [hszero, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨mid, hr, hshape, hleft, hright, hframe⟩ := exec_scaledProducts I hI tag τ scratch
        scale b s c t (hτ' ▸ hb) (hτ' ▸ hs) (hτ' ▸ hc) (hτ' ▸ ht) (hτ' ▸ hsh)
      have hfm : ScanFrame tag st.store scratch index mid.store :=
        hfτ.trans ⟨hshape, fun q buf j hb _ => hframe q buf j (Or.inl hb)⟩
      have hread (j : ℕ) (hj : j ≠ 4 ∧ j ≠ 5) :
          mid.store.read tag scratch j = st.store.read tag scratch j :=
        (hframe tag scratch j (Or.inr hj)).trans (congrArg (fun s => s.read tag scratch j) hτ')
      have hscale : mid.store.read tag scale.buf scale.idx.eval = some t :=
        (hframe tag scale.buf scale.idx.eval (Or.inl hst.symm)).trans (hτ' ▸ ht)
      have hindex : mid.store.read tag index.buf index.idx.eval = some iw :=
        (hframe tag index.buf index.idx.eval (Or.inl hsi.symm)).trans (hτ' ▸ hidx)
      obtain ⟨out, hr', hq⟩ := exec_test I tag mid .lt ⟨scratch, 4⟩ ⟨scratch, 5⟩
        (b * t) (c * s) (decide (b * t < c * s)) hleft hright
        (by simp [hI, exactSem]) (scaledAccept tag scratch scale index k).run .skip Q (by
          intro υ hυ
          have he : b * t < c * s ↔ b / s < c / t := by
            exact (div_lt_div_iff₀ (lt_of_le_of_ne hs0 (Ne.symm hszero))
              (lt_of_le_of_ne ht0 (Ne.symm htzero))).symm
          simpa only [decide_eq_true_eq] using finish υ (hυ ▸ hfm)
            (hυ ▸ (hread 1 (by omega)).trans hb)
            (hυ ▸ (hread 2 (by omega)).trans hs)
            (hυ ▸ (hread 3 (by omega)).trans hc) (hυ ▸ hscale) (hυ ▸ hindex)
            (hυ ▸ (hread 0 (by omega)).trans hz) (b * t < c * s) he)
      refine ⟨out, ?_, hq⟩
      change exec I (scaledProducts tag scratch scale >>= fun _ =>
        ifThenElse tag .lt ⟨scratch, 4⟩ ⟨scratch, 5⟩
          (scaledAccept tag scratch scale index k) (pure ())).run τ = some out
      rw [exec_run_bind I (b := scaledProducts tag scratch scale) (fun _ => rfl), hr,
        Option.bind_some]
      exact hr'

private structure ScaledState {N : ℕ} (tag : P) (x scales : Fin N → ℝ)
    (scratch : ℕ) (index : Cell ℕ ℕ) (initial : Store P ℝ) (k : ℕ)
    (s : Store P ℝ) : Prop where
  frame : ScanFrame tag initial scratch index s
  zero : s.read tag scratch 0 = some 0
  values : ∃ chosen : Fin N,
    s.read tag scratch 1 = some |x chosen| ∧
    s.read tag scratch 2 = some (scales chosen) ∧
    s.read tag index.buf index.idx.eval = some (chosen.val : ℝ) ∧
    (∀ j : Fin N, j.val < k → |x j| / scales j ≤ |x chosen| / scales chosen) ∧
    (∀ j : Fin N, j < chosen → |x j| / scales j < |x chosen| / scales chosen)

private def scaledStep {P ι VB VI : Type} (tag : P) (x : VB) (xo : IExp VI)
    (scratch : VB) (scale index : Cell VB VI) (k : IExp VI) : Builder P ι VB VI Unit := do
  copyAbs tag ⟨scratch, 3⟩ ⟨x, xo + k⟩ ⟨scratch, 0⟩
  scaledDecision tag scratch scale index k

private theorem exec_scaledStep (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    {N : ℕ} (tag : P) (initial : Store P ℝ) (x scales : Fin N → ℝ)
    (xb sb scratch : ℕ) (xo so : IExp ℕ) (index : Cell ℕ ℕ)
    (hx : ReadsDecoded initial (fun _ a => a) tag xb xo.eval x)
    (hs : ReadsDecoded initial (fun _ a => a) tag sb so.eval scales)
    (hscales : ∀ i, 0 ≤ scales i) (hcompat : ∀ i, scales i = 0 → x i = 0)
    (hsh : initial.shape[scratch]? = some (tag, 6))
    (hxs : xb ≠ scratch) (hss : sb ≠ scratch) (hxi : xb ≠ index.buf)
    (hsi : sb ≠ index.buf) (hsidx : scratch ≠ index.buf)
    (k : ℕ) (hk : k < N) (st : St P ℝ C)
    (hstate : ScaledState tag x scales scratch index initial k st.store) :
    ∃ out, exec I (scaledStep tag xb xo scratch ⟨sb, so + IExp.var k⟩ index (.var k)).run st =
      some out ∧ ScaledState tag x scales scratch index initial (k + 1) out.store := by
  obtain ⟨chosen, hb, hscale, hindex, hdom, hfirst⟩ := hstate.values
  obtain ⟨v, hv, hdv⟩ := hx ⟨k, hk⟩
  obtain ⟨t, ht, hdt⟩ := hs ⟨k, hk⟩
  change v = x ⟨k, hk⟩ at hdv
  change t = scales ⟨k, hk⟩ at hdt
  subst v; subst t
  have hv' : st.store.read tag xb (xo.eval + k) = some (x ⟨k, hk⟩) :=
    (hstate.frame.2 tag xb _ hxs (Or.inl hxi)).trans hv
  have ht' : st.store.read tag sb (so.eval + k) = some (scales ⟨k, hk⟩) :=
    (hstate.frame.2 tag sb _ hss (Or.inl hsi)).trans ht
  have hrel : IsRelErrSem (fun _ => 0) (fun (_ : P) (a : ℝ) => a) (fun _ _ => True) I.sem :=
    hI ▸ isRelErrSem_exactSem
  obtain ⟨mid, c, hr₁, hw₁, hdc⟩ := hrel.exec_copyAbs I tag st ⟨scratch, 3⟩
    ⟨xb, xo + IExp.var k⟩ ⟨scratch, 0⟩ (x ⟨k, hk⟩) 0 hv' hstate.zero rfl
    ⟨6, hstate.frame.1 ▸ hsh, by norm_num [IExp.eval]⟩
  change c = |x ⟨k, hk⟩| at hdc
  subst c
  have hb' : mid.store.read tag scratch 1 = some |x chosen| :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 1 ≠ 3))).trans hb
  have hs' : mid.store.read tag scratch 2 = some (scales chosen) :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 2 ≠ 3))).trans hscale
  have hi' : mid.store.read tag index.buf index.idx.eval = some (chosen.val : ℝ) :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hsidx.symm)).trans hindex
  have ht'' : mid.store.read tag sb (so.eval + k) = some (scales ⟨k, hk⟩) :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hss)).trans ht'
  have hz' : mid.store.read tag scratch 0 = some 0 :=
    (Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 0 ≠ 3))).trans hstate.zero
  obtain ⟨out, hr₂, hf₂, hb₂, hs₂, hi₂, hz₂⟩ := exec_scaledDecision I hI tag mid scratch
    ⟨sb, so + IExp.var k⟩ index (.var k) |x chosen| (scales chosen) |x ⟨k, hk⟩|
    (scales ⟨k, hk⟩) chosen.val hb' hs' (Store.read_of_write_eq_some hw₁) ht'' hi' hz'
    ((Store.shape_of_write_eq_some hw₁).trans hstate.frame.1 ▸ hsh) hsidx hss.symm
    (abs_nonneg _) (hscales chosen) (hscales ⟨k, hk⟩)
    (fun h => by rw [hcompat chosen h, abs_zero])
    (fun h => by rw [hcompat ⟨k, hk⟩ h, abs_zero])
  let candidate : Fin N := ⟨k, hk⟩
  let selected := if |x chosen| / scales chosen < |x candidate| / scales candidate
    then candidate else chosen
  obtain ⟨-, hdom', hfirst'⟩ := Fin.max_eq_score_choose_of_prefix
    (fun i => |x i| / scales i) chosen candidate rfl hdom hfirst
  refine ⟨out, ?_, ⟨(hstate.frame.scratch_write hw₁).trans hf₂, hz₂,
    selected, ?_, ?_, ?_, hdom', hfirst'⟩⟩
  · change exec I (copyAbs tag ⟨scratch, 3⟩ ⟨xb, xo + IExp.var k⟩ ⟨scratch, 0⟩ >>= fun _ =>
      scaledDecision tag scratch ⟨sb, so + IExp.var k⟩ index (.var k)).run st = some out
    rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 3⟩ ⟨xb, xo + IExp.var k⟩ ⟨scratch, 0⟩)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · simpa only [selected, candidate, apply_ite, abs_ite] using hb₂
  · simpa only [selected, candidate, apply_ite] using hs₂
  · simpa only [selected, candidate, apply_ite, IExp.eval_var] using hi₂

private def initializeScaled {P ι VB VI : Type} (tag : P) (x scales scratch : VB)
    (xo so : IExp VI) (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  ins (.lit tag ⟨scratch, 0⟩ 0)
  copyAbs tag ⟨scratch, 1⟩ ⟨x, xo⟩ ⟨scratch, 0⟩
  ins (.copy tag ⟨scratch, 2⟩ ⟨scales, so⟩)
  ins (.litIdx tag index 0)

private theorem exec_initializeScaled (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    {N : ℕ} (hN : 0 < N) (tag : P) (st : St P ℝ C) (x scales : Fin N → ℝ)
    (xb sb scratch : ℕ) (xo so : IExp ℕ) (index : Cell ℕ ℕ)
    (hx : ReadsDecoded st.store (fun _ a => a) tag xb xo.eval x)
    (hs : ReadsDecoded st.store (fun _ a => a) tag sb so.eval scales)
    (hsh : st.store.shape[scratch]? = some (tag, 6))
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    (hxs : xb ≠ scratch) (hss : sb ≠ scratch) (hsi : scratch ≠ index.buf) :
    ∃ out, exec I (initializeScaled tag xb sb scratch xo so index).run st = some out ∧
      ScaledState tag x scales scratch index st.store 0 out.store := by
  obtain ⟨v, hv, hdv⟩ := hx ⟨0, hN⟩
  obtain ⟨t, ht, hdt⟩ := hs ⟨0, hN⟩
  change v = x ⟨0, hN⟩ at hdv
  change t = scales ⟨0, hN⟩ at hdt
  subst v; subst t
  obtain ⟨s₁, hs₁, -, hshape₁, hread₁, -⟩ := exec_scalar_lit I tag st
    ⟨scratch, 0⟩ 0 0 (by simp [hI, exactSem]) ⟨6, hsh, by norm_num [IExp.eval]⟩
  let σ₁ : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.lit tag) }
  have hv₁ : s₁.read tag xb xo.eval = some (x ⟨0, hN⟩) := by
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hxs)]
    simpa using hv
  have hrel : IsRelErrSem (fun _ => 0) (fun (_ : P) (a : ℝ) => a)
      (fun _ _ => True) I.sem := hI ▸ isRelErrSem_exactSem
  obtain ⟨σ₂, b, hr₂, hs₂, hdb⟩ := hrel.exec_copyAbs I tag σ₁ ⟨scratch, 1⟩
    ⟨xb, xo⟩ ⟨scratch, 0⟩ (x ⟨0, hN⟩) 0 hv₁ hread₁ rfl
    ⟨6, hshape₁ ▸ hsh, by norm_num [IExp.eval]⟩
  change b = |x ⟨0, hN⟩| at hdb
  subst b
  have ht₂ : σ₂.store.read tag sb so.eval = some (scales ⟨0, hN⟩) := by
    rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hss),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hss)]
    simpa using ht
  have hshape₂ : σ₂.store.shape = st.store.shape :=
    (Store.shape_of_write_eq_some hs₂).trans hshape₁
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape (scales ⟨0, hN⟩)
    (hshape₂.symm ▸ hsh) (by omega : 2 < 6)
  let σ₃ : St P ℝ C := { σ₂ with store := s₃, cnt := σ₂.cnt + I.charge (.copy tag) }
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  obtain ⟨s₄, hs₄⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (((Store.shape_of_write_eq_some hs₃).trans hshape₂).symm ▸ hlen) (by simpa using hlt)
  let out : St P ℝ C := { σ₃ with store := s₄, cnt := σ₃.cnt + I.charge (.lit tag) }
  have hf₁ := (ScanFrame.refl tag st.store scratch index).scratch_write hs₁
  have hf₂ := hf₁.scratch_write hs₂
  have hf₃ := hf₂.scratch_write hs₃
  have hf₄ := hf₃.index_write hs₄
  refine ⟨out, ?_, ⟨hf₄, ?_, ⟨0, hN⟩, ?_, ?_,
    by simpa using Store.read_of_write_eq_some hs₄, ?_, ?_⟩⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]
    change exec I (.seq (.instr (.lit tag ⟨scratch, 0⟩ 0)) _) st = some out
    rw [exec_seq_instr_lit I (by simp [hI, exactSem]) hs₁]
    change exec I (copyAbs tag ⟨scratch, 1⟩ ⟨xb, xo⟩ ⟨scratch, 0⟩ >>= fun _ => do
      ins (.copy tag ⟨scratch, 2⟩ ⟨sb, so⟩)
      ins (.litIdx tag index 0)).run σ₁ = some out
    rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 1⟩ ⟨xb, xo⟩ ⟨scratch, 0⟩)
      (fun _ => rfl), hr₂, Option.bind_some]
    change exec I (.seq (.instr (.copy tag ⟨scratch, 2⟩ ⟨sb, so⟩)) _) σ₂ = some out
    rw [exec_seq_instr_copy I ht₂ hs₃]
    change exec I (.seq (.instr (.litIdx tag index 0)) .skip) σ₃ = some out
    rw [exec_seq_instr_litIdx I (by simp [hI, exactSem]) hs₄, exec_skip]
  · rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by omega : 0 ≠ 2)),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by omega : 0 ≠ 1))]
    exact hread₁
  · rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by omega : 1 ≠ 2))]
    exact Store.read_of_write_eq_some hs₂
  · rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hsi)]
    exact Store.read_of_write_eq_some hs₃
  · intro j hj; omega
  · intro j hj; exact (Nat.not_lt_zero _ hj).elim

/-- In exact arithmetic, a nonempty scaled pivot scan succeeds and writes the exact index of
its first largest absolute-value-to-scale ratio. Scales are nonnegative and a zero scale must
have zero numerator. Division-free zero guards implement the usual zero-score convention;
all other cells are retained. Input and scale buffers may overlap each other, while the index
has a separate buffer. This is an exact policy theorem, with no rounded product-comparison
claim. [Higham2002, §9.3]. -/
theorem exec_argmaxScaledAbs (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n : IExp ℕ) (hN : 0 < n.eval)
    (x scales : Fin n.eval → ℝ) (xb sb : ℕ) (xo so : IExp ℕ) (index : Cell ℕ ℕ)
    (hx : ReadsDecoded st.store (fun _ a => a) tag xb xo.eval x)
    (hs : ReadsDecoded st.store (fun _ a => a) tag sb so.eval scales)
    (hscales : ∀ i, 0 ≤ scales i) (hcompat : ∀ i, scales i = 0 → x i = 0)
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    (hxi : xb ≠ index.buf) (hsi : sb ≠ index.buf) :
    ∃ (out : St P ℝ C) (chosen : Fin n.eval),
      exec I (argmaxScaledAbs tag n xb xo sb so index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[(chosen.val : ℝ)] = some out.store ∧
      (∀ j, |x j| / scales j ≤ |x chosen| / scales chosen) ∧
      (∀ j, j < chosen → |x j| / scales j < |x chosen| / scales chosen) := by
  let Q : Store P ℝ → Prop := fun s => ∃ chosen : Fin n.eval,
    st.store.writeBlock tag index.buf index.idx.eval #[(chosen.val : ℝ)] = some s ∧
    (∀ j, |x j| / scales j ≤ |x chosen| / scales chosen) ∧
    (∀ j, j < chosen → |x j| / scales j < |x chosen| / scales chosen)
  have hidx : index.buf < st.store.size := hw.lt_size (by omega)
  obtain ⟨v, hv, -⟩ := hx ⟨0, hN⟩
  obtain ⟨t, ht, -⟩ := hs ⟨0, hN⟩
  have hxb : xb < st.store.size := Store.lt_size_of_read_eq_some hv
  have hsb : sb < st.store.size := Store.lt_size_of_read_eq_some ht
  have hbody : ∀ σ : St P ℝ C,
      σ.store = st.store.push (tag, Array.replicate 6 none) →
      ∃ out, exec I (do
        initializeScaled tag xb sb st.store.size xo so index
        forRange n fun k => scaledStep tag xb xo st.store.size
          ⟨sb, so + IExp.var k⟩ index (.var k)).run σ = some out ∧ Q out.store.pop := by
    intro σ hσ
    have hxσ : ReadsDecoded σ.store (fun _ a => a) tag xb xo.eval x :=
      hσ ▸ hx.push (tag, Array.replicate 6 none)
    have hsσ : ReadsDecoded σ.store (fun _ a => a) tag sb so.eval scales :=
      hσ ▸ hs.push (tag, Array.replicate 6 none)
    have hwσ : Writable σ.store tag index.buf index.idx.eval 1 :=
      hσ ▸ hw.push (tag, Array.replicate 6 none)
    have hsh : σ.store.shape[st.store.size]? = some (tag, 6) := by
      rw [hσ]; exact Store.getElem?_shape_push_size _ _ _
    obtain ⟨mid, hr₁, hinit⟩ := exec_initializeScaled I hI hN tag σ x scales xb sb
      st.store.size xo so index hxσ hsσ hsh hwσ (Nat.ne_of_lt hxb) (Nat.ne_of_lt hsb)
      (Nat.ne_of_gt hidx)
    obtain ⟨out, hr₂, hfinal⟩ := exists_exec_loop_eq_some_of_forall I (n := n)
      (body := fun k => (scaledStep tag xb xo st.store.size
        ⟨sb, so + IExp.var k⟩ index (.var k)).run)
      (st := mid) (fun k s => ScaledState tag x scales st.store.size index σ.store k s.store)
      hinit (fun k hk s hstate => exec_scaledStep I hI tag σ.store x scales xb sb st.store.size
        xo so index hxσ hsσ hscales hcompat hsh (Nat.ne_of_lt hxb) (Nat.ne_of_lt hsb)
        hxi hsi (Nat.ne_of_gt hidx) k hk s hstate)
    obtain ⟨chosen, -, -, hread, hdom, hfirst⟩ := hfinal.values
    have hshape : out.store.shape = Store.shape (st.store.push (tag, Array.replicate 6 none)) :=
      hfinal.frame.1.trans (congrArg Store.shape hσ)
    have hsize : out.store.size = st.store.size + 1 := by
      simpa only [Array.size_push] using Store.size_eq_of_shape_eq hshape
    refine ⟨out, ?_, chosen, ?_, fun j => hdom j j.isLt, hfirst⟩
    · rw [exec_run_bind I (b := initializeScaled tag xb sb st.store.size xo so index)
        (fun _ => rfl), hr₁, Option.bind_some]
      change exec I (.seq (.loop n _) .skip) mid = some out
      rw [exec_seq_skip]; exact hr₂
    · apply Store.writeBlock_eq_some_of_read
      · rw [Store.shape_pop, hshape]
        simp only [Store.shape, Array.map_push, Array.pop_push]
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst j
        rw [Nat.add_zero, Store.read_pop_of_lt (by omega), hread]
        rfl
      · intro q b j hout
        by_cases hb : b < st.store.size
        · rw [Store.read_pop_of_lt (by omega), hfinal.frame.2 q b j (by omega) (by
            simp only [Array.size_singleton] at hout; omega), hσ, Store.read_push_of_lt hb]
        · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
            Store.read_eq_none_of_size_le (by omega)]
  obtain ⟨out, hr, chosen, hwrite, hdom, hfirst⟩ := exists_exec_alloc I tag 6
    (fun scratch => ((do
      initializeScaled tag xb sb scratch xo so index
      forRange n fun k => scaledStep tag xb xo scratch
        ⟨sb, so + IExp.var k⟩ index (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q hbody
  refine ⟨out, chosen, ?_, hwrite, hdom, hfirst⟩
  change exec I (.seq (.alloc tag 6 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.Computation
