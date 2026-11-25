/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Fin.Embedding
public import NLAlib.Matrix.Computation.PivotScan
public import NLAlib.Computation.IndexBinder

/-!
# Threshold partial pivot selection

The first active column maximum supplies a fallback row. The diagonal is accepted whenever
its magnitude is at least the exact rational threshold times that maximum, including equality.
The scalar threshold is stored and multiplied by an actual instruction. This exact-arithmetic
policy performs no division and leaves the source matrix unchanged.

## Main definitions

* `NLAlib.Computation.thresholdPivotChoice`: stored threshold partial-pivot selection.

## Main results

* `NLAlib.Computation.exec_thresholdPivotChoice`: success, quality and exact singleton frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Apply a threshold decision after the fallback's relative row has been decoded. Four
caller-owned workspace cells hold the two magnitudes, zero and the scaled fallback magnitude. -/
def thresholdPivotAt {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A scratch : VB) (off : IExp VI) (τ : ℚ) (rel : IExp VI) (index : Cell VB VI) :
    Builder P ι VB VI Unit := do
  ins (.lit tag ⟨scratch, 1⟩ 0)
  copyAbs tag ⟨scratch, 0⟩ ⟨A, off + (k + rel) + n * k⟩ ⟨scratch, 1⟩
  ins (.lit tag ⟨scratch, 3⟩ τ)
  ins (.bin tag .mul ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩)
  copyAbs tag ⟨scratch, 2⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
  ins (.litIdx tag index k)
  pivotScanUpdate tag ⟨scratch, 2⟩ index ⟨scratch, 3⟩ (k + rel)

/-- Select the diagonal if it meets the rational threshold; otherwise select the first active
column maximum. The stored result is an absolute row index and four temporary words are scoped.
The success theorem requires a nonempty active column and a threshold in `(0,1]`. -/
def thresholdPivotChoice {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (τ : ℚ) (index : Cell VB VI) :
    Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 4
  argmaxAbs tag (n - k) A (off + k + n * k) index
  bindIdx tag index (n - k) fun rel =>
    thresholdPivotAt tag n k A scratch off τ (.var rel) index

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- The threshold selector releases its scratch buffer before a following routine. -/
theorem executionComposable_thresholdPivotChoice (I : Interp P ι ℝ C) (tag : P)
    (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ) (τ : ℚ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (thresholdPivotChoice tag n k A off τ index) :=
  executionComposable_single I (fun _ => rfl)

namespace ThresholdPivot

private theorem exec_scale (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (τ : ℚ) (v : ℝ)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    (hv : st.store.read tag scratch 0 = some v)
    {base : Store P ℝ} {index : Cell ℕ ℕ} {g : ℕ → Option ℝ}
    (hF : Store.BlockFrame base tag scratch index.buf index.idx.eval 1 st.store g)
    (hsi : scratch ≠ index.buf) :
    ∃ out, exec I (do
      ins (.lit tag ⟨scratch, 3⟩ τ)
      ins (.bin tag .mul ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩)).run st = some out ∧
      out.store.read tag scratch 3 = some ((τ : ℝ) * v) ∧
      Store.BlockFrame base tag scratch index.buf index.idx.eval 1 out.store g ∧
      (∀ i, i ≠ 3 → out.store.read tag scratch i = st.store.read tag scratch i) := by
  obtain ⟨s₁, hw₁, hr₁, hsh₁, hv₁, hf₁⟩ := exec_scalar_lit I tag st ⟨scratch, 3⟩ τ
    (τ : ℝ) (by simp [hI, exactSem]) ⟨4, hsh, by norm_num [IExp.eval]⟩
  let mid : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s₂, hw₂, hr₂, -, hv₂, hf₂⟩ := exec_scalar_bin I tag mid .mul
    ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩ (τ : ℝ) v ((τ : ℝ) * v) hv₁
    (by rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by norm_num [IExp.eval]))]; exact hv)
    (by simp [hI, exactSem]) ⟨4, hsh₁ ▸ hsh, by norm_num [IExp.eval]⟩
  refine ⟨{ mid with store := s₂, cnt := mid.cnt + I.charge (.bin tag .mul) },
    ?_, hv₂, (hF.write_scratch (fun _ => hsi.symm) hw₁).write_scratch
      (fun _ => hsi.symm) hw₂, ?_⟩
  · rw [exec_run_bind I (b := ins (.lit tag ⟨scratch, 3⟩ τ)) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro i hi
    exact (hf₂ tag scratch i (Or.inr (Or.inr hi))).trans
      (hf₁ tag scratch i (Or.inr (Or.inr hi)))

private theorem exec_finish (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch A : ℕ) (off n k rel : IExp ℕ)
    (index : Cell ℕ ℕ) (v t : ℝ)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    (hv : st.store.read tag A (off + k + n * k).eval = some v)
    (hz : st.store.read tag scratch 1 = some 0)
    (ht : st.store.read tag scratch 3 = some t)
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    {base : Store P ℝ} {g : ℕ → Option ℝ}
    (hF : Store.BlockFrame base tag scratch index.buf index.idx.eval 1 st.store g)
    (hsi : scratch ≠ index.buf) :
    ∃ (out : St P ℝ C) (w : ℝ), exec I (do
      copyAbs tag ⟨scratch, 2⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
      ins (.litIdx tag index k)
      pivotScanUpdate tag ⟨scratch, 2⟩ index ⟨scratch, 3⟩ (k + rel)).run st = some out ∧
      w = (if |v| < t then ((k.eval + rel.eval : ℕ) : ℝ) else k.eval) ∧
      out.store.read tag index.buf index.idx.eval = some w ∧
      Store.BlockFrame base tag scratch index.buf index.idx.eval 1 out.store
        (fun _ => some w) := by
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, b, he₁, hs₁, hb⟩ := h.exec_copyAbs I tag st ⟨scratch, 2⟩
    ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩ v 0 hv hz rfl
    ⟨4, hsh, by norm_num [IExp.eval]⟩
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape (k.eval : ℝ)
    ((Store.shape_of_write_eq_some hs₁).symm ▸ hlen) (by simpa using hlt)
  let ready : St P ℝ C := { mid with store := s₂, cnt := mid.cnt + I.charge (.lit tag) }
  have hF₂ := (hF.write_scratch (fun _ => hsi.symm) hs₁).write_of_lt (by omega : 0 < 1)
    (by simpa using hs₂)
  have hb₂ : ready.store.read tag scratch 2 = some b := by
    rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hsi)]
    exact Store.read_of_write_eq_some hs₁
  have ht₂ : ready.store.read tag scratch 3 = some t := by
    rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inr (by norm_num [IExp.eval]))]
    exact ht
  obtain ⟨out, b', w, he₂, hshape, -, hiw, -, hdw, hf⟩ := h.exec_pivotScanUpdate I
    (hI ▸ isExactIntLit_exactSem (k.eval + rel.eval)) tag ready
    ⟨scratch, 2⟩ index ⟨scratch, 3⟩ (k + rel) (by simp [IExp.eval])
    b (k.eval : ℝ) t hb₂ (Store.read_of_write_eq_some hs₂) ht₂ (Or.inl hsi)
  refine ⟨out, w, ?_, by simpa only [hb, IExp.eval_add] using hdw, hiw,
    hshape.trans hF₂.1, ?_, ?_⟩
  · rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 2⟩
      ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩) (fun _ => rfl), he₁, Option.bind_some]
    change exec I (.seq (.instr (.litIdx tag index k)) _) mid = some out
    rw [exec_seq_instr_litIdx I (by simp [hI, exactSem]) hs₂]
    exact he₂
  · intro q b i hbs hout
    by_cases hcell : b = index.buf ∧ i = index.idx.eval
    · obtain ⟨rfl, rfl⟩ := hcell
      have hq : q ≠ tag := fun hq => hout ⟨hq, rfl, by omega, by omega⟩
      rw [Store.read_eq_none_of_getElem?_shape_of_ne
        (by rw [hshape, Store.shape_of_write_eq_some hs₂,
          Store.shape_of_write_eq_some hs₁]; exact hlen) hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hF.1 ▸ hlen) hq]
    · rw [hf q b i (Or.inl hbs) (by tauto)]
      exact hF₂.2.1 q b i hbs hout
  · intro m hm
    have hm0 : m = 0 := by omega
    simpa only [hm0, Nat.add_zero] using hiw

private theorem exec_prepare (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch A : ℕ) (off n k rel : IExp ℕ)
    (τ : ℚ) (index : Cell ℕ ℕ) (v d : ℝ)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    {base : Store P ℝ} {g : ℕ → Option ℝ}
    (hF : Store.BlockFrame base tag scratch index.buf index.idx.eval 1 st.store g)
    (hv : base.read tag A (off + (k + rel) + n * k).eval = some v)
    (hd : base.read tag A (off + k + n * k).eval = some d)
    (hw : Writable base tag index.buf index.idx.eval 1)
    (hsi : scratch ≠ index.buf) (hAS : A ≠ scratch) (hAI : A ≠ index.buf) :
    ∃ (out : St P ℝ C) (w : ℝ),
      exec I (thresholdPivotAt tag n k A scratch off τ rel index).run st = some out ∧
      w = (if |d| < (τ : ℝ) * |v| then ((k.eval + rel.eval : ℕ) : ℝ) else k.eval) ∧
      out.store.read tag index.buf index.idx.eval = some w ∧
      Store.BlockFrame base tag scratch index.buf index.idx.eval 1 out.store
        (fun _ => some w) := by
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) (0 : ℝ) hsh (by omega)
  let first : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.lit tag) }
  have hF₁ := hF.write_scratch (fun _ => hsi.symm) hs₁
  have hv₁ : first.store.read tag A (off + (k + rel) + n * k).eval = some v := by
    rw [hF₁.read_of_ne hAS (by rintro ⟨_, hbuf, -⟩; exact hAI hbuf)]
    exact hv
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, b, he₂, hs₂, hb⟩ := h.exec_copyAbs I tag first ⟨scratch, 0⟩
    ⟨A, off + (k + rel) + n * k⟩ ⟨scratch, 1⟩ v 0 hv₁
    (Store.read_of_write_eq_some hs₁) rfl
    ⟨4, (Store.shape_of_write_eq_some hs₁).symm ▸ hsh, by norm_num [IExp.eval]⟩
  have hF₂ := hF₁.write_scratch (fun _ => hsi.symm) hs₂
  have hsh₂ : mid.store.shape[scratch]? = some (tag, 4) := by
    rw [Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]
    exact hsh
  obtain ⟨scaled, he₃, ht, hF₃, hf₃⟩ := exec_scale I hI tag mid scratch τ b hsh₂
    (Store.read_of_write_eq_some hs₂) hF₂ hsi
  have hz : scaled.store.read tag scratch 1 = some 0 := by
    rw [hf₃ 1 (by omega), Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by norm_num [IExp.eval]))]
    exact Store.read_of_write_eq_some hs₁
  obtain ⟨out, w, he₄, hdw, hrw, hF₄⟩ := exec_finish I hI tag scaled scratch A off n k rel
    index d ((τ : ℝ) * b) (by rw [hF₃.1, ← hF₂.1]; exact hsh₂)
    (by rw [hF₃.read_of_ne hAS (by rintro ⟨_, hbuf, -⟩; exact hAI hbuf)]; exact hd) hz ht
    (hw.of_shape_eq hF₃.1) hF₃ hsi
  refine ⟨out, w, ?_, by simpa only [hb] using hdw, hrw, hF₄⟩
  change exec I (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0)) _) st = some out
  rw [exec_seq_instr_lit I (by simp [hI, exactSem]) hs₁]
  change exec I (do
    copyAbs tag ⟨scratch, 0⟩ ⟨A, off + (k + rel) + n * k⟩ ⟨scratch, 1⟩
    ins (.lit tag ⟨scratch, 3⟩ τ)
    ins (.bin tag .mul ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩)
    copyAbs tag ⟨scratch, 2⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
    ins (.litIdx tag index k)
    pivotScanUpdate tag ⟨scratch, 2⟩ index ⟨scratch, 3⟩ (k + rel)).run first = some out
  rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 0⟩
    ⟨A, off + (k + rel) + n * k⟩ ⟨scratch, 1⟩) (fun _ => rfl), he₂, Option.bind_some]
  have hcomp := (executionComposable_single I
    (b := ins (.lit tag ⟨scratch, 3⟩ τ)) (fun _ => rfl)).bind
    (executionComposable_single I
      (b := ins (.bin tag .mul ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩)) (fun _ => rfl))
  change exec I ((do
    ins (.lit tag ⟨scratch, 3⟩ τ)
    ins (.bin tag .mul ⟨scratch, 3⟩ ⟨scratch, 3⟩ ⟨scratch, 0⟩)) >>= fun _ => do
      copyAbs tag ⟨scratch, 2⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
      ins (.litIdx tag index k)
      pivotScanUpdate tag ⟨scratch, 2⟩ index ⟨scratch, 3⟩ (k + rel)).run mid = some out
  rw [hcomp, he₃, Option.bind_some]
  exact he₄

private def Result {N : ℕ} (tag : P) (initial : Store P ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) (k : Fin N) (τ : ℚ) (index : Cell ℕ ℕ)
    (final : Store P ℝ) : Prop :=
  ∃ r : Fin N, initial.writeBlock tag index.buf index.idx.eval #[(r.val : ℝ)] = some final ∧
    k ≤ r ∧ (∀ i : Fin N, k ≤ i → (τ : ℝ) * |M i k| ≤ |M r k|) ∧
    ((∀ i : Fin N, k ≤ i → (τ : ℝ) * |M i k| ≤ |M k k|) → r = k)

private theorem choice_quality {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (k b : Fin N) (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) (hkb : k ≤ b)
    (hmax : ∀ i : Fin N, k ≤ i → |M i k| ≤ |M b k|) :
    let r := if |M k k| < (τ : ℝ) * |M b k| then b else k
    k ≤ r ∧ (∀ i : Fin N, k ≤ i → (τ : ℝ) * |M i k| ≤ |M r k|) ∧
    ((∀ i : Fin N, k ≤ i → (τ : ℝ) * |M i k| ≤ |M k k|) → r = k) := by
  have ht₀ : (0 : ℝ) ≤ τ := (Rat.cast_pos.mpr hτ₀).le
  have ht₁ : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ₁
  dsimp only
  split_ifs with ht
  · refine ⟨hkb, fun i hi => ?_, fun hdiag => ?_⟩
    · exact (mul_le_mul_of_nonneg_left (hmax i hi) ht₀).trans
        (mul_le_of_le_one_left (abs_nonneg _) ht₁)
    · exact False.elim (not_lt_of_ge (hdiag b hkb) ht)
  · exact ⟨le_rfl, fun i hi => (mul_le_mul_of_nonneg_left (hmax i hi) ht₀).trans
      (le_of_not_gt ht), fun _ => rfl⟩

private theorem result_of_frame (tag : P) (st σ : Store P ℝ) (n k : IExp ℕ)
    (index : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (τ : ℚ)
    (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hσ : σ = st.push (tag, Array.replicate 4 none))
    (hw : Writable st tag index.buf index.idx.eval 1) (b : Fin (n.eval - k.eval))
    (hm : ∀ j : Fin (n.eval - k.eval),
      |M ((Fin.natAdd_castLEEmb (htail)) j) ⟨k.eval, hk⟩| ≤
      |M ((Fin.natAdd_castLEEmb (htail)) b) ⟨k.eval, hk⟩|)
    (out : Store P ℝ) (ow : ℝ)
    (how : ow = if |M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩| < (τ : ℝ) *
      |M ((Fin.natAdd_castLEEmb (htail)) b) ⟨k.eval, hk⟩|
      then ((k.eval + b.val : ℕ) : ℝ) else k.eval)
    (hF : Store.BlockFrame σ tag st.size index.buf index.idx.eval 1 out (fun _ => some ow)) :
    Result tag st M ⟨k.eval, hk⟩ τ index out.pop := by
  let best := (Fin.natAdd_castLEEmb (htail)) b
  have hkb : (⟨k.eval, hk⟩ : Fin n.eval) ≤ best := by
    change k.eval ≤ best.val
    simp only [best, Fin.val_natAdd_castLEEmb_sub]
    omega
  have hmax : ∀ i : Fin n.eval, (⟨k.eval, hk⟩ : Fin n.eval) ≤ i →
      |M i ⟨k.eval, hk⟩| ≤ |M best ⟨k.eval, hk⟩| := by
    intro i hi
    change k.eval ≤ i.val at hi
    let j : Fin (n.eval - k.eval) := ⟨i.val - k.eval, by have := i.isLt; omega⟩
    have hj : (Fin.natAdd_castLEEmb (htail)) j = i := by
      ext; simp only [Fin.val_natAdd_castLEEmb_sub, j]; omega
    simpa only [hj, best] using hm j
  let r := if |M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩| < (τ : ℝ) * |M best ⟨k.eval, hk⟩|
    then best else ⟨k.eval, hk⟩
  have hor : ow = (r.val : ℝ) := by
    rw [how]; dsimp only [r]; split_ifs <;>
      simp only [best, Fin.val_natAdd_castLEEmb_sub]
  obtain ⟨final, hwrite⟩ := (show Writable st tag index.buf index.idx.eval
    (#[(r.val : ℝ)] : Array ℝ).size by simpa using hw).exists_writeBlock
  have hpop : out.pop = final := (hσ ▸ hF).pop_eq hwrite (by simp)
    (fun m hm => by
      have hm0 : m = 0 := by omega
      subst m
      simp [hor])
  obtain ⟨hkr, hquality, hdiag⟩ := choice_quality M ⟨k.eval, hk⟩ best τ hτ₀ hτ₁ hkb hmax
  exact ⟨r, hpop ▸ hwrite, hkr, hquality, hdiag⟩

private theorem exec_body (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st σ : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (τ : ℚ) (index : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hM : Holds st.store tag A off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hAI : A ≠ index.buf)
    (hσ : σ.store = st.store.push (tag, Array.replicate 4 none)) :
    ∃ out, exec I (do
      argmaxAbs tag (n - k) A (off + k + n * k) index
      bindIdx tag index (n - k) fun rel =>
        thresholdPivotAt tag n k A st.store.size off τ (.var rel) index).run σ = some out ∧
      Result tag st.store M ⟨k.eval, hk⟩ τ index out.store.pop := by
  let emb := Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)
  let x : Fin (n.eval - k.eval) → ℝ := fun i => M (emb i) ⟨k.eval, hk⟩
  have hA : A < st.store.size := Store.lt_size_of_read_eq_some (hM ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
  have hidx : index.buf < st.store.size := hw.lt_size (by omega)
  have hin : ReadsDecoded σ.store (fun _ v => v) tag A (off + k + n * k).eval x := by
    intro i
    refine ⟨x i, ?_, rfl⟩
    rw [hσ, Store.read_push_of_lt hA]
    simpa only [x, emb, Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, IExp.eval_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hM (emb i) ⟨k.eval, hk⟩
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, w, b, he₁, hs₁, hdw, hm, -⟩ := h.exec_argmaxAbs I
    (hI ▸ isExactIntLit_exactSem n.eval) (Nat.sub_le _ _) (Nat.sub_pos_of_lt hk)
    tag σ x A (off + k + n * k) index hin
    (hσ ▸ hw.push (tag, Array.replicate 4 none)) hAI
  have he₁' : exec I (argmaxAbs tag (n - k) A (off + k + n * k) index).run σ = some mid :=
    (exec_eq_of_normIdx_eq I
      (s := (argmaxAbs tag (n - k) A (off + k + n * k) index).run)
      (s' := (argmaxAbs tag (.const (n.eval - k.eval)) A (off + k + n * k) index).run)
      rfl σ).trans he₁
  let ready : St P ℝ C := { mid with cnt := mid.cnt + I.charge (.toNat tag) }
  have hF : Store.BlockFrame σ.store tag st.store.size index.buf index.idx.eval 1
      ready.store (fun _ => some w) := by
    have hF₀ : Store.BlockFrame σ.store tag st.store.size index.buf index.idx.eval 1
        σ.store (fun j => σ.store.read tag index.buf (index.idx.eval + j)) :=
      ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
    exact (hF₀.writeBlock (off := 0) (by simpa using hs₁) (by simp)).congr
      (fun j hj => by
        have hj0 : j = 0 := by omega
        subst j
        simp)
  obtain ⟨out, ow, he₂, how, hor, hFout⟩ := exec_prepare I hI tag ready st.store.size A
    off n k (.var b.val) τ index (x b) (M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
    (by rw [hF.1, hσ]; exact Store.getElem?_shape_push_size _ _ _) hF
    (by rw [hσ, Store.read_push_of_lt hA];
        simpa only [x, emb, Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, IExp.eval_mul,
          IExp.eval_var, Nat.add_assoc] using
          hM (emb b) ⟨k.eval, hk⟩)
    (by rw [hσ, Store.read_push_of_lt hA]; simpa [IExp.eval] using hM ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
    (hσ ▸ hw.push (tag, Array.replicate 4 none)) (by omega) (by omega) hAI
  have hto : I.sem.toNat tag w = some b.val := by simp [hI, exactSem, hdw]
  refine ⟨out, ?_, ?_⟩
  · rw [exec_run_bind I (b := argmaxAbs tag (n - k) A (off + k + n * k) index)
      (fun _ => rfl), he₁', Option.bind_some]
    change exec I (.seq (.bindIdx tag index (n - k) _) .skip) mid = _
    rw [exec_seq_skip, exec_bindIdx_of_read I
      (by simpa using Store.read_of_writeBlock_eq_some_of_lt hs₁ (by simp : 0 < #[w].size))
      hto (by change b.val ≤ n.eval - k.eval; omega)]
    exact he₂
  · exact result_of_frame tag st.store σ.store n k index M τ hk (Nat.sub_le _ _) hτ₀ hτ₁ hσ hw b hm
      out.store ow (by simpa only [x, emb, IExp.eval_var] using how) hFout

end ThresholdPivot

/-- Exact threshold partial pivot selection succeeds on every nonempty active column. The
chosen absolute row satisfies the threshold quality bound and a qualifying diagonal is always
accepted, including equality. The only net write is its exact index literal; the source is
retained. A zero chosen pivot implies a zero active column, with no nonsingularity premise. -/
theorem exec_thresholdPivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (τ : ℚ) (index : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hM : Holds st.store tag A off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hAI : A ≠ index.buf) :
    ∃ (out : St P ℝ C) (r : Fin n.eval),
      exec I (thresholdPivotChoice tag n k A off τ index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[(r.val : ℝ)] = some out.store ∧
      k.eval ≤ r.val ∧ Holds out.store tag A off.eval M ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → (τ : ℝ) * |M i ⟨k.eval, hk⟩| ≤
        |M r ⟨k.eval, hk⟩|) ∧
      ((∀ i : Fin n.eval, k.eval ≤ i.val → (τ : ℝ) * |M i ⟨k.eval, hk⟩| ≤
        |M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩|) → r = ⟨k.eval, hk⟩) ∧
      (M r ⟨k.eval, hk⟩ = 0 → ∀ i : Fin n.eval, k.eval ≤ i.val → M i ⟨k.eval, hk⟩ = 0) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → M r ⟨k.eval, hk⟩ ≠ 0 →
        |M i ⟨k.eval, hk⟩ / M r ⟨k.eval, hk⟩| ≤ (τ : ℝ)⁻¹) := by
  let Q := ThresholdPivot.Result tag st.store M ⟨k.eval, hk⟩ τ index
  obtain ⟨out, he, r, hs, hkr, hquality, hdiag⟩ := exists_exec_alloc I tag 4
    (fun scratch => ((do
      argmaxAbs tag (n - k) A (off + k + n * k) index
      bindIdx tag index (n - k) fun rel =>
        thresholdPivotAt tag n k A scratch off τ (.var rel) index) :
          Builder P ι ℕ ℕ Unit).run) st Q
    (fun σ hσ => ThresholdPivot.exec_body I hI tag st σ n k A off τ index M
      hk hτ₀ hτ₁ hM hw hAI hσ)
  refine ⟨out, r, ?_, hs, hkr, ?_, hquality, hdiag, ?_, ?_⟩
  · change exec I (.seq (.alloc tag 4 _) .skip) st = some out
    rw [exec_seq_skip]
    exact he
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hAI)]
    exact hM i j
  · intro hz i hi
    have hq := hquality i hi
    rw [hz, abs_zero] at hq
    have ht : (0 : ℝ) < τ := Rat.cast_pos.mpr hτ₀
    exact abs_eq_zero.mp (le_antisymm (by nlinarith [abs_nonneg (M i ⟨k.eval, hk⟩)])
      (abs_nonneg _))
  · intro i hi hp
    have ht : (0 : ℝ) < τ := Rat.cast_pos.mpr hτ₀
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hp)).mpr
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ ht).mpr (by simpa [mul_comm] using hquality i hi)

end NLAlib.Computation
