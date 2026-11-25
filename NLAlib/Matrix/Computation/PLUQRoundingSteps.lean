/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQRoundingState
public import NLAlib.Matrix.Computation.PLUQRoundingPivot
public import NLAlib.Matrix.Computation.LURoundingStep
public import NLAlib.Matrix.Computation.PLUQPrefix

/-!
# Actual rounded complete-pivot LU iterations

Both current-position logs determine the input permutation. Their actual row and column
exchanges transport the existing numerical prefix before the shared rounded elimination phase.

## Main results

* `NLAlib.Computation.PLUQRounding.exec_iteration`: actual complete-pivot iteration success.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQRounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem exec_totalPhase {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (S L U Hr Hc : ℕ) (lo uo hro hco : IExp ℕ)
    (B M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec tag S 0 M)
    (hF : HoldsDecoded st.store dec tag L lo.eval F)
    (hG : HoldsDecoded st.store dec tag U uo.eval G)
    (hmax : ∀ i : Fin n.eval, ⟨k.eval, hk⟩ ≤ i →
      |M i ⟨k.eval, hk⟩| ≤ |M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩|)
    (hpref : u tag < 1 → IsLURoundingPrefix (u tag) k.eval B M F G)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hLU : L ≠ U)
    (hLR : L ≠ Hr) (hUR : U ≠ Hr) (base : Store P K)
    (hf : PLUQ.Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    ∃ (out : St P K C) (M' : Matrix (Fin n.eval) (Fin n.eval) ℝ) (v : Fin n.eval → ℝ),
      exec I (do luColumnTotal tag n k S L U 0 lo uo
                 schurStepTotal tag n S 0 k).run st = some out ∧
      PLUQ.Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      HoldsDecoded out.store dec tag S 0 M' ∧
      HoldsDecoded out.store dec tag L lo.eval (F.updateCol r v) ∧
      HoldsDecoded out.store dec tag U uo.eval
        (G.updateRow r (fun j => if j < r then 0 else M r j)) ∧
      (∀ i, i < r → v i = 0) ∧ v r = 1 ∧
      (∀ i, r < i → RelErr (u tag) (M i r / M r r) (v i)) ∧
      (u tag < 1 → IsLURoundingPrefix (u tag) (k.eval + 1) B M'
        (F.updateCol r v) (G.updateRow r (fun j => if j < r then 0 else M r j))) ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U → out.store.read q b i = st.store.read q b i := by
  obtain ⟨out, M', v, hr, hf', hM', hF', hG', hv0, hv1, hvrel, hnum, hhist⟩ :=
    PLURounding.exec_totalPhase I h n k hi tag st S L U Hr lo uo hro B M F G hk
      hM hF hG hmax hpref hSL hSU hSR hLU hLR hUR st.store
      (PLU.Frame.refl st.store n.eval S L U Hr lo.eval uo.eval hro.eval)
  refine ⟨out, M', v, hr, ⟨hf'.shape.trans hf.shape, ?_⟩, hM', hF', hG',
    hv0, hv1, hvrel, hnum, ?_⟩
  · intro q b i hbS hbL hbU hbR hbC
    exact (hf'.outside q b i hbS hbL hbU hbR).trans (hf.outside q b i hbS hbL hbU hbR hbC)
  · intro q b i hbS hbL hbU
    by_cases hb : b = Hr
    · subst b; exact hhist q i
    · exact hf'.outside q b i (Or.inl hbS) (Or.inl hbL) (Or.inl hbU) (Or.inl hb)

private theorem log_update {N k H ho : ℕ} {s t : Store P K} {dec : P → K → ℝ} {tag : P}
    (p : Fin N → Fin N) (r : Fin N) (hk : k < N) (hkr : k ≤ r.val) (w : K)
    (hr : t.read tag H (ho + k) = some w) (hd : dec tag w = r.val)
    (hread : ∀ j : Fin N, j.val < k → t.read tag H (ho + j) = s.read tag H (ho + j))
    (hlog : ∀ j : Fin N, j.val < k → ∃ a,
      s.read tag H (ho + j) = some a ∧ dec tag a = (p j).val ∧ j ≤ p j) :
    ∀ j : Fin N, j.val < k + 1 → ∃ a,
      t.read tag H (ho + j) = some a ∧
      dec tag a = ((Function.update p ⟨k, hk⟩ r) j).val ∧
      j ≤ Function.update p ⟨k, hk⟩ r j := by
  intro j hj
  by_cases he : j = ⟨k, hk⟩
  · subst j
    exact ⟨w, hr, by simpa only [Function.update_self] using hd,
      by simpa only [Function.update_self, Fin.le_def] using hkr⟩
  · have hj' : j.val < k := by
      have hne : j.val ≠ k := fun e => he (Fin.ext e)
      omega
    obtain ⟨a, ha, hd, hle⟩ := hlog j hj'
    rw [Function.update_of_ne he]
    exact ⟨a, (hread j hj').trans ha, hd, hle⟩

/-- Both actual pivot choices and rounded elimination advance the stored two-log prefix.
Scalar results are assumed in range by `safeTrue`; this theorem makes no claim that a finite
floating-point format satisfies that assumption. A zero active pivot is division-free. -/
theorem exec_iteration {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (base : Store P K) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (S L U Hr Hc : ℕ) (lo uo hro hco : IExp ℕ)
    (hR : Writable base tag Hr hro.eval n.eval) (hC : Writable base tag Hc hco.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (k : ℕ) (hk : k < n.eval) (st : St P K C)
    (hs : State dec (u tag) base tag A S L U Hr Hc lo.eval uo.eval hro.eval hco.eval k st.store) :
    ∃ out, exec I (do
      completePivotChoice tag n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n S 0 (.var k) (.var row)
        swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n S 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out ∧
      State dec (u tag) base tag A S L U Hr Hc lo.eval uo.eval hro.eval hco.eval
        (k + 1) out.store := by
  obtain ⟨p, q, R, F, G, hS, hF, hG, hlower, hdiag, hupper, hbound, hpref,
    hrow, hcol⟩ := hs.values
  let a : Fin n.eval := ⟨k, hk⟩
  obtain ⟨swapped, r, c, rw, cw, hr₁, hkr, hkc, hf₁, hS₁, hF₁, hG₁, hmax₁,
    hrow₁, hcol₁, hdr, hdc, hreads⟩ := exec_pivotPhase I h tag st n (.var k) hi S L U Hr Hc
      lo uo hro hco R F G hk hS hF hG (hR.of_shape_eq hs.frame.shape)
      (hC.of_shape_eq hs.frame.shape) hSL hSU hSR hSC hLU hLR hLC hUR hUC hRC base hs.frame
  let τ := Equiv.swap a r
  let υ := Equiv.swap a c
  let R' := R.submatrix τ υ
  let F' := F.submatrix τ id
  let G' := G.submatrix id υ
  let B' := A.submatrix (luPivotPermutation (Function.update p a r) (k + 1))
    (luPivotPermutation (Function.update q a c) (k + 1))
  have hfixr : ∀ i : Fin n.eval, i.val < k → τ i = i :=
    Fin.swap_apply_of_lt_of_le a r hkr
  have hfixc : ∀ j : Fin n.eval, j.val < k → υ j = j :=
    Fin.swap_apply_of_lt_of_le a c hkc
  have hmax : ∀ i, a ≤ i → |R' i a| ≤ |R' a a| := by
    intro i hai
    simpa only [R', Matrix.submatrix_apply, τ, υ, Equiv.swap_apply_left, a, IExp.eval_var] using
      hmax₁ (τ i) c (Fin.le_swap_apply_of_le a r hkr i hai) hkc
  have hnum : u tag < 1 → IsLURoundingPrefix (u tag) k B' R' F' G' := by
    intro hu1
    dsimp only [B']
    rw [PLUQ.submatrix_luPivotPermutation_update]
    simpa only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id] using
      ((hpref hu1).submatrix_left τ hfixr).submatrix_right υ hfixc
  obtain ⟨out, R'', v, hr₂, hf₂, hS₂, hF₂, hG₂, hv0, hv1, hvrel, hnum₂, hhist₂⟩ :=
    exec_totalPhase I h n (.var k) hi tag swapped S L U Hr Hc lo uo hro hco B' R' F' G' hk
      hS₁ hF₁ hG₁ hmax hnum hSL hSU hSR hLU hLR hUR base hf₁
  have hvbound := PLURounding.abs_column_le_one_add (h.nonneg (p := tag) trivial)
    R' a v hv0 hv1 hvrel hmax
  have hupper' : ∀ i j, i.val < k → j < i → G' i j = 0 := by
    intro i j hi hji
    change G i (υ j) = 0
    rw [hfixc j (lt_trans hji hi)]
    exact hupper i j hi hji
  obtain ⟨hlower₂, hdiag₂, hupper₂, hbound₂⟩ := PLURounding.shape_update F G' a r rfl hkr v
    (fun j => if j < a then 0 else R' a j) hlower hdiag hupper' hbound hv0 hv1
    (fun j hj => if_pos hj) hvbound
  refine ⟨out, ?_, hf₂, Function.update p a r, Function.update q a c, R'', _, _, hS₂, hF₂,
    hG₂, hlower₂, hdiag₂, hupper₂, hbound₂, hnum₂, ?_, ?_⟩
  · have hcomp : ExecutionComposable I (do
        completePivotChoice tag n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I ((do
      completePivotChoice tag n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n S 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)) >>= fun _ => do
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out
    rw [hcomp, hr₁, Option.bind_some]
    exact hr₂
  · apply log_update p r hk hkr rw
      ((hhist₂ tag Hr _ hSR.symm hLR.symm hUR.symm).trans hrow₁) hdr _ hrow
    intro j hj
    rw [hhist₂ tag Hr _ hSR.symm hLR.symm hUR.symm]
    exact hreads tag Hr _ hSR.symm hLR.symm hUR.symm
      (Or.inr (by change hro.eval + j.val ≠ hro.eval + k; omega)) (Or.inl hRC)
  · apply log_update q c hk hkc cw
      ((hhist₂ tag Hc _ hSC.symm hLC.symm hUC.symm).trans hcol₁) hdc _ hcol
    intro j hj
    rw [hhist₂ tag Hc _ hSC.symm hLC.symm hUC.symm]
    exact hreads tag Hc _ hSC.symm hLC.symm hUC.symm (Or.inl hRC.symm)
      (Or.inr (by change hco.eval + j.val ≠ hco.eval + k; omega))

end NLAlib.Computation.PLUQRounding
