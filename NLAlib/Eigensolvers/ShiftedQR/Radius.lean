/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Matrix.QRIteration.ShiftSearch

/-!
# Scalar exceptional-shift radius

Iterated square roots evaluate the fractional power in the exceptional radius. Their
nonnegative inputs follow from the actual squared-modulus product and conditioning bound.
All square roots, products and literals remain scalar calls in the fixed syntax.

## Main results

* `NLAlib.ShiftedQR.squareRoots_writes`: the total exact iterated-square-root loop.
* `NLAlib.ShiftedQR.radiusWithScratch`: the actual scalar radius implementation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Apply the scalar square root `m` times to one exactly aliased input/output word. -/
def squareRoots : Impl Op Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .loop (.var 0) (.call (Has.inj ScalarOp.sqrt) []
    [⟨0, .var 1⟩] [⟨1, .var 2⟩])

/-- The actual in-place scalar loop returns the iterated mathematical square root. Its initial
word is nonnegative, so every executed root meets the exact model's numerical domain. -/
theorem squareRoots_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {x : ℕ × ℕ} {v : ℝ} (hx : m.store.get x.1 x.2 = some v) (hv : 0 ≤ v) :
    Writes .total I τ squareRoots.body (Env.frame [k] [x, x]) (Store.inBlock x.1 x.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get x.1 x.2 = some (Real.sqrt^[k] v)) m := by
  unfold squareRoots
  refine writes_loop rfl (fun _ => Store.inBlock x.1 x.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.get x.1 x.2 = some (Real.sqrt^[i] v))
    (And.intro rfl hx) ?_
  intro i _ m' _ ⟨hp, hVal⟩
  have hn : 0 ≤ Real.sqrt^[i] v := by
    cases i with
    | zero => exact hv
    | succ i => rw [Function.iterate_succ_apply']; exact Real.sqrt_nonneg _
  have he : M.sqrt (Real.sqrt^[i] v) = Real.sqrt (Real.sqrt^[i] v) := hE.sqrt _ hn
  refine (writes_call_un (hS .sqrt) rfl rfl trivial hVal rfl
    (Store.lt_len_of_get hVal)).mono le_rfl ?_
  intro m'' _ ⟨hp', hSqrt⟩
  exact ⟨hp'.trans hp, by simpa only [he, Function.iterate_succ_apply'] using hSqrt⟩

/-- Compute `sqrt^[m](2*B*sqrt P)*θ*α` with one caller-owned scratch word. -/
def radiusWithScratch : Impl Op Tst := opsImpl% [m] (P, B, theta, alpha, T) → (R) {
  call (Has.inj ScalarOp.sqrt) [] (P) → (R);
  call (Has.inj (ScalarOp.lit 2)) [] () → (T);
  call (Has.inj ScalarOp.mul) [] (T, B) → (T);
  call (Has.inj ScalarOp.mul) [] (T, R) → (R);
  run squareRoots.body [m] (R, R);
  call (Has.inj ScalarOp.mul) [] (R, theta) → (R);
  call (Has.inj ScalarOp.mul) [] (R, alpha) → (R)
}

/-- Scope one real scratch word around the exceptional-radius computation. -/
def radius : Impl Op Tst := opsImpl% [m] (P, B, theta, alpha) → (R) {
  let T ← alloc 1;
  run radiusWithScratch.body [m] (P, B, theta, alpha, T, R)
}

/-- Actual scalar radius calculation with one scratch word. The squared-product input and
conditioning bound are nonnegative; all other operations are exact products. The scratch and
result views are separated from each other and from the three still-needed input parameters. -/
theorem radiusWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {p b theta alpha t r : ℕ × ℕ} {P B θ α : ℝ}
    (hP : m.store.get p.1 p.2 = some P) (hB : m.store.get b.1 b.2 = some B)
    (hθ : m.store.get theta.1 theta.2 = some θ)
    (hα : m.store.get alpha.1 alpha.2 = some α) (hP0 : 0 ≤ P) (hB0 : 0 ≤ B)
    (ht : t.2 < m.store.len t.1) (hr : r.2 < m.store.len r.1)
    (htr : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock r.1 r.2 1))
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock r.1 r.2 1)
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock theta.1 theta.2 1 ⊔
        Store.inBlock alpha.1 alpha.2 1)) :
    Writes .total I τ radiusWithScratch.body (Env.frame [k] [p, b, theta, alpha, t, r])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock r.1 r.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get r.1 r.2 = some (Real.sqrt^[k] (2 * B * Real.sqrt P) * θ * α)) m := by
  let input : Store ℝ → Prop := fun st => st.get b.1 b.2 = some B ∧
    st.get theta.1 theta.2 = some θ ∧ st.get alpha.1 alpha.2 = some α
  have hinput : Store.ReadsOnly
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock theta.1 theta.2 1 ⊔
        Store.inBlock alpha.1 alpha.2 1) input :=
    ((Store.readsOnly_get _ _ _).and ((Store.readsOnly_get _ _ _).and
      (Store.readsOnly_get _ _ _))).mono (by fp_sub)
  have hinput₀ : input m.store := ⟨hB, hθ, hα⟩
  have htl := Store.lt_length_of_lt_len ht
  have hrl := Store.lt_length_of_lt_len hr
  have hbl := Store.lt_length_of_get hB
  have hthetal := Store.lt_length_of_get hθ
  have halphal := Store.lt_length_of_get hα
  have hmul (x y : ℝ) : M.mul x y = x * y := hE.mul x y
  have hsqrt : M.sqrt P = Real.sqrt P := hE.sqrt P hP0
  have htwo : M.lit 2 = (2 : ℝ) := by simpa using hE.lit 2
  unfold radiusWithScratch
  refine ((writes_call_un (hS .sqrt) rfl rfl trivial hP rfl hr).keep hinput
    (hsep.mono le_sup_right le_rfl) hinput₀).seq_le le_sup_right ?_
  intro m₁ hfr₁ ⟨⟨hp₁, hR₁⟩, hB₁, hθ₁, hα₁⟩
  refine ((writes_call_const (hS (.lit 2)) rfl trivial
    (by rw [hfr₁.len_eq]; exact ht)).keep hinput
    (hsep.mono le_sup_left le_rfl) ⟨hB₁, hθ₁, hα₁⟩).seq_le le_sup_left ?_
  intro m₂ hfr₂ ⟨⟨hp₂, hT₂⟩, hB₂, hθ₂, hα₂⟩
  have hR₂ := hfr₂.keep (Store.readsOnly_get _ _ _) htr hR₁
  refine ((writes_call_bin (hS .mul) rfl rfl trivial hT₂ hB₂ rfl
    (fun _ => ⟨by room, by room⟩)).keep hinput
    (hsep.mono le_sup_left le_rfl) ⟨hB₂, hθ₂, hα₂⟩).seq_le le_sup_left ?_
  intro m₃ hfr₃ ⟨⟨hp₃, hT₃⟩, hB₃, hθ₃, hα₃⟩
  have hR₃ := hfr₃.keep (Store.readsOnly_get _ _ _) htr hR₂
  refine ((writes_call_bin (hS .mul) rfl rfl trivial hT₃ hR₃ rfl
    (fun _ => ⟨by room, by room⟩)).keep hinput
    (hsep.mono le_sup_right le_rfl) ⟨hB₃, hθ₃, hα₃⟩).seq_le le_sup_right ?_
  intro m₄ _ ⟨⟨hp₄, hR₄⟩, hB₄, hθ₄, hα₄⟩
  have hR₄' : m₄.store.get r.1 r.2 = some (2 * B * Real.sqrt P) := by
    simpa only [hmul, hsqrt, htwo] using hR₄
  have hroots := squareRoots_writes (τ := τ) (m := m₄) (k := k) hS hE hR₄'
    (mul_nonneg (mul_nonneg (by norm_num) hB0) (Real.sqrt_nonneg P))
  refine (hroots.keep hinput (hsep.mono le_sup_right le_rfl) ⟨hB₄, hθ₄, hα₄⟩).frame_seq_le
    rfl rfl (by simpa [Mem.Live] using Store.lt_length_of_get hR₄') le_sup_right ?_
  intro m₅ _ ⟨⟨hp₅, hR₅⟩, hB₅, hθ₅, hα₅⟩
  refine ((writes_call_bin (hS .mul) rfl rfl trivial hR₅ hθ₅ rfl
    (fun _ => ⟨by room, by room⟩)).keep hinput
    (hsep.mono le_sup_right le_rfl) ⟨hB₅, hθ₅, hα₅⟩).seq_le le_sup_right ?_
  intro m₆ _ ⟨⟨hp₆, hR₆⟩, _, _, hα₆⟩
  refine (writes_call_bin (hS .mul) rfl rfl trivial hR₆ hα₆ rfl
    (fun _ => ⟨by room, by room⟩)).mono le_sup_right ?_
  intro m₇ _ ⟨hp₇, hR₇⟩
  exact ⟨hp₇.trans (hp₆.trans (hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))))),
    by simpa only [hmul] using hR₇⟩

/-- The scoped exceptional-radius routine computes its exact real value and releases its
single scratch word. The product input may alias the output because it is read first. -/
theorem radius_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {p b theta alpha r : ℕ × ℕ} {P B θ α : ℝ}
    (hP : m.store.get p.1 p.2 = some P) (hB : m.store.get b.1 b.2 = some B)
    (hθ : m.store.get theta.1 theta.2 = some θ)
    (hα : m.store.get alpha.1 alpha.2 = some α) (hP0 : 0 ≤ P) (hB0 : 0 ≤ B)
    (hr : r.2 < m.store.len r.1)
    (hsep : Fp.Disj (Store.inBlock r.1 r.2 1)
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock theta.1 theta.2 1 ⊔
        Store.inBlock alpha.1 alpha.2 1)) :
    Writes .total I τ radius.body (Env.frame [k] [p, b, theta, alpha, r])
      (Store.inBlock r.1 r.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get r.1 r.2 = some (Real.sqrt^[k] (2 * B * Real.sqrt P) * θ * α)) m := by
  have hpl := Store.lt_length_of_get hP
  have hbl := Store.lt_length_of_get hB
  have hthetal := Store.lt_length_of_get hθ
  have halphal := Store.lt_length_of_get hα
  have hrl := Store.lt_length_of_lt_len hr
  change Writes .total I τ (Stmt.allocs [.const 1] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [1]) rfl
    (fun hBelow hp => ⟨hp.1, ((hBelow r.1 hrl).2 r.2).trans hp.2⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 1 := by simpa [t] using hlens 0 (by simp)
  have htr : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock r.1 r.2 1) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hprotected : Fp.Disj (Store.inBlock t.1 t.2 1)
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock theta.1 theta.2 1 ⊔
        Store.inBlock alpha.1 alpha.2 1) := by
    dsimp only [t]
    disjoint
  have hbody := radiusWithScratch_writes (τ := τ) (m := ⟨store, m.pos⟩)
    (k := k) (t := t) (r := r) hS hE
    (((hBelow p.1 hpl).2 p.2).trans hP) (((hBelow b.1 hbl).2 b.2).trans hB)
    (((hBelow theta.1 hthetal).2 theta.2).trans hθ)
    (((hBelow alpha.1 halphal).2 alpha.2).trans hα) hP0 hB0
    (by dsimp [t]; rw [ht]; omega) (by rw [(hBelow r.1 hrl).1]; exact hr) htr
    (Fp.disj_sup_left.mpr ⟨hprotected, hsep⟩)
  exact (hbody.in_frame rfl rfl
    (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left) (fun _ _ h => h)

end NLAlib.ShiftedQR
