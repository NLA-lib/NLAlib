/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveFactor
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveStorage
public import NLAlib.Eigensolvers.ShiftedQR.RowRotation

/-!
# Applying the saved row-solve rotations

The row-vector program reads the actual stored Givens coefficients and applies each pair
rotation using ordinary scalar operations. Saved coefficients are visited in reverse order,
with the same ten scratch words reused by every adjacent pair update.

## Main results

* `NLAlib.ShiftedQR.vectorRotation`: one saved rotation applied to two adjacent vector entries.
* `NLAlib.ShiftedQR.reverseVectorRotations`: the actual reverse-order coefficient loop.
* `NLAlib.ShiftedQR.reverseVectorRotations_writes`: the stored mathematical reverse rotations.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Apply saved rotation `k` to its two adjacent vector entries using caller-owned scratch. -/
def vectorRotation : Impl Op Tst := opsImpl% [n, k] (V, Cf, T) → (V) {
  run rotateRowWithScratch.body []
    (Cf[4 * k], Cf[4 * k + 2], V[2 * k], V[2 * (k + 1)], T,
      V[2 * k], V[2 * (k + 1)])
}

/-- Visit saved rotations from `n-2` through zero, retaining exactly aliased vector storage. -/
def reverseVectorRotations : Impl Op Tst := opsImpl% [n] (V, Cf, T) → (V) {
  for r < n - 1 {
    run vectorRotation.body [n, n - 2 - r] (V, Cf, T, V)
  }
}

private theorem row_givens_left {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (c s : ℂ) (v : Fin n → ℂ) :
    (v ᵥ* givens i j c s) i = v i * c - v j * star s := by
  exact mul_givens_apply_left hij c s (fun _ : Fin 1 => v) 0

private theorem row_givens_right {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (c s : ℂ) (v : Fin n → ℂ) :
    (v ᵥ* givens i j c s) j = v i * s + v j * star c := by
  exact mul_givens_apply_right hij c s (fun _ : Fin 1 => v) 0

private theorem row_givens_other {n : ℕ} {i j q : Fin n} (hqi : q ≠ i) (hqj : q ≠ j)
    (c s : ℂ) (v : Fin n → ℂ) : (v ᵥ* givens i j c s) q = v q := by
  exact mul_givens_apply_of_ne hqi hqj c s (fun _ : Fin 1 => v) 0

private theorem vector_givens_readback {n : ℕ} {v t : ℕ × ℕ}
    {w : Fin n → ℂ} {store store' : Store ℝ} {i j : Fin n} {c s : ℂ}
    (hV : HoldsVector v w store) (htv : t.1 ≠ v.1) (hij : i ≠ j)
    (hfr : store.EqOff (Fp.blocks [t, (v.1, v.2 + 2 * i), (v.1, v.2 + 2 * j)]
      [10, 2, 2]) store')
    (hx : store'.readBlock v.1 (v.2 + 2 * i) 2 =
      some [(w i * c - w j * star s).re, (w i * c - w j * star s).im])
    (hy : store'.readBlock v.1 (v.2 + 2 * j) 2 =
      some [(w i * s + w j * star c).re, (w i * s + w j * star c).im]) :
    HoldsVector v (w ᵥ* givens i j c s) store' := by
  have hdis (p q : Fin n) (hne : p ≠ q) :
      Fp.Disj (Store.inBlock v.1 (v.2 + 2 * p) 2)
        (Store.inBlock v.1 (v.2 + 2 * q) 2) := by
    have hpq : (p, (0 : Fin 1)) ≠ (q, (0 : Fin 1)) := fun h => hne (congrArg Prod.fst h)
    simpa only [EntryCodec.entryBlock, EntryCodec.pair, Fin.val_zero, zero_mul, zero_add,
      Nat.mul_comm 2] using
      (EntryCodec.pair ℝ).disj_entryBlock_matrix (b := v.1) (off := v.2) hpq
  have hkeep (q : Fin n) (hqi : q ≠ i) (hqj : q ≠ j) :
      store'.readBlock v.1 (v.2 + 2 * q) 2 = some [(w q).re, (w q).im] := by
    refine hfr.keep (Store.readsOnly_readBlock _ _ _ _) ?_ (HoldsVector.read_entry hV q)
    simp only [Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left]
    exact ⟨Fp.disj_inBlock_of_ne htv, (hdis q i hqi).symm, (hdis q j hqj).symm, trivial⟩
  apply HoldsVector.of_get
  · intro q
    by_cases hqi : q = i
    · subst q
      rw [row_givens_left hij c s w]
      simpa using Store.get_of_readBlock hx (j := 0) (by omega) (0 : ℝ)
    by_cases hqj : q = j
    · subst q
      rw [row_givens_right hij c s w]
      simpa using Store.get_of_readBlock hy (j := 0) (by omega) (0 : ℝ)
    rw [row_givens_other hqi hqj c s w]
    simpa using Store.get_of_readBlock (hkeep q hqi hqj) (j := 0) (by omega) (0 : ℝ)
  · intro q
    by_cases hqi : q = i
    · subst q
      rw [row_givens_left hij c s w]
      simpa using Store.get_of_readBlock hx (j := 1) (by omega) (0 : ℝ)
    by_cases hqj : q = j
    · subst q
      rw [row_givens_right hij c s w]
      simpa using Store.get_of_readBlock hy (j := 1) (by omega) (0 : ℝ)
    rw [row_givens_other hqi hqj c s w]
    simpa using Store.get_of_readBlock (hkeep q hqi hqj) (j := 1) (by omega) (0 : ℝ)

/-- One saved rotation is read from its actual coefficient words and applied to the two
adjacent stored vector coordinates. All other vector words are preserved. -/
theorem vectorRotation_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {v cf t : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (hV : HoldsVector v w m.store) (hCf : HoldsCoefficients cf D (n - 1) m.store)
    (hk : k + 1 < n) (htv : t.1 ≠ v.1) (htc : t.1 ≠ cf.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ vectorRotation.body (Env.frame [n, k] [v, cf, t, v])
      (Store.inBlock v.1 v.2 (2 * n) ⊔ Store.inBlock t.1 t.2 10)
      (fun μ => μ.pos = m.pos ∧ HoldsVector v (reverseRotationStep D w k) μ.store) m := by
  let i : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hk⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; dsimp [i, j] at this; omega
  obtain ⟨hc, hs⟩ := hCf k (by omega)
  have hcap : v.2 + 2 * n ≤ m.store.len v.1 := by
    simpa only [one_mul] using Store.le_len_of_readBlock hV (by omega)
  have hxy : Fp.Disj (Store.inBlock v.1 (v.2 + 2 * k) 2)
      (Store.inBlock v.1 (v.2 + 2 * (k + 1)) 2) := by
    intro b q hx hy
    dsimp only [Store.inBlock] at hx hy
    omega
  have hc0 := Store.get_of_readBlock hc (j := 0) (by omega) (0 : ℝ)
  have hcl := Store.lt_length_of_get hc0
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV i)
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  have hrot := writes_rotateRowWithScratch (τ := τ) (m := m)
    (c := (cf.1, cf.2 + 4 * k)) (s := (cf.1, cf.2 + 4 * k + 2))
    (x := (v.1, v.2 + 2 * k)) (y := (v.1, v.2 + 2 * (k + 1))) (t := t)
    (cv := (stepCoefs D k).1) (sv := (stepCoefs D k).2) (xv := w i) (yv := w j)
    hS hE htc htc htv htv hxy (by simpa using hc0)
    (by simpa using Store.get_of_readBlock hc (j := 1) (by omega) (0 : ℝ))
    (by simpa using Store.get_of_readBlock hs (j := 0) (by omega) (0 : ℝ))
    (by simpa [Nat.add_assoc] using Store.get_of_readBlock hs (j := 1) (by omega) (0 : ℝ))
    (HoldsVector.get_re hV i) (HoldsVector.get_im hV i)
    (HoldsVector.get_re hV j) (HoldsVector.get_im hV j) ht
    (by dsimp; omega) (by dsimp; omega)
  refine (hrot.in_frame rfl rfl (by simp [Mem.Live]; omega)).mono (by fp_sub) ?_
  intro μ hfr ⟨hp, hout⟩
  have hx := (Mem.readBlocks_cons_iff.mp hout).1
  have hy := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hout).2).1
  refine ⟨hp, ?_⟩
  rw [reverseRotationStep, stepCoefs_givens D hk]
  exact vector_givens_readback hV htv hij hfr hx hy


/-- The actual reverse loop applies every stored factorization rotation, from the last
adjacent pair to the first, and returns the mathematical reverse-rotation state. -/
theorem reverseVectorRotations_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v cf t : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (hV : HoldsVector v w m.store) (hCf : HoldsCoefficients cf D (n - 1) m.store)
    (hvc : v.1 ≠ cf.1) (htv : t.1 ≠ v.1) (htc : t.1 ≠ cf.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ reverseVectorRotations.body (Env.frame [n] [v, cf, t, v])
      (Store.inBlock v.1 v.2 (2 * n) ⊔ Store.inBlock t.1 t.2 10)
      (fun μ => μ.pos = m.pos ∧
        HoldsVector v (reverseRotations D (n - 1) w (n - 1)) μ.store) m := by
  let F := Store.inBlock v.1 v.2 (2 * n) ⊔ Store.inBlock t.1 t.2 10
  refine writes_loop (n := .var 0 - .const 1) (N := n - 1) rfl
    (fun _ => F) (fun _ _ => le_rfl)
    (fun r μ => μ.pos = m.pos ∧ HoldsVector v (reverseRotations D (n - 1) w r) μ.store)
    ⟨rfl, hV⟩ ?_
  intro r hr μ hfr ⟨hp, hV'⟩
  have hCf' := hfr.keep (readsOnly_holdsCoefficients cf D (n - 1))
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hvc, Fp.disj_inBlock_of_ne htc⟩) hCf
  have hk : n - 2 - r + 1 < n := by omega
  have hround := vectorRotation_writes (τ := τ) hS hE hV' hCf' hk htv htc
    (by rw [hfr.len_eq]; exact ht)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV' ⟨n - 2 - r, by omega⟩)
  have hcoef := (hCf' (n - 2 - r) (by omega)).1
  have hcl := Store.lt_length_of_get
    (Store.get_of_readBlock hcoef (j := 0) (by omega) (0 : ℝ))
  have htl := Store.lt_length_of_lt_len (show t.2 < μ.store.len t.1 by
    rw [hfr.len_eq]; omega)
  refine (hround.in_frame rfl rfl (by simp [Mem.Live]; omega)).mono le_rfl ?_
  intro μ' _ ⟨hp', hV''⟩
  refine ⟨hp'.trans hp, ?_⟩
  simpa only [reverseRotations, Nat.sub_sub, Nat.reduceAdd] using hV''


end NLAlib.ShiftedQR
