/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyFactorization
public import NLAlib.Matrix.Computation.SemidefiniteCholeskyColumn

/-!
# Stored positive semidefinite Cholesky factorization

The exact stored algorithm handles zero pivots without division. Positive semidefinite
inputs yield the canonical lower triangular factor with nonnegative diagonal, including
singular matrices. Source and destination may overlap because input is copied first.

## Main results

* `NLAlib.Computation.exec_semidefiniteCholesky`: success, full output frame and Gram identity.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder
open scoped Matrix

/-- Factor a positive semidefinite stored matrix. A zero pivot writes a zero factor
column and skips elimination; a positive pivot uses square-root normalization and the
existing rank-one Schur kernel. All residual storage is scoped. [GolubVanLoan2013, §4.2]. -/
def semidefiniteCholesky {P ι VB VI : Type} (p : P) (n : IExp VI) (A : VB) (ao : IExp VI)
    (L : VB) (lo : IExp VI) : Builder P ι VB VI Unit := scope do
  let R ← alloc p (n * n)
  copyv p A ao R 0 (n * n)
  forRange n fun k => do
    choleskyColumnTotal p n R L 0 lo (.var k)
    schurStepTotal p n R 0 (.var k)

/-- The scoped full Cholesky routine composes under any interpretation. -/
theorem executionComposable_semidefiniteCholesky {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) : ExecutionComposable I (semidefiniteCholesky p n A ao L lo) :=
  executionComposable_single I (fun _ => rfl)

open CholeskyFactorization

variable {P ι : Type} [DecidableEq P]

private theorem exec_semidefiniteIteration (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (base : Store P ℝ)
    (n : IExp ℕ) (R L : ℕ) (lo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosSemidef) (hRL : R ≠ L) (hL : Writable base p L lo.eval (n.eval * n.eval))
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hInv : FactorState base p R L lo.eval A k st.store) :
    ∃ out, exec I (do
      choleskyColumnTotal p n R L 0 lo (.var k)
      schurStepTotal p n R 0 (.var k)).run st = some out ∧
      FactorState base p R L lo.eval A (k + 1) out.store := by
  obtain ⟨⟨g, hF⟩, hR, hprefix⟩ := hInv
  have hcap : Writable st.store p L (lo.eval + n.eval * k) n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL (i + n.eval * k)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hF.1 ▸ hlen, by omega⟩
  obtain ⟨s₁, hr₁, hw₁⟩ := exec_choleskyColumnTotal_of_posSemidef I hI hc p st n R L
    0 lo (.var k) A hA hk hR hRL hcap
  have hR₁ : Holds s₁.store p R 0 (gaussState A k) := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRL)).trans (hR i j)
  obtain ⟨g', hF₁⟩ := frame_column A hk hF hw₁
  have hprefix₁ := read_column A hk hprefix hw₁
  obtain ⟨out, hr₂, hw₂, hR₂⟩ := exec_schurStepTotal I hI hc p s₁ n R 0 (.var k)
    (gaussState A k) hk hR₁
  refine ⟨out, ?_, ⟨g', hF₁.writeBlock_scratch (fun _ => hRL.symm) hw₂⟩, ?_, ?_⟩
  · rw [exec_run_bind I
      (b := choleskyColumnTotal p n R L 0 lo (.var k)) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · rw [gaussState_succ A hk]
    exact hR₂
  · intro i j hj
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRL.symm),
      hprefix₁ i j hj]

private theorem exists_exec_semidefiniteCholesky_of_push (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (initial : Store P ℝ)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosSemidef)
    (hinput : Holds initial p Ab ao.eval A)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv p Ab ao initial.size 0 (n * n)
      forRange n fun k => do
        choleskyColumnTotal p n initial.size L 0 lo (.var k)
        schurStepTotal p n initial.size 0 (.var k)).run st = some out ∧
      initial.writeBlock p L lo.eval (flatten (choleskyLower A)) = some out.store.pop := by
  have hLb : 0 < n.eval * n.eval → L < initial.size := by
    intro hn
    obtain ⟨len, hlen, _⟩ := hL 0 hn
    have := (Array.getElem?_eq_some_iff.mp hlen).1
    simpa only [Store.size_shape] using this
  have hAb : 0 < n.eval → Ab < initial.size := fun hn =>
    Store.lt_size_of_read_eq_some (hinput ⟨0, hn⟩ ⟨0, hn⟩)
  have hinput' : Holds st.store p Ab ao.eval A := fun i j => by
    rw [hst, Store.read_push_of_lt (hAb (Nat.zero_lt_of_lt i.isLt))]
    exact hinput i j
  have hR : Writable st.store p initial.size 0 (n.eval * n.eval) := by
    intro i hi
    exact ⟨n.eval * n.eval, by rw [hst]; exact
      Store.getElem?_shape_push_size initial p (n.eval * n.eval), by omega⟩
  have hL' : Writable st.store p L lo.eval (n.eval * n.eval) := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL i hi
    refine ⟨len, ?_, hlt⟩
    rw [hst, Store.getElem?_shape_push_of_lt _ (hLb (by omega))]
    exact hlen
  obtain ⟨s₁, hr₁, hw₁, hR₁⟩ := exec_copy_residual I hc p st n Ab initial.size ao A
    hinput' hR (fun hn => Nat.ne_of_lt (hAb hn))
  have hF : Store.BlockFrame st.store p initial.size L lo.eval (n.eval * n.eval) st.store
      (fun i => st.store.read p L (lo.eval + i)) :=
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hInv : FactorState st.store p initial.size L lo.eval A 0 s₁.store :=
    ⟨⟨_, hF.writeBlock_scratch (fun hn => Nat.ne_of_lt (hLb hn)) hw₁⟩,
      hR₁, fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain ⟨out, hr₂, ⟨g, hFout⟩, _, hprefix⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => FactorState st.store p initial.size L lo.eval A k σ.store) hInv
    (fun k hk σ hσ => exec_semidefiniteIteration I hI hc p st.store n initial.size L lo A hA
      (Nat.ne_of_gt (hLb (Nat.mul_pos (by omega) (by omega)))) hL' k hk σ hσ)
  have hfinal : Holds out.store p L lo.eval (choleskyLower A) := fun i j =>
    hprefix i j j.isLt
  refine ⟨out, ?_, writeBlock_flatten_of_pop_frame (hst ▸ hFout) hfinal hL⟩
  rw [exec_run_bind I (b := copyv p Ab ao initial.size 0 (n * n)) (fun _ => rfl),
    hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) s₁ = some out
  rw [exec_seq_skip]
  exact hr₂

/-- Under exact real arithmetic, readable positive semidefinite input and a writable factor block
suffice for the full Cholesky routine to succeed. Its final store is exactly the original store
with the full lower triangular factor written at the output offset. The input and output may
coincide or overlap: the routine first copies the input into scoped scratch. Empty matrices
require no valid matrix or factor buffer handle. The stored factor is lower triangular with
nonnegative diagonal, and its Gram product is the original matrix. [GolubVanLoan2013, §4.2]. -/
theorem exec_semidefiniteCholesky (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosSemidef)
    (hinput : Holds st.store p Ab ao.eval A)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (semidefiniteCholesky p n Ab ao L lo).run st = some out ∧
      st.store.writeBlock p L lo.eval (flatten (choleskyLower A)) = some out.store ∧
      Holds out.store p L lo.eval (choleskyLower A) ∧
      (choleskyLower A).IsLowerTriangular ∧
      (∀ i, 0 ≤ choleskyLower A i i) ∧ A = choleskyLower A * (choleskyLower A)ᴴ := by
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p (n * n)
    (fun R => (do
      copyv p Ab ao R 0 (n * n)
      forRange n fun k => do
        choleskyColumnTotal p n R L 0 lo (.var k)
        schurStepTotal p n R 0 (.var k)).run) st
    (fun s => st.store.writeBlock p L lo.eval (flatten (choleskyLower A)) = some s)
    (fun σ hσ => exists_exec_semidefiniteCholesky_of_push I hI hc p st.store σ n
      Ab L ao lo A hA hinput hL hσ)
  refine ⟨out, ?_, hw, ?_, isLowerTriangular_choleskyLower A,
    hA.isHermitian.choleskyLower_apply_self_nonneg,
    hA.eq_choleskyLower_mul_conjTranspose⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    simpa only [Nat.add_assoc] using
      (Store.read_of_writeBlock_eq_some_of_lt hw
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten (choleskyLower A) i j)

end NLAlib.Computation
