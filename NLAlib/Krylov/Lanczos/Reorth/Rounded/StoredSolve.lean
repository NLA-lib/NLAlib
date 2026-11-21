/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.Solve
public import NLAlib.Krylov.Lanczos.Reorth.Rounded.Solve
public import NLAlib.Ops.Profiles.ContextLinearRoundedGuarded
public import NLAlib.Ops.RoutineData
public import NLAlib.Krylov.Lanczos.Reorth.StoredRoutine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Reorthogonalized Lanczos on a stored dense matrix: the rounded specification

The routine `NLAlib.Krylov.Lanczos.Stored.Reorth.solveRoutine` meets a second specification, in
rounded arithmetic: the packed basis and coefficients are a rounded two-pass output for the
matrix decoded from the stored words. The accuracy of the product with the stored matrix is a
hypothesis on the scalar machine, for every stored word list.

## Main definitions

* `NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded.solveSpec`: the rounded specification.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded.solveRoutine_meets`: the routine meets the rounded
  specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ} {u em E : ℝ}
  {e : Blas1Err} {ok : ℕ → Prop}

/-- For a matrix of order `n` decoded from the stored words, the rounded specification of the
matrix-free two-pass routine at that matrix, with the stated allowances. -/
noncomputable def solveSpec (n : ℕ) (em u E : ℝ) (e : Blas1Err) : Routine.Spec ℝ :=
  .onData 1 (fun d _ => d.headD 0 = n)
    (fun _ raws =>
      Lanczos.Reorth.Rounded.solveSpec id (StoredOperator.denseMatrix n n (raws.headD [])) em u E e)

/-- Reorthogonalized Lanczos on a stored dense matrix meets its rounded specification under the
standard model of scalar arithmetic, rounded vector contracts and a normwise bound on the product
with every stored matrix: it is the matrix-free rounded routine on stored data
(`NLAlib.Ops.Routine.Meets.withData`). -/
theorem solveRoutine_meets (hS : IsScalar M I) (hM : StdModel u id M) (hB : IsBlas1 id e ok I)
    {n : ℕ} (hok : ok n) (hCmp : IsCmp id I) (hprec : Lanczos.Rounded.Precision em u E e n)
    (hem : 0 ≤ em)
    (hError : ∀ raw xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          em * specNorm (StoredOperator.denseMatrix n n raw) *
            ‖WithLp.toLp 2 (decv id n xs)‖) :
    solveRoutine.Meets I (solveSpec n em u E e) :=
  Routine.Meets.withData _ _
    (fun _ raws => ContextLinearRounded.relation M e
      (StoredOperator.denseMatrix n n (raws.headD []))
      (em * specNorm (StoredOperator.denseMatrix n n (raws.headD []))))
    (fun _ => ContextLinearRounded.admissible ok n)
    (fun _ raws => ContextLinearRounded.fallback I
      (StoredOperator.denseMatrix n n (raws.headD [])))
    rfl rfl
    (fun d ctx m raws hc hr hP => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
        rw [← hP]
        exact hraw
      exact ContextLinearRounded.satisfies_guarded hS hB [a] ⟨0, by simp⟩ m.store raw
        (mul_nonneg hem (specNorm_nonneg _)) (hError raw)
        (fun z hz => List.mem_map_of_mem hz) hraw')
    (fun d ctx m raws hc hr hP => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
        rw [← hP]
        exact hraw
      obtain ⟨hs, hb', hA, hc⟩ := ContextLinearRounded.guarded_laws hS hB hCmp [a]
        ⟨0, by simp⟩ m.store raw (mul_nonneg hem (specNorm_nonneg _)) (hError raw)
        (fun z hz => List.mem_map_of_mem hz) hraw'
      exact Lanczos.Reorth.Rounded.solveRoutine_meets hs hM hb' hok hA hc hprec)

end NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded
