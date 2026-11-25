/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.ScaledPLUInitialize
public import NLAlib.Matrix.Computation.PLURoutine
public import NLAlib.Matrix.Computation.GuardedElimination
public import NLAlib.Matrix.Computation.LU

/-!
# Stored LU with fixed original row scales

Original row norms are computed once. Every selected row exchanges both its residual and its
fixed scale, and the actual stored pivot controls the exchange of lower-factor rows. The
zero-safe materialization and Schur update admit all singular matrices.

## Main definitions

* `NLAlib.Computation.scaledPluFactor`: the full fixed-scale pivoted LU driver.

## Main results

* `NLAlib.Computation.exec_scaledPluFactor`: actual exact all-input execution and factors.
* `NLAlib.Computation.isPLURoutine_scaledPluFactor`: its typed zero-error routine certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

/-- Factor a stored square matrix by fixed-scale partial pivoting, writing separate lower and upper
factors and an absolute pivot-index log. An active-column scan exchanges residual rows; the
recorded index is consumed by a bounded binder to exchange earlier multiplier rows before
zero-safe column materialization and Schur elimination. The residual and original row scales
share one scoped buffer.
The permutation convention is that the row-permuted input equals the factor product.
[Higham2002, §9.3]. -/
def scaledPluFactor {P ι VB VI : Type} (tag : P) (n : IExp VI) (A L U H : VB)
    (ao lo uo ho : IExp VI) : Builder P ι VB VI Unit := scope do
  let S ← alloc tag (n * n + n)
  rowScales tag n n A ao S (n * n)
  copyv tag A ao S 0 (n * n)
  forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
  forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
  forRange n fun k => do
    scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
    bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
      swapRows tag n n L lo (.var k) (.var selected)
    luColumnTotal tag n (.var k) S L U 0 lo uo
    schurStepTotal tag n S 0 (.var k)

variable {P ι : Type} [DecidableEq P]

/-- The fixed-scale factorization releases its residual workspace before executing its
continuation, independently of its scalar interpretation. -/
theorem executionComposable_scaledPluFactor {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (n : IExp ℕ) (A L U H : ℕ)
    (ao lo uo ho : IExp ℕ) : ExecutionComposable I (scaledPluFactor tag n A L U H ao lo uo ho) :=
  executionComposable_single I (fun _ => rfl)

/-- Full fixed-scale pivoted LU succeeds on every stored real square matrix under exact semantics
and standard instruction charges. Its actual absolute pivot-index log decodes the row
permutation for which the canonical factors multiply to the permuted input, using fixed
original row scales. No unweighted multiplier bound is asserted. The only net writes are the
lower factor, upper factor
and pivot log, in that order. The three output buffers are distinct; separation from the
input preserves it. Empty inputs require no valid input or output handles. No nonsingularity
or nonzero-pivot premise is required. [Higham2002, §9.3]. -/
theorem exec_scaledPluFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hH : Writable st.store tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H) :
    ∃ (out : St P ℝ (OpCount P ι)) (p : Fin n.eval → Fin n.eval),
      exec I (scaledPluFactor tag n A L U H ao lo uo ho).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (H, ho.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) id)),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) id)),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some out.store ∧
      (∀ j, j ≤ p j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) id)
        (luLower (M.submatrix (luPivotPermutation p n.eval) id))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      Holds out.store tag L lo.eval (luLower (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      Holds out.store tag U uo.eval (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      (∀ j : Fin n.eval, out.store.read tag H (ho.eval + j) = some ((p j).val : ℝ)) ∧
      Holds out.store tag A ao.eval M := by
  let Q : Store P ℝ → Prop := fun store => ∃ p : Fin n.eval → Fin n.eval,
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
      (H, ho.eval, n.eval)]
      [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) id)),
        flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) id)),
        Array.ofFn (fun j => ((p j).val : ℝ))] = some store ∧
    (∀ j, j ≤ p j) ∧
    IsLU (M.submatrix (luPivotPermutation p n.eval) id)
      (luLower (M.submatrix (luPivotPermutation p n.eval) id))
      (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    Holds store tag L lo.eval (luLower (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    Holds store tag U uo.eval (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    (∀ j : Fin n.eval, store.read tag H (ho.eval + j) = some ((p j).val : ℝ))
  obtain ⟨out, hr, p, hw, hp, hf, hLf, hUf, hlog⟩ := exists_exec_alloc I tag (n * n + n)
    (fun S => ((do
      rowScales tag n n A ao S (n * n)
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
      intro σ hσ
      obtain ⟨final, hrun, hs⟩ := ScaledPLU.exec_body I hI hc tag st.store σ n A L U H ao lo uo ho
        M hM hL hU hH hLU hLH hUH (by simpa only [IExp.eval_add, IExp.eval_mul] using hσ)
      obtain ⟨p, hw, hp, hf, hLf, hUf, hl⟩ := ScaledPLU.State.writeBlocks_pop
        (hσ ▸ hs) hL hU hH hLU hLH hUH
      exact ⟨final, hrun, p, hw, hp, hf, hLf, hUf, hl⟩)
  refine ⟨out, p, ?_, hw, hp, hf, hLf, hUf, hlog, ?_⟩
  · change exec I (.seq (.alloc tag (n * n + n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    have hN : 0 < n.eval := Nat.zero_lt_of_lt i.isLt
    exact (Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN)
      · exact Or.inl (hAH hN))).trans (hM i j)

/-- The actual fixed-scale pivoted driver supplies a zero-error row-pivoted LU certificate for
every real square matrix, including singular inputs. Exact scalar semantics and standard
charges suffice; no nonzero-pivot premise is needed. The source and three output buffers are
separate, and arbitrary offsets are allowed. [Higham2002, §9.3]. -/
theorem isPLURoutine_scaledPluFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Pb : ℕ) (ao lo uo po : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAP : Ab ≠ Pb)
    (hLU : Lb ≠ Ub) (hLP : Lb ≠ Pb) (hUP : Ub ≠ Pb) :
    IsPLURoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Pb lo uo po (scaledPluFactor tag (.const N) Ab Lb Ub Pb ao lo uo po) where
  composable := executionComposable_scaledPluFactor I tag (.const N) Ab Lb Ub Pb ao lo uo po
  run st hA hw _ _ _ := by
    obtain ⟨out, p, hr, hs, hp, he, -, -, hlog, -⟩ := exec_scaledPluFactor I hI hc tag st
      (.const N) Ab Lb Ub Pb ao lo uo po A hA
      (hw _ List.mem_cons_self) (hw (Ub, uo.eval, N * N) (by simp))
      (hw (Pb, po.eval, N) (by simp)) hLU hLP hUP
      (fun _ => hAL) (fun _ => hAU) (fun _ => hAP)
    change Fin N → Fin N at p
    refine ⟨out, flatten (luLower (A.submatrix (luPivotPermutation p N) id)),
      flatten (luUpper (A.submatrix (luPivotPermutation p N) id)),
      Array.ofFn (fun j => ((p j).val : ℝ)), p, size_flatten _, size_flatten _,
      Array.size_ofFn, hr, hs, ?_, hp, ?_⟩
    · intro i
      exact ⟨((p i).val : ℝ), hlog i, rfl⟩
    · rw [Array.map_id', Array.map_id', unflatten_flatten, unflatten_flatten]
      exact he.isLUErr

end NLAlib.Computation
