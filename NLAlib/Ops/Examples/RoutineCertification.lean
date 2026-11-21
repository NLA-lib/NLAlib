/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Routine
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Example: a certificate that can be read

The composite routine `NLAlib.Ops.Examples.Routines.sum2` is certified over the scalar-only
model with unit weights, in rounded arithmetic. The last theorem states what the certificate
means with no reference to the logic that produced it: for every pair of real vectors, every
interpretation of scalar arithmetic satisfying the standard model, and every tape, the counted
run of the fixed tree succeeds, executes at most `24 n + 63` instructions, and leaves in its
output cell a value within the stated error of the sum of all entries.

To check the claim one reads that statement, the definition of the problem and the model. The
instruction count is computed by the kernel from the tree.

## Main results

* `NLAlib.Ops.Examples.Routines.sum2Algorithm`: the certificate.
* `NLAlib.Ops.Examples.Routines.sum2_checked`: what it states, in terms of the evaluator.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Routines

/-- Two real vectors of length `d 0` and two uninitialized cells. -/
def sum2Problem : Problem ℝ 1 4 where
  formats _ := .cell
  valid _ := True
  Data d := (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  admissible _ x buffers :=
    buffers = ![(List.ofFn x.1).map some, (List.ofFn x.2).map some, [none], [none]]
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨(fun _ => 0, fun _ => 0), _, rfl⟩

/-- Admissibility states exactly which raw buffers have been supplied. -/
theorem initial_sum2Problem (d : Fin 1 → ℕ) (x : sum2Problem.Input d) :
    sum2Problem.initial d x =
      ⟨[(List.ofFn x.val.1.1).map some, (List.ofFn x.val.1.2).map some, [none], [none]], 0⟩ := by
  obtain ⟨⟨x, buffers⟩, h⟩ := x
  change buffers = ![(List.ofFn x.1).map some, (List.ofFn x.2).map some, [none], [none]] at h
  subst buffers
  rfl

/-- A supplied vector is read back from its buffer. -/
theorem readBlock_ofFn_map_some {n : ℕ} (v : Fin n → ℝ) (s : Store ℝ) (b : ℕ)
    (hb : s[b]? = some ((List.ofFn v).map some)) :
    s.readBlock b 0 n = some (List.ofFn v) := by
  rw [Store.readBlock_eq_some_iff]
  refine ⟨List.length_ofFn, fun j hj => ?_⟩
  simp [Store.get, hb, hj]

/-- The blocks read: the two supplied vectors. -/
def sum2Input (d : Fin 1 → ℕ) (x : sum2Problem.Input d) : List (List ℝ) :=
  [List.ofFn x.val.1.1, List.ofFn x.val.1.2]

/-- The scalar-only model with unit weights, for a scalar machine `M`. -/
noncomputable abbrev sum2Model (M : Machine ℝ) : AccessModel ScalarOp CmpTst sum2Problem :=
  RoundedScalarBlas.model sum2Problem M

/-- The fixed program: the composite routine on the four supplied buffers. -/
def sum2Program : Program ScalarOp CmpTst 1 4 := (sum2 (Tst := CmpTst)).close 1 4

/-- The number of instructions of the program at length `d 0`, at most. -/
def sum2Work (d : Fin 1 → ℕ) : ℕ := 24 * d 0 + 63

/-- The instruction polynomial of the program, evaluated by the kernel. -/
theorem countPoly_sum2Program : sum2Program.countPoly = [(24, [0]), (63, [])] := by
  rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_sum2Program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) sum2Program.countPoly = sum2Work d := by
  rw [countPoly_sum2Program]
  simp only [CountPoly.eval, CountPoly.monoEval, sum2Work, List.ofFn_succ, List.ofFn_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
    List.getD_cons_zero]
  ring

/-- **The certificate of the composite routine**, over the scalar-only model with unit weights
and the standard model of arithmetic at unit roundoff `u`. -/
noncomputable def sum2Algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u) :
    Algorithm (sum2Model M)
      ((sum2 (Tst := CmpTst)).specification (fun _ _ => sum2Spec id u) (sum2Model M).resources
        sum2Input
        (fun d => 2 * d 0 + 2) sum2Work) :=
  Routine.certify sum2 (fun _ _ => sum2Spec id u) sum2Input (fun d => 2 * d 0 + 2) sum2Work
    (fun _ _ _ _ hI => sum2_meets (RoundedScalarBlas.model_laws hI).1 hM hu)
    (fun d _ x => by
      rw [initial_sum2Problem]
      refine ⟨?_, fun _ => trivial, ?_⟩
      · exact Mem.readBlocks_of_cons (readBlock_ofFn_map_some _ _ 0 rfl)
          (Mem.readBlocks_of_cons (readBlock_ofFn_map_some _ _ 1 rfl) rfl)
      · change Mem.Room _ [(2, 0), (3, 0)] [1, 1]
        simp [Mem.Room, Store.len])
    (fun d _ x => by
      rw [Problem.initialBytes]
      obtain ⟨⟨x, buffers⟩, h⟩ := x
      change buffers = ![(List.ofFn x.1).map some, (List.ofFn x.2).map some, [none], [none]] at h
      subst buffers
      simp only [sum2Problem, List.ofFn_succ, List.ofFn_zero, StorageFormat.bytes_cell, one_mul,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, List.length_map,
        List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      have h1 : (List.ofFn x.1).length = d 0 := List.length_ofFn (n := d 0) (f := x.1)
      have h2 : (List.ofFn x.2).length = d 0 := List.length_ofFn (n := d 0) (f := x.2)
      omega)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (eval_countPoly_sum2Program d).le)

/-- The sum of a supplied vector over its positions. -/
theorem sum_range_vec_ofFn {n : ℕ} (f : Fin n → ℝ) :
    ∑ k ∈ Finset.range n, vec (List.ofFn f) k = ∑ i, f i := by
  rw [Finset.sum_range fun k => vec (List.ofFn f) k]
  exact Finset.sum_congr rfl fun i _ => by simp [vec]

/-- The sum of the absolute values of a supplied vector over its positions. -/
theorem sum_range_abs_vec_ofFn {n : ℕ} (f : Fin n → ℝ) :
    ∑ k ∈ Finset.range n, |vec (List.ofFn f) k| = ∑ i, |f i| := by
  rw [Finset.sum_range fun k => |vec (List.ofFn f) k|]
  exact Finset.sum_congr rfl fun i _ => by simp [vec]

/-- What the certificate states, with no reference to routines or contracts. Let `M` be a
scalar machine satisfying the standard model of arithmetic at unit roundoff $u \ge 0$. For every
length `n = d 0`, every pair of real vectors $x, y$ supplied in the first two buffers, every
interpretation `I` of the scalar operations of the model, and every tape, the counted run of the
fixed program succeeds, its work is at most $24 n + 63$ instructions, and the third buffer holds
a value $v$ with
$$\lvert v - (\textstyle\sum_i x_i + \sum_i y_i) \rvert \le
  \bigl((1 + u)(1 + u)^{n - 1} - 1\bigr) \bigl(\textstyle\sum_i \lvert x_i \rvert +
  \sum_i \lvert y_i \rvert\bigr).$$ -/
theorem sum2_checked (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (d : Fin 1 → ℕ) (x : sum2Problem.Input d) (I : Interp ScalarOp CmpTst ℝ)
    (hI : (sum2Model M).contracts d x I) (τ : Tape ℝ) :
    ∃ st, exec sum2Program I (sum2Model M).resources sum2Problem.formats τ d
        (sum2Problem.initial d x) = some st ∧
      (sum2Model M).resources.work st.cost ≤ 24 * d 0 + 63 ∧
      ∃ v, st.mem.store.get 2 0 = some v ∧
        |v - (∑ i, x.val.1.1 i + ∑ i, x.val.1.2 i)| ≤
          ((1 + u) * (1 + u) ^ (d 0 - 1) - 1) *
            (∑ i, |x.val.1.1 i| + ∑ i, |x.val.1.2 i|) := by
  obtain ⟨st, hr, -, -, hw, -, -, -, ys, hys, hpost⟩ :=
    (sum2Algorithm M u hM hu).correct d trivial x I hI τ
  refine ⟨st, hr, hw, ?_⟩
  read_outputs hys as (zs)
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  refine ⟨v, hv, ?_⟩
  have h : |v - (∑ k ∈ Finset.range (d 0), vec (List.ofFn x.val.1.1) k +
      ∑ k ∈ Finset.range (d 0), vec (List.ofFn x.val.1.2) k)| ≤
      ((1 + u) * (1 + u) ^ (d 0 - 1) - 1) *
        (∑ k ∈ Finset.range (d 0), |vec (List.ofFn x.val.1.1) k| +
          ∑ k ∈ Finset.range (d 0), |vec (List.ofFn x.val.1.2) k|) := hpost
  rw [sum_range_vec_ofFn, sum_range_vec_ofFn, sum_range_abs_vec_ofFn,
    sum_range_abs_vec_ofFn] at h
  exact h

end NLAlib.Ops.Examples.Routines
