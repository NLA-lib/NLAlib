/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Routine
public import NLAlib.Ops.RoutineProblem
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
* `NLAlib.Ops.Examples.Routines.sum2_checked`: what it states, in terms of the execution rules.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Routines

/-- The admitted inputs of `sum2`: every pair of real vectors of length `d 0`, each in its
buffer; the two cells are blank. -/
def sum2Domain : (sum2 (Op := ScalarOp) (Tst := CmpTst)).Domain ℝ 1 4 where
  valid _ := True
  In d := (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) Prod.fst, .stored (Codec.vector (d 0)) Prod.snd,
    .blank 1, .blank 1]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.vector (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(fun _ => 0, fun _ => 0), trivial⟩

/-- Two real vectors of length `d 0` and two uninitialized cells: the problem of `sum2`. -/
abbrev sum2Problem : Problem ℝ 1 4 := sum2Domain.problem

/-- The blocks read: the two supplied vectors. -/
def sum2Input (d : Fin 1 → ℕ) (x : sum2Problem.Input d) : List (List ℝ) :=
  sum2Domain.blocks d x.val.1

/-- The blocks read are the two vectors, as lists. -/
theorem sum2Input_eq (d : Fin 1 → ℕ) (x : sum2Problem.Input d) :
    sum2Input d x = [List.ofFn x.val.1.1, List.ofFn x.val.1.2] := rfl

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
  poly_eval [sum2Work]

/-- **The certificate of the composite routine**, over the scalar-only model with unit weights
and the standard model of arithmetic at unit roundoff `u`: the counted certificate of the
routine on its problem (`NLAlib.Ops.Routine.Domain.certify`). -/
noncomputable def sum2Algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u) :
    Algorithm (sum2Model M)
      ((sum2 (Tst := CmpTst)).specification (P := sum2Problem) (fun _ _ => sum2Spec id u)
        (sum2Model M).resources sum2Input sum2Domain.bytes sum2Work) :=
  sum2Domain.certify (fun _ _ => sum2Spec id u) sum2Work
    (fun _ _ _ _ hI => sum2_meets (RoundedScalarBlas.model_laws hI).1 hM hu)
    (fun _ _ _ _ _ => trivial)
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
length `n = d 0`, every pair of real vectors $x, y$, every interpretation `I` of the scalar
operations of the model, and every tape, the counted run of the fixed program from the two
vectors and two blank cells succeeds, its work is at most $24 n + 63$ instructions, its resident
memory is at most the payload of the four buffers plus the static scratch of the tree, and the
third buffer holds a value $v$ with
$$\lvert v - (\textstyle\sum_i x_i + \sum_i y_i) \rvert \le
  \bigl((1 + u)(1 + u)^{n - 1} - 1\bigr) \bigl(\textstyle\sum_i \lvert x_i \rvert +
  \sum_i \lvert y_i \rvert\bigr).$$
Every pair of vectors is admitted (`NLAlib.Ops.Inputs.covers`). -/
theorem sum2_checked (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (d : Fin 1 → ℕ) (x y : Fin (d 0) → ℝ) (I : Interp ScalarOp CmpTst ℝ)
    (hI : (sum2Model M).contracts d (sum2Domain.input d (x, y) trivial) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution sum2Program I (sum2Model M).resources sum2Domain.formats τ d
        (sum2Domain.memory d (x, y)) st ∧
      (sum2Model M).resources.work st.cost ≤ 24 * d 0 + 63 ∧
      sum2Domain.bytes d + st.peak ≤
        sum2Domain.bytes d + staticPeak (sum2Model M).resources sum2Program d ∧
      ∃ v, st.mem.Holds Codec.scalar 2 v ∧
        |v - (∑ i, x i + ∑ i, y i)| ≤
          ((1 + u) * (1 + u) ^ (d 0 - 1) - 1) * (∑ i, |x i| + ∑ i, |y i|) := by
  obtain ⟨st, hr, hw, hm, ys, hys, hpost⟩ :=
    sum2Domain.checked_post (Sp := fun _ _ => sum2Spec id u) (work := sum2Work)
      (sum2Algorithm M u hM hu) d trivial (x, y) trivial I hI τ
  refine ⟨st, hr, hw, hm, ?_⟩
  read_outputs hys as (zs)
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  refine ⟨v, hzs, ?_⟩
  have h : |v - (∑ k ∈ Finset.range (d 0), vec (List.ofFn x) k +
      ∑ k ∈ Finset.range (d 0), vec (List.ofFn y) k)| ≤
      ((1 + u) * (1 + u) ^ (d 0 - 1) - 1) *
        (∑ k ∈ Finset.range (d 0), |vec (List.ofFn x) k| +
          ∑ k ∈ Finset.range (d 0), |vec (List.ofFn y) k|) := hpost
  rw [sum_range_vec_ofFn, sum_range_vec_ofFn, sum_range_abs_vec_ofFn,
    sum_range_abs_vec_ofFn] at h
  exact h

end NLAlib.Ops.Examples.Routines
