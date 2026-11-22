/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Example: a loop over the cells of a block, from the tree to the readable statement

`NLAlib.Ops.Examples.VectorSum.vadd` is `[n] (x : read n, y : read n) → (z : write n)`: a loop
of `z_i := x_i + y_i` over scalar additions. It is the smallest routine whose tree is a loop
over calls on indexed cells, and the worked example of the contributor guide for the loop
invariant, the read of one cell of a block, and a block-valued output in the readable statement
(`docs/contributing/routines.md`).

## Main definitions

* `NLAlib.Ops.Examples.VectorSum.vadd`, `NLAlib.Ops.Examples.VectorSum.vaddSpec`: the routine
  and its specification.
* `NLAlib.Ops.Examples.VectorSum.vaddDomain`: its admitted inputs.
* `NLAlib.Ops.Examples.VectorSum.vaddAlgorithm`: the certificate.

## Main results

* `NLAlib.Ops.Examples.VectorSum.vadd_meets`: the routine meets its specification.
* `NLAlib.Ops.Examples.VectorSum.vadd_checked`: what the certificate states, in terms of the
  evaluator.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.VectorSum

variable {K Op Tst : Type} [Has ScalarOp Op]

/-! ### Mathematics -/

/-- The words written by the loop: the machine sums of the entries. -/
def vaddF (M : Machine K) (x y : ℕ → K) (n : ℕ) : List K :=
  (List.range n).map fun i => M.add (x i) (y i)

omit [Has ScalarOp Op] in
/-- One more round appends the sum of the next entries. -/
theorem vaddF_succ (M : Machine K) (x y : ℕ → K) (n : ℕ) :
    vaddF M x y (n + 1) = vaddF M x y n ++ [M.add (x n) (y n)] := by
  simp [vaddF, List.range_succ]

/-! ### The routine, its specification and its judgment -/

/-- The entrywise sum: `z_i := x_i + y_i`. -/
def vadd : Routine Op Tst := routine% [n] (x : n, y : n) → (z : n) {
  for i < n {
    call (Has.inj ScalarOp.add) [] (x[i], y[i]) → (z[i])
  }
}

variable [Inhabited K]

/-- The block written holds the machine sums of the entries of the two blocks read. -/
def vaddSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (xs, ys) → (zs) ensures zs = vaddF M (vec xs) (vec ys) n

/-- The entrywise sum meets its specification, for any machine. -/
theorem vadd_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (vadd (Op := Op) (Tst := Tst)).Meets I (vaddSpec M) := by
  routine_intro [n] (x, y, z) reads (xs, ys)
  loop_inv (fun _ => Fp.blocks [z] [n])
    (fun i m' => m'.pos = m.pos ∧
      m'.store.readBlock z.1 z.2 i = some (vaddF M (vec xs) (vec ys) i))
    with i hi m₁ hfr hP
  case round =>
    obtain ⟨hpos₁, hz₁⟩ := hP
    have hxs₁ : m₁.store.readBlock x.1 x.2 n = some xs := by keep
    have hys₁ : m₁.store.readBlock y.1 y.2 n = some ys := by keep
    have hxi : m₁.store.get x.1 (x.2 + i) = some (vec xs i) :=
      Store.get_of_readBlock hxs₁ hi default
    have hyi : m₁.store.get y.1 (y.2 + i) = some (vec ys i) :=
      Store.get_of_readBlock hys₁ hi default
    step (hI .add) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    refine ⟨hpos₂.trans hpos₁, ?_⟩
    rw [vaddF_succ]
    exact Store.readBlock_succ_of (by keep) hv
  case exit =>
    rintro m₁ - ⟨hpos₁, hz₁⟩
    exact ⟨hpos₁, [vaddF M (vec xs) (vec ys) n], Mem.readBlocks_of_cons hz₁ rfl, rfl⟩

/-! ### The problem, the certificate and the readable statement -/

/-- The admitted inputs of `vadd`: every pair of real vectors of length `d 0`, each in its
buffer; the third buffer is `d 0` blank cells. -/
def vaddDomain : (vadd (Op := ScalarOp) (Tst := CmpTst)).Domain ℝ 1 3 where
  valid _ := True
  In d := (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) Prod.fst, .stored (Codec.vector (d 0)) Prod.snd,
    .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.vector (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(fun _ => 0, fun _ => 0), trivial⟩

/-- Two real vectors of length `d 0` and `d 0` uninitialized cells: the problem of `vadd`. -/
abbrev vaddProblem : Problem ℝ 1 3 := vaddDomain.problem

/-- The blocks read: the two supplied vectors. -/
def vaddInput (d : Fin 1 → ℕ) (x : vaddProblem.Input d) : List (List ℝ) :=
  vaddDomain.blocks d x.val.1

/-- The scalar-only model with unit weights, for a scalar machine `M`. -/
noncomputable abbrev vaddModel (M : Machine ℝ) : AccessModel ScalarOp CmpTst vaddProblem :=
  RoundedScalarBlas.model vaddProblem M

/-- The fixed program: the routine on the three supplied buffers. -/
def vaddProgram : Program ScalarOp CmpTst 1 3 := (vadd (Tst := CmpTst)).close 1 3

/-- The number of instructions of the program at length `d 0`, at most. -/
def vaddWork (d : Fin 1 → ℕ) : ℕ := 14 * d 0 + 2

/-- The instruction polynomial of the program, evaluated by the kernel. -/
theorem countPoly_vaddProgram : vaddProgram.countPoly = [(14, [0]), (2, [])] := by
  rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_vaddProgram (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) vaddProgram.countPoly = vaddWork d := by
  rw [countPoly_vaddProgram]
  poly_eval [vaddWork]

/-- **The certificate of the entrywise sum**, over the scalar-only model with unit weights, for
any scalar machine `M`: the counted certificate of the routine on its problem
(`NLAlib.Ops.Routine.Domain.certify`). -/
noncomputable def vaddAlgorithm (M : Machine ℝ) :
    Algorithm (vaddModel M)
      ((vadd (Tst := CmpTst)).specification (P := vaddProblem) (fun _ _ => vaddSpec M)
        (vaddModel M).resources vaddInput vaddDomain.bytes vaddWork) :=
  vaddDomain.certify (fun _ _ => vaddSpec M) vaddWork
    (fun _ _ _ _ hI => vadd_meets (RoundedScalarBlas.model_laws hI).1)
    (fun _ _ _ _ _ => trivial)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (eval_countPoly_vaddProgram d).le)

/-- The words written, at two supplied vectors, are the encoding of their entrywise machine
sum. -/
theorem vaddF_ofFn (M : Machine ℝ) {n : ℕ} (x y : Fin n → ℝ) :
    vaddF M (vec (List.ofFn x)) (vec (List.ofFn y)) n = List.ofFn fun i => M.add (x i) (y i) := by
  refine List.ext_getElem (by simp [vaddF]) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa [vaddF] using h₁
  simp [vaddF, vec, hi]

/-- What the certificate states, with no reference to routines or contracts. Let `M` be a
scalar machine. For every length `n = d 0`, every pair of real vectors $x, y$, every
interpretation `I` of the scalar operations of the model, and every tape, the counted run of the
fixed program from the two vectors and `n` blank cells succeeds, its work is at most $14 n + 2$
instructions, its resident memory is at most the payload of the three buffers plus the static
scratch of the tree, and the third buffer holds the vector of the machine sums
`M.add (x i) (y i)`. Every pair of vectors is admitted (`NLAlib.Ops.Inputs.covers`). -/
theorem vadd_checked (M : Machine ℝ) (d : Fin 1 → ℕ) (x y : Fin (d 0) → ℝ)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (vaddModel M).contracts d (vaddDomain.input d (x, y) trivial) I) (τ : Tape ℝ) :
    ∃ st, exec vaddProgram I (vaddModel M).resources vaddDomain.formats τ d
        (vaddDomain.memory d (x, y)) = some st ∧
      (vaddModel M).resources.work st.cost ≤ 14 * d 0 + 2 ∧
      vaddDomain.bytes d + st.peak ≤
        vaddDomain.bytes d + staticPeak (vaddModel M).resources vaddProgram d ∧
      st.mem.Holds (Codec.vector (d 0)) 2 fun i => M.add (x i) (y i) := by
  obtain ⟨st, hr, hw, hm, ys, hys, hpost⟩ :=
    vaddDomain.checked_post (Sp := fun _ _ => vaddSpec M) (work := vaddWork)
      (vaddAlgorithm M) d trivial (x, y) trivial I hI τ
  refine ⟨st, hr, hw, hm, ?_⟩
  read_outputs hys as (zs)
  obtain rfl : zs = vaddF M (vec (List.ofFn x)) (vec (List.ofFn y)) (d 0) := hpost
  rw [vaddF_ofFn] at hzs
  exact hzs

end NLAlib.Ops.Examples.VectorSum
