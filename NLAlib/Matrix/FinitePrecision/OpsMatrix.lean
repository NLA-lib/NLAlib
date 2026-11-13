/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import NLAlib.Ops.Blas.MatrixCorrect

/-!
# Packed matrix transformations and their mathematical machine outputs

The scalar-visible interleaved matrix kernels compute the existing finite mathematical
machine's word-valued transformations. Packed input and output statements let algorithm proofs
compose these transformations with matrix multiplication without exposing entry layouts.

## Main results

* `NLAlib.Ops.PairMatrix.writes_conjTranspose_packed`: the actual packed conjugate transpose.
* `NLAlib.Ops.PairMatrix.writes_traceRe_packed`: the actual rounded finite trace.
-/

@[expose] public section

namespace NLAlib.Ops.PairMatrix

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
  {M : Machine K} {dec : K → ℝ} {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- Conjugate transpose writes exactly the mathematical machine's packed finite output.
Readable input and disjoint writable output blocks suffice, including distinct regions of one
buffer. No numerical accuracy or successful-execution premise is assumed. -/
theorem writes_conjTranspose_packed {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K}
    {k r : ℕ} (Q : Matrix (Fin k) (Fin r) (K × K)) {x y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (k * r)))
      (Store.inBlock y.1 y.2 (2 * (k * r))))
    (hQ : μ.store.readBlock x.1 x.2 (2 * (k * r)) = some ((EntryCodec.pair K).packFinMatrix Q))
    (hY : y.2 + 2 * (k * r) ≤ μ.store.len y.1) (hl : μ.Live [x, y]) :
    Writes .total I τ (conjTranspose (Op := Op) (Tst := Tst)).body
      (Env.frame [k, r] [x, y]) (Store.inBlock y.1 y.2 (2 * (k * r)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (k * r)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q))) μ := by
  let C := EntryCodec.pair K
  let B : ℕ → ℕ → K × K := fun i j => C.entry (C.packFinMatrix Q) (j * k + i)
  have hB : μ.store.HoldsEntries C ⟨x.1, x.2, k, r, k⟩ B :=
    Store.holdsEntries_of_readBlock rfl (by simpa only [Nat.mul_comm] using hQ)
  have hfinite : (Matrix.of fun (i : Fin k) (j : Fin r) => B i j) = Q :=
    C.matrix_packFinMatrix Q
  refine (writes_conjTranspose hI B hl hB hY (by
    simpa only [Nat.mul_comm] using hxy)).mono le_rfl ?_
  intro μ' _ ⟨houtput, hpos⟩
  have hread := houtput.readBlock_packFinMatrix rfl
  change μ'.store.readBlock y.1 y.2 (k * r * 2) =
    some (C.packFinMatrix ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat
      (Matrix.of fun (i : Fin k) (j : Fin r) => B i j))) at hread
  rw [hfinite] at hread
  exact ⟨hpos, by simpa only [Nat.mul_comm] using hread⟩

omit [Inhabited K] in
/-- The scalar trace recurrence is exactly a left fold over its visited diagonal words. -/
theorem traceReF_eq_foldl (n : ℕ) (v : ℕ → K) (N : ℕ) :
    traceReF M n v N = (List.range N).foldl
      (fun acc i => M.add acc (v (2 * (i * n + i)))) (M.lit 0) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [traceReF, ih, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

/-- The packed trace's word recurrence is the existing finite mathematical trace, with the
same left-to-right rounded additions and the same literal-zero initial accumulator. -/
theorem traceReF_packFinMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) :
    traceReF M n (vec ((EntryCodec.pair K).packFinMatrix A)) n =
      (M.toFloatMachine dec mm qr unif normal).traceRe A := by
  have hrange : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  rw [traceReF_eq_foldl, ← hrange, List.foldl_map]
  change (List.finRange n).foldl _ (M.lit 0) = (List.finRange n).foldl _ (M.lit 0)
  apply congrArg (fun f : K → Fin n → K => (List.finRange n).foldl f (M.lit 0))
  funext acc i
  apply congrArg (M.add acc)
  simpa [EntryCodec.pair, Nat.mul_comm] using
    (EntryCodec.pair K).vec_packFinMatrix A i i ⟨0, Nat.zero_lt_succ 1⟩

/-- The actual packed trace kernel stores the existing machine's rounded finite trace.
The accumulator need not be initialized, and disjoint regions of one buffer are supported. -/
theorem writes_traceRe_packed {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K}
    {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) {x y : ℕ × ℕ} {μ : Mem K}
    (hA : μ.store.readBlock x.1 x.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hy : y.2 < μ.store.len y.1)
    (hdisj : Fp.Disj (Store.inBlock y.1 y.2 1) (Store.inBlock x.1 x.2 (2 * (n * n)))) :
    Writes .total I τ (traceRe (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, y])
      (Store.inBlock y.1 y.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.get y.1 y.2 =
        some ((M.toFloatMachine dec mm qr unif normal).traceRe A)) μ := by
  refine (writes_traceRe hI (Store.holdsVec_of_readBlock hA) hy hdisj).mono le_rfl ?_
  intro μ' _ ⟨htrace, hpos⟩
  rw [traceReF_packFinMatrix (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal)] at htrace
  exact ⟨hpos, htrace⟩

end NLAlib.Ops.PairMatrix
