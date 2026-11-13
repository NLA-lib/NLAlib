/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import NLAlib.Ops.Blas.HermitianCorrect

/-!
# Stored Hermitian operations and their mathematical machine outputs

The scalar-visible Ops kernels compute the existing mathematical machine's Hermitian shift,
scaling and averaging functions. These are exact equalities of stored words, independent of
numerical accuracy. Matrix error theorems can therefore be reused on the actual program output.

## Main results

* `NLAlib.Ops.Hermitian.completeUpper_eq_hermFrom`: finite and logical completions agree.
* `NLAlib.Ops.Hermitian.completeUpper_shift_eq_hermShift`: the actual shifted word formula.
* `NLAlib.Ops.Hermitian.completeUpper_scale_eq_hermScale`: the actual scaled word formula.
* `NLAlib.Ops.Hermitian.completeUpper_average_eq_hermAvg`: the actual averaged word formula.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Su Sg : Type} (M : Machine K) (dec : K → ℝ)
  (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  (unif : K → Su → K) (normal : Sg → K × K)

/-- Logical upper and diagonal words yield exactly the existing finite mathematical Hermitian
completion. This identifies stored words without assuming exact scalar arithmetic. -/
theorem completeUpper_eq_hermFrom (n : ℕ) (U : ℕ → ℕ → K × K) (D : ℕ → K) :
    (Matrix.of fun (i j : Fin n) => completeUpper M
      (fun i j => if i = j then (D i, M.lit 0) else U i j) i j) =
      (M.toFloatMachine dec mm qr unif normal).hermFrom (fun i j => U i j) (fun i => D i) := by
  funext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hle : (i : ℕ) ≤ j := hij.le
    have hne : (i : ℕ) ≠ j := ne_of_lt hij
    simp only [Matrix.of_apply, completeUpper, FloatMachine.hermFrom, hle, hne,
      hij, ite_true, ite_false]
  · simp only [Matrix.of_apply, completeUpper, FloatMachine.hermFrom, le_refl,
      lt_self_iff_false, ite_true, ite_false, Machine.toFloatMachine]
  · have hle : ¬(i : ℕ) ≤ j := not_le.mpr hji
    have hne : (j : ℕ) ≠ i := ne_of_lt hji
    have hnot : ¬i < j := not_lt.mpr hji.le
    simp only [Matrix.of_apply, completeUpper, FloatMachine.hermFrom, hle, hne,
      hnot, hji, ite_true, ite_false, Machine.toFloatMachine]

/-- The actual rounded shift formula is the mathematical machine's Hermitian shift. -/
theorem completeUpper_shift_eq_hermShift (n : ℕ) (A : ℕ → ℕ → K × K) (d : K) :
    (Matrix.of fun (i j : Fin n) => completeUpper M (fun i j => if i = j then
      (M.sub (A i i).1 d, M.lit 0) else A i j) i j) =
      (M.toFloatMachine dec mm qr unif normal).hermShift (Matrix.of fun (i j : Fin n) => A i j) d :=
  completeUpper_eq_hermFrom M dec mm qr unif normal n A (fun i => M.sub (A i i).1 d)

/-- The actual rounded division formula is the mathematical machine's Hermitian scaling. -/
theorem completeUpper_scale_eq_hermScale (n : ℕ) (A : ℕ → ℕ → K × K) (d : K) :
    (Matrix.of fun (i j : Fin n) => completeUpper M (fun i j => if i = j then
      (M.div (A i i).1 d, M.lit 0) else (M.div (A i j).1 d, M.div (A i j).2 d)) i j) =
      (M.toFloatMachine dec mm qr unif normal).hermScale (Matrix.of fun (i j : Fin n) => A i j) d :=
  completeUpper_eq_hermFrom M dec mm qr unif normal n
    (fun i j => (M.div (A i j).1 d, M.div (A i j).2 d)) (fun i => M.div (A i i).1 d)

/-- The actual rounded addition, subtraction and division formula is the mathematical
machine's Hermitian average, including its preserved exact word order. -/
theorem completeUpper_average_eq_hermAvg (n : ℕ) (A : ℕ → ℕ → K × K) (d : K) :
    (Matrix.of fun (i j : Fin n) => completeUpper M (fun i j => if i = j then
      (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0) else
      (M.div (M.add (A i j).1 (A j i).1) d, M.div (M.sub (A i j).2 (A j i).2) d)) i j) =
      (M.toFloatMachine dec mm qr unif normal).hermAvg (Matrix.of fun (i j : Fin n) => A i j) d :=
  completeUpper_eq_hermFrom M dec mm qr unif normal n
    (fun i j => (M.div (M.add (A i j).1 (A j i).1) d,
      M.div (M.sub (A i j).2 (A j i).2) d)) (fun i => M.div (M.add (A i i).1 (A i i).1) d)

/-- Mapping scalar negation over the packed words is exactly packing the mathematical
machine's entrywise pair negation. The equality preserves the actual component order. -/
theorem map_neg_packFinMatrix {r c : ℕ} (A : Matrix (Fin r) (Fin c) (K × K)) :
    ((EntryCodec.pair K).packFinMatrix A).map M.neg =
      (EntryCodec.pair K).packFinMatrix
        ((M.toFloatMachine dec mm qr unif normal).negMat A) := by
  simp only [EntryCodec.packFinMatrix, List.map_ofFn]
  apply congrArg List.ofFn
  funext q
  simp only [FloatMachine.negMat, Matrix.map_apply, Machine.toFloatMachine]
  dsimp only [Function.comp_apply]
  generalize (finProdFinEquiv.symm q).2 = z
  fin_cases z <;> rfl

variable {M dec mm qr unif normal}

/-- The scalar-visible shift program writes exactly the existing mathematical machine's
packed output on the actual stored finite matrix. Spatially disjoint arena regions are allowed;
numerical accuracy is a separate property of the same machine functions. -/
theorem writes_shift_packed {Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : K) {x c y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : μ.store.readBlock x.1 x.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hc : μ.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ μ.store.len y.1) (hl : μ.Live [x, c, y]) :
    Writes .total I τ (shift (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermShift A d))) μ := by
  let C := EntryCodec.pair K
  let B : ℕ → ℕ → K × K := fun i j => C.entry (C.packFinMatrix A) (j * n + i)
  have hB : μ.store.HoldsEntries C ⟨x.1, x.2, n, n, n⟩ B :=
    Store.holdsEntries_of_readBlock rfl (by simpa only [Nat.mul_comm] using hX)
  have hfinite : (Matrix.of fun (i j : Fin n) => B i j) = A := C.matrix_packFinMatrix A
  refine (writes_shift hI hxy hcy hB hc hY hl).mono le_rfl ?_
  intro μ' _ ⟨houtput, hpos⟩
  have hread := houtput.readBlock_packFinMatrix rfl
  rw [completeUpper_shift_eq_hermShift M dec mm qr unif normal] at hread
  rw [hfinite] at hread
  exact ⟨hpos, by simpa only [Nat.mul_comm] using hread⟩

/-- The scalar-visible scale program writes exactly the existing mathematical machine's
packed output on the actual stored finite matrix. Spatially disjoint arena regions are allowed;
numerical accuracy is a separate property of the same machine functions. -/
theorem writes_scale_packed {Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : K) {x c y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : μ.store.readBlock x.1 x.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hc : μ.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ μ.store.len y.1) (hl : μ.Live [x, c, y]) :
    Writes .total I τ (scale (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermScale A d))) μ := by
  let C := EntryCodec.pair K
  let B : ℕ → ℕ → K × K := fun i j => C.entry (C.packFinMatrix A) (j * n + i)
  have hB : μ.store.HoldsEntries C ⟨x.1, x.2, n, n, n⟩ B :=
    Store.holdsEntries_of_readBlock rfl (by simpa only [Nat.mul_comm] using hX)
  have hfinite : (Matrix.of fun (i j : Fin n) => B i j) = A := C.matrix_packFinMatrix A
  refine (writes_scale hI hxy hcy hB hc hY hl).mono le_rfl ?_
  intro μ' _ ⟨houtput, hpos⟩
  have hread := houtput.readBlock_packFinMatrix rfl
  rw [completeUpper_scale_eq_hermScale M dec mm qr unif normal] at hread
  rw [hfinite] at hread
  exact ⟨hpos, by simpa only [Nat.mul_comm] using hread⟩

/-- The scalar-visible average program writes exactly the existing mathematical machine's
packed output on the actual stored finite matrix. Spatially disjoint arena regions are allowed;
numerical accuracy is a separate property of the same machine functions. -/
theorem writes_average_packed {Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : K) {x c y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : μ.store.readBlock x.1 x.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hc : μ.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ μ.store.len y.1) (hl : μ.Live [x, c, y]) :
    Writes .total I τ (average (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermAvg A d))) μ := by
  let C := EntryCodec.pair K
  let B : ℕ → ℕ → K × K := fun i j => C.entry (C.packFinMatrix A) (j * n + i)
  have hB : μ.store.HoldsEntries C ⟨x.1, x.2, n, n, n⟩ B :=
    Store.holdsEntries_of_readBlock rfl (by simpa only [Nat.mul_comm] using hX)
  have hfinite : (Matrix.of fun (i j : Fin n) => B i j) = A := C.matrix_packFinMatrix A
  refine (writes_average hI hxy hcy hB hc hY hl).mono le_rfl ?_
  intro μ' _ ⟨houtput, hpos⟩
  have hread := houtput.readBlock_packFinMatrix rfl
  rw [completeUpper_average_eq_hermAvg M dec mm qr unif normal] at hread
  rw [hfinite] at hread
  exact ⟨hpos, by simpa only [Nat.mul_comm] using hread⟩


/-- Scalar negation of a packed matrix returns exactly the existing mathematical negation.
Input and output may coincide exactly or occupy spatially disjoint blocks of the same buffer.
The theorem is total under readable input, writable output and the scalar functional contract. -/
theorem writes_negate_packed {Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {r c : ℕ}
    (A : Matrix (Fin r) (Fin c) (K × K)) {x y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (r * c)))
      (Store.inBlock y.1 y.2 (2 * (r * c))) ∨ x = y)
    (hX : μ.store.readBlock x.1 x.2 (2 * (r * c)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hY : y.2 + 2 * (r * c) ≤ μ.store.len y.1) (hl : μ.Live [x, y]) :
    Writes .total I τ (negate (Op := Op) (Tst := Tst)).body (Env.frame [r, c] [x, y])
      (Store.inBlock y.1 y.2 (2 * (r * c)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (r * c)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).negMat A))) μ := by
  have hrun : Wp .total I τ negate.body (Env.frame [r, c] [x, y])
      (fun μ' => μ' = μ.updBlock y (((EntryCodec.pair K).packFinMatrix A).map M.neg)) μ :=
    wp_frame rfl rfl hl (wp_unaryMap_of_disj_or_eq (hI .neg) hxy hX hY rfl)
  refine (Writes.of_wp_eq_updBlock hrun).mono ?_ ?_
  · simp only [List.length_map, EntryCodec.length_packFinMatrix, EntryCodec.pair]
    simp only [Nat.mul_comm]
    exact le_rfl
  · intro μ' _ he
    subst μ'
    refine ⟨rfl, ?_⟩
    have hlen : (((EntryCodec.pair K).packFinMatrix A).map M.neg).length = 2 * (r * c) := by
      simp [Nat.mul_comm]
    have hr := Store.readBlock_updBlock_self (s := μ.store) (b := y.1) (off := y.2)
      (xs := ((EntryCodec.pair K).packFinMatrix A).map M.neg) (by rwa [hlen])
    rw [hlen, map_neg_packFinMatrix M dec mm qr unif normal] at hr
    simpa only [Mem.store_updBlock, map_neg_packFinMatrix M dec mm qr unif normal] using hr

end NLAlib.Ops.Hermitian
