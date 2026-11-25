/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.FactorizationSolve
public import NLAlib.Matrix.Computation.PivotLogPermutation
public import NLAlib.Matrix.Computation.PLU
public import NLAlib.Matrix.Computation.PLUQ

/-!
# Solving through actual pivoted factorizations

Full pivoted factorization is followed by the actual recorded right-hand-side swaps and
triangular solves. Complete pivoting additionally reverses its column swaps on the solution.
Nonsingularity is required of the original matrix, and implies nonzero computed upper pivots
through the actual exact factorization. All factor and log workspace is scoped.

## Main definitions

* `NLAlib.Computation.pluSolve`: partial-pivoted factorization and solve.
* `NLAlib.Computation.pluqSolve`: complete-pivoted factorization and solve.

## Main results

* `NLAlib.Computation.executionComposable_pluSolve`: scoped composition.
* `NLAlib.Computation.executionComposable_pluqSolve`: scoped composition.
* `NLAlib.Computation.exec_pluSolve`, `NLAlib.Computation.exec_pluqSolve`: original systems.
* `NLAlib.Computation.isLinearSolveRoutine_pluSolve`: the exact partial-pivoted certificate.
* `NLAlib.Computation.isLinearSolveRoutine_pluqSolve`: the exact complete-pivoted certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

/-- Factor by actual partial pivoting, apply the stored row swaps to the RHS, and solve the
lower/upper systems. All factor and log buffers are scoped. The input matrix may overlap the
RHS because factorization finishes before the first RHS write. [GolubVanLoan2013, §3.4]. -/
def pluSolve {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  let lower ← alloc tag (n * n)
  let upper ← alloc tag (n * n)
  let rows ← alloc tag n
  pluFactor tag n matrix lower upper rows off 0 0 0
  applyPivotLog tag n rows 0 xb xo
  trsvLower tag n lower 0 xb xo
  trsvUpper tag n upper 0 xb xo

/-- Factor by actual complete pivoting, apply the stored row swaps to the RHS, solve both
triangular systems, then undo the stored column swaps in reverse order on the solution.
Factors and both logs are scoped. The input matrix may overlap the RHS.
[GolubVanLoan2013, §3.4]. -/
def pluqSolve {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  let lower ← alloc tag (n * n)
  let upper ← alloc tag (n * n)
  let rows ← alloc tag n
  let cols ← alloc tag n
  pluqFactor tag n matrix lower upper rows cols off 0 0 0 0
  applyPivotLog tag n rows 0 xb xo
  trsvLower tag n lower 0 xb xo
  trsvUpper tag n upper 0 xb xo
  applyPivotLogReverse tag n cols 0 xb xo

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Partial-pivoted factor-then-solve releases all workspace before its continuation. -/
theorem executionComposable_pluSolve (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (pluSolve tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

/-- Complete-pivoted factor-then-solve releases all workspace before its continuation. -/
theorem executionComposable_pluqSolve (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (pluqSolve tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

namespace PivotedSolve

private theorem rhs_read {N : ℕ} {before after : Store P ℝ} {tag : P}
    {xb off : ℕ} {x : Fin N → ℝ}
    (hw : before.writeBlock tag xb off (Array.ofFn x) = some after) (i : Fin N) :
    after.read tag xb (off + i) = some (x i) := by
  have hr := Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val)
    (by rw [Array.size_ofFn]; exact i.isLt)
  rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact i.isLt),
    Array.getElem_ofFn] at hr
  exact hr

private theorem exec_logTriangular {C : Type} [AddMonoid C]
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) (N : ℕ)
    (st : St P ℝ C) (B L U : Matrix (Fin N) (Fin N) ℝ) (hB : IsUnit B)
    (hf : IsLU B L U) (p : Fin N → Fin N) (b : Fin N → ℝ)
    (lower upper log xb : ℕ) (xo : IExp ℕ)
    (hL : Holds st.store tag lower 0 L) (hU : Holds st.store tag upper 0 U)
    (hlog : ReadsDecoded st.store (fun _ x => x) tag log 0 (fun i => (p i).val))
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i))
    (hLX : 0 < N → lower ≠ xb) (hUX : 0 < N → upper ≠ xb)
    (hPX : 0 < N → log ≠ xb) :
    ∃ (out : St P ℝ C) (z : Fin N → ℝ), exec I (do
      applyPivotLog tag (.const N) log 0 xb xo
      trsvLower tag (.const N) lower 0 xb xo
      trsvUpper tag (.const N) upper 0 xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn z) = some out.store ∧
      B *ᵥ z = b ∘ luPivotPermutation p N := by
  have hi : IsIndexExactSem (fun _ x => x) N I.sem := by
    rw [hI]; exact isIndexExactSem_exactSem _
  obtain ⟨permuted, he₁, hw₁⟩ := exec_applyPivotLog I tag (.const N) hi st log 0 xb xo p b
    hlog hb hPX
  have hL' : Holds permuted.store tag lower 0 L := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (hLX (Nat.zero_lt_of_lt i.isLt)))]
    exact hL i j
  have hU' : Holds permuted.store tag upper 0 U := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (hUX (Nat.zero_lt_of_lt i.isLt)))]
    exact hU i j
  have hdU : ∀ i, U i i ≠ 0 := fun i => isUnit_iff_ne_zero.mp
    ((hf.isUnit_det_iff.mp ((Matrix.isUnit_iff_isUnit_det B).mp hB)) i)
  have hdL : ∀ i, L i i ≠ 0 := fun i => by
    rw [hf.isUnitLowerTriangular.apply_self]; exact one_ne_zero
  obtain ⟨out, z, he₂, hw₂, hz⟩ := FactorizationSolve.exec_luTriangularSolves I hI tag
    permuted N B L U hf hdL hdU lower upper xb xo (b ∘ luPivotPermutation p N) hL' hU'
    (rhs_read hw₁) hLX hUX
  refine ⟨out, z, ?_, Store.writeBlock_writeBlock_self hw₁ hw₂ (by simp), hz⟩
  rw [exec_run_bind I (b := applyPivotLog tag (.const N) log 0 xb xo) (fun _ => rfl),
    he₁, Option.bind_some]
  exact he₂

private theorem writeBlock_of_original_frame {N : ℕ} (initial final popped : Store P ℝ)
    (tag : P) (xb off : ℕ) (x : Fin N → ℝ) (hshape : popped.shape = initial.shape)
    (hkeep : ∀ q b i, b < initial.size → popped.read q b i = final.read q b i)
    (hxb : 0 < N → xb < initial.size)
    (hread : ∀ i : Fin N, final.read tag xb (off + i) = some (x i))
    (hframe : ∀ q b i, b < initial.size → (b ≠ xb ∨ i < off ∨ off + N ≤ i) →
      final.read q b i = initial.read q b i) :
    initial.writeBlock tag xb off (Array.ofFn x) = some popped := by
  apply Store.writeBlock_eq_some_of_read hshape
  · intro i hi
    have hin : i < N := by simpa only [Array.size_ofFn] using hi
    rw [hkeep tag xb (off + i) (hxb (Nat.zero_lt_of_lt hin)), hread ⟨i, hin⟩,
      Array.getElem?_eq_getElem hi, Array.getElem_ofFn]
  · intro q b i hout
    by_cases hb : b < initial.size
    · rw [hkeep q b i hb]
      exact hframe q b i hb (by simpa only [Array.size_ofFn] using hout)
    · rw [Store.read_eq_none_of_size_le (s := popped) (by
        rw [Store.size_eq_of_shape_eq hshape]; omega),
        Store.read_eq_none_of_size_le (by omega)]

private theorem read_pop_iterate (s : Store P ℝ) (d : ℕ) (q : P) (b i : ℕ)
    (hb : b + d < s.size) : Store.read ((Array.pop^[d]) s) q b i = s.read q b i := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    rw [ih s.pop (by simp only [Array.size_pop]; omega)]
    exact Store.read_pop_of_lt (by omega)

omit [DecidableEq P] in
private theorem shape_pop_iterate (s : Store P ℝ) (d : ℕ) :
    Store.shape ((Array.pop^[d]) s) = (Array.pop^[d]) s.shape := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih, Store.shape_pop, Function.iterate_succ_apply]

private theorem finish_popped (initial start factored final : Store P ℝ) (tag : P)
    (N xb off d : ℕ) (x : Fin N → ℝ)
    (hstart : (Array.pop^[d]) start.shape = initial.shape)
    (hsize : start.size = initial.size + d) (hF : factored.shape = start.shape)
    (hw : factored.writeBlock tag xb off (Array.ofFn x) = some final)
    (hxb : 0 < N → xb < initial.size)
    (hreads : ∀ q b i, b < initial.size → factored.read q b i = initial.read q b i) :
    initial.writeBlock tag xb off (Array.ofFn x) = some ((Array.pop^[d]) final) := by
  have hshape := (Store.shape_of_writeBlock_eq_some hw).trans hF
  have hfinalsize : final.size = initial.size + d :=
    (Store.size_eq_of_shape_eq hshape).trans hsize
  apply writeBlock_of_original_frame initial final _ tag xb off x
  · rw [shape_pop_iterate, hshape, hstart]
  · intro q b i hb
    exact read_pop_iterate final d q b i (by omega)
  · exact hxb
  · exact rhs_read hw
  · intro q b i hb hout
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
      simpa only [Array.size_ofFn] using hout)]
    exact hreads q b i hb

private theorem scope_three_data (initial start : Store P K) (tag : P) (N : ℕ)
    (hs : start = ((initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate (N * N) none)).push (tag, Array.replicate N none)) :
    (∀ q b i, b < initial.size → start.read q b i = initial.read q b i) ∧
    Writable start tag initial.size 0 (N * N) ∧
    Writable start tag (initial.size + 1) 0 (N * N) ∧
    Writable start tag (initial.size + 2) 0 N := by
  have cap0 := writable_of_shape_eq rfl
    (Store.getElem?_shape_push_size initial tag (N * N)) (by omega : 0 + N * N ≤ N * N)
  have cap1 := writable_of_shape_eq rfl (Store.getElem?_shape_push_size
    (initial.push (tag, Array.replicate (N * N) none)) tag (N * N))
    (by omega : 0 + N * N ≤ N * N)
  have cap2 := writable_of_shape_eq rfl (Store.getElem?_shape_push_size
    ((initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate (N * N) none)) tag N) (by omega : 0 + N ≤ N)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q b i hb
    rw [hs, Store.read_push_of_lt (by simp only [Array.size_push]; omega),
      Store.read_push_of_lt (by simp only [Array.size_push]; omega), Store.read_push_of_lt hb]
  · rw [hs]
    exact (cap0.push (tag, Array.replicate (N * N) none)).push (tag, Array.replicate N none)
  · rw [hs]
    simpa only [Array.size_push] using cap1.push (tag, Array.replicate N none)
  · rw [hs]
    simpa only [Array.size_push, Nat.add_assoc] using cap2

private theorem scope_four_data (initial start : Store P K) (tag : P) (N : ℕ)
    (hs : start = (((initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate (N * N) none)).push (tag, Array.replicate N none)).push
        (tag, Array.replicate N none)) :
    (∀ q b i, b < initial.size → start.read q b i = initial.read q b i) ∧
    Writable start tag initial.size 0 (N * N) ∧
    Writable start tag (initial.size + 1) 0 (N * N) ∧
    Writable start tag (initial.size + 2) 0 N ∧
    Writable start tag (initial.size + 3) 0 N := by
  let prior := ((initial.push (tag, Array.replicate (N * N) none)).push
    (tag, Array.replicate (N * N) none)).push (tag, Array.replicate N none)
  obtain ⟨hr, hL, hU, hR⟩ := scope_three_data initial prior tag N rfl
  have hlast := writable_of_shape_eq rfl (Store.getElem?_shape_push_size prior tag N)
    (by omega : 0 + N ≤ N)
  refine ⟨?_, hs ▸ hL.push _, hs ▸ hU.push _, hs ▸ hR.push _, ?_⟩
  · intro q b i hb
    rw [hs, Store.read_push_of_lt (by simp only [Array.size_push]; omega)]
    exact hr q b i hb
  · rw [hs]
    simpa only [prior, Array.size_push, Nat.add_assoc] using hlast

private theorem factor_original_reads (initial start final : Store P ℝ) (tag : P)
    (blocks : List (ℕ × ℕ × ℕ)) (words : List (Array ℝ))
    (hw : start.writeBlocks tag blocks words = some final)
    (hstart : ∀ q b i, b < initial.size → start.read q b i = initial.read q b i)
    (hfar : ∀ block ∈ blocks, initial.size ≤ block.1) :
    ∀ q b i, b < initial.size → final.read q b i = initial.read q b i := by
  intro q b i hb
  rw [Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hm =>
    Or.inl (by have := hfar block hm; omega))]
  exact hstart q b i hb

private theorem exec_pluSolveBody (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (tag : P) (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A) (b : Fin N → ℝ)
    (matrix xb : ℕ) (off xo : IExp ℕ) (hM : Holds initial tag matrix off.eval A)
    (hb : ∀ i : Fin N, initial.read tag xb (xo.eval + i) = some (b i))
    (hstore : st.store = (((initial.push (tag, Array.replicate (N * N) none)).push (tag,
      Array.replicate (N * N) none)).push (tag, Array.replicate (N) none))) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ), exec I (do
      pluFactor tag (.const N) matrix initial.size (initial.size + 1) (initial.size + 2) off 0 0 0
      applyPivotLog tag (.const N) (initial.size + 2) 0 xb xo
      trsvLower tag (.const N) initial.size 0 xb xo
      trsvUpper tag (.const N) (initial.size + 1) 0 xb xo).run st = some out ∧
      initial.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store.pop.pop.pop ∧ A *ᵥ x = b
        := by
  have hxb : 0 < N → xb < initial.size := fun hN =>
    Store.lt_size_of_read_eq_some (hb ⟨0, hN⟩)
  have hmb : 0 < N → matrix < initial.size := fun hN =>
    Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  obtain ⟨hstart, cap0, cap1, cap2⟩ :=
    scope_three_data initial st.store tag N hstore
  have hMp : Holds st.store tag matrix off.eval A := fun i j =>
    (hstart tag matrix _ (hmb (Nat.zero_lt_of_lt i.isLt))).trans (hM i j)
  obtain ⟨outFactor, p, heF, hwF, hp, hf, -, hL, hU, hrow, -⟩ := exec_pluFactor I hI hc tag st
    (.const N) matrix initial.size (initial.size + 1) (initial.size + 2) off 0 0 0 A hMp
    cap0 cap1 cap2 (by omega) (by omega) (by omega)
    (fun hN => by have := hmb hN; omega) (fun hN => by have := hmb hN; omega)
    (fun hN => by have := hmb hN; omega)
  change Fin N → Fin N at p
  let B := A.submatrix (luPivotPermutation p N) id
  have hUnitB : IsUnit B := (Matrix.isUnit_submatrix_equiv (luPivotPermutation p N)
    (Equiv.refl _)).mpr hA
  have hreads := factor_original_reads initial st.store outFactor.store tag _ _ hwF hstart
    (by intro block hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact le_rfl
        · exact Nat.le_add_right _ _
        · exact Nat.le_add_right _ _)
  have hbF : ∀ i : Fin N, outFactor.store.read tag xb (xo.eval + i) = some (b i) :=
    fun i => (hreads tag xb _ (hxb (Nat.zero_lt_of_lt i.isLt))).trans (hb i)
  obtain ⟨solved, z, heZ, hwZ, hz⟩ := exec_logTriangular I hI tag N outFactor B
    (luLower (A.submatrix (luPivotPermutation p N) id)) (luUpper (A.submatrix (luPivotPermutation
      p N) id)) hUnitB hf p b initial.size (initial.size + 1) (initial.size + 2)
    xb xo hL hU (fun j => ⟨((p j).val : ℝ), hrow j, rfl⟩) hbF
    (fun hN => by have := hxb hN; omega) (fun hN => by have := hxb hN; omega)
    (fun hN => by have := hxb hN; omega)
  let x := z
  let out := solved
  have hwX := hwZ
  have hsol : A *ᵥ x = b := by
    have hEq : (A *ᵥ x) ∘ luPivotPermutation p N = b ∘ luPivotPermutation p N := by
      have hz' : A.submatrix (luPivotPermutation p N) (Equiv.refl _) *ᵥ z =
          b ∘ luPivotPermutation p N := hz
      rw [Matrix.submatrix_mulVec_equiv] at hz'
      simpa only [x, Equiv.refl_symm, Equiv.refl_apply, Function.comp_def] using hz'
    funext i
    have hh := congrFun hEq ((luPivotPermutation p N).symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
  have hpost := finish_popped initial st.store outFactor.store out.store tag N xb xo.eval
    3 x (by simp only [hstore, Store.shape, Array.map_push, Function.iterate_succ_apply,
      Function.iterate_zero_apply, Array.pop_push])
    (by rw [hstore]; simp only [Array.size_push, Nat.add_assoc])
    (Store.shape_of_writeBlocks_eq_some hwF) hwX hxb hreads
  refine ⟨out, x, ?_, ?_, hsol⟩
  · rw [exec_run_bind I (b := pluFactor tag (.const N) matrix initial.size (initial.size + 1)
    (initial.size + 2) off 0 0 0) (fun _ => rfl), heF, Option.bind_some]
    exact heZ
  · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hpost

private theorem exec_pluqSolveBody (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (tag : P) (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A) (b : Fin N → ℝ)
    (matrix xb : ℕ) (off xo : IExp ℕ) (hM : Holds initial tag matrix off.eval A)
    (hb : ∀ i : Fin N, initial.read tag xb (xo.eval + i) = some (b i))
    (hstore : st.store = ((((initial.push (tag, Array.replicate (N * N) none)).push (tag,
      Array.replicate (N * N) none)).push (tag, Array.replicate (N) none)).push (tag,
      Array.replicate (N) none))) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ), exec I (do
      pluqFactor tag (.const N) matrix initial.size (initial.size + 1) (initial.size + 2)
        (initial.size + 3) off 0 0 0 0
      applyPivotLog tag (.const N) (initial.size + 2) 0 xb xo
      trsvLower tag (.const N) initial.size 0 xb xo
      trsvUpper tag (.const N) (initial.size + 1) 0 xb xo
      applyPivotLogReverse tag (.const N) (initial.size + 3) 0 xb xo).run st = some out ∧
      initial.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store.pop.pop.pop.pop ∧ A *ᵥ x =
        b := by
  have hxb : 0 < N → xb < initial.size := fun hN =>
    Store.lt_size_of_read_eq_some (hb ⟨0, hN⟩)
  have hmb : 0 < N → matrix < initial.size := fun hN =>
    Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  obtain ⟨hstart, cap0, cap1, cap2, cap3⟩ :=
    scope_four_data initial st.store tag N hstore
  have hMp : Holds st.store tag matrix off.eval A := fun i j =>
    (hstart tag matrix _ (hmb (Nat.zero_lt_of_lt i.isLt))).trans (hM i j)
  obtain ⟨outFactor, p, q, heF, hwF, hp, hq, hf, -, hL, hU, hrow, hcol, -⟩ :=
    exec_pluqFactor I hI hc tag st (.const N) matrix initial.size (initial.size + 1)
      (initial.size + 2) (initial.size + 3) off 0 0 0 0 A hMp cap0 cap1 cap2 cap3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun hN => by have := hmb hN; omega) (fun hN => by have := hmb hN; omega)
      (fun hN => by have := hmb hN; omega) (fun hN => by have := hmb hN; omega)
  change Fin N → Fin N at p q
  let B := A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)
  have hUnitB : IsUnit B := (Matrix.isUnit_submatrix_equiv (luPivotPermutation p N)
    (luPivotPermutation q N)).mpr hA
  have hreads := factor_original_reads initial st.store outFactor.store tag _ _ hwF hstart
    (by intro block hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl
        · exact le_rfl
        · exact Nat.le_add_right _ _
        · exact Nat.le_add_right _ _
        · exact Nat.le_add_right _ _)
  have hbF : ∀ i : Fin N, outFactor.store.read tag xb (xo.eval + i) = some (b i) :=
    fun i => (hreads tag xb _ (hxb (Nat.zero_lt_of_lt i.isLt))).trans (hb i)
  obtain ⟨solved, z, heZ, hwZ, hz⟩ := exec_logTriangular I hI tag N outFactor B
    (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) (luUpper
      (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) hUnitB hf p b initial.size
      (initial.size + 1) (initial.size + 2)
    xb xo hL hU (fun j => ⟨((p j).val : ℝ), hrow j, rfl⟩) hbF
    (fun hN => by have := hxb hN; omega) (fun hN => by have := hxb hN; omega)
    (fun hN => by have := hxb hN; omega)
  have hi : IsIndexExactSem (fun _ x => x) N I.sem := by
    rw [hI]; exact isIndexExactSem_exactSem _
  have hcols : ReadsDecoded solved.store (fun _ x => x) tag (initial.size + 3) 0
      (fun j => (q j).val) := by
    intro j
    refine ⟨((q j).val : ℝ), ?_, rfl⟩
    rw [Store.read_of_writeBlock_eq_some_of_ne hwZ (Or.inl (by
      have := hxb (Nat.zero_lt_of_lt j.isLt); omega))]
    exact hcol j
  obtain ⟨out, heR, hwR⟩ := exec_applyPivotLogReverse I tag (.const N) hi solved
    (initial.size + 3) 0 xb xo q z hcols (rhs_read hwZ)
    (fun hN => by have := hxb hN; omega)
  let x := z ∘ (luPivotPermutation q N).symm
  have hwX : outFactor.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store :=
    Store.writeBlock_writeBlock_self hwZ hwR (by simp)
  have hsol : A *ᵥ x = b := by
    have hEq : (A *ᵥ x) ∘ luPivotPermutation p N = b ∘ luPivotPermutation p N := by
      simpa only [B, Matrix.submatrix_mulVec_equiv, x] using hz
    funext i
    have hh := congrFun hEq ((luPivotPermutation p N).symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
  have hpost := finish_popped initial st.store outFactor.store out.store tag N xb xo.eval
    4 x (by simp only [hstore, Store.shape, Array.map_push, Function.iterate_succ_apply,
      Function.iterate_zero_apply, Array.pop_push])
    (by rw [hstore]; simp only [Array.size_push, Nat.add_assoc])
    (Store.shape_of_writeBlocks_eq_some hwF) hwX hxb hreads
  refine ⟨out, x, ?_, ?_, hsol⟩
  · rw [exec_run_bind I (b := pluqFactor tag (.const N) matrix initial.size (initial.size + 1)
    (initial.size + 2) (initial.size + 3) off 0 0 0 0) (fun _ => rfl), heF, Option.bind_some]
    have hcomp : ExecutionComposable I (do
        applyPivotLog tag (.const N) (initial.size + 2) 0 xb xo
        trsvLower tag (.const N) initial.size 0 xb xo
        trsvUpper tag (.const N) (initial.size + 1) 0 xb xo) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I ((do
      applyPivotLog tag (.const N) (initial.size + 2) 0 xb xo
      trsvLower tag (.const N) initial.size 0 xb xo
      trsvUpper tag (.const N) (initial.size + 1) 0 xb xo) >>= fun _ =>
      applyPivotLogReverse tag (.const N) (initial.size + 3) 0 xb xo).run outFactor = some out
    rw [hcomp, heZ, Option.bind_some]; exact heR
  · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hpost

private theorem exec_scope_three (I : Interp P ι ℝ C) (tag : P)
    (la lb lc : IExp ℕ) (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit)
    (st : St P ℝ C) (Q : Store P ℝ → Prop)
    (hbody : ∀ σ : St P ℝ C, σ.store = (((st.store.push (tag, Array.replicate la.eval none)).push
      (tag, Array.replicate lb.eval none)).push (tag, Array.replicate lc.eval none)) →
      ∃ out, exec I (body st.store.size (st.store.size + 1) (st.store.size + 2)).run σ = some out
        ∧ Q out.store.pop.pop.pop) :
    ∃ out, exec I ((scope do
      let a ← alloc tag la
      let b ← alloc tag lb
      let c ← alloc tag lc
      body a b c) : Builder P ι ℕ ℕ Unit).run st = some out ∧ Q out.store := by
  obtain ⟨out0, he0, hQ0⟩ := exists_exec_alloc I tag la
    (fun a => .alloc tag lb fun b => .alloc tag lc fun c => (body a b c).run) st
    (fun s => Q s) (by
      intro σ1 hs1
      obtain ⟨out1, he1, hQ1⟩ := exists_exec_alloc I tag lb
        (fun b => .alloc tag lc fun c => (body st.store.size b c).run) σ1
        (fun s => Q s.pop) (by
          intro σ2 hs2
          obtain ⟨out2, he2, hQ2⟩ := exists_exec_alloc I tag lc
            (fun c => (body st.store.size σ1.store.size c).run) σ2
            (fun s => Q s.pop.pop) (by
              intro σ3 hs3
              have hs : σ3.store = (((st.store.push (tag, Array.replicate la.eval none)).push
                (tag, Array.replicate lb.eval none)).push (tag, Array.replicate lc.eval none)) :=
                by
                rw [hs3, hs2, hs1]
              obtain ⟨final, he, hQ⟩ := hbody σ3 hs
              refine ⟨final, ?_, hQ⟩
              simpa only [hs1, hs2, Array.size_push, Nat.add_assoc] using he)
          exact ⟨out2, he2, hQ2⟩)
      exact ⟨out1, he1, hQ1⟩)
  refine ⟨out0, ?_, hQ0⟩
  change exec I (.seq (.alloc tag la _) .skip) st = some out0
  rw [exec_seq_skip]; exact he0

private theorem exec_scope_four (I : Interp P ι ℝ C) (tag : P)
    (la lb lc ld : IExp ℕ) (body : ℕ → ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit)
    (st : St P ℝ C) (Q : Store P ℝ → Prop)
    (hbody : ∀ σ : St P ℝ C, σ.store = ((((st.store.push (tag, Array.replicate la.eval none)).push
      (tag, Array.replicate lb.eval none)).push (tag, Array.replicate lc.eval none)).push (tag,
      Array.replicate ld.eval none)) →
      ∃ out, exec I (body st.store.size (st.store.size + 1) (st.store.size + 2) (st.store.size +
        3)).run σ = some out ∧ Q out.store.pop.pop.pop.pop) :
    ∃ out, exec I ((scope do
      let a ← alloc tag la
      let b ← alloc tag lb
      let c ← alloc tag lc
      let d ← alloc tag ld
      body a b c d) : Builder P ι ℕ ℕ Unit).run st = some out ∧ Q out.store := by
  obtain ⟨out0, he0, hQ0⟩ := exists_exec_alloc I tag la
    (fun a => .alloc tag lb fun b => .alloc tag lc fun c => .alloc tag ld fun d => (body a b c
      d).run) st
    (fun s => Q s) (by
      intro σ1 hs1
      obtain ⟨out1, he1, hQ1⟩ := exists_exec_alloc I tag lb
        (fun b => .alloc tag lc fun c => .alloc tag ld fun d => (body st.store.size b c d).run) σ1
        (fun s => Q s.pop) (by
          intro σ2 hs2
          obtain ⟨out2, he2, hQ2⟩ := exists_exec_alloc I tag lc
            (fun c => .alloc tag ld fun d => (body st.store.size σ1.store.size c d).run) σ2
            (fun s => Q s.pop.pop) (by
              intro σ3 hs3
              obtain ⟨out3, he3, hQ3⟩ := exists_exec_alloc I tag ld
                (fun d => (body st.store.size σ1.store.size σ2.store.size d).run) σ3
                (fun s => Q s.pop.pop.pop) (by
                  intro σ4 hs4
                  have hs : σ4.store = ((((st.store.push (tag, Array.replicate la.eval none)).push
                    (tag, Array.replicate lb.eval none)).push (tag, Array.replicate lc.eval
                    none)).push (tag, Array.replicate ld.eval none)) := by
                    rw [hs4, hs3, hs2, hs1]
                  obtain ⟨final, he, hQ⟩ := hbody σ4 hs
                  refine ⟨final, ?_, hQ⟩
                  simpa only [hs1, hs2, hs3, Array.size_push, Nat.add_assoc] using he)
              exact ⟨out3, he3, hQ3⟩)
          exact ⟨out2, he2, hQ2⟩)
      exact ⟨out1, he1, hQ1⟩)
  refine ⟨out0, ?_, hQ0⟩
  change exec I (.seq (.alloc tag la _) .skip) st = some out0
  rw [exec_seq_skip]; exact he0

end PivotedSolve
/-- Full actual partial-pivoted factorization and solve succeeds for every nonsingular
original real matrix under exact semantics and standard charges. Only the original RHS block
is written. Factor and log storage is scoped; the matrix may overlap the RHS, and empty inputs
require no valid handles. No computed-pivot or successful-factorization premise is assumed.
[GolubVanLoan2013, §3.4]. -/
theorem exec_pluSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A) (b : Fin N → ℝ) (matrix xb : ℕ) (off xo : IExp ℕ)
    (hM : Holds st.store tag matrix off.eval A)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ),
      exec I (pluSolve tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ A *ᵥ x = b := by
  let Q : Store P ℝ → Prop := fun store => ∃ x : Fin N → ℝ,
    st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some store ∧ A *ᵥ x = b
  obtain ⟨out, he, x, hw, hsol⟩ := PivotedSolve.exec_scope_three I tag
    (.const N * .const N) (.const N * .const N) (.const N)
    (fun lower upper rows => do
      pluFactor tag (.const N) matrix lower upper rows off 0 0 0
      applyPivotLog tag (.const N) rows 0 xb xo
      trsvLower tag (.const N) lower 0 xb xo
      trsvUpper tag (.const N) upper 0 xb xo) st Q (by
      intro σ hσ
      obtain ⟨out, x, he, hw, hsol⟩ := PivotedSolve.exec_pluSolveBody I hI hc tag st.store σ N
        A hA b matrix xb off xo hM hb
        (by simpa only [IExp.eval_mul, IExp.eval_const] using hσ)
      exact ⟨out, he, x, hw, hsol⟩)
  exact ⟨out, x, he, hw, hsol⟩

/-- The actual partial-pivoted factor-then-solve program has zero componentwise backward
error for a nonsingular original matrix in exact arithmetic. This certificate retains the
single RHS footprint and allows matrix/RHS overlap and empty invalid handles.
[GolubVanLoan2013, §3.4]. -/
theorem isLinearSolveRoutine_pluSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A)
    (matrix xb : ℕ) (off xo : IExp ℕ) :
    IsLinearSolveRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag matrix off.eval A)
      xb xo (pluSolve tag (.const N) matrix off xb xo) where
  composable := executionComposable_pluSolve I tag (.const N) matrix off xb xo
  run st b hM hb _ := by
    obtain ⟨out, x, he, hw, hsol⟩ := exec_pluSolve I hI hc tag st N A hA b matrix xb off xo hM
      (fun i => by obtain ⟨w, hw, hd⟩ := hb i; simpa only [hd] using hw)
    exact ⟨out, x, he, hw, IsLinearSolveErr.of_mulVec_eq (le_refl 0) hsol⟩

/-- Full actual complete-pivoted factorization and solve succeeds for every nonsingular
original real matrix under exact semantics and standard charges. Only the original RHS block
is written. Factor and log storage is scoped; the matrix may overlap the RHS, and empty inputs
require no valid handles. No computed-pivot or successful-factorization premise is assumed.
[GolubVanLoan2013, §3.4]. -/
theorem exec_pluqSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A) (b : Fin N → ℝ) (matrix xb : ℕ) (off xo : IExp ℕ)
    (hM : Holds st.store tag matrix off.eval A)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ),
      exec I (pluqSolve tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ A *ᵥ x = b := by
  let Q : Store P ℝ → Prop := fun store => ∃ x : Fin N → ℝ,
    st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some store ∧ A *ᵥ x = b
  obtain ⟨out, he, x, hw, hsol⟩ := PivotedSolve.exec_scope_four I tag
    (.const N * .const N) (.const N * .const N) (.const N) (.const N)
    (fun lower upper rows cols => do
      pluqFactor tag (.const N) matrix lower upper rows cols off 0 0 0 0
      applyPivotLog tag (.const N) rows 0 xb xo
      trsvLower tag (.const N) lower 0 xb xo
      trsvUpper tag (.const N) upper 0 xb xo
      applyPivotLogReverse tag (.const N) cols 0 xb xo) st Q (by
      intro σ hσ
      obtain ⟨out, x, he, hw, hsol⟩ := PivotedSolve.exec_pluqSolveBody I hI hc tag st.store σ N
        A hA b matrix xb off xo hM hb
        (by simpa only [IExp.eval_mul, IExp.eval_const] using hσ)
      exact ⟨out, he, x, hw, hsol⟩)
  exact ⟨out, x, he, hw, hsol⟩

/-- The actual complete-pivoted factor-then-solve program has zero componentwise backward
error for a nonsingular original matrix in exact arithmetic. This certificate retains the
single RHS footprint and allows matrix/RHS overlap and empty invalid handles.
[GolubVanLoan2013, §3.4]. -/
theorem isLinearSolveRoutine_pluqSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A)
    (matrix xb : ℕ) (off xo : IExp ℕ) :
    IsLinearSolveRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag matrix off.eval A)
      xb xo (pluqSolve tag (.const N) matrix off xb xo) where
  composable := executionComposable_pluqSolve I tag (.const N) matrix off xb xo
  run st b hM hb _ := by
    obtain ⟨out, x, he, hw, hsol⟩ := exec_pluqSolve I hI hc tag st N A hA b matrix xb off xo hM
      (fun i => by obtain ⟨w, hw, hd⟩ := hb i; simpa only [hd] using hw)
    exact ⟨out, x, he, hw, IsLinearSolveErr.of_mulVec_eq (le_refl 0) hsol⟩

end NLAlib.Computation
