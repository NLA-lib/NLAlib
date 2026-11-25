/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.BlockedScaleColumn
public import NLAlib.Matrix.Factorizations.CholeskyLU
public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Ops.Logic.EntryColumn

/-!
# Actual column scaling from blocked LU to Cholesky

Each column uses the shared scalar root/fill/multiply routine. The upper factor supplies
one original pivot per column and is retained. Exact arithmetic on positive-definite input
identifies the resulting words with the canonical Cholesky factor through the existing
LU/Cholesky mathematical bridge.

## Main results

* `NLAlib.Cholesky.scaleLuColumns_meets`: actual word-level column scaling.
* `NLAlib.Cholesky.decodeMatrix_eq_choleskyLower_of_scaleLuColumnsSpec`:
  exact canonical numerical readback.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Scale each unit-lower LU column by its upper pivot's square root. The scalar routine
writes actual zero literals above the diagonal and includes the diagonal in its product loop. -/
def scaleLuColumns : Routine Op Tst := routine% [n] (L : n * n, U : n * n) → (L) {
  for j < n {
    run scaleLuColumn [n, j] (U[j * n + j], L[j * n])
  }
}

/-- Actual machine words of the complete root-scaled matrix. -/
def scaleLuValues (M : Machine K) (L U : ℕ → ℕ → K) : ℕ → ℕ → K :=
  fun i j => if i < j then M.lit 0 else M.mul (L i j) (M.sqrt (U j j))

variable [Inhabited K]

/-- The complete output word block, independent of any arithmetic accuracy assumption. -/
def scaleLuColumnsSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (Ls, Us) → (Bs) ensures
    Bs = (EntryCodec.scalar K).packMatrix n n
      (scaleLuValues M (fun i j => vec Ls (j * n + i)) (fun i j => vec Us (j * n + i)))

omit [Has ScalarOp Op] in
private theorem scaleLuColumnWords_pack (M : Machine K) (p : K) (X : ℕ → K) (n k : ℕ) :
    scaleLuColumnWords M p ((EntryCodec.scalar K).pack n X) n k =
      (EntryCodec.scalar K).pack n
        (fun i => if i < k then M.lit 0 else M.mul (X i) (M.sqrt p)) := by
  apply List.ext_getElem
  · simp [scaleLuColumnWords]
  · intro i hi hi'
    have hin : i < n := by simpa [scaleLuColumnWords] using hi
    simp [scaleLuColumnWords, EntryCodec.scalar_pack, hin]

/-- The actual complete column loop meets its word specification on every scalar machine,
including order zero. Only the lower operand is modified and no tape words are consumed. -/
theorem scaleLuColumns_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (scaleLuColumns (Op := Op) (Tst := Tst)).Meets I (scaleLuColumnsSpec M) := by
  routine_intro [n] (L, U) reads (Ls, Us)
  let C := EntryCodec.scalar K
  let layout : MatLayout := ⟨L.1, L.2, n, n, n⟩
  let old := fun i j => vec Ls (j * n + i)
  let new := scaleLuValues M old (fun i j => vec Us (j * n + i))
  have hstart : m.store.HoldsEntries C layout old := by
    simpa only [C, layout, EntryCodec.scalar_entry, Nat.mul_one] using
      (Store.holdsEntries_of_readBlock (C := C) (L := layout) rfl
        (by simpa only [C, layout, Nat.mul_one] using hLs))
  loop_inv (fun _ => Fp.blocks [L] [n * n])
    (fun j μ => μ.pos = m.pos ∧ μ.store.HoldsEntries C layout
      (fun i c => if c < j then new i c else old i c)) with j hj μ hfr hP
  case round =>
    obtain ⟨hp, hmatrix⟩ := hP
    have hUs₁ : μ.store.readBlock U.1 U.2 (n * n) = some Us := by keep
    have hdiag := Store.get_of_readBlock hUs₁ (Idx.add_lt_mul hj hj) default
    have hdiag' : μ.store.get U.1 (U.2 + j * n + j) = some (vec Us (j * n + j)) := by
      simpa only [Nat.add_assoc] using hdiag
    have hcol : μ.store.readBlock L.1 (L.2 + j * n) n =
        some (C.pack n (fun i => old i j)) := by
      simpa only [C, layout, Nat.one_mul, Nat.mul_one, if_neg (Nat.lt_irrefl j)] using
        hmatrix.readBlock_column hj
    have hcolroom : L.2 + j * n + n ≤ μ.store.len L.1 := by
      rw [hfr.len_eq]
      have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at hm
      omega
    call (scaleLuColumn_meets hI) [n, j] ((U.1, U.2 + j * n + j), (L.1, L.2 + j * n))
      (pre := hj.le) as ν hfr' hpos' (bs) hpost
    have hwords : bs = C.pack n (fun i => new i j) := by
      rw [hpost]
      exact scaleLuColumnWords_pack M (vec Us (j * n + j)) (fun i => old i j) n j
    have hnew := hmatrix.update_column_of_frame (hL := le_rfl) (j := j) (F := ⊥)
      (by simp) (by simpa only [C, layout, Fp.blocks, Nat.one_mul, Nat.mul_one,
        sup_bot_eq] using hfr')
      (fun i => new i j) (by simpa only [C, layout, Nat.one_mul, Nat.mul_one, hwords] using hbs)
    refine ⟨hpos'.trans hp, fun i hi c hc z => ?_⟩
    have hh := hnew i hi c hc z
    by_cases hcj : c = j
    · subst c
      simpa only [if_pos rfl, ite_true, if_pos (Nat.lt_succ_self j)] using hh
    · by_cases hlt : c < j
      · simpa only [if_neg hcj, if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)] using hh
      · simpa only [if_neg hcj, if_neg hlt, if_neg (show ¬c < j + 1 by omega)] using hh
  case exit =>
    rintro μ _ ⟨hp, hmatrix⟩
    have hm : μ.store.HoldsEntries C layout new := by
      intro i hi c hc z
      have hc' : c < n := hc
      simpa only [if_pos hc'] using hmatrix i hi c hc z
    refine ⟨hp, [C.packMatrix n n new], Mem.readBlocks_of_cons ?_ rfl, rfl⟩
    simpa only [C, layout, Nat.mul_one] using hm.readBlock rfl

omit [Has ScalarOp Op] in
/-- Upper output words are the actual zero literal, independently of all arithmetic accuracy
laws and independently of whether the input lower words were triangular. -/
theorem vec_eq_lit_zero_of_scaleLuColumnsSpec {M : Machine K} {N : ℕ}
    {Ls Us Bs : List K} {τ : Tape K}
    (hpost : (scaleLuColumnsSpec M).post [N] τ [Ls, Us] [Bs])
    (i j : Fin N) (hij : i < j) : vec Bs (j.val * N + i.val) = M.lit 0 := by
  obtain rfl : Bs = (EntryCodec.scalar K).packMatrix N N
      (scaleLuValues M (fun i j => vec Ls (j * N + i)) (fun i j => vec Us (j * N + i))) := hpost
  have he := congrFun (congrFun ((EntryCodec.scalar K).matrix_packMatrix N N
    (scaleLuValues M (fun i j => vec Ls (j * N + i)) (fun i j => vec Us (j * N + i)))) i) j
  simpa only [EntryCodec.matrix, EntryCodec.scalar_entry, scaleLuValues,
    if_pos (show i.val < j.val from hij)] using he

omit [Has ScalarOp Op] in
/-- The actual word postcondition scales canonical LU factors to the canonical Cholesky
factor on positive-definite input. Every root law is justified by an original positive pivot. -/
theorem decodeMatrix_eq_choleskyLower_of_scaleLuColumnsSpec {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {Ls Us Bs : List K} {τ : Tape K}
    (hpost : (scaleLuColumnsSpec M).post [N] τ [Ls, Us] [Bs])
    (hL : decodeMatrix dec N N Ls = luLower A) (hU : decodeMatrix dec N N Us = luUpper A) :
    decodeMatrix dec N N Bs = choleskyLower A := by
  obtain rfl : Bs = (EntryCodec.scalar K).packMatrix N N
      (scaleLuValues M (fun i j => vec Ls (j * N + i)) (fun i j => vec Us (j * N + i))) := hpost
  rw [decodeMatrix, EntryCodec.matrix_packMatrix]
  ext i j
  change dec (scaleLuValues M (fun i j => vec Ls (j * N + i))
    (fun i j => vec Us (j * N + i)) i j) = _
  by_cases hij : i.val < j.val
  · rw [scaleLuValues, if_pos hij, hM.lit]
    simpa using (isLowerTriangular_choleskyLower A (show i < j from hij)).symm
  · have hp : 0 ≤ dec (vec Us (j.val * N + j.val)) := by
      rw [← decodeMatrix_apply dec N N Us j j, hU, luUpper_apply_self]
      exact (hA.gaussState_apply_self_pos j).le
    rw [scaleLuValues, if_neg hij, hM.mul, hM.sqrt _ hp,
      ← decodeMatrix_apply dec N N Ls i j, ← decodeMatrix_apply dec N N Us j j, hL, hU]
    simpa using hA.luLower_mul_sqrt_luUpper_apply i j

end NLAlib.Cholesky
