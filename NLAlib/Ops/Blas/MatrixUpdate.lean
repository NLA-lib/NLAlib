/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.MatrixSubtract
public import NLAlib.Ops.Blas.MatrixMultiplyExact
public import NLAlib.Ops.Blas.Dot

/-!
# Packed scalar matrix-product corrections

Pack the two rectangular inputs, compute their complete scalar matrix product, and subtract
it from a strided destination. Caller-owned workspaces can be reused across panels. The
operation tree consists of the shared scalar copy, product, and subtraction routines; no
matrix-product primitive or assumed whole-algorithm result enters its contract.

## Main results

* `NLAlib.Ops.ScalarMatrix.updateWithScratch_meets`: the actual packed scalar correction.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarMatrix

open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Compute and subtract a scalar matrix-product correction, reusing three caller-owned
workspaces. Updated and workspace buffers are separate from the read-only input views. -/
def updateWithScratch : Routine Op Tst :=
  routine% [rows, inner, cols, lda, ldb, ldr]
      (A : rows × inner every lda, B : inner × cols every ldb,
        R : rows × cols every ldr) →
      (R, unreported AP : rows * inner, unreported BP : inner * cols,
        unreported C : rows * cols) {
    run copyMatrixRoutine [rows, inner, lda, rows] (A, AP);
    run copyMatrixRoutine [inner, cols, ldb, inner] (B, BP);
    run multiply [rows, inner, cols] (AP, BP, C);
    run subtractMatrixRoutine [rows, cols, ldr] (C, R)
  }

variable [Inhabited K]

/-- The output words subtract the actual scalar product from the original destination
words. Only nonoverlapping logical destination columns are required of the dimensions. -/
def updateSpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, inner, cols, _lda, _ldb, ldr] (as, bs, rs) → (ts)
    requires (0 < cols * rows → rows ≤ ldr) ensures
    ts = (List.range (cols * rows)).map fun i => M.sub (vec rs i)
      (vec ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)) i)

/-- The actual scalar packing, multiplication, and subtraction routines satisfy the same
word specification under every scalar machine, including empty shapes. -/
theorem updateWithScratch_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (updateWithScratch (Op := Op) (Tst := Tst)).Meets I (updateSpec M) := by
  routine_intro [rows, inner, cols, lda, ldb, ldr] (A, B, R, AP, BP, C) reads (as, bs, rs)
  call (copyMatrixRoutine_meets hI) [rows, inner, lda, rows] (A, AP)
    as m₁ hfr₁ hpos₁ (aps) hcopyA
  case' hcall => exact [as]
  case' hr => exact Mem.readViews_of_cons has rfl
  case' hpre => exact fun _ => le_rfl
  case' hroom =>
    change (⟨rows, some (inner, rows)⟩ : View).Fits AP.2 (m.store.len AP.1) ∧ True
    refine ⟨?_, trivial⟩
    intro q hq
    simp only [View.offset_packedMatrix]
    have hq' : q < inner * rows := hq
    nlinarith [hroom.2.1]
  simp only [Store.readView_packedMatrix] at haps
  simp only [Fp.views, Fp.inView_packedMatrix, sup_bot_eq] at hfr₁
  have hcopyA' : aps = as := hcopyA
  subst aps
  have hbs₁ : m₁.store.readView B.1 B.2 ⟨inner, some (cols, ldb)⟩ = some bs :=
    hfr₁.keep (Store.readsOnly_readView _ _ _ _) (Fp.disj_inView_inBlock_of_ne hBAP).symm hbs
  have hrs₁ : m₁.store.readView R.1 R.2 ⟨rows, some (cols, ldr)⟩ = some rs :=
    hfr₁.keep (Store.readsOnly_readView _ _ _ _) (Fp.disj_inView_inBlock_of_ne hRAP).symm hrs
  call (copyMatrixRoutine_meets hI) [inner, cols, ldb, inner] (B, BP)
    as m₂ hfr₂ hpos₂ (bps) hcopyB
  case' hcall => exact [bs]
  case' hr => exact Mem.readViews_of_cons hbs₁ rfl
  case' hpre => exact fun _ => le_rfl
  case' hroom =>
    change (⟨inner, some (cols, inner)⟩ : View).Fits BP.2 (m₁.store.len BP.1) ∧ True
    refine ⟨?_, trivial⟩
    intro q hq
    simp only [View.offset_packedMatrix]
    rw [hfr₁.len_eq]
    have hq' : q < cols * inner := hq
    nlinarith [hroom.2.2.1]
  simp only [Store.readView_packedMatrix] at hbps
  simp only [Fp.views, Fp.inView_packedMatrix, sup_bot_eq] at hfr₂
  have hcopyB' : bps = bs := hcopyB
  subst bps
  have haps₂ : m₂.store.readBlock AP.1 AP.2 (rows * inner) = some as := by keep
  have hrs₂ : m₂.store.readView R.1 R.2 ⟨rows, some (cols, ldr)⟩ = some rs :=
    hfr₂.keep (Store.readsOnly_readView _ _ _ _) (Fp.disj_inView_inBlock_of_ne hRBP).symm hrs₁
  call (multiply_meets hI) [rows, inner, cols] (AP, BP, C)
    as m₃ hfr₃ hpos₃ (cs) hproduct
  have hp : cs = (EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs) :=
    hproduct
  have hrs₃ : m₃.store.readView R.1 R.2 ⟨rows, some (cols, ldr)⟩ = some rs :=
    hfr₃.keep (Store.readsOnly_readView _ _ _ _)
      (by simpa only [Fp.blocks, sup_bot_eq] using
        (Fp.disj_inView_inBlock_of_ne hRC).symm) hrs₂
  call (subtractMatrixRoutine_meets hI) [rows, cols, ldr] (C, R)
    (pre := hpre) as m₄ hfr₄ hpos₄ (ts) hsubtract
  case' hcall => exact [cs, rs]
  case' hr =>
    change m₃.readViews [C, R] [View.block (rows * cols), ⟨rows, some (cols, ldr)⟩] = some _
    exact Mem.readViews_of_cons (by simpa using hcs) (Mem.readViews_of_cons hrs₃ rfl)
  case' hpre => exact hpre
  refine ⟨by omega, [ts], Mem.readViews_of_cons hts rfl, ?_⟩
  change ts = _
  rw [hsubtract, hp]

omit [Has ScalarOp Op] in
/-- Exact decoded arithmetic turns the actual packed scalar correction into the usual
matrix-product update. No list-length, rank, or execution premise is required. -/
theorem updateSpec_decode {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {rows inner cols lda ldb ldr : ℕ} {as bs rs ts : List K} {τ : Tape K}
    (hpost : (updateSpec M).post [rows, inner, cols, lda, ldb, ldr] τ [as, bs, rs] [ts]) :
    decodeMatrix dec rows cols ts = decodeMatrix dec rows cols rs -
      decodeMatrix dec rows inner as * decodeMatrix dec inner cols bs := by
  have hts : ts = (List.range (cols * rows)).map fun i => M.sub (vec rs i)
      (vec ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)) i) := hpost
  have hprod : decodeMatrix dec rows cols
      ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)) =
      decodeMatrix dec rows inner as * decodeMatrix dec inner cols bs := by
    rw [decodeMatrix, EntryCodec.matrix_packFinMatrix]
    exact map_wordMatrix hM rows inner cols as bs
  rw [← hprod]
  ext i j
  simp only [Matrix.sub_apply, decodeMatrix_apply, hts,
    vec_map_range _ (Idx.add_lt_mul j.isLt i.isLt), hM.sub]

/-- Compute a matrix-product correction with scoped packed operands and product storage.
Only logical destination cells remain changed after the workspaces are released. -/
def update : Routine Op Tst :=
  routine% [rows, inner, cols, lda, ldb, ldr]
      (A : rows × inner every lda, B : inner × cols every ldb,
        R : rows × cols every ldr) → (R) {
    let AP ← alloc (rows * inner);
    let BP ← alloc (inner * cols);
    let C ← alloc (rows * cols);
    run updateWithScratch [rows, inner, cols, lda, ldb, ldr] (A, B, R, AP, BP, C)
  }

/-- Scoped packing and cleanup preserve the same actual-word correction specification.
The fixed routine consists entirely of scalar kernels and restores every scratch buffer. -/
theorem update_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (update (Op := Op) (Tst := Tst)).Meets I (updateSpec M) := by
  routine_intro [rows, inner, cols, lda, ldb, ldr] (A, B, R) reads (as, bs, rs)
  change Writes .total I τ _ (Env.frame [rows, inner, cols, lda, ldb, ldr] [A, B, R, R])
    (Fp.views [R] [⟨rows, some (cols, ldr)⟩]) _ m
  alloc as AP BP C
  have hAAP : A.1 ≠ AP := by change A.1 ≠ m.store.length + 0; omega
  have hABP : A.1 ≠ BP := by change A.1 ≠ m.store.length + 1; omega
  have hAC : A.1 ≠ C := by change A.1 ≠ m.store.length + 2; omega
  have hBAP : B.1 ≠ AP := by change B.1 ≠ m.store.length + 0; omega
  have hBBP : B.1 ≠ BP := by change B.1 ≠ m.store.length + 1; omega
  have hBC : B.1 ≠ C := by change B.1 ≠ m.store.length + 2; omega
  have hRAP : R.1 ≠ AP := by change R.1 ≠ m.store.length + 0; omega
  have hRBP : R.1 ≠ BP := by change R.1 ≠ m.store.length + 1; omega
  have hRC : R.1 ≠ C := by change R.1 ≠ m.store.length + 2; omega
  have hAPBP : AP ≠ BP := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hAPC : AP ≠ C := by change m.store.length + 0 ≠ m.store.length + 2; omega
  have hBPC : BP ≠ C := by change m.store.length + 1 ≠ m.store.length + 2; omega
  have has₀ := Store.Below.readView_of hbelow_AP hl.1 has
  have hbs₀ := Store.Below.readView_of hbelow_AP hl.2.1 hbs
  have hrs₀ := Store.Below.readView_of hbelow_AP hl.2.2 hrs
  have hrroom : (⟨rows, some (cols, ldr)⟩ : View).Fits R.2 (s_AP.len R.1) := by
    rw [(hbelow_AP R.1 hl.2.2).1]
    exact hroom
  call (updateWithScratch_meets hI) [rows, inner, cols, lda, ldb, ldr]
    (A, B, R, (AP, 0), (BP, 0), (C, 0)) (pre := hpre)
    as m₁ hfr₁ hpos₁ (ts) hpost
  case' hr =>
    exact Mem.readViews_of_cons has₀ (Mem.readViews_of_cons hbs₀
      (Mem.readViews_of_cons hrs₀ rfl))
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change A.1 < s_AP.length ∧ B.1 < s_AP.length ∧ R.1 < s_AP.length ∧
      m.store.length < s_AP.length ∧ m.store.length + 1 < s_AP.length ∧
      m.store.length + 2 < s_AP.length
    simp only [List.length_cons, List.length_nil] at hlen_AP
    omega
  case' hroom =>
    change (⟨rows, some (cols, ldr)⟩ : View).Fits R.2 (s_AP.len R.1) ∧
      (0 + rows * inner ≤ s_AP.len AP) ∧ (0 + inner * cols ≤ s_AP.len BP) ∧
      (0 + rows * cols ≤ s_AP.len C) ∧ True
    exact ⟨hrroom, by simpa only [Nat.zero_add] using hAP.ge,
      by simpa only [Nat.zero_add] using hBP.ge,
      by simpa only [Nat.zero_add] using hC.ge, trivial⟩
  intro s₂ hs₂ hB₂
  refine ⟨by omega, [ts], Mem.readViews_of_cons ?_ rfl, hpost⟩
  exact Store.Below.readView_of hB₂ hl.2.2 hts

end NLAlib.Ops.ScalarMatrix
