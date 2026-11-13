/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Normalize
public import NLAlib.Matrix.Factorizations.MGS.Sweep
public import NLAlib.Ops.Logic.EntryColumn
public import NLAlib.Ops.Logic.Allocation

/-!
# Full in-place rank-revealing MGS

The column loop follows the mathematical matrix with completed Gram–Schmidt columns
and unchanged original columns. Its invariant uses ordinary packed matrix storage.

## Main results

The local column lemmas connect the pure residual identity to the shared sweep,
normalization and column-frame rules.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜]

/-- Zero supplies the raw word padding convention for the matrix layout. -/
local instance instInhabitedFactor : Inhabited 𝕜 := ⟨0⟩

private noncomputable def stage {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) (j i c : ℕ) : 𝕜 :=
  if hi : i < n then
    if hc : c < k then
      if c < j then gramSchmidtQ A ⟨i, hi⟩ ⟨c, hc⟩ else A ⟨i, hi⟩ ⟨c, hc⟩
    else 0
  else 0

private theorem stage_zero_pack {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) :
    (EntryCodec.scalar 𝕜).packMatrix n k (stage A 0) =
      (EntryCodec.scalar 𝕜).packFinMatrix A := by
  rw [← EntryCodec.packFinMatrix_eq_packMatrix]
  congr 1
  ext i j
  simp [stage]

private theorem stage_final_pack {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) :
    (EntryCodec.scalar 𝕜).packMatrix n k (stage A k) =
      (EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ A) := by
  rw [← EntryCodec.packFinMatrix_eq_packMatrix]
  congr 1
  ext i j
  simp [stage]

private theorem read_stage_column {n k j c : ℕ} {A : Matrix (Fin n) (Fin k) 𝕜}
    {s : Store 𝕜} {y : ℕ × ℕ}
    (hs : s.HoldsEntries (EntryCodec.scalar 𝕜) ⟨y.1, y.2, n, k, n⟩ (stage A j))
    (hc : c < k) :
    s.readBlock y.1 (y.2 + n * c) n = some (List.ofFn fun i : Fin n =>
      if c < j then gramSchmidtQ A i ⟨c, hc⟩ else A i ⟨c, hc⟩) := by
  have h := hs.readBlock_column hc
  simpa [EntryCodec.scalar_pack, stage, EntryCodec.scalar, Nat.mul_comm, hc] using h

private theorem stage_update {n k j : ℕ} {A : Matrix (Fin n) (Fin k) 𝕜}
    {s s' : Store 𝕜} {y t : ℕ × ℕ} (hj : j < k)
    (hs : s.HoldsEntries (EntryCodec.scalar 𝕜) ⟨y.1, y.2, n, k, n⟩ (stage A j))
    (ht : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 y.2 (k * n)))
    (hfr : s.EqOff (Store.inBlock y.1 (y.2 + n * j) n ⊔
      Store.inBlock t.1 t.2 2) s')
    (hcol : s'.readBlock y.1 (y.2 + n * j) n =
      some (List.ofFn ((gramSchmidtQ A).col ⟨j, hj⟩))) :
    s'.HoldsEntries (EntryCodec.scalar 𝕜) ⟨y.1, y.2, n, k, n⟩ (stage A (j + 1)) := by
  let v : ℕ → 𝕜 := fun i => if hi : i < n then gramSchmidtQ A ⟨i, hi⟩ ⟨j, hj⟩ else 0
  have hv : s'.readBlock y.1 (y.2 + n * j) n =
      some ((EntryCodec.scalar 𝕜).pack n v) := by
    change s'.readBlock y.1 (y.2 + n * j) n =
      some (List.ofFn fun i : Fin n => gramSchmidtQ A i ⟨j, hj⟩) at hcol
    simpa [EntryCodec.scalar_pack, v] using hcol
  have hu := hs.update_column_of_frame (by exact le_rfl) (by simpa [EntryCodec.scalar] using ht)
    (by simpa [EntryCodec.scalar, Nat.mul_comm] using hfr) v
    (by simpa [EntryCodec.scalar, Nat.mul_comm] using hv)
  intro i hi c hc z
  have h := hu i hi c hc z
  by_cases he : c = j
  · subst c
    simpa [stage, v, hi, hj] using h
  · have he' : (c < j + 1) = (c < j) := propext (by omega)
    simpa [stage, v, hi, hc, he, he'] using h

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- One full column step produces its Gram–Schmidt column at every rank, using
readable preceding columns and a disjoint two-cell scalar workspace. -/
theorem writes_factorColumn (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n k j : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) (hj : j < k) {y t : ℕ × ℕ}
    (hl : m.Live [y, t])
    (hQ : ∀ i (hi : i < j), m.store.readBlock y.1 (y.2 + n * i) n =
      some (List.ofFn ((gramSchmidtQ A).col ⟨i, hi.trans hj⟩)))
    (hv : m.store.readBlock y.1 (y.2 + n * j) n = some (List.ofFn (A.col ⟨j, hj⟩)))
    (hdis : ∀ i < j, Fp.Disj
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock y.1 (y.2 + n * j) n)
      (Store.inBlock y.1 (y.2 + n * i) n))
    (htv : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 (y.2 + n * j) n))
    (ht : t.2 + 2 ≤ m.store.len t.1)
    (hz : y.2 + n * j + n ≤ m.store.len y.1) :
    Writes .total I τ factorColumn.body (Env.frame [n, j] [y, t])
      (Store.inBlock y.1 (y.2 + n * j) n ⊔ Store.inBlock t.1 t.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 (y.2 + n * j) n =
        some (List.ofFn ((gramSchmidtQ A).col ⟨j, hj⟩))) m := by
  let Q : ℕ → Fin n → 𝕜 := fun c a =>
    if hc : c < k then gramSchmidtQ A a ⟨c, hc⟩ else 0
  have hQ' : ∀ i < j, m.store.readBlock y.1 (y.2 + n * i) n = some (List.ofFn (Q i)) := by
    intro i hi
    have hh := hQ i hi
    change m.store.readBlock y.1 (y.2 + n * i) n =
      some (List.ofFn fun a : Fin n => gramSchmidtQ A a ⟨i, hi.trans hj⟩) at hh
    simpa [Q, hi.trans hj] using hh
  have ht₀ : Store.inBlock t.1 t.2 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have hl₃ : m.Live [y, (y.1, y.2 + n * j), t] := by
    simpa only [Mem.live_cons, Mem.live_nil] using
      And.intro (hl y (by simp)) ⟨hl y (by simp), hl t (by simp), trivial⟩
  unfold factorColumn
  dsimp only
  refine Writes.seq_le ((writes_sweep hS hB Q (A.col ⟨j, hj⟩) hl₃ hQ' hv hdis
    (htv.mono ht₀ le_rfl) (by omega) hz).in_frame rfl rfl hl₃)
    (sup_le (ht₀.trans le_sup_right) le_sup_left) ?_
  intro m₁ hfr ⟨hp, hv₁⟩
  have hv₁' : m₁.store.readBlock y.1 (y.2 + n * j) n = some (List.ofFn
      (gramSchmidtR A ⟨j, hj⟩ ⟨j, hj⟩ • (gramSchmidtQ A).col ⟨j, hj⟩)) := by
    simpa only [Q, mgsSweep_gramSchmidtQ A j hj] using hv₁
  have hl₂ : m₁.Live [(y.1, y.2 + n * j), t] := by
    simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hfr.length_eq
  refine ((writes_normalize_residual hS hB hC ((gramSchmidtQ A).col ⟨j, hj⟩)
    (gramSchmidtR A ⟨j, hj⟩ ⟨j, hj⟩) (gramSchmidtR_apply_self_nonneg A _)
    (fun h => (gramSchmidtQ_col_eq_zero_iff A _).mpr h)
    (fun h => by rw [dotProduct_gramSchmidtQ_col, if_pos rfl, if_neg h])
    hl₂ hv₁' htv (by simpa only [hfr.len_eq] using ht)
    (by simpa only [hfr.len_eq] using hz)).in_frame rfl rfl hl₂).mono
      (by exact sup_le le_sup_right le_sup_left) ?_
  intro m₂ _ ⟨hp₂, hv₂⟩
  exact ⟨hp₂.trans hp, hv₂⟩

/-- The full rank-revealing column loop computes the existing mathematical
`gramSchmidtQ` for every matrix, using caller-owned disjoint scalar workspace. -/
theorem writes_factorWithScratch (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) {y t : ℕ × ℕ}
    (hl : m.Live [y, t])
    (hA : m.store.readBlock y.1 y.2 (k * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix A))
    (hty : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 y.2 (k * n)))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hy : y.2 + k * n ≤ m.store.len y.1) :
    Writes .total I τ factorWithScratch.body (Env.frame [n, k] [y, t])
      (Store.inBlock y.1 y.2 (k * n) ⊔ Store.inBlock t.1 t.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 (k * n) =
        some ((EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ A))) m := by
  have hcol : ∀ j < k, Store.inBlock y.1 (y.2 + n * j) n ≤
      Store.inBlock y.1 y.2 (k * n) := by
    intro j hj
    have hb := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ, Nat.mul_comm n k] at hb
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  have hs : m.store.HoldsEntries (EntryCodec.scalar 𝕜) ⟨y.1, y.2, n, k, n⟩
      (stage A 0) := Store.holdsEntries_of_readBlock_packMatrix rfl
        (by simpa [EntryCodec.scalar, stage_zero_pack] using hA)
  unfold factorWithScratch
  dsimp only
  refine (writes_loop rfl (fun _ => Store.inBlock y.1 y.2 (k * n) ⊔
    Store.inBlock t.1 t.2 2) (fun _ _ => le_rfl)
    (fun j m' => m'.pos = m.pos ∧ m'.store.HoldsEntries (EntryCodec.scalar 𝕜)
      ⟨y.1, y.2, n, k, n⟩ (stage A j)) ⟨rfl, hs⟩ ?_).mono le_rfl ?_
  · intro j hj m' hfr ⟨hp, hs'⟩
    have hl' := hl.congr hfr.length_eq
    have hQ : ∀ i (hi : i < j), m'.store.readBlock y.1 (y.2 + n * i) n =
        some (List.ofFn ((gramSchmidtQ A).col ⟨i, hi.trans hj⟩)) := by
      intro i hi
      have hc := read_stage_column hs' (hi.trans hj)
      change _ = some (List.ofFn fun a : Fin n => gramSchmidtQ A a ⟨i, hi.trans hj⟩)
      simpa only [if_pos hi] using hc
    have hv : m'.store.readBlock y.1 (y.2 + n * j) n = some (List.ofFn (A.col ⟨j, hj⟩)) := by
      have hc := read_stage_column hs' hj
      change _ = some (List.ofFn fun a : Fin n => A a ⟨j, hj⟩)
      simpa only [lt_self_iff_false, if_false] using hc
    have hdis : ∀ i < j, Fp.Disj
        (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock y.1 (y.2 + n * j) n)
        (Store.inBlock y.1 (y.2 + n * i) n) := by
      intro i hi
      refine Fp.disj_sup_left.mpr ⟨hty.mono (Fp.inBlock_le_inBlock le_rfl (by omega))
        (hcol i (hi.trans hj)), ?_⟩
      simpa [EntryCodec.scalar, Nat.mul_comm] using
        (EntryCodec.scalar 𝕜).disj_columns (L := ⟨y.1, y.2, n, k, n⟩)
          (by exact le_rfl) (ne_of_gt hi)
    refine ((writes_factorColumn hS hB hC A hj hl' hQ hv hdis
      (hty.mono le_rfl (hcol j hj)) (by simpa only [hfr.len_eq] using ht)
      (by have hb := hcol j hj; have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
          rw [Nat.mul_succ, Nat.mul_comm n k] at hm
          rw [hfr.len_eq]; omega)).in_frame rfl rfl hl').mono
      (sup_le ((hcol j hj).trans le_sup_left) le_sup_right) ?_
    intro m'' hfr' ⟨hp', hc⟩
    exact ⟨hp'.trans hp, stage_update hj hs' hty hfr' hc⟩
  · intro m' _ ⟨hp, hs'⟩
    exact ⟨hp, by simpa [EntryCodec.scalar, stage_final_pack] using hs'.readBlock rfl⟩

/-- Full rank-revealing MGS is total on every readable matrix. Its two scalar scratch
cells are scoped, the caller's storage shape is preserved, and no rank assumption is needed. -/
theorem writes_factor (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) {y : ℕ × ℕ}
    (hl : m.Live [y])
    (hA : m.store.readBlock y.1 y.2 (k * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix A))
    (hy : y.2 + k * n ≤ m.store.len y.1) :
    Writes .total I τ factor.body (Env.frame [n, k] [y])
      (Store.inBlock y.1 y.2 (k * n))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 (k * n) =
        some ((EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ A))) m := by
  apply writes_allocs_readBlock (lens := [.const 2]) (ns := [2]) rfl (hl y (by simp))
  intro store hlength hlens hBelow
  have hyLive : y.1 < m.store.length := hl y (by simp)
  have ht : store.len m.store.length = 2 := by simpa using hlens 0 (by simp)
  have hNew : m.store.length < store.length :=
    Store.lt_length_of_lt_len (show 0 < store.len m.store.length by rw [ht]; omega)
  have hLive : (Mem.mk store m.pos).Live [y, (m.store.length, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega,
      hNew, trivial⟩
  refine ((writes_factorWithScratch hS hB hC A hLive (by kept)
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyLive)))
    (by simpa using ht.ge) (by simpa only [(hBelow y.1 hyLive).1] using hy)).in_frame
      rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)

end NLAlib.MGS
