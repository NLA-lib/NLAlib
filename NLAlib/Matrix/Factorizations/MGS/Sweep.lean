/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Reduce
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# A modified Gram–Schmidt sweep

`NLAlib.MGS.sweepRoutine` is `[n, k] (Q : k * n, v : n) → (v, unreported r : 1)`: it reduces the
vector `v` in place against the first `k` columns of the packed matrix `Q`, with the scalar cell
`r` as scratch. It is a routine, not a fragment of one: in-place modified Gram–Schmidt
(`NLAlib.MGS.factorRoutine`) and the probe projection of Hutch++ both run it. Its operands are
separated by block, so `v` may be a later column of the buffer that holds `Q`. The loop follows the
mathematical recurrence `NLAlib.MGS.mgsSweep`, with no orthogonality or rank assumption.

## Main definitions

* `NLAlib.MGS.sweepRoutine`, `NLAlib.MGS.sweepSpec`.

## Main results

* `NLAlib.MGS.sweepRoutine_meets`: the sweep meets its specification.
* `NLAlib.MGS.sweep_writes`: the same, read with the columns of `Q` given one by one.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies the default of the column reads. -/
local instance instInhabitedSweep : Inhabited 𝕜 := ⟨0⟩

/-- At the dimensions `[n₀, k]`, for a matrix block whose first `k` columns are `Q 0, …, Q (k-1)`
and a vector `w`, the vector written is the sweep `mgsSweep Q w k`. -/
noncomputable def sweepSpec {n₀ : ℕ} (Q : ℕ → Fin n₀ → 𝕜) (w : Fin n₀ → 𝕜) : Routine.Spec 𝕜 :=
  spec% [n, k] (qs, vs) → (vs') requires
    n = n₀ ∧ (∀ i < k, (qs.drop (n * i)).take n = List.ofFn (Q i)) ∧ vs = List.ofFn w
  ensures vs' = List.ofFn (mgsSweep Q w k)

/-- The sweep meets its specification for every exact operation interpretation: it reduces `v`
against the columns of `Q` by the recurrence `mgsSweep`, with no orthogonality or rank
assumption. -/
theorem sweepRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n₀ : ℕ} (Q : ℕ → Fin n₀ → 𝕜) (w : Fin n₀ → 𝕜) :
    (sweepRoutine (Op := Op) (Tst := Tst)).Meets I (sweepSpec Q w) := by
  routine_intro [n, k] (q, v, r) reads (qs, vs)
  obtain ⟨rfl, hcols, rfl⟩ := hpre
  have hQ : ∀ i < k, m.store.readBlock q.1 (q.2 + n * i) n = some (List.ofFn (Q i)) :=
    fun i hi => (Store.readBlock_column hqs hi).trans (by rw [hcols i hi])
  obtain ⟨hvr, hvq, hrq⟩ : Fp.Disj (Store.inBlock v.1 v.2 n) (Store.inBlock r.1 r.2 1) ∧
      Fp.Disj (Store.inBlock v.1 v.2 n) (Store.inBlock q.1 q.2 (k * n)) ∧
      Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock q.1 q.2 (k * n)) := by
    obtain ⟨hw, hwq, -⟩ := hblocks
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_left, Fp.disj_sup_right,
      Fp.disj_bot_left, Fp.disj_bot_right, and_true] at hw hwq
    exact ⟨hw, hwq.1, hwq.2⟩
  have hcol : ∀ i < k, Store.inBlock q.1 (q.2 + n * i) n ≤ Store.inBlock q.1 q.2 (k * n) := by
    intro i hi
    have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ, Nat.mul_comm n k] at hm
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  have hrun : Writes .total I τ sweep (Env.frame [n, k] [q, v, r])
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn (mgsSweep Q w k))) m := by
    unfold sweep
    refine writes_loop rfl (fun _ => Store.inBlock r.1 r.2 1 ⊔
      Store.inBlock v.1 v.2 n) (fun _ _ => le_rfl)
      (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn (mgsSweep Q w i))) ⟨rfl, hvs⟩ ?_
    intro i hi m' hfr ⟨hp, hvec⟩
    have hdis : Fp.Disj (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
        (Store.inBlock q.1 (q.2 + n * i) n) :=
      Fp.disj_sup_left.mpr ⟨hrq.mono le_rfl (hcol i hi), hvq.mono le_rfl (hcol i hi)⟩
    have hcolm := hfr.keep (Store.readsOnly_readBlock q.1 (q.2 + n * i) n
      (List.ofFn (Q i))) hdis (hQ i hi)
    have hl' : m'.Live [(q.1, q.2 + n * i), v, r] := by
      simpa only [Mem.live_cons, Mem.live_nil] using hlive.congr hfr.length_eq
    refine writes_frame rfl rfl hl' ?_
    refine (reduce_writes hS hB (List.ofFn (Q i)) (List.ofFn (mgsSweep Q w i))
      hl' hcolm hvec (hdis.mono le_sup_left le_rfl) hvr.symm
      (Or.inl ((hdis.mono le_sup_right le_rfl).symm))
      (by simpa only [hfr.len_eq] using hroom.2)
      (by simpa only [hfr.len_eq] using hroom.1)).mono le_rfl ?_
    intro m'' _ ⟨hp', hv'⟩
    refine ⟨hp'.trans hp, ?_⟩
    change m''.store.readBlock v.1 v.2 n = some (List.ofFn fun a : Fin n =>
      mgsSweep Q w i a - (star (Q i) ⬝ᵥ mgsSweep Q w i) * Q i a)
    simpa [RCLikeBlas.dot_ofFn, List.getD_eq_getElem?_getD, dotProduct] using hv'
  refine hrun.mono (by fp_sub) ?_
  rintro μ' - ⟨hpos, hread⟩
  routine_exit
  rfl

/-- The sweep with the columns of `Q` given one by one, as the trees that run it hold them: the
column loop of `NLAlib.MGS.factorRoutine` and the probe projection of Hutch++ keep their basis
as a list of column facts. It is the judgment `NLAlib.MGS.sweepRoutine_meets` at the block of the
first `k` columns. -/
theorem sweep_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n k : ℕ} {q v r : ℕ × ℕ}
    (Q : ℕ → Fin n → 𝕜) (w : Fin n → 𝕜) (hl : m.Live [q, v, r])
    (hQ : ∀ i < k, m.store.readBlock q.1 (q.2 + n * i) n = some (List.ofFn (Q i)))
    (hv : m.store.readBlock v.1 v.2 n = some (List.ofFn w))
    (hdis : ∀ i < k, Fp.Disj
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (Store.inBlock q.1 (q.2 + n * i) n))
    (hrv : Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock v.1 v.2 n))
    (hr : r.2 + 1 ≤ m.store.len r.1) (hz : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ sweep (Env.frame [n, k] [q, v, r])
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn (mgsSweep Q w k))) m := by
  have hqs := Store.readBlock_columns (cols := fun i => List.ofFn (Q i)) hQ
  have hQdis := Fp.disj_columns_block hdis
  have hvq : Fp.Disj (Store.inBlock v.1 v.2 n) (Store.inBlock q.1 q.2 (k * n)) :=
    (Fp.disj_sup_left.mp hQdis).2
  have hrq : Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock q.1 q.2 (k * n)) :=
    (Fp.disj_sup_left.mp hQdis).1
  have hvr : Fp.Disj (Store.inBlock v.1 v.2 n) (Store.inBlock r.1 r.2 1) := hrv.symm
  have h := sweepRoutine_meets (Op := Op) (Tst := Tst) hS hB Q w [n, k] [q, v, r] τ m
    [(List.range k).flatMap fun i => List.ofFn (Q i), List.ofFn w] rfl rfl hl
    (by routine_sep)
    (by routine_nf; exact Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hv rfl))
    ⟨rfl, fun i hi => by
      rw [← Option.some.injEq, ← Store.readBlock_column hqs hi, hQ i hi], rfl⟩
    (by routine_nf; exact ⟨hz, hr, trivial⟩)
  refine (h.mono (by routine_nf; fp_sub) ?_)
  rintro μ' - ⟨hpos, ys, hys, hpost⟩
  routine_nf at hys
  split_reads hys as (vs')
  refine ⟨by simpa [Routine.Advances, sweepRoutine] using hpos, ?_⟩
  rw [hvs']
  exact congrArg some hpost

end NLAlib.MGS
