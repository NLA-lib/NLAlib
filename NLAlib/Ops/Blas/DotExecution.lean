/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Blas
public import NLAlib.Ops.Logic.Writes

/-!
# Exact word execution of sequential dot products

The actual dot-over-sum tree is linked with sequential summation. Its returned word
is the sequential sum of the actual rounded products, independently of any error model.

## Main results

* `NLAlib.Ops.wp_dotSum_seq`: the scalar-lowered kernel writes its exact word result.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- Sequential summation depends only on the first `n` supplied words. -/
theorem sumSeqF_congr (M : Machine K) {x y : ℕ → K} {n : ℕ}
    (h : ∀ i < n, x i = y i) : sumSeqF M x n = sumSeqF M y n := by
  cases n with
  | zero => rfl
  | succ n =>
    suffices seqF M x n = seqF M y n by simpa [sumSeqF] using this
    induction n with
    | zero => exact h 0 (by omega)
    | succ n ih =>
      simp only [seqF]
      rw [ih (fun i hi => h i (by omega)), h (n + 1) (by omega)]

variable [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op]
  [Inhabited K]

/-- The linked dot tree executes using only scalar contracts. Products and accumulations
are the actual machine operations; the only caller-visible update is the destination cell. -/
theorem wp_dotSum_seq {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x y z : ℕ × ℕ} {m : Mem K} {xs ys : List K}
    (hl : m.Live [x, y, z])
    (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : m.store.readBlock y.1 y.2 n = some ys)
    (hz : z.2 < m.store.len z.1) :
    Wp .total I τ (dotSum.body.link Blas.sumSeqTable) (Env.frame [n] [x, y, z])
      (fun m' => m' = m.upd z
        (sumSeqF M (fun i => M.mul (vec xs i) (vec ys i)) n)) m := by
  obtain ⟨hlx, hly, hlz⟩ :
      x.1 < m.store.length ∧ y.1 < m.store.length ∧ z.1 < m.store.length := by
    simpa using hl
  have hshape : (dotSum (Op := Op) (Tst := Tst)).body.link Blas.sumSeqTable =
      .alloc (.var 0)
        (.seq (prodLoop (.var 0) ⟨0, .var 1 + .var 4⟩ ⟨1, .var 2 + .var 4⟩ ⟨3, .var 4⟩)
          (.frame [.var 0] [⟨3, .const 0⟩, ⟨2, .var 3⟩] sumSeq.body)) := by
    simp [dotSum, Stmt.alloc, Stmt.link, prodLoop, Blas.sumSeqTable, Apart.proj_inj,
      Has.proj_inj, Impl.Fits, sumSeq]
  rw [hshape]
  refine wp_alloc rfl (wp_seq (wp_prodLoop hI (a := vec xs) (b := vec ys) rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hlx.ne hly.ne (by simp) ?_ ?_
    fun s' hfr hr => ?_))
  · exact fun k hk => by store_simp [Store.get_of_readBlock hx hk default]
  · exact fun k hk => by store_simp [Store.get_of_readBlock hy hk default]
  have hlen : s'.length = m.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlenz : s'.len z.1 = m.store.len z.1 := by
    rw [hfr.len_eq, Store.len_push_of_lt hlz]
  apply wp_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega,
      by omega, trivial⟩)
  refine wp_sumSeq hI (by omega : m.store.length ≠ z.1) hr (by rw [hlenz]; exact hz) ?_
  have hv := sumSeqF_congr M (n := n)
    (fun i hi => vec_map_range (fun k => M.mul (vec xs k) (vec ys k)) hi)
  simp only [hv, Mem.upd]
  rw [Store.pop_upd_of_lt (by omega), hfr.pop_eq]

end NLAlib.Ops
