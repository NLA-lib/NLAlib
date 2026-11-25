/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames

/-!
# Execution of strided writes

A loop that writes consecutive members of a positive-stride address sequence retains every
other cell, including cells between the written addresses. The result is independent of
scalar arithmetic and applies to both exact and rounded analyses of stored kernels.

## Main results

* `NLAlib.Computation.exec_strided_writes`: successful strided execution, shape and full frame.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- If every iteration succeeds and writes its specified word at one address of a
positive-stride sequence, the actual loop succeeds, initializes that sequence and preserves
the original shape and all other cells. Each iteration may use the current shape and the
unchanged cells outside the target buffer. The word carrier, scalar semantics and charge
monoid are arbitrary. Empty loops impose no buffer capacity requirement. -/
theorem exec_strided_writes (I : Interp P ι K C) (p : P) (st : St P K C)
    (len : IExp ℕ) (U base stride : ℕ) (hstride : 0 < stride)
    (value : ℕ → K) (body : ℕ → Builder P ι ℕ ℕ Unit)
    (hstep : ∀ i < len.eval, ∀ σ : St P K C, σ.store.shape = st.store.shape →
      (∀ q b j, b ≠ U → σ.store.read q b j = st.store.read q b j) →
      ∃ out, exec I (body i).run σ = some out ∧
        σ.store.write p U (base + stride * i) (value i) = some out.store) :
    ∃ out, exec I (.loop len fun i => (body i).run) st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < len.eval, out.store.read p U (base + stride * i) = some (value i)) ∧
      ∀ q b j, (b ≠ U ∨ ∀ i < len.eval, j ≠ base + stride * i) →
        out.store.read q b j = st.store.read q b j := by
  let R := fun t (σ : St P K C) => σ.store.shape = st.store.shape ∧
    (∀ i < t, σ.store.read p U (base + stride * i) = some (value i)) ∧
    ∀ q b j, (b ≠ U ∨ ∀ i < t, j ≠ base + stride * i) →
      σ.store.read q b j = st.store.read q b j
  have h0 : R 0 st := ⟨rfl, fun _ hi => (Nat.not_lt_zero _ hi).elim,
    fun _ _ _ _ => rfl⟩
  exact exists_exec_loop_eq_some_of_forall I R h0 (fun t ht σ hR => by
    obtain ⟨hshape, hread, hframe⟩ := hR
    obtain ⟨out, hr, hw⟩ := hstep t ht σ hshape (fun q b j hb => hframe q b j (Or.inl hb))
    refine ⟨out, hr, (Store.shape_of_write_eq_some hw).trans hshape, ?_, ?_⟩
    · intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hit
      · exact Store.read_of_write_eq_some hw
      · have haddr : base + stride * i < base + stride * t :=
          Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hit hstride) base
        rw [Store.read_of_write_eq_some_of_ne hw (Or.inr haddr.ne), hread i hit]
    · intro q b j hj
      have hne : b ≠ U ∨ j ≠ base + stride * t := hj.imp_right (fun hh => hh t (by omega))
      rw [Store.read_of_write_eq_some_of_ne hw hne]
      exact hframe q b j (hj.imp_right (fun hh i hi => hh i (by omega))))


end NLAlib.Computation
