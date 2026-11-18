/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward

/-!
# The rounded deflation worklist always terminates

The termination-only counterpart of `NLAlib.ShiftedQR.solveRounded_backward`: on every tape and
from every stored matrix, `NLAlib.ShiftedQR.solveRounded` runs to completion when its decoupler
and its leaf do (`NLAlib.ShiftedQR.TerminatingDecoupler`, `NLAlib.ShiftedQR.TerminatingLeaf`).
The proof follows the backward-error proof round by round with a value-free state: the views keep
their geometry, every word read is stored, and the stack holds nonempty ranges inside the order
whose sizes sum to at most the order, which leaves room for the two pushes of a split. The fuel
of the loop makes the run finite.

## Main definitions

* `NLAlib.ShiftedQR.RangesFit`: nonempty ranges inside the order, of total size at most it.
* `NLAlib.ShiftedQR.RoundedStoredState`: the value-free state between two rounds.

## Main results

* `NLAlib.ShiftedQR.solveRoundedWith_terminates`: one round keeps the value-free state.
* `NLAlib.ShiftedQR.solveRoundedWith_terminates`: the rounded worklist terminates.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- The ranges $(lo_j, d_j)$ fit in the order $N$: each has $d_j \ge 1$ and $lo_j + d_j \le N$,
and $\sum_j d_j \le N$. -/
def RangesFit (N : ℕ) (rs : List (ℕ × ℕ)) : Prop :=
  (∀ r ∈ rs, 1 ≤ r.2 ∧ r.1 + r.2 ≤ N) ∧ (rs.map Prod.snd).sum ≤ N

/-- If the ranges $(lo, d) :: rs$ fit in the order $N$ (each nonempty and inside, sizes summing
to at most $N$), then the number of ranges of $rs$ plus $d$ is at most $N$. -/
theorem RangesFit.length_add_le {N lo d : ℕ} {rs : List (ℕ × ℕ)}
    (h : RangesFit N ((lo, d) :: rs)) : rs.length + d ≤ N := by
  have hl := List.length_le_sum_of_one_le (rs.map Prod.snd) (by
    intro i hi
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
    exact (h.1 r (List.mem_cons_of_mem _ hr)).1)
  have hs := h.2
  simp only [List.length_map, List.map_cons, List.sum_cons] at hl hs
  omega

/-- If the ranges $x :: rs$ fit in the order $N$, so do the ranges $rs$. -/
theorem RangesFit.of_cons {N : ℕ} {x : ℕ × ℕ} {rs : List (ℕ × ℕ)} (h : RangesFit N (x :: rs)) :
    RangesFit N rs := by
  refine ⟨fun r hr => h.1 r (List.mem_cons_of_mem _ hr), ?_⟩
  have hs := h.2
  simp only [List.map_cons, List.sum_cons] at hs
  omega

/-- If the ranges $rs$ followed by $x$ fit in the order $N$, so do the ranges $x :: rs$. -/
theorem RangesFit.cons_of_concat {N : ℕ} {x : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    (h : RangesFit N (rs ++ [x])) : RangesFit N (x :: rs) := by
  refine ⟨fun r hr => h.1 r ?_, ?_⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    exacts [List.mem_append_right _ (List.mem_singleton_self _), List.mem_append_left _ hr]
  · have hs := h.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hs ⊢
    omega

/-- If the ranges $(lo, d) :: rs$ fit in the order $N$ and $i + 1 < d$, then so do the ranges
$rs$ followed by the two children $(lo + i + 1, d - i - 1)$ and $(lo, i + 1)$ of the split. -/
theorem RangesFit.split {N lo d i : ℕ} {rs : List (ℕ × ℕ)} (h : RangesFit N ((lo, d) :: rs))
    (hi : i + 1 < d) : RangesFit N (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) := by
  have h0 := h.1 (lo, d) List.mem_cons_self
  dsimp only at h0
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact h.1 r (List.mem_cons_of_mem _ hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega
  · have hs := h.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hs ⊢
    omega

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded worklist in Schur mode terminates, and its accumulator stays near a unitary on
every tape**: on a scalar machine with the standard model, natural literals up to $n + 1$ exact,
exact `toNat` and comparisons, let the decoupling routine terminate with a closed log
(`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) and the leaf routine terminate with an
accumulator within $\varepsilon_L$ of a unitary on orders at most $\min(k, n + 1)$
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`). Then for any matrix $\mathbf{H}$ and accumulator
$\mathbf{U}$, any threshold word and on every tape, `solveRoundedWith D L` runs to completion,
writes only the matrix, the accumulator and the failure word, and the stored accumulator is
within $((1 + 24\boldsymbol{u})^{2(n+1)(n_s w + 2k(k+2))}(1 + \varepsilon_L)^{n+1} - 1)
\|\mathbf{U}\|_2$ of $\mathbf{U}\mathbf{V}$ for an exact unitary $\mathbf{V}$, whatever the
shifts (each replayed rotation and each leaf product is a near-unitary update). -/
theorem solveRoundedWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w : ℕ} {ps : List ℝ} {εL : ℝ} (hεL : 0 ≤ εL) (D : Impl O Q)
    (hD : TerminatingDecouplerRoutine n k F T ps ns w D I) (L : Impl O Q)
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p uo f : ℕ × ℕ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU : HoldsMatrix uo U μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (solveRoundedWith D L).body
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ U' Tm V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (U' - U * V) ≤
          ((1 + 24 * u) ^ (2 * (n + 1) * (ns * w + 2 * k * (k + 2))) * (1 + εL) ^ (n + 1) - 1) *
            specNorm U) μ :=
  sorry

end Theorems

end NLAlib.ShiftedQR
