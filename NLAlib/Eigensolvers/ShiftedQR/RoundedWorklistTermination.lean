/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveUpdates

/-!
# The value-free state of the Schur-mode worklist

The state that the termination proof of the rounded deflation worklist in Schur mode
(`NLAlib.ShiftedQR.solveRoundedWith_terminates`) follows from round to round, with no values:
the views keep their geometry, every word read is stored, the stack holds nonempty ranges inside
the order whose sizes plus the number of finished leaves sum to at most the order, and the stored
accumulator is near the input accumulator times a unitary, within a factor that grows with the
replays and the leaves. The large-block steps of a round keep it.

## Main definitions

* `NLAlib.ShiftedQR.RangesFit`: nonempty ranges inside the order, of total size at most it.
* `NLAlib.ShiftedQR.SchurGeometry`, `NLAlib.ShiftedQR.schurRoundFp`: the views and the writes of
  a round.
* `NLAlib.ShiftedQR.AccumNear`: a stored accumulator near $\mathbf{U}$ times a unitary.
* `NLAlib.ShiftedQR.SchurStoredState`: the value-free state between two rounds.

## Main results

* `NLAlib.ShiftedQR.roundedSplitUpdate_core`, `NLAlib.ShiftedQR.roundedLargeRest_terminates`,
  `NLAlib.ShiftedQR.roundedLarge_terminates`: the large-block steps keep the state.
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

/-- The regions a round of the rounded worklist in Schur mode may write: the matrix, the
accumulator, the failure word, the stack, the work matrix, the leaf accumulator and the scan
registers. -/
def schurRoundFp (N : ℕ) (a uo f st w ub r : ℕ × ℕ) : Fp :=
  Fp.blocks [a, uo, f, st, w, ub, r]
    [2 * (N * N), 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5]

/-- **The separation of the five operand views** of the rounded shifted QR algorithm (matrix,
threshold word, parameter words, accumulator, failure word): every view is apart from the three
written ones (matrix, accumulator, failure word). The threshold word and the parameter words are
only read, so they may overlap each other; no pair of blocks is required apart beyond that. -/
def ShQRViewsApart (N np : ℕ) (a t p uo f : ℕ × ℕ) : Prop :=
  Fp.Apart [a, t, uo, f] [2 * (N * N), 1, 2 * (N * N), 1] ∧
    Fp.Apart [a, p, uo, f] [2 * (N * N), np, 2 * (N * N), 1]

/-- Five views that are pairwise apart are separated. -/
theorem ShQRViewsApart.of_apart {N np : ℕ} {a t p uo f : ℕ × ℕ}
    (h : Fp.Apart [a, t, p, uo, f] [2 * (N * N), 1, np, 2 * (N * N), 1]) :
    ShQRViewsApart N np a t p uo f := by
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq,
    Fp.disj_bot_right, and_true] at h
  simp only [ShQRViewsApart, Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
    sup_bot_eq, Fp.disj_bot_right, and_true]
  tauto

/-- The nine views of the rounded worklist in Schur mode (matrix, threshold, parameters,
accumulator, failure word, stack, work matrix, leaf accumulator, scan registers) are live, have
room and are apart, except that the threshold word and the parameter words, which no round
writes, may overlap each other: the geometry (`NLAlib.Ops.Geometry`) of the views without the
parameter words, and that of the views without the threshold word. -/
structure SchurGeometry (N np : ℕ) (a t p uo f st w ub r : ℕ × ℕ) (μ : Mem ℝ) : Prop where
  /-- The geometry of the views other than the parameter words. -/
  thr : Geometry [a, t, uo, f, st, w, ub, r]
    [2 * (N * N), 1, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] μ
  /-- The geometry of the views other than the threshold word. -/
  par : Geometry [a, p, uo, f, st, w, ub, r]
    [2 * (N * N), np, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] μ

namespace SchurGeometry

variable {N np : ℕ} {a t p uo f st w ub r : ℕ × ℕ} {μ μ' : Mem ℝ}

/-- All nine views are live. -/
theorem live (h : SchurGeometry N np a t p uo f st w ub r μ) :
    μ.Live [a, t, p, uo, f, st, w, ub, r] := by
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.par.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)
  · exact h.thr.live _ (by simp)

/-- Each of the nine views has room for its length. -/
theorem room (h : SchurGeometry N np a t p uo f st w ub r μ) :
    μ.Room [a, t, p, uo, f, st, w, ub, r]
      [2 * (N * N), 1, np, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] :=
  ⟨h.thr.room.1, h.thr.room.2.1, h.par.room.2.1, h.thr.room.2.2⟩

/-- Any list of the views is live. -/
theorem live_of_subset (h : SchurGeometry N np a t p uo f st w ub r μ) {l : List (ℕ × ℕ)}
    (hl : ∀ x ∈ l, x ∈ [a, t, p, uo, f, st, w, ub, r]) : μ.Live l :=
  fun x hx => h.live x (hl x hx)

/-- The geometry survives every write that keeps the buffer lengths. -/
theorem of_eqOff {F : Fp} (h : SchurGeometry N np a t p uo f st w ub r μ)
    (hfr : μ.store.EqOff F μ'.store) : SchurGeometry N np a t p uo f st w ub r μ' :=
  ⟨h.thr.of_eqOff hfr, h.par.of_eqOff hfr⟩

/-- The geometry of five separated operand views, extended by the four scratch buffers of the
worklist allocated on top of them. -/
theorem allocated {n np : ℕ} {a t p uo f : ℕ × ℕ} {μ : Mem ℝ} {s : Store ℝ}
    (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, np, 2 * ((n + 1) * (n + 1)), 1])
    (ha : ShQRViewsApart (n + 1) np a t p uo f)
    (hs : s.length = μ.store.length +
      [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 5].length)
    (hlens : ∀ i (hi : i <
        [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 5].length),
      s.len (μ.store.length + i) =
        [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 5][i])
    (hBelow : Store.Below μ.store.length μ.store s) :
    SchurGeometry (n + 1) np a t p uo f (μ.store.length, 0) (μ.store.length + 1, 0)
      (μ.store.length + 2, 0) (μ.store.length + 3, 0) ⟨s, μ.pos⟩ := by
  have hT : Geometry [a, t, uo, f] [2 * ((n + 1) * (n + 1)), 1, 2 * ((n + 1) * (n + 1)), 1] μ :=
    ⟨fun z hz => hl z (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        tauto), ⟨hr.1, hr.2.1, hr.2.2.2⟩, ha.1⟩
  have hP : Geometry [a, p, uo, f] [2 * ((n + 1) * (n + 1)), np, 2 * ((n + 1) * (n + 1)), 1] μ :=
    ⟨fun z hz => hl z (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        tauto), ⟨hr.1, hr.2.2.1, hr.2.2.2⟩, ha.2⟩
  exact ⟨by simpa [List.range_succ] using hT.allocated hs hlens hBelow,
    by simpa [List.range_succ] using hP.allocated hs hlens hBelow⟩

end SchurGeometry

/-- The block of the view `i` of the worklist in Schur mode (in the order of
`NLAlib.ShiftedQR.SchurGeometry`). -/
abbrev schurBlock (N np : ℕ) (a t p uo f st w ub r : ℕ × ℕ) (i : ℕ) : Fp :=
  Store.inBlock (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD i (0, 0)).1
    (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD i (0, 0)).2
    (([2 * (N * N), 1, np, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] :
      List ℕ).getD i 0)

/-- Two distinct views of the worklist in Schur mode have disjoint words, unless they are the
threshold word and the parameter words (views 1 and 2), which may overlap. -/
theorem SchurGeometry.disj' {N np : ℕ} {a t p uo f st w ub r : ℕ × ℕ} {μ : Mem ℝ}
    (h : SchurGeometry N np a t p uo f st w ub r μ) (i j : Fin 9) (hne : i ≠ j)
    (htp : ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) := by
      first
        | decide
        | exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩) :
    Fp.Disj
      (Store.inBlock (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD i (0, 0)).1
        (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD i (0, 0)).2
        (([2 * (N * N), 1, np, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] :
          List ℕ).getD i 0))
      (Store.inBlock (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD j (0, 0)).1
        (([a, t, p, uo, f, st, w, ub, r] : List (ℕ × ℕ)).getD j (0, 0)).2
        (([2 * (N * N), 1, np, 2 * (N * N), 1, 1 + 2 * N, 2 * (N * N), 2 * (N * N), 5] :
          List ℕ).getD j 0)) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij : i ≠ j := fun e => hne (Fin.ext e)
  have h12 : ¬(i = 1 ∧ j = 2) := fun e => htp.1 ⟨Fin.ext e.1, Fin.ext e.2⟩
  have h21 : ¬(i = 2 ∧ j = 1) := fun e => htp.2 ⟨Fin.ext e.1, Fin.ext e.2⟩
  by_cases h2 : i = 2 ∨ j = 2
  · have hi1 : i ≠ 1 := by omega
    have hj1 : j ≠ 1 := by omega
    have key := h.par.disj (i := if i < 1 then i else i - 1) (j := if j < 1 then j else j - 1)
      (by simp only [List.length_cons, List.length_nil]; split_ifs <;> omega)
      (by simp only [List.length_cons, List.length_nil]; split_ifs <;> omega)
      (by split_ifs <;> omega)
    interval_cases i <;> interval_cases j <;>
      first
        | exact absurd rfl hij
        | exact absurd rfl hi1
        | exact absurd rfl hj1
        | exact key
  · have hi2 : i ≠ 2 := fun e => h2 (Or.inl e)
    have hj2 : j ≠ 2 := fun e => h2 (Or.inr e)
    have key := h.thr.disj (i := if i < 2 then i else i - 1) (j := if j < 2 then j else j - 1)
      (by simp only [List.length_cons, List.length_nil]; split_ifs <;> omega)
      (by simp only [List.length_cons, List.length_nil]; split_ifs <;> omega)
      (by split_ifs <;> omega)
    interval_cases i <;> interval_cases j <;>
      first
        | exact absurd rfl hij
        | exact absurd rfl hi2
        | exact absurd rfl hj2
        | exact key

/-- The side condition of `NLAlib.ShiftedQR.SchurGeometry.disj'` when the first view is neither
the threshold word nor the parameter words. -/
theorem SchurGeometry.side {i j : Fin 9} (h1 : i ≠ 1 := by decide) (h2 : i ≠ 2 := by decide) :
    ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) :=
  ⟨fun h => h1 h.1, fun h => h2 h.1⟩

/-- The writes of a round leave the threshold and the parameter words alone. -/
theorem SchurGeometry.disj_params {N np : ℕ} {a t p uo f st w ub r : ℕ × ℕ} {μ : Mem ℝ}
    (h : SchurGeometry N np a t p uo f st w ub r μ) :
    Fp.Disj (schurRoundFp N a uo f st w ub r)
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock p.1 p.2 np) := by
  have hT := h.thr.disj_select [0, 2, 3, 4, 5, 6, 7] [1] (by simp) (by simp) (by simp)
  have hP := h.par.disj_select [0, 2, 3, 4, 5, 6, 7] [1] (by simp) (by simp) (by simp)
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] at hT hP
  exact Fp.disj_sup_right.mpr ⟨by simpa only [schurRoundFp, Fp.blocks_cons, Fp.blocks_nil,
    sup_bot_eq] using hT, by simpa only [schurRoundFp, Fp.blocks_cons, Fp.blocks_nil,
    sup_bot_eq] using hP⟩

/-- The accumulator stays near $\mathbf{U}$ times a unitary: if $\|\mathbf{U}_1 -
\mathbf{U}\mathbf{V}_1\|_2 \le (a - 1)\|\mathbf{U}\|_2$ and $\|\mathbf{U}_2 -
\mathbf{U}_1\mathbf{W}\|_2 \le (b - 1)\|\mathbf{U}_1\|_2$ with $\mathbf{V}_1$, $\mathbf{W}$ unitary
and $1 \le b$, then $\|\mathbf{U}_2 - \mathbf{U}\mathbf{V}_1\mathbf{W}\|_2 \le
(ab - 1)\|\mathbf{U}\|_2$. -/
theorem specNorm_sub_mul_mul_le_of_near {N : ℕ} {U U₁ U₂ V₁ W : Matrix (Fin N) (Fin N) ℂ}
    {a b : ℝ} (hb : 1 ≤ b) (hV₁ : HasOrthonormalCols V₁) (hW : HasOrthonormalCols W)
    (h₁ : specNorm (U₁ - U * V₁) ≤ (a - 1) * specNorm U)
    (h₂ : specNorm (U₂ - U₁ * W) ≤ (b - 1) * specNorm U₁) :
    specNorm (U₂ - U * (V₁ * W)) ≤ (a * b - 1) * specNorm U := by
  have hU₁ : specNorm U₁ ≤ a * specNorm U := by
    have := specNorm_add_le (U₁ - U * V₁) (U * V₁)
    rw [sub_add_cancel, hV₁.specNorm_mul_right] at this
    linarith
  have e : U₂ - U * (V₁ * W) = (U₂ - U₁ * W) + (U₁ - U * V₁) * W := by
    rw [Matrix.sub_mul, ← Matrix.mul_assoc]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hW.specNorm_mul_right]
  have := mul_le_mul_of_nonneg_left hU₁ (show (0 : ℝ) ≤ b - 1 by linarith)
  nlinarith [specNorm_nonneg U]

/-- The stored accumulator at `uo` is within $(c - 1)\|\mathbf{U}\|_2$ of $\mathbf{U}$ times a
unitary. -/
def AccumNear {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (uo : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  ∃ U' V : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix uo U' μ.store ∧ HasOrthonormalCols V ∧
    specNorm (U' - U * V) ≤ (c - 1) * specNorm U

/-- A larger factor is weaker. -/
theorem AccumNear.mono {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c c' : ℝ} {uo : ℕ × ℕ}
    {μ : Mem ℝ} (h : AccumNear U c uo μ) (hc : c ≤ c') : AccumNear U c' uo μ := by
  obtain ⟨U', V, hU', hV, hb⟩ := h
  exact ⟨U', V, hU', hV, hb.trans (mul_le_mul_of_nonneg_right (by linarith) (specNorm_nonneg U))⟩

/-- A write apart from the accumulator keeps it. -/
theorem AccumNear.of_eqOff {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c : ℝ} {uo : ℕ × ℕ}
    {μ μ' : Mem ℝ} {F : Fp} (h : AccumNear U c uo μ) (hfr : μ.store.EqOff F μ'.store)
    (hd : Fp.Disj F (Store.inBlock uo.1 uo.2 (2 * (N * N)))) : AccumNear U c uo μ' := by
  obtain ⟨U', V, hU', hV, hb⟩ := h
  exact ⟨U', V, hU'.of_eqOff hfr hd, hV, hb⟩

/-- The accumulator survives dropping scratch buffers above its buffer. -/
theorem AccumNear.of_below {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c : ℝ} {uo : ℕ × ℕ}
    {s s' : Store ℝ} {pos L : ℕ} (h : AccumNear U c uo ⟨s, pos⟩) (hBelow : Store.Below L s s')
    (hu : uo.1 < L) : AccumNear U c uo ⟨s', pos⟩ := by
  obtain ⟨U', V, hU', hV, hb⟩ := h
  exact ⟨U', V, hU'.of_below hBelow hu, hV, hb⟩

/-- A near-unitary update of the stored accumulator: if it was within factor $c$ with the
matrix $\mathbf{U}_1$ and is now $\mathbf{U}_2$ within $(b - 1)\|\mathbf{U}_1\|_2$ of
$\mathbf{U}_1\mathbf{W}$, $\mathbf{W}$ unitary, $b \ge 1$ and $cb \le c'$, then it is within
factor $c'$. -/
theorem AccumNear.step {N : ℕ} {U U₁ U₂ W : Matrix (Fin N) (Fin N) ℂ} {c b c' : ℝ} {uo : ℕ × ℕ}
    {μ μ' : Mem ℝ} (h : AccumNear U c uo μ) (hU₁ : HoldsMatrix uo U₁ μ.store)
    (hU₂ : HoldsMatrix uo U₂ μ'.store) (hW : HasOrthonormalCols W) (hb : 1 ≤ b)
    (h₂ : specNorm (U₂ - U₁ * W) ≤ (b - 1) * specNorm U₁) (hc : c * b ≤ c') :
    AccumNear U c' uo μ' := by
  obtain ⟨U', V, hU', hV, hb'⟩ := h
  have e : U' = U₁ := by rw [hU'.eq_storedMatrix, hU₁.eq_storedMatrix]
  subst e
  refine ⟨U₂, V * W, hU₂, hV.mul hW, ?_⟩
  refine (specNorm_sub_mul_mul_le_of_near hb hV hW hb' h₂).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (specNorm_nonneg U)

/-- A stored accumulator at `uo`, within $(c - 1)\|\mathbf{U}\|_2$ of $\mathbf{U}$ times a
unitary if `P` holds (`P` carries the rounding model the bound needs). -/
def AccumIf (P : Prop) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (uo : ℕ × ℕ)
    (μ : Mem ℝ) : Prop :=
  (∃ U' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix uo U' μ.store) ∧ (P → AccumNear U c uo μ)

/-- A larger factor is weaker. -/
theorem AccumIf.mono {P : Prop} {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c c' : ℝ} {uo : ℕ × ℕ}
    {μ : Mem ℝ} (h : AccumIf P U c uo μ) (hc : P → c ≤ c') : AccumIf P U c' uo μ :=
  ⟨h.1, fun hp => (h.2 hp).mono (hc hp)⟩

/-- A write apart from the accumulator keeps it. -/
theorem AccumIf.of_eqOff {P : Prop} {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c : ℝ}
    {uo : ℕ × ℕ} {μ μ' : Mem ℝ} {F : Fp} (h : AccumIf P U c uo μ) (hfr : μ.store.EqOff F μ'.store)
    (hd : Fp.Disj F (Store.inBlock uo.1 uo.2 (2 * (N * N)))) : AccumIf P U c uo μ' :=
  ⟨h.1.imp fun _ hU => hU.of_eqOff hfr hd, fun hp => (h.2 hp).of_eqOff hfr hd⟩

/-- The accumulator survives dropping scratch buffers above its buffer. -/
theorem AccumIf.of_below {P : Prop} {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ} {c : ℝ}
    {uo : ℕ × ℕ} {s s' : Store ℝ} {pos L : ℕ} (h : AccumIf P U c uo ⟨s, pos⟩)
    (hBelow : Store.Below L s s') (hu : uo.1 < L) : AccumIf P U c uo ⟨s', pos⟩ :=
  ⟨h.1.imp fun _ hU => hU.of_below hBelow hu, fun hp => (h.2 hp).of_below hBelow hu⟩

/-- **The value-free core of the worklist in Schur mode before round `j`**, for the input
accumulator $\mathbf{U}$, the per-round accumulator factor $(1 + 24\boldsymbol{u})^m$ and the
per-leaf factor $1 + \varepsilon_L$: the failure word and some matrix are stored, the stack
holds ranges that fit in the order $n + 1$, a count $\ell$ of finished leaves with $\ell$ plus the
sizes of the ranges at most $n + 1$, and the stored accumulator is within
$((1 + 24\boldsymbol{u})^{jm}(1 + \varepsilon_L)^{\ell} - 1)\|\mathbf{U}\|_2$ of $\mathbf{U}$
times a unitary. -/
def SchurStoredCore (n : ℕ) (P : Prop) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL : ℝ) (m : ℕ)
    (a uo f st : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  (∃ x, μ.store.get f.1 f.2 = some x) ∧
    (∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A μ.store) ∧
    ∃ (rs : List (ℕ × ℕ)) (ℓ : ℕ), StackHolds st rs μ.store ∧ RangesFit (n + 1) rs ∧
      ℓ + (rs.map Prod.snd).sum ≤ n + 1 ∧
      AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ

/-- **The value-free state of the worklist in Schur mode before round `j`**: the geometry, the
threshold and parameter words stored, and the core `NLAlib.ShiftedQR.SchurStoredCore`. -/
def SchurStoredState (n : ℕ) (P : Prop) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL : ℝ)
    (m : ℕ)
    (ps : List ℝ) (a t p uo f st w ub r : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  SchurGeometry (n + 1) ps.length a t p uo f st w ub r μ ∧ (∃ x, μ.store.get t.1 t.2 = some x) ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧ SchurStoredCore n P U u εL m a uo f st j μ

/-- From the geometry with the threshold and parameter words stored at `μ`, a write inside the
round footprint to `μ'` keeps them, so the core at `μ'` gives the state at `μ'`. -/
theorem SchurStoredState.of_core {n : ℕ} {P : Prop} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {u εL : ℝ}
    {m : ℕ} {ps : List ℝ} {a t p uo f st w ub r : ℕ × ℕ} {j : ℕ} {μ μ' : Mem ℝ} {F : Fp}
    (h : SchurGeometry (n + 1) ps.length a t p uo f st w ub r μ)
    (ht : ∃ x, μ.store.get t.1 t.2 = some x)
    (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfr : μ.store.EqOff F μ'.store) (hF : F ≤ schurRoundFp (n + 1) a uo f st w ub r)
    (hcore : SchurStoredCore n P U u εL m a uo f st j μ') :
    SchurStoredState n P U u εL m ps a t p uo f st w ub r j μ' := by
  have hd := h.disj_params.mono hF le_rfl
  obtain ⟨x, hx⟩ := ht
  exact ⟨h.of_eqOff hfr, ⟨x, hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_left) hx⟩,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hd.mono le_rfl le_sup_right) hp, hcore⟩

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The abort keeps the value-free core: on a machine whose natural literals up to $n + 1$ are
exact, from the geometry of the worklist in Schur mode with some matrix stored, a count
$\ell \le n + 1$ and the accumulator within its factor, `roundedAbort` writes the failure word and
the stack count and leaves the core `NLAlib.ShiftedQR.SchurStoredCore` (an empty stack).
Shared by the trees of `NLAlib.ShiftedQR.roundedProcessLargeWith`,
`NLAlib.ShiftedQR.roundedWorklistWith`, `NLAlib.ShiftedQR.roundedLargeRest`. -/
theorem roundedAbort_writes_schurCore {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit Mch I) {n : ℕ} (hN : IsExactNatLit id Mch (n + 1)) {np : ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} {P : Prop} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {u εL : ℝ} {m j ℓ : ℕ}
    {a t p uo f st w ub r : ℕ × ℕ} (hG : SchurGeometry (n + 1) np a t p uo f st w ub r μ)
    (hA : ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A μ.store) (hℓ : ℓ ≤ n + 1)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ) :
    Writes .total I τ (roundedAbort (O := O) (Q := Q)) (Env.frame [] [st, f])
      (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 1)
      (SchurStoredCore n P U u εL m a uo f st j) μ := by
  obtain ⟨A, hA⟩ := hA
  have hFA : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using hG.disj' 4 0 (by simp)
  have hFU : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 4 3 (by simp)
  have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 5 0 (by simp)
  have hSU : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 5 3 (by simp)
  have hFS : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by
    simpa using hG.disj' 4 5 (by simp)
  refine (roundedAbort_writes hL hN (by omega) (by have := hG.room.2.2.2.2.2.1; omega)
    (by have := hG.room.2.2.2.2.1; omega) (hFS.mono le_rfl (by fp_sub))).mono le_rfl ?_
  rintro m' hfr ⟨h1, h0⟩
  have hd : ∀ {X : Fp}, Fp.Disj (Store.inBlock f.1 f.2 1) X →
      Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) X →
      Fp.Disj (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 1) X := fun h₁ h₂ =>
    Fp.disj_sup_left.mpr ⟨h₁, h₂.mono (by fp_sub) le_rfl⟩
  exact ⟨⟨1, h1⟩, ⟨A, hA.of_eqOff hfr (hd hFA hSA)⟩, [], ℓ,
    ⟨by simpa using h0, fun _ h => absurd h (by simp)⟩, by simp [RangesFit],
    by simpa using hℓ,
    hacc.of_eqOff hfr (hd hFU hSU)⟩

/-- The part of `NLAlib.ShiftedQR.roundedProcessLargeWith` after the decoupling call: abort on a
failure, else scan the bottom couplings and split and update, or abort. -/
def roundedLargeRest : Stmt O Q :=
  Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 7, off := IExp.var 16 }]
    (Stmt.frame [] [{ buf := 3, off := IExp.var 12 }, { buf := 7, off := IExp.var 16 }]
      (roundedAbort (O := O) (Q := Q)))
    ((Stmt.frame [IExp.var 8, IExp.var 1]
        [{ buf := 5, off := IExp.var 14 }, { buf := 1, off := IExp.var 10 },
          { buf := 6, off := IExp.var 15 }] (bottomScan (O := O) (Q := Q))).seq
      (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 6, off := IExp.var 15 + IExp.const 3 }]
        (Stmt.bindIdx (Has.inj IdxTst.toNat) [{ buf := 6, off := IExp.var 15 + IExp.const 4 }]
          (IExp.var 8)
          ((Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17]
              [{ buf := 0, off := IExp.var 9 }, { buf := 3, off := IExp.var 12 },
                { buf := 5, off := IExp.var 14 }] (writeAndSplit (O := O) (Q := Q))).seq
            (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17, IExp.var 5, IExp.var 6]
              [{ buf := 8, off := IExp.const 0 }, { buf := 0, off := IExp.var 9 },
                { buf := 4, off := IExp.var 13 }] (roundedDecoupleUpdate (O := O) (Q := Q)))))
        (Stmt.frame [] [{ buf := 3, off := IExp.var 12 }, { buf := 7, off := IExp.var 16 }]
          (roundedAbort (O := O) (Q := Q)))))

/-- The large branch is a scoped log, the decoupling call and
`NLAlib.ShiftedQR.roundedLargeRest`. -/
theorem roundedProcessLargeWith_body (D : Stmt O Q) :
    (roundedProcessLargeWith D) =
      Stmt.alloc (IExp.var 5 * (IExp.const 1 + IExp.const 5 * IExp.var 6))
        ((Stmt.frame [IExp.var 8, IExp.var 1, IExp.var 2, IExp.var 3, IExp.var 4, IExp.var 5,
            IExp.var 6]
          [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
            { buf := 5, off := IExp.var 14 }, { buf := 7, off := IExp.var 16 },
            { buf := 8, off := IExp.const 0 }] D).seq roundedLargeRest) := rfl

/-- The split after a decoupled block and its update keep the core: on a scalar machine with
the standard model at $\boldsymbol{u} \le 1/100$, exact natural literals up to $n + 1$ and exact
`toNat` and comparisons, with the stack holding `rs` after the popped $(lo, d + 1)$, a closed log
at `(lgb, 0)` whose entries are inside the block, some matrix of order $d + 1$ in the work matrix
and the index $i < d$ of a cut, `writeAndSplit` and `roundedDecoupleUpdate` reach the core of
round $j + 1$. -/
theorem roundedSplitUpdate_core {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I) {n : ℕ}
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm : ns * w ≤ m) {np : ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    {lo d i j ℓ lgb : ℕ} {a t p uo f st wk ub r : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {x εL : ℝ} (hεL : P → 0 ≤ εL) {L : List (Option (List GivensEntry))}
    (hG : SchurGeometry (n + 1) np a t p uo f st wk ub r μ) (hf : μ.store.get f.1 f.2 = some x)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix wk H' μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d + 1) :: rs))
    (hℓ : ℓ + (d + 1) + (rs.map Prod.snd).sum ≤ n + 1) (hi : i < d)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ)
    (hlog : HoldsSlottedLog (lgb, 0) ns w L [] μ.store) (hlen : L.length = ns)
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d + 1) (hlgb : lgb < μ.store.length)
    (hlgv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < lgb) :
    Writes .total I tape
      ((Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17]
          [{ buf := 0, off := IExp.var 9 }, { buf := 3, off := IExp.var 12 },
            { buf := 5, off := IExp.var 14 }] (writeAndSplit (O := O) (Q := Q))).seq
        (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17, IExp.var 5, IExp.var 6]
          [{ buf := 8, off := IExp.const 0 }, { buf := 0, off := IExp.var 9 },
            { buf := 4, off := IExp.var 13 }] (roundedDecoupleUpdate (O := O) (Q := Q))))
      ((⟨(Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).idx,
        (Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).buf ++
          [lgb]⟩ : Env).pushIdx i)
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredCore n P U u εL m a uo f st (j + 1)) μ := by
  have hu0 : P → 0 ≤ u := fun hp => (abs_nonneg _).trans (by simpa using (hP hp).1.lit 1)
  have hfit0 := hfit.1 _ List.mem_cons_self
  have hlen' := hfit.length_add_le
  dsimp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  have hWA : Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 6 0 (by simp)
  have hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
        by simpa [schurBlock] using hG.disj' 0 5 (by simp)
  have hAU : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 0 3 (by simp)
  have hSU : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 5 3 (by simp)
  have hFA : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using hG.disj' 4 0 (by simp)
  have hFS : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by
    simpa using hG.disj' 4 5 (by simp)
  have hFU : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using hG.disj' 4 3 (by simp)
  have hlASW : μ.Live [a, st, wk] := hG.live_of_subset (by simp)
  have hsplit := writeAndSplit_writes_mem (O := O) (Q := Q) (τ := tape) (i := i) hS hL hQ hNat
    hlASW hA hW hSt hfit0.2 (by omega) (by omega) hG.room.1 hG.room.2.2.2.2.2.1
    (hWA.mono hWw le_rfl) hAS
  refine (hsplit.in_frame rfl rfl hlASW).seq_le (by fp_sub [schurRoundFp]) ?_
  rintro μ₃ hfr₃ ⟨-, hA₃, hSt₃⟩
  obtain ⟨⟨U₁, hU₁⟩, hacc'⟩ := hacc
  have hU₁' := hU₁.of_eqOff hfr₃ (Fp.disj_sup_left.mpr ⟨hAU, hSU⟩)
  have hne : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 ≠ lgb := fun v hv => by
    have := hlgv v hv; omega
  have hlog₃ := hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (hne a (by simp)),
      Fp.disj_inBlock_of_ne (hne st (by simp))⟩) hlog
  have es_ok : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < n + 1 := fun e he => by
    have := hpl e he; omega
  have hl₃ : μ₃.Live [(lgb, 0), a, uo] := fun v hv => by
    rw [hfr₃.length_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> rw [h]
    exacts [hlgb, hG.live a (by simp), hG.live uo (by simp)]
  refine ((roundedDecoupleUpdate_writes (O := O) (Q := Q) (τ := tape) (M := Mch) hS hQ hC
    (hfit0.2) (show i + 1 < d + 1 by omega) es_ok (lg := (lgb, 0)) hl₃ hlog₃ hlen hA₃ hU₁'
    (by rw [hfr₃.len_eq]; exact hG.room.1)
    (Fp.disj_inBlock_of_ne (hne a (by simp)).symm) (Fp.disj_inBlock_of_ne (hne uo (by simp)).symm)
    hAU).in_frame rfl rfl hl₃).mono (by fp_sub [schurRoundFp]) ?_
  rintro μ₄ hfr₄ ⟨-, hA₄, hU₄⟩
  have hSt₄ := hSt₃.of_eqOff hfr₄ (Fp.disj_sup_left.mpr ⟨hAS.mono le_rfl (by
    simp only [List.length_append, List.length_cons, List.length_nil]; fp_sub), hSU.symm.mono le_rfl
      (by simp only [List.length_append, List.length_cons, List.length_nil]; fp_sub)⟩)
  set es := slotEntries w L
  have hes : es.length ≤ ns * w := hlen ▸ hlog.length_slotEntries_le
  refine ⟨⟨x, (hfr₃.trans' hfr₄).keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr
      ⟨Fp.disj_sup_left.mpr ⟨hFA.symm, hFS.symm⟩, Fp.disj_sup_left.mpr ⟨hFA.symm, hFU.symm⟩⟩) hf⟩,
    ⟨_, hA₄⟩, _, ℓ, hSt₄, hfit.split (by omega), ?_, ⟨⟨_, hU₄⟩, fun hp => ?_⟩⟩
  · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith [hu0 hp]
  have hbound : specNorm (es.foldl (replayColumnStep Mch lo 0 (n + 1)) U₁ -
      U₁ * embedBlock lo (givensLog (d + 1) es)) ≤ ((1 + 24 * u) ^ (ns * w) - 1) * specNorm U₁ :=
    (specNorm_foldl_replayColumnStep_sub_le (hP hp).1 (hu0 hp) (hP hp).2 hfit0.2 es
      (fun e he => ⟨es_ok e he, Or.inl (hpl e he)⟩) U₁).trans
      (mul_le_mul_of_nonneg_right (by linarith [pow_le_pow_right₀ hX1 hes]) (specNorm_nonneg _))
  refine AccumNear.step ((hacc' hp).of_eqOff hfr₃ (Fp.disj_sup_left.mpr ⟨hAU, hSU⟩)) hU₁' hU₄
    (hasOrthonormalCols_embedBlock hfit0.2 (hasOrthonormalCols_givensLog _ _))
    (one_le_pow₀ hX1) hbound ?_
  rw [add_mul, one_mul, pow_add]
  have h1 : (1 + 24 * u) ^ (ns * w) ≤ (1 + 24 * u) ^ m := pow_le_pow_right₀ hX1 hm
  have h0 : 0 ≤ (1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith [hεL hp]) _)
  nlinarith

/-- The accumulator factor grows with the rounds. -/
theorem accumFactor_le_succ {u εL : ℝ} (hu0 : 0 ≤ u) (hεL : 0 ≤ εL) (j m ℓ : ℕ) :
    (1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ ≤ (1 + 24 * u) ^ ((j + 1) * m) * (1 + εL) ^ ℓ :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right m j.le_succ))
    (pow_nonneg (by linarith) _)

/-- The rest of the large branch after the decoupling call keeps the core: from the geometry of
the worklist in Schur mode, the threshold word, any failure word, some matrix stored, any matrix
$\mathbf{H}'$ of order $d + 1 \ge k + 1$ in the work matrix, a stack whose ranges after the
popped $(lo, d + 1)$ fit, the accumulator within its factor at round $j$, and a closed log at
`(lgb, 0)` (a fresh buffer) whose entries are inside the block, `NLAlib.ShiftedQR.roundedLargeRest`
runs to completion and reaches the core of round $j + 1$. -/
theorem roundedLargeRest_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm : ns * w ≤ m) {np : ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    {lo d j ℓ lgb : ℕ} {a t p uo f st wk ub r : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {x thr εL : ℝ} (hεL : P → 0 ≤ εL) {L : List (Option (List GivensEntry))}
    (hG : SchurGeometry (n + 1) np a t p uo f st wk ub r μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hf : μ.store.get f.1 f.2 = some x)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix wk H' μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d + 1) :: rs))
    (hℓ : ℓ + (d + 1) + (rs.map Prod.snd).sum ≤ n + 1) (hk : k ≤ d)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ)
    (hlog : HoldsSlottedLog (lgb, 0) ns w L [] μ.store) (hlen : L.length = ns)
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d + 1) (hlgb : lgb < μ.store.length)
    (hlgv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < lgb) :
    Writes .total I tape (roundedLargeRest (O := O) (Q := Q))
      ⟨(Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).idx,
        (Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).buf ++
          [lgb]⟩
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredCore n P U u εL m a uo f st (j + 1)) μ := by
  have hu0 : P → 0 ≤ u := fun hp => (abs_nonneg _).trans (by simpa using (hP hp).1.lit 1)
  have hlen' := hfit.length_add_le
  have hfit0 := hfit.1 _ List.mem_cons_self
  dsimp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  have hacc' := hacc.mono (fun hp => accumFactor_le_succ (hu0 hp) (hεL hp) j m ℓ)
  have hlSF : μ.Live [st, f] := hG.live_of_subset (by simp)
  unfold roundedLargeRest
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hf) ?_
  by_cases hx : 0 < x
  · rw [if_pos (by simpa [schurBlock] using hx)]
    exact ((roundedAbort_writes_schurCore hL hNat hG ⟨A, hA⟩ (by omega) hacc').in_frame rfl rfl
      hlSF).mono (by fp_sub [schurRoundFp]) fun _ _ h => h
  rw [if_neg (by simpa [schurBlock] using hx)]
  have hRW : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using hG.disj' 8 6 (by simp)
  have hRT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1) := by
    simpa using hG.disj' 8 1 (by simp)
  have hRX : ∀ i : Fin 9, i ≠ 8 → Fp.Disj (Store.inBlock r.1 r.2 5)
      (schurBlock (n + 1) np a t p uo f st wk ub r i) :=
    fun i hi => hG.disj' 8 i (Ne.symm hi)
  have hlS : μ.Live [wk, t, r] := hG.live_of_subset (by simp)
  have hb := bottomScan_terminates (τ := tape) (n := d) (k := k) hS hL (hNat.mono (by omega)) hC
    hk hW ht hlS hG.room.2.2.2.2.2.2.2.2.1 (hRW.mono le_rfl hWw) hRT
  refine (hb.in_frame rfl rfl hlS).seq_le (by fp_sub [schurRoundFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hscan⟩
  have hG₂ := hG.of_eqOff hfr₂
  have hA₂ := hA.of_eqOff hfr₂ (by simpa [schurBlock] using hRX 0 (by simp))
  have hf₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using hRX 4 (by simp)) hf
  have hSt₂ := hSt.of_eqOff hfr₂ ((by simpa [schurBlock] using hRX 5 (by simp) :
    Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
      (by have := hlen'; fp_sub))
  have hacc₂ := hacc.of_eqOff hfr₂ (by simpa [schurBlock] using hRX 3 (by simp))
  have hlog₂ := hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_inBlock_of_ne (by have := hlgv r (by simp); omega)) hlog
  rcases hscan with ⟨hR1, i, hRi⟩ | ⟨hR0, -⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR1) ?_
    rw [if_pos (by simp)]
    have hi := i.isLt
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hRi rfl (by omega) ?_
    exact roundedSplitUpdate_core hS hP hL hNat hQ hC hm hεL hG₂ hf₂ hA₂
      (hW.of_eqOff hfr₂ (hRW.mono le_rfl hWw)) hSt₂ hfit hℓ hi hacc₂ hlog₂ hlen hpl
      (by rw [hfr₂.length_eq]; exact hlgb) hlgv
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR0) ?_
    rw [if_neg (by simp)]
    exact ((roundedAbort_writes_schurCore hL hNat hG₂ ⟨A, hA₂⟩ (by omega)
      (hacc₂.mono (fun hp => accumFactor_le_succ (hu0 hp) (hεL hp) j m ℓ))).in_frame rfl rfl
      (hG₂.live_of_subset (by simp))).mono (by fp_sub [schurRoundFp]) fun _ _ h => h

/-- The core survives dropping scratch buffers above its views. -/
theorem SchurStoredCore.of_below {n : ℕ} {P : Prop} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {u εL : ℝ}
    {m j L : ℕ} {a uo f st : ℕ × ℕ} {s s' : Store ℝ} {pos : ℕ}
    (h : SchurStoredCore n P U u εL m a uo f st j ⟨s, pos⟩) (hBelow : Store.Below L s s')
    (ha : a.1 < L) (hu : uo.1 < L) (hf : f.1 < L) (hs : st.1 < L) :
    SchurStoredCore n P U u εL m a uo f st j ⟨s', pos⟩ := by
  obtain ⟨⟨x, hx⟩, ⟨A, hA⟩, rs, ℓ, hSt, hfit, hℓ, hacc⟩ := h
  exact ⟨⟨x, ((hBelow f.1 hf).2 _).trans hx⟩, ⟨A, hA.of_below hBelow ha⟩, rs, ℓ,
    hSt.of_below hBelow hs, hfit, hℓ, hacc.of_below hBelow hu⟩

/-- The geometry survives an allocation on top of the views. -/
theorem SchurGeometry.of_below {N np : ℕ} {a t p uo f st w ub r : ℕ × ℕ} {μ : Mem ℝ}
    {s : Store ℝ} (h : SchurGeometry N np a t p uo f st w ub r μ)
    (hlen : μ.store.length ≤ s.length) (hBelow : Store.Below μ.store.length μ.store s) :
    SchurGeometry N np a t p uo f st w ub r ⟨s, μ.pos⟩ :=
  ⟨⟨fun z hz => (h.thr.live z hz).trans_le hlen,
      by rw [Mem.room_eq_of_below hBelow (fun z hz => h.thr.live z hz)]; exact h.thr.room,
      h.thr.apart⟩,
    ⟨fun z hz => (h.par.live z hz).trans_le hlen,
      by rw [Mem.room_eq_of_below hBelow (fun z hz => h.par.live z hz)]; exact h.par.room,
      h.par.apart⟩⟩

/-- The large branch keeps the core: on a scalar machine with the standard model at
$\boldsymbol{u} \le 1/100$, exact natural literals up to $n + 1$, exact `toNat` and comparisons,
and a terminating decoupling routine (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) of bottom
width $k \le d$ and log shape (`ns` slots of `w` entries, $n_s w \le m$), from the geometry of the
worklist in Schur mode with the threshold and parameter words stored, a matrix $\mathbf{A}$ whose
block on $(lo, d + 1)$ is in the work matrix, a stack whose ranges after $(lo, d + 1)$ fit, and the
accumulator within its factor at round $j$, `NLAlib.ShiftedQR.roundedProcessLargeWith` reaches
the core of round $j + 1$. -/
theorem roundedLarge_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm : ns * w ≤ m) {ps : List ℝ} (D : Stmt O Q)
    (hD : TerminatingDecouplerRoutine n k F T ps ns w D I) {tape : Tape ℝ} {μ : Mem ℝ}
    {lo d j ℓ : ℕ} {a t p uo f st wk ub r : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr εL : ℝ} (hεL : P → 0 ≤ εL)
    (hG : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix wk (subBlock A (lo, d + 1)) μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d + 1) :: rs))
    (hℓ : ℓ + (d + 1) + (rs.map Prod.snd).sum ≤ n + 1) (hk : k ≤ d)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ) :
    Writes .total I tape (roundedProcessLargeWith D)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredCore n P U u εL m a uo f st (j + 1)) μ := by
  have hlen' := hfit.length_add_le
  have hfit0 := hfit.1 _ List.mem_cons_self
  dsimp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  have hW' : ∀ i : Fin 9, i ≠ 6 → Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i hi => hG.disj' 6 i (Ne.symm hi)
  rw [roundedProcessLargeWith_body]
  change Writes .total I tape
    (Stmt.allocs [IExp.var 5 * (IExp.const 1 + IExp.const 5 * IExp.var 6)] _) _ _ _ μ
  set Lc := μ.store.length with hLc
  have hv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < Lc := fun v hv => hG.live v hv
  refine writes_allocs_preserving_post (ns := [ns * (1 + 5 * w)])
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (fun hBelow h => h.of_below hBelow (hv a (by simp)) (hv uo (by simp)) (hv f (by simp))
      (hv st (by simp))) ?_
  intro s₁ hlen hlens hBelow
  simp only [List.length_cons, List.length_nil] at hlen
  have hL0 : s₁.len Lc = ns * (1 + 5 * w) := by simpa [schurBlock] using hlens 0 (by simp)
  have hG₁ := hG.of_below (s := s₁) (by omega) hBelow
  set μ₁ : Mem ℝ := ⟨s₁, μ.pos⟩
  have hLW : Fp.Disj (Store.inBlock Lc 0 (ns * (1 + 5 * w))) (Store.inBlock wk.1 wk.2
      (2 * ((d + 1) * (d + 1)))) := Fp.disj_inBlock_of_ne (by have := hv wk (by simp); omega)
  have hLF : Fp.Disj (Store.inBlock Lc 0 (ns * (1 + 5 * w))) (Store.inBlock f.1 f.2 1) :=
    Fp.disj_inBlock_of_ne (by have := hv f (by simp); omega)
  have hlD : μ₁.Live [wk, p, wk, f, (Lc, 0)] := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h | h | h <;> rw [h] <;>
      first | (change Lc < s₁.length; omega) | exact hG₁.live _ (by simp)
  have hw := hD (tape := tape) (lg := (Lc, 0)) (subBlock A (lo, d + 1)) hk (by omega)
    (hW.of_below hBelow (hv wk (by simp)))
    ((hBelow.readBlock (hv p (by simp)) p.2 ps.length).trans hp) hlD
    (by have := hG₁.room.2.2.2.2.2.2.1; have := Nat.mul_le_mul hd hd; omega)
    hG₁.room.2.2.2.2.1 (by simp [μ₁, hL0])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with h | h | h <;> rw [h] <;> simp only <;>
          [have := hv wk (by simp); have := hv p (by simp); have := hv f (by simp)] <;> omega)
    ⟨Fp.disj_sup_right.mpr ⟨(hW' 4 (by simp)).mono hWw (by simp [schurBlock]),
      Fp.disj_sup_right.mpr ⟨hLW.symm, fun _ _ _ h => h⟩⟩,
      Fp.disj_sup_right.mpr ⟨hLF.symm, fun _ _ _ h => h⟩, fun _ _ _ h => h, trivial⟩
    (Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨((hW' 2 (by simp)).mono hWw le_rfl).symm,
      (by simpa [schurBlock] using hG.disj' 2 4 (by simp))⟩,
      Fp.disj_inBlock_of_ne (by have := hv p (by simp); omega)⟩)
  have hDF : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
      Store.inBlock Lc 0 (ns * (1 + 5 * w)) ≤
        schurRoundFp (n + 1) a uo f st wk ub r ⊔ Fp.above Lc :=
    sup_le (sup_le (hWw.trans (by fp_sub [schurRoundFp])) (by fp_sub [schurRoundFp]))
      (fun b z h => Or.inr (show Lc ≤ b from h.1 ▸ le_rfl))
  refine hw.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame]) rfl hlD hDF ?_
  rintro μ₂ hfr₂ ⟨⟨x, hf₂⟩, ⟨H', hW₂⟩, L, hLlen, hpl, hlog⟩
  have hDX : ∀ (i : Fin 9), i ≠ 6 → i ≠ 4 →
      ([a, t, p, uo, f, st, wk, ub, r] : List (ℕ × ℕ)).getD i (0, 0) ∈
        [a, t, p, uo, f, st, wk, ub, r] →
      Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock Lc 0 (ns * (1 + 5 * w)))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h6 h4 hm => Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨(hW' i h6).mono hWw le_rfl,
      hG.disj' 4 i (Ne.symm h4)⟩, Fp.disj_inBlock_of_ne (by have := hv _ hm; omega)⟩
  set DF := Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
    Store.inBlock Lc 0 (ns * (1 + 5 * w))
  have hDa : Fp.Disj DF (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    hDX 0 (by simp) (by simp) (by simp)
  have hDt : Fp.Disj DF (Store.inBlock t.1 t.2 1) := hDX 1 (by simp) (by simp) (by simp)
  have hDu : Fp.Disj DF (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
    hDX 3 (by simp) (by simp) (by simp)
  have hDs : Fp.Disj DF (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    hDX 5 (by simp) (by simp) (by simp)
  exact (roundedLargeRest_terminates hS hP hL hNat hQ hC hm hεL (hG₁.of_eqOff hfr₂)
    (hfr₂.keep (Store.readsOnly_get _ _ _) hDt (((hBelow t.1 (hv t (by simp))).2 _).trans ht))
    hf₂ (hfr₂.keep (readsOnly_holdsMatrix _ _) hDa (hA.of_below hBelow (hv a (by simp)))) hW₂
    ((StackHolds.of_below hSt hBelow (hv st (by simp))).of_eqOff hfr₂ (hDs.mono le_rfl
      (Fp.inBlock_le_inBlock le_rfl (by omega))))
    hfit hℓ hk ((AccumIf.of_below (pos := μ.pos) hacc hBelow (hv uo (by simp))).of_eqOff hfr₂ hDu)
    hlog hLlen hpl
    (by rw [hfr₂.length_eq]; change Lc < s₁.length; omega) hv).mono le_sup_left fun _ _ h => h

end Theorems
end NLAlib.ShiftedQR
