/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Output
public import NLAlib.Ops.Logic.While

/-!
# Progress and stopping of the exact deflation worklist

The active ranges are stored in reverse order, with the first mathematical range on top of
the stack. Finishing a range or splitting it increases the progress measure by one. The
nonempty partition bound proves that the actual capped loop cannot stop with active work.

## Main results

* `NLAlib.ShiftedQR.WorklistInv`: mathematical and actual stored state of the worklist.
* `NLAlib.ShiftedQR.WorklistInv.continue_lt`: the partition proves remaining loop fuel.
* `NLAlib.ShiftedQR.WorklistInv.output`: an empty worklist gives the actual complete output.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The named regions modified by worklist processing; parameter words are read-only. -/
def worklistFp (N : ℕ) (a stack out w r : ℕ × ℕ) : Fp :=
  Fp.blocks [a, stack, out, w, r] [2 * (N * N), 1 + 2 * N, 2 * N, 2 * (N * N), 5]

/-- The mathematical deflation invariant and its actual persistent storage. Only finished
output ranges are initialized. Error is charged once per split, while the measure counts
both finishes and splits. No future execution or success condition occurs in this predicate. -/
def WorklistInv {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (τ : ℝ)
    (a stack out : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ (active done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (roots : Fin (n + 1) → ℂ) (ε : ℝ),
    DeflationInv H ε active done A roots ∧ HoldsMatrix a A μ.store ∧
    FinishedHolds out done roots μ.store ∧ StackHolds stack active.reverse μ.store ∧
    ε = (((active ++ done).length - 1 : ℕ) : ℝ) * τ ∧
    2 * done.length + active.length = j + 1

/-- The stored count determines whether a mathematical worklist state has active ranges. -/
theorem WorklistInv.count {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ}
    {a stack out : ℕ × ℕ} {j : ℕ} {μ : Mem ℝ} (h : WorklistInv H τ a stack out j μ) :
    ∃ count : ℕ, μ.store.get stack.1 stack.2 = some (count : ℝ) ∧
      (0 < count → j + 1 < 2 * (n + 1)) := by
  obtain ⟨active, done, A, roots, ε, hInv, _, _, hStack, _, hmeasure⟩ := h
  refine ⟨active.length, by simpa using hStack.1, fun hc => ?_⟩
  have hne : active ≠ [] := fun he => by simp [he] at hc
  have hb := hInv.two_mul_length_add_length_lt hne
  omega

/-- A continuing worklist test leaves room for another range-processing visit. -/
theorem WorklistInv.continue_lt {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ}
    {a stack out : ℕ × ℕ} {j count : ℕ} {μ : Mem ℝ}
    (h : WorklistInv H τ a stack out j μ)
    (hc : μ.store.get stack.1 stack.2 = some (count : ℝ)) (hpos : 0 < count) :
    j + 1 < 2 * (n + 1) := by
  obtain ⟨c, hc', hb⟩ := h.count
  have he : c = count := by exact_mod_cast Option.some.inj (hc'.symm.trans hc)
  exact hb (he.symm ▸ hpos)

/-- An empty actual count gives the complete packed output and the accumulated error bound. -/
theorem WorklistInv.output {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ}
    {a stack out : ℕ × ℕ} {j : ℕ} {μ : Mem ℝ} (h : WorklistInv H τ a stack out j μ)
    (hzero : μ.store.get stack.1 stack.2 = some 0) (hτ : 0 ≤ τ) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ) (ε : ℝ),
      ∃ done, DeflationInv H ε [] done A roots ∧ HoldsMatrix a A μ.store ∧
        HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ.store ∧
        ε ≤ (n : ℝ) * τ := by
  obtain ⟨active, done, A, roots, ε, hInv, hA, hOut, hStack, hε, _⟩ := h
  have hlen : active.length = 0 := by
    have he := Option.some.inj (hStack.1.symm.trans hzero)
    simpa using he
  have hempty := List.length_eq_zero_iff.mp hlen
  subst active
  have hpart : IsRangePartition (n + 1) done := by simpa using hInv.partition
  have hbound := hInv.length_le
  simp only [List.nil_append] at hε hbound
  refine ⟨A, roots, ε, done, hInv, hA, hOut.holdsMatrix_of_partition hpart, ?_⟩
  rw [hε]
  have hcast : ((done.length - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega)
  exact mul_le_mul_of_nonneg_right hcast hτ

/-- One raw Hessenberg matrix and a literal-built singleton stack initialize the invariant.
No output words have been written or assumed at this point. -/
theorem WorklistInv.init {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ}
    {a stack out : ℕ × ℕ} {μ : Mem ℝ} (hH : IsUpperHessenberg H)
    (hA : HoldsMatrix a H μ.store) (hSt : StackHolds stack [(0, n + 1)] μ.store) :
    WorklistInv H τ a stack out 0 μ := by
  exact ⟨[(0, n + 1)], [], H, fun _ => 0, 0, hH.deflationInv_init _, hA,
    fun _ hr => by simp only [List.not_mem_nil] at hr,
    by simpa using hSt, by simp, by simp⟩

variable {O Q : Type} [Has CmpTst Q]

/-- The actual count-controlled worklist traversal. The supplied range-processing body is a
fixed implementation, not an operation or a primitive contract. -/
def worklistLoop (round : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (A, Params, St) → (Out, W, R) {
    while j < 2 * N, (Has.inj CmpTst.isPos) [] (St) {
      run round.body [N, m, k, F, M] (A, Params, St, Out, W, R)
    } then { skip }
  }

/-- A total local range-processing proof composes into a stopped worklist. The invariant's
partition and progress measure exclude active work at the cap, rather than assuming success
or assuming that the loop has stopped. -/
theorem worklistLoop_writes (round : Impl O Q) {I : Interp O Q ℝ} (hC : IsCmp id I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m k F M : ℕ} {a p stack out w r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ}
    (hl : μ.Live [a, p, stack, out, w, r]) (hInv : WorklistInv H τ a stack out 0 μ)
    (hround : ∀ j < 2 * (n + 1), ∀ μ',
      μ.store.EqOff (worklistFp (n + 1) a stack out w r) μ'.store →
      WorklistInv H τ a stack out j μ' → ∀ count : ℕ,
      μ'.store.get stack.1 stack.2 = some (count : ℝ) → 0 < count →
      Writes .total I tape round.body (Env.frame [n + 1, m, k, F, M] [a, p, stack, out, w, r])
        (worklistFp (n + 1) a stack out w r)
        (fun μ'' => μ''.pos = μ'.pos ∧ WorklistInv H τ a stack out (j + 1) μ'') μ') :
    Writes .total I tape (worklistLoop round).body
      (Env.frame [n + 1, m, k, F, M] [a, p, stack, out, w, r])
      (worklistFp (n + 1) a stack out w r)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ j, WorklistInv H τ a stack out j μ' ∧
        μ'.store.get stack.1 stack.2 = some 0) μ := by
  unfold worklistLoop
  refine (writes_whileFuel rfl (fun _ => worklistFp (n + 1) a stack out w r)
    (fun _ _ => le_rfl) ⊥
    (fun j μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out j μ')
    _ ⟨rfl, hInv⟩ ?_ ?_).mono (by simp) (fun _ _ hp => hp)
  · intro j hj μ' hfr ⟨hp, hi⟩
    obtain ⟨count, hc, _⟩ := hi.count
    have ht := hC.test_isPos (d := []) (x := stack) hc
    have ht' : I.testAt (Has.inj CmpTst.isPos) [] [⟨2, .var 7⟩]
        ((Env.frame [n + 1, m, k, F, M] [a, p, stack, out, w, r]).pushIdx j) μ' =
        some (decide (0 < (count : ℝ))) := by
      simpa [Interp.testAt, Operand.eval, Env.frame, Env.pushIdx, IExp.eval] using ht
    rw [ht']
    apply Mode.holds_some
    simp only [decide_eq_true_eq]
    by_cases hpos : 0 < count
    · have hposR : (0 : ℝ) < count := by exact_mod_cast hpos
      rw [if_pos hposR]
      have hw := hround j hj μ' hfr hi count hc hpos
      refine (hw.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
      intro _ _ ⟨hp', hs'⟩
      exact ⟨hp'.trans hp, hs'⟩
    · have hcount : count = 0 := by omega
      subst count
      simp only [Nat.cast_zero, lt_self_iff_false, ite_false]
      exact Writes.skip ⟨hp, j, hi, by simpa using hc⟩
  · intro μ' _ ⟨hp, hi⟩
    obtain ⟨count, hc, hb⟩ := hi.count
    have hcount : count = 0 := by
      by_contra hne
      have hpos : 0 < count := by omega
      have := hb hpos
      omega
    subst count
    exact Writes.skip ⟨hp, 2 * (n + 1), hi, by simpa using hc⟩

end NLAlib.ShiftedQR
