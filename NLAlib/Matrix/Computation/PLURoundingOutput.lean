/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingState

/-!
# Outputs of rounded partial-pivoted LU

A completed stored factorization prefix yields actual factor and pivot-log word arrays.
Popping the residual scratch leaves exactly their three output writes. Decoding those arrays
recovers the same factor values, including their triangular structure, multiplier bound and
conditional componentwise backward error.

## Main results

* `NLAlib.Computation.PLURounding.State.writeBlocks_pop`: actual factor and pivot-log outputs,
  their complete store frame and the numerical guarantees of the completed prefix.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

variable {P K : Type} [DecidableEq P] {N : ℕ}

/-- A completed rounded pivoted-LU state releases its residual scratch to give actual sized
lower, upper and pivot-log arrays and exactly their three output block writes. The decoded
arrays retain the stored triangular shapes, exact unit lower diagonal and multiplier bound
$1+u$. If $u<1$, they also satisfy componentwise backward error with factor $N+4$. The word
carrier and scratch array are arbitrary, and empty output blocks require no valid handles.
The three output buffers are distinct. [Higham2002, §9.3]. -/
theorem State.writeBlocks_pop {dec : P → K → ℝ} {u : ℝ} {initial final : Store P K} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {L U H lo uo ho : ℕ} {scratch : Array (Option K)}
    (hs : State dec u (initial.push (tag, scratch)) tag A
      initial.size L U H lo uo ho N final)
    (hLcap : Writable initial tag L lo (N * N)) (hUcap : Writable initial tag U uo (N * N))
    (hHcap : Writable initial tag H ho N) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hu : 0 ≤ u) :
    ∃ (WL WU WH : Array K) (history : Fin N → Fin N),
      WL.size = N * N ∧ WU.size = N * N ∧ WH.size = N ∧
      initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
        [WL, WU, WH] = some final.pop ∧
      ReadsDecoded final.pop dec tag H ho (fun j => ((history j).val : ℝ)) ∧
      (∀ j, j ≤ history j) ∧
      (unflatten N N (WL.map (dec tag))).IsLowerTriangular ∧
      (∀ j, unflatten N N (WL.map (dec tag)) j j = 1) ∧
      (unflatten N N (WU.map (dec tag))).IsUpperTriangular ∧
      (∀ i j, |unflatten N N (WL.map (dec tag)) i j| ≤ 1 + u) ∧
      (u < 1 → IsLUErr (roundingFactor (N + 4) u)
        (A.submatrix (luPivotPermutation history N) id)
        (unflatten N N (WL.map (dec tag))) (unflatten N N (WU.map (dec tag)))) ∧
      HoldsDecoded final.pop dec tag L lo (unflatten N N (WL.map (dec tag))) ∧
      HoldsDecoded final.pop dec tag U uo (unflatten N N (WU.map (dec tag))) := by
  classical
  obtain ⟨history, R, F, G, -, hF, hG, hlower, hdiag, hupper, hbound, hprefix, hlog⟩ := hs.values
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hLb : 0 < N → L < initial.size := fun hN => hLcap.lt_size (Nat.mul_pos hN hN)
  have hUb : 0 < N → U < initial.size := fun hN => hUcap.lt_size (Nat.mul_pos hN hN)
  have hHb : 0 < N → H < initial.size := fun hN => hHcap.lt_size hN
  have hFpop : HoldsDecoded final.pop dec tag L lo F := by
    intro i j
    obtain ⟨w, hw, hd⟩ := hF i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_pop_of_lt (by have := hLb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hw
  have hGpop : HoldsDecoded final.pop dec tag U uo G := by
    intro i j
    obtain ⟨w, hw, hd⟩ := hG i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_pop_of_lt (by have := hUb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hw
  choose words hwords hdecode hrange using fun j : Fin N => hlog j j.isLt
  let WH := Array.ofFn words
  have hHpop (j : Fin N) : Store.read final.pop tag H (ho + j) = some (words j) := by
    rw [Store.read_pop_of_lt (by have := hHb (Nat.zero_lt_of_lt j.isLt); omega)]
    exact hwords j
  obtain ⟨WL, hWL, hflatL, hdecL⟩ := hFpop.exists_array
  obtain ⟨WU, hWU, hflatU, hdecU⟩ := hGpop.exists_array
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hwrite : initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
      [WL, WU, WH] = some final.pop := by
    refine Store.writeBlocks_eq_some_of_read
      (.cons hWL (.cons hWU (.cons (by simp only [WH, Array.size_ofFn]) .nil)))
      ?_ hshape ?_ ?_
    · simp [List.pairwise_cons, blockDisjoint, hLU, hLH, hUH]
    · intro k x y hx hy j hj
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        exact hflatL j hj
      · rcases k with _ | k
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst x; subst y
          exact hflatU j hj
        · rcases k with _ | k
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
            subst x; subst y
            simpa only [WH, Array.getElem?_ofFn, hj, ↓reduceDIte] using hHpop ⟨j, hj⟩
          · simp at hx
    · intro q b j hout
      have hbL := hout (L, lo, N * N) List.mem_cons_self
      have hbU := hout (U, uo, N * N) (List.mem_cons_of_mem _ List.mem_cons_self)
      have hbH := hout (H, ho, N)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      by_cases hb : b < initial.size
      · rw [Store.read_pop_of_lt (by omega),
          hs.frame.outside q b j (Or.inl (by omega)) hbL hbU hbH,
          Store.read_push_of_lt hb]
      · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
          Store.read_eq_none_of_size_le (by omega)]
  refine ⟨WL, WU, WH, history, hWL, hWU, by simp only [WH, Array.size_ofFn], hwrite,
    fun j => ⟨words j, hHpop j, hdecode j⟩, hrange, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecL]
    exact fun i j hij => hlower i j j.isLt hij
  · rw [hdecL]
    exact fun j => hdiag j j.isLt
  · rw [hdecU]
    exact fun i j hji => hupper i j i.isLt hji
  · rw [hdecL]
    exact fun i j => hbound i j j.isLt
  · intro hu1
    rw [hdecL, hdecU]
    exact (hprefix hu1).isLUErr hu hu1
  · rwa [hdecL]
  · rwa [hdecU]

end NLAlib.Computation.PLURounding
