/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQRoundingState

/-!
# Outputs of rounded complete-pivoted LU

A completed stored factorization prefix yields actual factor and pivot-log word arrays.
Popping the residual scratch leaves exactly their four output writes. Decoding those arrays
recovers the same factor values, including their triangular structure, multiplier bound and
conditional componentwise backward error.

## Main results

* `NLAlib.Computation.PLUQRounding.State.writeBlocks_pop`: actual factor and pivot-log outputs,
  their complete store frame and the numerical guarantees of the completed prefix.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQRounding

variable {P K : Type} [DecidableEq P] {N : ℕ}

private theorem write_outputBlocks {initial final : Store P K} {tag : P}
    {L U Hr Hc lo uo hro hco : ℕ} (WL WU WR WC : Array K)
    (hWL : WL.size = N * N) (hWU : WU.size = N * N) (hWR : WR.size = N) (hWC : WC.size = N)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hshape : final.shape = initial.shape)
    (hL : ∀ j, j < N * N → final.read tag L (lo + j) = WL[j]?)
    (hU : ∀ j, j < N * N → final.read tag U (uo + j) = WU[j]?)
    (hR : ∀ j, j < N → final.read tag Hr (hro + j) = WR[j]?)
    (hC : ∀ j, j < N → final.read tag Hc (hco + j) = WC[j]?)
    (hframe : ∀ q b j, (b ≠ L ∨ j < lo ∨ lo + N * N ≤ j) →
      (b ≠ U ∨ j < uo ∨ uo + N * N ≤ j) →
      (b ≠ Hr ∨ j < hro ∨ hro + N ≤ j) →
      (b ≠ Hc ∨ j < hco ∨ hco + N ≤ j) → final.read q b j = initial.read q b j) :
    initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (Hr, hro, N), (Hc, hco, N)]
      [WL, WU, WR, WC] = some final := by
  refine Store.writeBlocks_eq_some_of_read
    (.cons hWL (.cons hWU (.cons hWR (.cons hWC .nil)))) ?_ hshape ?_ ?_
  · simp [List.pairwise_cons, blockDisjoint, hLU, hLR, hLC, hUR, hUC, hRC]
  · intro k x y hx hy j hj
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hL j hj
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        exact hU j hj
      · rcases k with _ | k
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst x; subst y
          exact hR j hj
        · rcases k with _ | k
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
            subst x; subst y
            exact hC j hj
          · simp at hx
  · intro q b j hout
    exact hframe q b j (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hout _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (hout _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- A completed rounded pivoted-LU state releases its residual scratch to give actual sized
lower, upper and pivot-log arrays and exactly their four output block writes. The decoded
arrays retain the stored triangular shapes, exact unit lower diagonal and multiplier bound
$1+u$. If $u<1$, they also satisfy componentwise backward error with factor $N+4$. The word
carrier and scratch array are arbitrary, and empty output blocks require no valid handles.
The four output buffers are distinct. [Higham2002, §9.3]. -/
theorem State.writeBlocks_pop {dec : P → K → ℝ} {u : ℝ} {initial final : Store P K} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {L U Hr Hc lo uo hro hco : ℕ} {scratch : Array (Option K)}
    (hs : State dec u (initial.push (tag, scratch)) tag A
      initial.size L U Hr Hc lo uo hro hco N final)
    (hLcap : Writable initial tag L lo (N * N)) (hUcap : Writable initial tag U uo (N * N))
    (hRcap : Writable initial tag Hr hro N) (hCcap : Writable initial tag Hc hco N)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hu : 0 ≤ u) :
    ∃ (WL WU WR WC : Array K) (rows cols : Fin N → Fin N),
      WL.size = N * N ∧ WU.size = N * N ∧ WR.size = N ∧ WC.size = N ∧
      initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (Hr, hro, N), (Hc, hco, N)]
        [WL, WU, WR, WC] = some final.pop ∧
      ReadsDecoded final.pop dec tag Hr hro (fun j => ((rows j).val : ℝ)) ∧
      ReadsDecoded final.pop dec tag Hc hco (fun j => ((cols j).val : ℝ)) ∧
      (∀ j, j ≤ rows j) ∧ (∀ j, j ≤ cols j) ∧
      (unflatten N N (WL.map (dec tag))).IsLowerTriangular ∧
      (∀ j, unflatten N N (WL.map (dec tag)) j j = 1) ∧
      (unflatten N N (WU.map (dec tag))).IsUpperTriangular ∧
      (∀ i j, |unflatten N N (WL.map (dec tag)) i j| ≤ 1 + u) ∧
      (u < 1 → IsLUErr (roundingFactor (N + 4) u)
        (A.submatrix (luPivotPermutation rows N) (luPivotPermutation cols N))
        (unflatten N N (WL.map (dec tag))) (unflatten N N (WU.map (dec tag)))) ∧
      HoldsDecoded final.pop dec tag L lo (unflatten N N (WL.map (dec tag))) ∧
      HoldsDecoded final.pop dec tag U uo (unflatten N N (WU.map (dec tag))) := by
  classical
  obtain ⟨rows, cols, R, F, G, -, hF, hG, hlower, hdiag, hupper, hbound, hprefix,
    hrow, hcol⟩ := hs.values
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hLb : 0 < N → L < initial.size := fun hN => hLcap.lt_size (Nat.mul_pos hN hN)
  have hUb : 0 < N → U < initial.size := fun hN => hUcap.lt_size (Nat.mul_pos hN hN)
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
  choose rw hrw hdr hrrange using fun j : Fin N => hrow j j.isLt
  choose cw hcw hdc hcrange using fun j : Fin N => hcol j j.isLt
  let WR := Array.ofFn rw
  let WC := Array.ofFn cw
  have hRpop (j : Fin N) : Store.read final.pop tag Hr (hro + j) = some (rw j) := by
    rw [Store.read_pop_of_lt (by have := hRcap.lt_size (Nat.zero_lt_of_lt j.isLt); omega)]
    exact hrw j
  have hCpop (j : Fin N) : Store.read final.pop tag Hc (hco + j) = some (cw j) := by
    rw [Store.read_pop_of_lt (by have := hCcap.lt_size (Nat.zero_lt_of_lt j.isLt); omega)]
    exact hcw j
  obtain ⟨WL, hWL, hflatL, hdecL⟩ := hFpop.exists_array
  obtain ⟨WU, hWU, hflatU, hdecU⟩ := hGpop.exists_array
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hwrite := write_outputBlocks WL WU WR WC hWL hWU (by simp [WR]) (by simp [WC])
    hLU hLR hLC hUR hUC hRC hshape hflatL hflatU
    (fun j hj => by simpa only [WR, Array.getElem?_ofFn, hj, ↓reduceDIte] using hRpop ⟨j, hj⟩)
    (fun j hj => by simpa only [WC, Array.getElem?_ofFn, hj, ↓reduceDIte] using hCpop ⟨j, hj⟩)
    (fun q b j hbL hbU hbR hbC => by
      by_cases hb : b < initial.size
      · rw [Store.read_pop_of_lt (by omega),
          hs.frame.outside q b j (Or.inl (by omega)) hbL hbU hbR hbC,
          Store.read_push_of_lt hb]
      · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
          Store.read_eq_none_of_size_le (by omega)])
  refine ⟨WL, WU, WR, WC, rows, cols, hWL, hWU, by simp [WR], by simp [WC], hwrite,
    fun j => ⟨rw j, hRpop j, hdr j⟩, fun j => ⟨cw j, hCpop j, hdc j⟩,
    hrrange, hcrange, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end NLAlib.Computation.PLUQRounding
