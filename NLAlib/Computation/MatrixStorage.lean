/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames

/-!
# Packed matrix storage and block writes

Readable entries of a rectangular stored matrix determine a column-major array of its actual
words, without algebraic assumptions on their carrier. A scoped scratch frame with stored
output entries gives one packed output write after the scratch is popped. The numerical
specializations use the existing encoding `flatten`. Empty dimensions impose no buffer-handle
or capacity requirement.

## Main results

* `NLAlib.Computation.writeBlocks_factors`: actual ordered writes of two stored factors.

* `NLAlib.Computation.HoldsDecoded.exists_array`: actual decoded packed words.
* `NLAlib.Computation.Holds.exists_array`: an actual packed array of arbitrary stored words.
* `NLAlib.Computation.Holds.writeBlock_of_blockFrame_pop`: a scoped matrix output write.
* `NLAlib.Computation.Holds.read_flatten`: flat readback from a stored matrix.
* `NLAlib.Computation.Holds.writeBlock_self`: rewriting the stored matrix changes nothing.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P 𝕜 : Type} [DecidableEq P] [RCLike 𝕜] {N k : ℕ}
    {s : Store P 𝕜} {p : P} {b off : ℕ} {M : Matrix (Fin N) (Fin k) 𝕜}

/-- A stored rectangular matrix reads back its column-major packing at every flat index in
range. The offset is arbitrary. If either dimension is zero there is no flat index to read,
and no condition on the buffer handle is imposed. -/
theorem Holds.read_flatten (h : Holds s p b off M) (t : ℕ) (ht : t < N * k) :
    s.read p b (off + t) = (flatten M)[t]? := by
  have hN : 0 < N := Nat.pos_of_ne_zero (fun hN => by
    rw [hN, zero_mul] at ht
    exact Nat.not_lt_zero _ ht)
  let i : Fin N := ⟨t % N, Nat.mod_lt _ hN⟩
  let j : Fin k := ⟨t / N, (Nat.div_lt_iff_lt_mul hN).mpr
    (by simpa only [Nat.mul_comm] using ht)⟩
  have hidx : (i : ℕ) + N * j = t := Nat.mod_add_div t N
  have hread := (h i j).trans (getElem?_flatten M i j).symm
  simpa only [Nat.add_assoc, hidx] using hread

/-- Writing a matrix already held by the store back into its own packed block leaves the
store unchanged. Readability supplies the necessary capacity; empty matrices require no valid
buffer handle, including when their offset is outside all existing buffers. -/
theorem Holds.writeBlock_self (h : Holds s p b off M) :
    s.writeBlock p b off (flatten M) = some s := by
  exact Store.writeBlock_eq_some_of_read rfl
    (fun t ht => h.read_flatten t (by simpa only [size_flatten] using ht))
    (fun _ _ _ _ => rfl)

/-- A readable rectangular stored matrix determines a packed array of its actual words. Flat
and coordinate reads agree with that array, and rewriting it leaves the store unchanged.
The carrier needs no zero or algebraic structure. Empty dimensions yield an empty array and
require neither a valid buffer handle nor extra capacity. -/
theorem Holds.exists_array {K : Type} {s : Store P K}
    {M : Matrix (Fin N) (Fin k) K} (h : Holds s p b off M) :
    ∃ W : Array K, W.size = N * k ∧
      (∀ t, t < N * k → s.read p b (off + t) = W[t]?) ∧
      (∀ i j, W[i.val + N * j.val]? = some (M i j)) ∧
      s.writeBlock p b off W = some s := by
  let f : Fin (N * k) → K := fun t =>
    have hN : 0 < N := Nat.pos_of_ne_zero (fun hN => by
      have ht := t.isLt
      have hz : N * k = 0 := by simp only [hN, zero_mul]
      omega)
    M ⟨t.val % N, Nat.mod_lt _ hN⟩
      ⟨t.val / N, (Nat.div_lt_iff_lt_mul hN).mpr
        (by simpa only [Nat.mul_comm] using t.isLt)⟩
  let W := Array.ofFn f
  have hsize : W.size = N * k := Array.size_ofFn
  have hread (t : ℕ) (ht : t < N * k) : s.read p b (off + t) = W[t]? := by
    have hN : 0 < N := Nat.pos_of_ne_zero (fun hN => by
      rw [hN, zero_mul] at ht
      exact Nat.not_lt_zero _ ht)
    let i : Fin N := ⟨t % N, Nat.mod_lt _ hN⟩
    let j : Fin k := ⟨t / N, (Nat.div_lt_iff_lt_mul hN).mpr
      (by simpa only [Nat.mul_comm] using ht)⟩
    have hidx : i.val + N * j.val = t := Nat.mod_add_div t N
    have hr := h i j
    rw [show off + i.val + N * j.val = off + t by omega] at hr
    simpa only [W, Array.getElem?_ofFn, ht, ↓reduceDIte, f, i, j] using hr
  refine ⟨W, hsize, hread, ?_, Store.writeBlock_eq_some_of_read rfl
    (fun t ht => hread t (by simpa only [hsize] using ht)) (fun _ _ _ _ => rfl)⟩
  intro i j
  have ht := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
  exact (hread (i.val + N * j.val) ht).symm.trans
    (by simpa only [Nat.add_assoc] using h i j)

/-- A decoded stored rectangular matrix determines actual words whose decoded existing
column-major encoding is that matrix. Empty dimensions require no valid buffer handle. -/
theorem HoldsDecoded.exists_array {K : Type} {s : Store P K} {dec : P → K → ℝ}
    {tag : P} {b off : ℕ} {M : Matrix (Fin N) (Fin k) ℝ}
    (h : HoldsDecoded s dec tag b off M) :
    ∃ W : Array K, W.size = N * k ∧
      (∀ t, t < N * k → s.read tag b (off + t) = W[t]?) ∧
      unflatten N k (W.map (dec tag)) = M := by
  classical
  choose Mw hMw hdMw using h
  change Matrix (Fin N) (Fin k) K at Mw
  have hraw : Holds s tag b off Mw := hMw
  obtain ⟨W, hsize, hflat, hcoords, -⟩ := hraw.exists_array
  refine ⟨W, hsize, hflat, ?_⟩
  ext i j
  simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    hcoords, Option.map_some, Option.getD_some, hdMw]

/-- A scoped scratch frame containing a stored output matrix pops to one packed output write
in the original store. The input matrix supplies the output capacity. Both matrices may have
arbitrary word carrier and empty dimensions, and the scratch array has arbitrary length.
No valid matrix handle is required when its packed block is empty. -/
theorem Holds.writeBlock_of_blockFrame_pop {K : Type} {initial final : Store P K}
    {A M : Matrix (Fin N) (Fin k) K} {scratch : Array (Option K)} {g : ℕ → Option K}
    (hInput : Holds initial p b off A)
    (hFrame : Store.BlockFrame (initial.push (p, scratch)) p initial.size b off (N * k) final g)
    (hOutput : Holds final p b off M) :
    ∃ W : Fin (N * k) → K,
      initial.writeBlock p b off (Array.ofFn W) = some final.pop ∧
        Holds final.pop p b off M := by
  obtain ⟨arr, hsize, hread, hcoords, -⟩ := hOutput.exists_array
  have hw : Writable initial p b off arr.size := by
    rw [hsize]
    exact hInput.writable
  obtain ⟨s₁, hs₁⟩ := hw.exists_writeBlock (y := arr)
  have hpop : final.pop = s₁ := hFrame.pop_eq hs₁ hsize
    (fun t ht => (hFrame.2.2 t ht).symm.trans (hread t ht))
  have hwrite : initial.writeBlock p b off arr = some final.pop := hpop ▸ hs₁
  let W : Fin (N * k) → K := fun t => arr[t.val]'(by rw [hsize]; exact t.isLt)
  have hW : Array.ofFn W = arr := by
    apply Array.ext (by simp only [Array.size_ofFn, hsize])
    intro t ht ht'
    simp only [Array.getElem_ofFn, W]
  refine ⟨W, by simpa only [hW] using hwrite, fun i j => ?_⟩
  have ht : i.val + N * j.val < arr.size := by
    rw [hsize]
    exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
  have hr := (Store.read_of_writeBlock_eq_some_of_lt hwrite ht).trans (hcoords i j)
  simpa only [Nat.add_assoc] using hr

/-- Two stored square factor matrices, the original shape and the complete outside-cell
frame determine exactly their lower-then-upper packed block writes. The carrier may be any
real or complex scalar type, offsets arbitrary, and empty matrices need no valid handles. -/
theorem writeBlocks_factors {N : ℕ} {initial final : Store P 𝕜} {p : P}
    {L U lo uo : ℕ} {B D : Matrix (Fin N) (Fin N) 𝕜} (hLU : L ≠ U)
    (hsh : final.shape = initial.shape) (hB : Holds final p L lo B)
    (hD : Holds final p U uo D)
    (hfr : ∀ q b idx, (b ≠ L ∨ idx < lo ∨ lo + N * N ≤ idx) →
      (b ≠ U ∨ idx < uo ∨ uo + N * N ≤ idx) →
      final.read q b idx = initial.read q b idx) :
    initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [flatten B, flatten D] =
      some final := by
  refine Store.writeBlocks_eq_some_of_read
    (bs := [(L, lo, N * N), (U, uo, N * N)]) (ys := [flatten B, flatten D])
    (.cons (size_flatten B) (.cons (size_flatten D) .nil)) ?_ hsh ?_ ?_
  · simp [List.pairwise_cons, blockDisjoint, hLU]
  · intro k x y hx hy t ht
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hB.read_flatten t ht
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        exact hD.read_flatten t ht
      · simp at hx
  · intro q b idx hout
    exact hfr q b idx (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))

end NLAlib.Computation
