/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Ops.Blas.BlockCopy
public import NLAlib.Matrix.QRIteration.HessenbergDeflation

/-!
# Copying active diagonal blocks to and from workspace

Both directions instantiate the shared scalar copy between pair-codec matrix views. The
global leading dimension remains the raw matrix size; workspace is dense. No block kernel or
preprocessed matrix input is introduced.

## Main results

* `NLAlib.ShiftedQR.copyToWork`, `NLAlib.ShiftedQR.copyToGlobal`: scalar block-copy programs.
* `NLAlib.ShiftedQR.copyToWork_writes`: the copied workspace is the actual diagonal block.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Copy a global diagonal block into dense workspace. All dimensions are actual runtime sizes. -/
def copyToWork : Impl Op Tst := opsImpl% [N, lo, d] (A) → (W) {
  run (copyStrided (Op := Op) (Tst := Tst)).body [d, d, N, d]
    (A[2 * (lo * N + lo)], W)
}

/-- Copy dense workspace back into the global matrix, retaining its original leading dimension. -/
def copyToGlobal : Impl Op Tst := opsImpl% [N, lo, d] (W) → (A) {
  run (copyStrided (Op := Op) (Tst := Tst)).body [d, d, d, N]
    (W, A[2 * (lo * N + lo)])
}

/-- The ordinary component pair of a finite complex matrix, extended by zero off its domain. -/
private def entryPairs {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℂ) (i j : ℕ) : ℝ × ℝ :=
  if hi : i < r then if hj : j < c then ((A ⟨i, hi⟩ ⟨j, hj⟩).re,
    (A ⟨i, hi⟩ ⟨j, hj⟩).im) else (0, 0) else (0, 0)

/-- The actual pair-codec words of a diagonal view occupy only the corresponding global block. -/
theorem blockFp_le {N lo d : ℕ} (b : ℕ × ℕ) (hr : lo + d ≤ N) :
    (EntryCodec.pair ℝ).regionFp b.1 (b.2 + 2 * (lo * N + lo)) d
      (fun i j => j * N + i) (fun _ => d) ≤ Store.inBlock b.1 b.2 (2 * (N * N)) := by
  rintro c x ⟨i, j, ⟨hj, hi⟩ | ⟨_, hi⟩, hx⟩
  · have hi' : i < d := hi
    have hj' : j < d := hj
    have hb := Idx.add_lt_mul (show lo + j < N by omega) (show lo + i < N by omega)
    change c = b.1 ∧ b.2 + 2 * (lo * N + lo) + 2 * (j * N + i) ≤ x ∧
      x < b.2 + 2 * (lo * N + lo) + 2 * (j * N + i) + 2 at hx
    exact ⟨hx.1, by nlinarith [hx.2.1], by nlinarith [hx.2.2]⟩
  · omega

/-- A packed global matrix supplies the exact component words of any bounded diagonal view. -/
private theorem HoldsMatrix.block_entries {n lo d : ℕ} {b : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {st : Store ℝ}
    (hH : HoldsMatrix b H st) (hr : lo + d ≤ n + 1) :
    st.HoldsEntries (EntryCodec.pair ℝ)
      ⟨b.1, b.2 + 2 * (lo * (n + 1) + lo), d, d, n + 1⟩
      (entryPairs (subBlock H (lo, d))) := by
  intro i hi j hj z
  have hi' : i < d := hi
  have hj' : j < d := hj
  have hib : lo + i ≤ n := by omega
  have hjb : lo + j ≤ n := by omega
  have he : b.2 + 2 * (lo * (n + 1) + lo) + 2 * (j * (n + 1) + i) =
      b.2 + 2 * ((lo + j) * (n + 1) + (lo + i)) := by ring
  fin_cases z
  · have hg := hH.get_re ⟨lo + i, by omega⟩ ⟨lo + j, by omega⟩
    simpa [entryPairs, hi, hj, subBlock, blockIndex, min_eq_left hib,
      min_eq_left hjb, he] using hg
  · have hg := hH.get_im ⟨lo + i, by omega⟩ ⟨lo + j, by omega⟩
    simpa [entryPairs, hi, hj, subBlock, blockIndex, min_eq_left hib,
      min_eq_left hjb, he, Nat.add_assoc] using hg

/-- Copying a bounded diagonal block uses its actual raw matrix words. Workspace capacity
is persistent, the matrix/work views are separate, and no initialized workspace is required. -/
theorem copyToWork_writes {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {n lo d : ℕ} {a w : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : m.Live [a, w]) (hH : HoldsMatrix a H m.store) (hr : lo + d ≤ n + 1)
    (hw : w.2 + 2 * (d * d) ≤ m.store.len w.1)
    (hd : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * (d * d)))) :
    Writes .total I τ (copyToWork (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, lo, d] [a, w]) (Store.inBlock w.1 w.2 (2 * (d * d)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix w (subBlock H (lo, d)) m'.store) m := by
  let B := subBlock H (lo, d)
  have hdst := (EntryCodec.pair ℝ).regionFp_le_inBlock w.1 w.2 d (d * d)
    (fun i j => j * d + i) (fun _ => d) (fun _ hj _ hi => Idx.add_lt_mul hj hi)
  have hc := writes_copyStrided (τ := τ) hS (entryPairs B)
    (x := (a.1, a.2 + 2 * (lo * (n + 1) + lo))) (y := w)
    (by simpa [Mem.Live] using hl) (hH.block_entries hr) le_rfl
    (fun j hj i hi => by have hb := Idx.add_lt_mul hj hi; omega)
    (hd.mono (blockFp_le a hr) hdst)
  unfold copyToWork
  refine (hc.in_frame rfl rfl (by simpa [Mem.Live] using hl)).mono hdst ?_
  intro m' _ ⟨he, hp⟩
  refine ⟨hp, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
  · simpa [entryPairs, i.isLt, j.isLt, B] using he i i.isLt j j.isLt 0
  · simpa [entryPairs, i.isLt, j.isLt, B, Nat.add_assoc] using he i i.isLt j j.isLt 1

/-- Writing one bounded diagonal view replaces exactly that mathematical submatrix.
The ordinary entry-region frame retains every global matrix entry outside the view. -/
private theorem HoldsMatrix.of_block_write {n lo d : ℕ} {a : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    {st st' : Store ℝ} (hH : HoldsMatrix a H st) (hr : lo + d ≤ n + 1)
    (hfr : st.EqOff ((EntryCodec.pair ℝ).regionFp a.1
      (a.2 + 2 * (lo * (n + 1) + lo)) d (fun i j => j * (n + 1) + i)
      (fun _ => d)) st')
    (hB : st'.HoldsEntries (EntryCodec.pair ℝ)
      ⟨a.1, a.2 + 2 * (lo * (n + 1) + lo), d, d, n + 1⟩ (entryPairs B)) :
    HoldsMatrix a (setSubBlock H (lo, d) B) st' := by
  have hget (i j : Fin (n + 1)) (z : Fin 2) :
      st'.get a.1 (a.2 + 2 * (j * (n + 1) + i) + z) =
        some ((EntryCodec.pair ℝ).words
          (entryPairs (setSubBlock H (lo, d) B) i j) z) := by
    by_cases hm : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d ∧
        lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d
    · have hi : (i : ℕ) - lo < d := by omega
      have hj : (j : ℕ) - lo < d := by omega
      have he : a.2 + 2 * (lo * (n + 1) + lo) +
          2 * (((j : ℕ) - lo) * (n + 1) + ((i : ℕ) - lo)) =
          a.2 + 2 * (j * (n + 1) + i) := by
        have hmul := congrArg (· * (n + 1)) (Nat.sub_add_cancel hm.2.2.1)
        have hadd := Nat.sub_add_cancel hm.1
        nlinarith
      have hw := hB _ hi _ hj z
      simpa [entryPairs, i.isLt, j.isLt, hi, hj, setSubBlock, hm, he] using hw
    · have hnot : ¬(EntryCodec.pair ℝ).regionFp a.1
          (a.2 + 2 * (lo * (n + 1) + lo)) d (fun u v => v * (n + 1) + u)
          (fun _ => d) a.1 (a.2 + 2 * (j * (n + 1) + i) + z) := by
        rintro ⟨u, v, ⟨hv, hu⟩ | ⟨_, hu⟩, hw⟩
        · have hu' : u < d := hu
          have hv' : v < d := hv
          have he : a.2 + 2 * (lo * (n + 1) + lo) + 2 * (v * (n + 1) + u) =
              a.2 + 2 * ((lo + v) * (n + 1) + (lo + u)) := by ring
          have hlo : a.2 + 2 * (lo * (n + 1) + lo) + 2 * (v * (n + 1) + u) ≤
              a.2 + 2 * (j * (n + 1) + i) + z := hw.2.1
          have hhi : a.2 + 2 * (j * (n + 1) + i) + z <
              a.2 + 2 * (lo * (n + 1) + lo) + 2 * (v * (n + 1) + u) + 2 := hw.2.2
          rw [he] at hlo hhi
          have hz := z.isLt
          have hidx : j * (n + 1) + i = (lo + v) * (n + 1) + (lo + u) := by omega
          have hri := congrArg (· % (n + 1)) hidx
          have hcj := congrArg (· / (n + 1)) hidx
          have hub : lo + u < n + 1 := by omega
          simp only [Idx.mod_add i.isLt, Idx.mod_add hub] at hri
          simp only [Idx.div_add i.isLt, Idx.div_add hub] at hcj
          exact hm ⟨by omega, by omega, by omega, by omega⟩
        · omega
      rw [hfr.get_eq hnot]
      fin_cases z
      · simpa [entryPairs, i.isLt, j.isLt, setSubBlock, hm] using hH.get_re i j
      · simpa [entryPairs, i.isLt, j.isLt, setSubBlock, hm] using hH.get_im i j
  apply HoldsMatrix.of_get
  · intro i j
    simpa [entryPairs, i.isLt, j.isLt] using hget i j 0
  · intro i j
    simpa [entryPairs, i.isLt, j.isLt, Nat.add_assoc] using hget i j 1

/-- Dense workspace is copied back into exactly its bounded global diagonal block. Global
capacity is the original matrix capacity, with no additional padding after the final column. -/
theorem copyToGlobal_writes {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {n lo d : ℕ} {a w : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hl : m.Live [w, a]) (hH : HoldsMatrix a H m.store) (hB : HoldsMatrix w B m.store)
    (hr : lo + d ≤ n + 1)
    (ha : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hd : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ (copyToGlobal (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, lo, d] [w, a])
      ((EntryCodec.pair ℝ).regionFp a.1 (a.2 + 2 * (lo * (n + 1) + lo)) d
        (fun i j => j * (n + 1) + i) (fun _ => d))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (setSubBlock H (lo, d) B) m'.store) m := by
  have hsrc := (EntryCodec.pair ℝ).regionFp_le_inBlock w.1 w.2 d (d * d)
    (fun i j => j * d + i) (fun _ => d) (fun _ hj _ hi => Idx.add_lt_mul hj hi)
  have hentries : m.store.HoldsEntries (EntryCodec.pair ℝ)
      ⟨w.1, w.2, d, d, d⟩ (entryPairs B) := by
    intro i hi j hj z
    have hi' : i < d := hi
    have hj' : j < d := hj
    fin_cases z
    · simpa [entryPairs, hi', hj'] using hB.get_re ⟨i, hi'⟩ ⟨j, hj'⟩
    · simpa [entryPairs, hi', hj', Nat.add_assoc] using hB.get_im ⟨i, hi'⟩ ⟨j, hj'⟩
  have hc := writes_copyStrided (τ := τ) hS (entryPairs B)
    (x := w) (y := (a.1, a.2 + 2 * (lo * (n + 1) + lo)))
    (by simpa [Mem.Live] using hl) hentries (by omega)
    (fun j hj i hi => by
      have hb := Idx.add_lt_mul (show lo + j < n + 1 by omega)
        (show lo + i < n + 1 by omega)
      dsimp only
      nlinarith) (hd.mono hsrc (blockFp_le a hr))
  unfold copyToGlobal
  refine (hc.in_frame rfl rfl (by simpa [Mem.Live] using hl)).mono le_rfl ?_
  intro m' hfr ⟨he, hp⟩
  exact ⟨hp, hH.of_block_write hr hfr he⟩

end NLAlib.ShiftedQR
