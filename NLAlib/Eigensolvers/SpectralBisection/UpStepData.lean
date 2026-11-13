/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.State
public import NLAlib.Eigensolvers.SpectralBisection.Result
public import NLAlib.Eigensolvers.SpectralBisection.NodeLayout

/-!
# Reading the mathematical node outcome for reconstruction

The stored outcome exposes its actual kind, split size and bases. A leaf already stores its
final mathematical result. These are projections of the existing tuple representation, not
additional execution assumptions or a separate stage state.

## Main results

* `NLAlib.SpectralBisection.StoresStep.kind_read`: actual stored constructor metadata.
* `NLAlib.SpectralBisection.StoresStep.leaf_storesResult`: a leaf's final output is already stored.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Read the actual machine word denoting the outcome constructor. -/
theorem StoresStep.kind_read {K : Type} {M : Machine K} {R : K} {n d lo k : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} {step : EighStep K k} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks step m) :
    m.store.get kd.1 (kd.2 + n * d + lo) =
      some (M.lit ((match step with
        | .leaf .. => 1
        | .shift side .. => if side then 2 else 3
        | .split .. => 4 : ℕ) : ℚ)) := by
  cases step with
  | leaf U values =>
    simpa [stepOutputs, stepOutputLengths, stepOutputWords] using
      Mem.get_of_readBlocks_getD h.2 (i := 2) (by simp [stepOutputs, stepOutputLengths]) rfl rfl
  | shift side A sigma =>
    simpa [stepOutputs, stepOutputLengths, stepOutputWords] using
      Mem.get_of_readBlocks_getD h.2 (i := 2) (by simp [stepOutputs, stepOutputLengths]) rfl rfl
  | split r hr Qp Qm Ap Am sigma =>
    simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths]
      using Mem.get_of_readBlocks_getD h.2 (i := 6)
        (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths]) rfl rfl

/-- A leaf's final basis and eigenvalue vector are already represented at its own level. -/
theorem StoresStep.leaf_storesResult {K : Type} {M : Machine K} {R : K} {n d lo k : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} {U : Matrix (Fin k) (Fin k) (K × K)}
    {values : Fin k → K} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks (.leaf U values) m) :
    StoresResult n d lo ua ea (U, values) m.store := by
  have hu := Mem.readBlocks_getD h.2 (i := 0) (by simp [stepOutputs, stepOutputLengths])
  have he := Mem.readBlocks_getD h.2 (i := 1) (by simp [stepOutputs, stepOutputLengths])
  simp only [stepOutputs, stepOutputLengths, stepOutputWords, List.getD_cons_zero,
    List.getD_cons_succ] at hu he
  simp [StoresResult, resultOperands, resultLengths, Mem.readBlocks, hu, he]

/-- Read the actual stored split size. -/
theorem StoresStep.split_size_read {K : Type} {M : Machine K} {R : K} {n d lo k r : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} {hr : r ≤ k}
    {Qp : Matrix (Fin k) (Fin r) (K × K)} {Qm : Matrix (Fin k) (Fin (k - r)) (K × K)}
    {Ap : Matrix (Fin r) (Fin r) (K × K)}
    {Am : Matrix (Fin (k - r)) (Fin (k - r)) (K × K)} {sigma : K} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks (.split r hr Qp Qm Ap Am sigma) m) :
    m.store.get ks.1 (ks.2 + n * d + lo) = some (M.lit (r : ℚ)) := by
  simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths]
    using Mem.get_of_readBlocks_getD h.2 (i := 7)
      (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths]) rfl rfl

/-- Read the first stored basis of a split. -/
theorem StoresStep.split_basis_left_read {K : Type} {M : Machine K} {R : K}
    {n d lo k r : ℕ} {ma ua qa ea sz kd ks : ℕ × ℕ} {hr : r ≤ k}
    {Qp : Matrix (Fin k) (Fin r) (K × K)} {Qm : Matrix (Fin k) (Fin (k - r)) (K × K)}
    {Ap : Matrix (Fin r) (Fin r) (K × K)}
    {Am : Matrix (Fin (k - r)) (Fin (k - r)) (K × K)} {sigma : K} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks (.split r hr Qp Qm Ap Am sigma) m) :
    m.store.readBlock qa.1 (qa.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * r)) =
      some ((EntryCodec.pair K).packFinMatrix Qp) := by
  simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths]
    using Mem.readBlocks_getD h.2 (i := 0)
      (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths])

/-- Read the second stored basis of a split. -/
theorem StoresStep.split_basis_right_read {K : Type} {M : Machine K} {R : K}
    {n d lo k r : ℕ} {ma ua qa ea sz kd ks : ℕ × ℕ} {hr : r ≤ k}
    {Qp : Matrix (Fin k) (Fin r) (K × K)} {Qm : Matrix (Fin k) (Fin (k - r)) (K × K)}
    {Ap : Matrix (Fin r) (Fin r) (K × K)}
    {Am : Matrix (Fin (k - r)) (Fin (k - r)) (K × K)} {sigma : K} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks (.split r hr Qp Qm Ap Am sigma) m) :
    m.store.readBlock qa.1 (qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * r))
      (2 * (k * (k - r))) = some ((EntryCodec.pair K).packFinMatrix Qm) := by
  simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths]
    using Mem.readBlocks_getD h.2 (i := 1)
      (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths])

/-- The stored split bases, represented child results and actual shift word supply exactly
all seven inputs of the checked upward split implementation. -/
theorem readBlocks_upSplit_sources {K : Type} {M : Machine K} {R : K} {n d lo k r : ℕ}
    {ma ua qa ea sz kd ks t : ℕ × ℕ} {hr : r ≤ k}
    {Qp : Matrix (Fin k) (Fin r) (K × K)} {Qm : Matrix (Fin k) (Fin (k - r)) (K × K)}
    {Ap : Matrix (Fin r) (Fin r) (K × K)}
    {Am : Matrix (Fin (k - r)) (Fin (k - r)) (K × K)} {sigma : K} {m : Mem K}
    (cp : Matrix (Fin r) (Fin r) (K × K) × (Fin r → K))
    (cm : Matrix (Fin (k - r)) (Fin (k - r)) (K × K) × (Fin (k - r) → K))
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks (.split r hr Qp Qm Ap Am sigma) m)
    (hp : StoresResult n (d + 1) lo ua ea cp m.store)
    (hm : StoresResult n (d + 1) (lo + r) ua ea cm m.store)
    (hs : m.store.get t.1 t.2 = some sigma) :
    m.readBlocks [(qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
      (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * r)),
      (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * (lo + r)),
      (ea.1, ea.2 + n * (d + 1) + lo), (ea.1, ea.2 + n * (d + 1) + lo + r), t]
      [r * k * 2, (k - r) * k * 2, r * r * 2, (k - r) * (k - r) * 2, r, k - r, 1] =
      some [(EntryCodec.pair K).packFinMatrix Qp, (EntryCodec.pair K).packFinMatrix Qm,
        (EntryCodec.pair K).packFinMatrix cp.1, (EntryCodec.pair K).packFinMatrix cm.1,
        List.ofFn cp.2, List.ofFn cm.2, [sigma]] := by
  have hqp := h.split_basis_left_read
  have hqm := h.split_basis_right_read
  have hpu := hp.matrix_read
  have hmu := hm.matrix_read
  have hpe := hp.values_read
  have hme := hm.values_read
  have hscalar := Store.readBlock_one_of_get hs
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc]
    at hqp hqm hpu hmu hpe hme ⊢
  simp [Mem.readBlocks, hqp, hqm, hpu, hmu, hpe, hme, hscalar]

end NLAlib.SpectralBisection
