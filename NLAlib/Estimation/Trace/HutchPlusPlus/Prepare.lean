/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Sketch
public import NLAlib.Estimation.Trace.HutchPlusPlus.Math
public import NLAlib.Matrix.Factorizations.MGS.Factor

/-!
# Preparing the Hutch++ basis and probes

The sketch image is factored by total rank-revealing MGS. Actual samples in the probe
tail are retained through that in-place prefix factorization.

## Main results

* `NLAlib.HutchPlusPlus.writes_prepare` computes the packed basis and actual probes.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜]

/-- Zero supplies the raw word padding convention in this module. -/
local instance instInhabitedPrepare : Inhabited 𝕜 := ⟨0⟩

private theorem read_basisProbes {n k ell : ℕ} {s : Store 𝕜} {b : ℕ × ℕ}
    (Q : Matrix (Fin n) (Fin k) 𝕜) (G : Matrix (Fin n) (Fin ell) 𝕜)
    (hQ : s.readBlock b.1 b.2 (k * n) = some ((EntryCodec.scalar 𝕜).packFinMatrix Q))
    (hG : s.readBlock b.1 (b.2 + n * k) (ell * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix G)) :
    s.readBlock b.1 b.2 ((k + ell) * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix (basisProbes Q G)) := by
  apply Store.readBlock_scalar_matrix_of_columns
  intro j
  by_cases hj : (j : ℕ) < k
  · have hh := Store.readBlock_scalar_matrix_column hQ ⟨j, hj⟩
    change s.readBlock b.1 (b.2 + j * n) n =
      some (List.ofFn fun i : Fin n => Q i ⟨j, hj⟩) at hh
    change _ = some (List.ofFn fun i : Fin n => basisProbes Q G i j)
    simpa only [basisProbes, Matrix.of_apply, dif_pos hj] using hh
  · let c : Fin ell := ⟨j - k, by omega⟩
    have hh := Store.readBlock_scalar_matrix_column hG c
    have he : b.2 + n * k + c * n = b.2 + j * n := by
      have hc : k + c = (j : ℕ) := by dsimp [c]; omega
      calc
        b.2 + n * k + c * n = b.2 + (k + c) * n := by ring
        _ = b.2 + j * n := by rw [hc]
    rw [he] at hh
    change s.readBlock b.1 (b.2 + j * n) n =
      some (List.ofFn fun i : Fin n => G i c) at hh
    change _ = some (List.ofFn fun i : Fin n => basisProbes Q G i j)
    simpa only [basisProbes, Matrix.of_apply, dif_neg hj, c] using hh

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]
  [Has StoredOperatorOp Op] [Has SampleOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- The preparation returns the rank-revealing basis and actual untouched probes.
Every temporary allocation is cleaned up and both sample windows are identified exactly. -/
theorem writes_prepare (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I) (hSample : IsSample I) (stream : ℕ)
    {n k ell : ℕ} {data b : ℕ × ℕ} (as : List 𝕜) (hl : m.Live [data, b])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hBA : Fp.Disj (Store.inBlock b.1 b.2 ((k + ell) * n))
      (Store.inBlock data.1 data.2 (dataLength n n)))
    (hb : b.2 + (k + ell) * n ≤ m.store.len b.1) :
    Writes .total I τ (prepare stream).body (Env.frame [n, k, ell] [data, b])
      (Store.inBlock b.1 b.2 ((k + ell) * n))
      (fun m' => m'.pos = m.pos + n * (k + ell) ∧
        m'.store.readBlock b.1 b.2 ((k + ell) * n) =
          some ((EntryCodec.scalar 𝕜).packFinMatrix (basisProbes
            (gramSchmidtQ (matrix n n as * (EntryCodec.scalar 𝕜).matrix n k
              (τ.window stream m.pos (n * k))))
            ((EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell))))))
      m := by
  have hsize : (k + ell) * n = n * k + n * ell := by ring
  have hsub : Store.inBlock b.1 b.2 (k * n) ≤ Store.inBlock b.1 b.2 ((k + ell) * n) :=
    Fp.inBlock_le_inBlock le_rfl (by rw [Nat.add_mul]; omega)
  have htail : Store.inBlock b.1 (b.2 + n * k) (n * ell) ≤
      Store.inBlock b.1 b.2 ((k + ell) * n) :=
    Fp.inBlock_le_inBlock (by omega) (by rw [hsize]; omega)
  have hdis : Fp.Disj (Store.inBlock b.1 b.2 (k * n))
      (Store.inBlock b.1 (b.2 + n * k) (n * ell)) :=
    Fp.disj_inBlock_of_le (by rw [Nat.mul_comm n k])
  unfold prepare
  dsimp only
  refine Writes.seq_le ((writes_sketch hI hSample stream as hl hA
    (hBA.mono hsub le_rfl) (by rw [Nat.add_mul] at hb; omega)).in_frame rfl rfl hl) hsub ?_
  intro m₁ hfr₁ ⟨hp₁, hImage⟩
  have hlG : m₁.Live [(b.1, b.2 + n * k)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨(hl.congr hfr₁.length_eq) b (by simp), trivial⟩
  refine Writes.seq_le ((writes_sampleVector hSample stream
    (by change b.2 + n * k + n * ell ≤ m₁.store.len b.1
        rw [hfr₁.len_eq]
        rw [hsize] at hb
        omega)).in_frame rfl rfl hlG) htail ?_
  intro m₂ hfr₂ ⟨hProbe, hp₂⟩
  have hImage₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) hdis.symm hImage
  let S := (EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k))
  let G := (EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell))
  have hG : m₂.store.readBlock b.1 (b.2 + n * k) (ell * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix G) := by
    have he : (EntryCodec.scalar 𝕜).packFinMatrix G =
        τ.window stream (m.pos + n * k) (n * ell) := by
      apply EntryCodec.packFinMatrix_matrix
      simp [Tape.window, Nat.mul_comm]
    simpa only [he, hp₁, Nat.mul_comm n ell] using hProbe
  have hlB : m₂.Live [b] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨(hl.congr (hfr₂.length_eq.trans hfr₁.length_eq)) b (by simp), trivial⟩
  refine ((MGS.writes_factor hS hB hC (matrix n n as * S) hlB hImage₂
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; rw [Nat.add_mul] at hb; omega)).in_frame
      rfl rfl hlB).mono hsub ?_
  intro m₃ hfr₃ ⟨hp₃, hQ⟩
  refine ⟨by rw [hp₃, hp₂, hp₁, Nat.mul_add]; omega, ?_⟩
  apply read_basisProbes _ _ hQ
  exact hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (by
    simpa only [Nat.mul_comm n ell] using hdis) hG

end NLAlib.HutchPlusPlus
