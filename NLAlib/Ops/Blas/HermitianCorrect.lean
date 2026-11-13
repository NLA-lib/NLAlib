/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.HermitianUpper
public import NLAlib.Ops.Blas.HermitianMirror

/-!
# Functional correctness of Hermitian scalar kernels

Upper-entry computations and mirroring compose through one shared completion theorem. The
computed words use the supplied scalar machine, including its literal zero and every rounded
division. Numerical accuracy and Hermitian decoding require the machine's numerical model;
functional execution itself makes neither assumption.

## Main results

* `NLAlib.Ops.Hermitian.writes_shift`: scalar-visible shifted Hermitian completion.
* `NLAlib.Ops.Hermitian.writes_scale`: scalar-visible division with Hermitian completion.
* `NLAlib.Ops.Hermitian.writes_average`: scalar-visible averaging with Hermitian completion.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- An upper-region implementation followed by the common mirror procedure returns the
complete matrix. The mirror's framing, buffer liveness and capacity transport are shared by
all three entrywise transformations. -/
theorem writes_complete {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} (up : Impl Op Tst) {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K}
    (U : ℕ → ℕ → K × K) (hy : y.1 < m.store.length)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1)
    (hu : Writes .total I τ up.body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) U ∧ μ.pos = m.pos) m) :
    Writes .total I τ (complete up).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M U) ∧ μ.pos = m.pos) m := by
  refine hu.seq_le le_rfl fun μ hfr hp => ?_
  have hy' : y.1 < μ.store.length := by rw [hfr.length_eq]; exact hy
  have hY' : y.2 + 2 * (n * n) ≤ μ.store.len y.1 := by rw [hfr.len_eq]; exact hY
  have hw := writes_mirror (md := .total) (τ := τ) hI U hy' hY' hp.1
  refine (writes_frame rfl rfl (by simp [Mem.Live, hy']) hw).mono ?_ ?_
  · exact (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
      (fun i j => i * n + j) id (fun j hj i hi => Idx.add_lt_mul (hi.trans hj) hj)
  · intro μ' _ h
    exact ⟨h.1, h.2.trans hp.2⟩

/-- A shifted Hermitian matrix is computed from copied upper entries and actual rounded
real diagonal differences. Disjoint input/output regions may belong to the same arena. -/
theorem writes_shift {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (shift (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then
          (M.sub (A i i).1 d, M.lit 0) else A i j)) ∧ μ.pos = m.pos) m :=
  writes_complete hI shiftUpper _ (hl y (by simp)) hY
    (writes_shiftUpper hI hxy hcy hX hc hY hl)

/-- Scalar division and Hermitian completion return the actual rounded word matrix.
A nonzero decoded divisor is needed for numerical error estimates, rather than this
functional execution theorem. -/
theorem writes_scale {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (scale (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then (M.div (A i i).1 d, M.lit 0)
          else (M.div (A i j).1 d, M.div (A i j).2 d))) ∧ μ.pos = m.pos) m :=
  writes_complete hI scaleUpper _ (hl y (by simp)) hY
    (writes_scaleUpper hI hxy hcy hX hc hY hl)

/-- Rounded addition/subtraction of transposed entries, rounded division, and completion
return the actual Hermitian-averaged word matrix with imaginary diagonal zero. -/
theorem writes_average {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (average (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then
          (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0)
          else (M.div (M.add (A i j).1 (A j i).1) d,
            M.div (M.sub (A i j).2 (A j i).2) d))) ∧ μ.pos = m.pos) m :=
  writes_complete hI averageUpper _ (hl y (by simp)) hY
    (writes_averageUpper hI hxy hcy hX hc hY hl)

end NLAlib.Ops.Hermitian
