/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination

/-!
# The order-one leaf of the small-eigenvalue solver

The worklist of the small-eigenvalue solver runs at the bottom width $k = 1$, so its leaves are
blocks of order $0$ or $1$, whose eigenvalue is the entry itself ([BanksGarzaVargasSrivastava2025,
§6], the base case, the paper's erratum P13). The leaf copies the diagonal entries: exact on
every tape, with backward error $0$ and failure $0$ on orders at most $1$.

## Main definitions

* `NLAlib.SmallEig.copyLeaf`: the program `[d, np, T] (Bk, P) → (Ev)`.

## Main results

* `NLAlib.SmallEig.copyLeaf_writes`, `NLAlib.SmallEig.copyLeaf_randomLeafRoutineContract`,
  `NLAlib.SmallEig.copyLeaf_terminates`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O]

/-- **The order-one Schur leaf**: a block of order $d \le 1$ is already upper triangular, so it is
kept and its accumulator `Ub` is the identity of order $d$ (column-major pairs). The interface is
`[d, np, T] (Bk, P) → (Bk, Ub)`, that of the Schur leaf routine of
`NLAlib.ShiftedQR.solveRoundedWith`; the block, the words and the cap are not read. At any order
it writes the identity.
Algorithm: small-eig -/
def identityLeaf : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Bk, Ub) {
  for j < d {
    for i < d {
      call (Has.inj (ScalarOp.lit 0)) [] () → (Ub[2 * (j * d + i)]);
      call (Has.inj (ScalarOp.lit 0)) [] () → (Ub[2 * (j * d + i) + 1])
    }
  };
  for i < d {
    call (Has.inj (ScalarOp.lit 1)) [] () → (Ub[2 * (i * d + i)])
  }
}

/-- `NLAlib.SmallEig.copyLeaf` on a scalar machine, at any order $d$: from a matrix
$\mathbf{B}$ of order $d$ at `w` and room for $2d$ words at `o`, apart from $\mathbf{B}$, on every
tape, it writes only those words and stores the diagonal of $\mathbf{B}$ as a column of pairs. -/
theorem copyLeaf_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {d np T : ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ} {w p o : ℕ × ℕ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : HoldsMatrix w B μ.store) (hl : μ.Live [w, p, o]) (ho : o.2 + 2 * d ≤ μ.store.len o.1)
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d))) :
    Writes .total I τ (copyLeaf (O := O) (Q := Q)).body (Env.frame [d, np, T] [w, p, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => B i i) μ'.store) μ := by
  unfold copyLeaf
  refine (writes_loop rfl (fun i => Store.inBlock o.1 o.2 (2 * i))
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i μ' => ∀ k (hk : k < d), k < i →
      μ'.store.get o.1 (o.2 + 2 * k) = some (B ⟨k, hk⟩ ⟨k, hk⟩).re ∧
      μ'.store.get o.1 (o.2 + 2 * k + 1) = some (B ⟨k, hk⟩ ⟨k, hk⟩).im)
    (fun k _ h => absurd h (Nat.not_lt_zero k)) ?_).mono le_rfl ?_
  · intro i hi μ' hfr hP
    have hB' := hB.of_eqOff hfr (hwo.symm.mono (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl)
    have hlen : μ'.store.len o.1 = μ.store.len o.1 := hfr.len_eq o.1
    have hre := hB'.get_re ⟨i, hi⟩ ⟨i, hi⟩
    have him := hB'.get_im ⟨i, hi⟩ ⟨i, hi⟩
    have hol : o.1 < μ'.store.length := by
      rw [hfr.length_eq]; exact hl o (by simp)
    refine (writes_call_un (hS .copy) (x := (w.1, w.2 + 2 * (i * d + i)))
      (z := (o.1, o.2 + 2 * i)) rfl rfl trivial hre rfl (by dsimp only; omega)).seq_le
      (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro μ₁ hfr₁ ⟨-, h₁⟩
    have him₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
      (hwo.symm.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
        (Fp.inBlock_le_inBlock (by omega) (by have := hi; nlinarith))) him
    refine (writes_call_un (hS .copy) (x := (w.1, w.2 + 2 * (i * d + i) + 1))
      (z := (o.1, o.2 + 2 * i + 1)) rfl rfl trivial him₁ rfl
      (by rw [hfr₁.len_eq]; dsimp only; omega)).mono
      (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro μ₂ hfr₂ ⟨-, h₂⟩
    intro k hk hki
    have hkeep : ∀ {j v}, j < 2 * i + 1 → μ₁.store.get o.1 (o.2 + j) = some v →
        μ₂.store.get o.1 (o.2 + j) = some v := fun hj hv =>
      hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hki with hk' | rfl
    · obtain ⟨hr, hm⟩ := hP k hk hk'
      have hr₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_le (by omega)).symm hr
      have hm₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_le (by omega)).symm hm
      refine ⟨hkeep (j := 2 * k) (by omega) hr₁, ?_⟩
      rw [Nat.add_assoc] at hm₁ ⊢
      exact hkeep (j := 2 * k + 1) (by omega) hm₁
    · exact ⟨hkeep (j := 2 * k) (by omega) h₁, h₂⟩
  · intro μ' _ hP
    refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
    · have := (hP i i.isLt i.isLt).1
      simpa [Fin.fin_one_eq_zero j] using this
    · have := (hP i i.isLt i.isLt).2
      simpa [Fin.fin_one_eq_zero j] using this

/-- **The leaf is exact on orders at most one** ([BanksGarzaVargasSrivastava2025, §6], the base
case): on a scalar machine, `NLAlib.SmallEig.copyLeaf` meets
`NLAlib.ShiftedQR.RandomLeafRoutineContract` with backward error $0$ and failure probability $0$
on orders at most $1$, for every norm bound, parameter words and cap, under every stream law. -/
theorem copyLeaf_randomLeafRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (law : ℕ → Measure ℝ) (Nmax : ℝ) (ps : List ℝ) (T : ℕ) :
    RandomLeafRoutineContract law 0 0 1 Nmax ps T (copyLeaf (O := O) (Q := Q)) I := by
  intro d w p o B hd _ _
  refine PWrites.of_writes le_rfl fun μ τ ⟨hH, _, hl, hroom, hwo, _⟩ => ?_
  refine (copyLeaf_writes hS hH hl hroom hwo).mono le_rfl fun μ' _ hO => ?_
  have hT : B.IsUpperTriangular := fun i j hji => absurd hji (by omega)
  exact ⟨fun i => B i i, 0, by simp, by simpa using hT.isEigenvalueListing_diag, hO⟩

/-- The leaf terminates on every tape, at every order bound: on a scalar machine
`NLAlib.SmallEig.copyLeaf` is a terminating leaf routine
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`) for every order bound, parameter words and cap. -/
theorem copyLeaf_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) (kmax : ℕ)
    (ps : List ℝ) (T : ℕ) : TerminatingLeafRoutine kmax ps T (copyLeaf (O := O) (Q := Q)) I :=
  fun _ _ hH _ hl hroom hwo _ =>
    (copyLeaf_writes hS hH hl hroom hwo).mono le_rfl fun _ _ h =>
      ⟨_, by simpa only [HoldsMatrix, Nat.one_mul] using h⟩

end NLAlib.SmallEig
