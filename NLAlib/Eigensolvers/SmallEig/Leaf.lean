/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.Schur.Contracts
public import NLAlib.Ops.Blas.Matrix

/-!
# The order-one leaf of the small-eigenvalue solver

The worklist of the small-eigenvalue solver runs at the bottom width $k = 1$, so its leaves are
blocks of order $0$ or $1$, whose eigenvalue is the entry itself ([BanksGarzaVargasSrivastava2025,
§6], the base case, the paper's erratum P13). In Schur mode the leaf keeps the block, which is
already upper triangular, and writes the identity accumulator: exact on
every tape, with backward error $0$ and failure $0$ on orders at most $1$.

## Main definitions

* `NLAlib.SmallEig.identityLeaf`: the order-one Schur leaf `[d, np, T] (Bk, P) → (Bk, Ub)`.

## Main results

* `NLAlib.SmallEig.identityLeaf_writes`,
  `NLAlib.SmallEig.identityLeaf_randomSchurLeafContract`,
  `NLAlib.SmallEig.identityLeaf_terminates`.
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
def identityLeaf : Stmt O Q := ops% [d, np, T] (Bk, P) → (Bk, Ub) {
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

/-- `NLAlib.SmallEig.identityLeaf` on a scalar machine with the literal $0$ exact, and $1$ exact
when $d > 0$, at any order $d$: with room for $2d^2$ words at `ub`, on every tape, it writes only
those words and stores the identity of order $d$. -/
theorem identityLeaf_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (h0 : M.lit 0 = 0) {d : ℕ} (h1 : 0 < d → M.lit 1 = 1) {τ : Tape ℝ} {μ : Mem ℝ}
    {w p ub : ℕ × ℕ} {ps : List ℝ} {T : ℕ} (hroom : ub.2 + 2 * (d * d) ≤ μ.store.len ub.1) :
    Writes .total I τ (identityLeaf (O := O) (Q := Q))
        (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix ub (1 : Matrix (Fin d) (Fin d) ℂ) μ'.store) μ := by
  classical
  let v : ℕ → ℕ → ℝ := fun i q =>
    if ∃ j < i, q = 2 * (j * d + j) then M.lit 1 else M.lit 0
  unfold identityLeaf
  refine Writes.seq_le (G := Store.inBlock ub.1 ub.2 (2 * (d * d)))
    (P := fun μ' => μ'.store.HoldsVec ub.1 ub.2 (2 * (d * d)) (v 0) ∧ μ'.pos = μ.pos) ?_ le_rfl
    ?_
  · refine (writes_loop₂ (N := d) (M := d) rfl (fun _ => rfl)
      (fun j i => Store.inBlock ub.1 ub.2 (2 * (j * d + i)))
      (fun j _ i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
      (fun j _ => Fp.inBlock_le_inBlock le_rfl
        (by have e : (j + 1) * d = j * d + d := by ring
            omega))
      (fun j i μ' => μ'.store.HoldsVec ub.1 ub.2 (2 * (j * d + i)) (v 0) ∧ μ'.pos = μ.pos)
      ⟨fun k hk => absurd hk (by simp), rfl⟩
      (fun j _ μ' h => by rwa [show (j + 1) * d + 0 = j * d + d by ring]) ?_).mono
      (Fp.inBlock_le_inBlock le_rfl (by simp)) (fun μ' _ h => by simpa using h)
    intro j hj i hi μ' hfr ⟨hv, hp⟩
    have hji : j * d + i < d * d := by nlinarith
    have hz : ub.2 + 2 * (j * d + i) < μ'.store.len ub.1 := by rw [hfr.len_eq]; omega
    refine (writes_call_const (hS (.lit 0)) (z := (ub.1, ub.2 + 2 * (j * d + i))) rfl trivial
      hz).seq_le (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro μ₁ hfr₁ ⟨hp₁, h₁⟩
    have hz₁ : ub.2 + 2 * (j * d + i) + 1 < μ₁.store.len ub.1 := by
      rw [hfr₁.len_eq, hfr.len_eq]; omega
    refine (writes_call_const (hS (.lit 0)) (z := (ub.1, ub.2 + 2 * (j * d + i) + 1)) rfl trivial
      hz₁).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro μ₂ hfr₂ ⟨hp₂, h₂⟩
    refine ⟨fun k hk => ?_, hp₂.trans (hp₁.trans hp)⟩
    have hv0 : v 0 k = M.lit 0 := by simp [v]
    rw [hv0]
    rcases lt_or_ge k (2 * (j * d + i)) with hk' | hk'
    · have h0' := hv k hk'
      rw [hv0] at h0'
      exact hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm
        (hfr₁.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm h0')
    · rcases (show k = 2 * (j * d + i) ∨ k = 2 * (j * d + i) + 1 by omega) with rfl | rfl
      · exact hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le le_rfl).symm h₁
      · rw [← Nat.add_assoc]; exact h₂
  · rintro μ₁ hfr₁ ⟨hv₁, hp₁⟩
    have hnext : ∀ i < d, v (i + 1) = Function.update (v i) (2 * (i * d + i)) (M.lit 1) := by
      intro i _
      funext q
      by_cases hq : q = 2 * (i * d + i)
      · subst q
        simp only [v, Function.update_self]
        exact if_pos ⟨i, by omega, rfl⟩
      · rw [Function.update_of_ne hq]
        dsimp only [v]
        have hequiv : (∃ j < i + 1, q = 2 * (j * d + j)) ↔ ∃ j < i, q = 2 * (j * d + j) := by
          constructor
          · rintro ⟨j, hj, hqj⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjlt | rfl
            · exact ⟨j, hjlt, hqj⟩
            · exact (hq hqj).elim
          · rintro ⟨j, hj, hqj⟩
            exact ⟨j, by omega, hqj⟩
        simp only [hequiv]
    refine (writes_patch rfl v (fun i => 2 * (i * d + i)) (fun _ => M.lit 1) hv₁
      (fun i hi => by nlinarith) hnext fun i hi μ₂ hfr₂ _ hpos => ?_).mono le_rfl ?_
    · have hz : ub.2 + 2 * (i * d + i) < μ₂.store.len ub.1 := by
        rw [hfr₂.len_eq, hfr₁.len_eq]
        nlinarith
      exact (writes_call_const (hS (.lit 1)) (z := (ub.1, ub.2 + 2 * (i * d + i))) rfl trivial
        hz).mono le_rfl fun _ _ h => ⟨h.2, h.1.trans hpos⟩
    · rintro μ₂ _ ⟨hv₂, hp₂⟩
      refine ⟨hp₂.trans hp₁, ?_⟩
      have hE := PairMatrix.holdsEntries_of_holdsVec (M := M) (n := d) hv₂
      refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
      · have := hE i i.isLt j j.isLt 0
        by_cases hij : i = j
        · subst hij; simpa [h1 i.pos, EntryCodec.pair] using this
        · simpa [h0, Fin.val_inj, hij, Matrix.one_apply_ne hij, EntryCodec.pair] using this
      · have := hE i i.isLt j j.isLt 1
        by_cases hij : i = j
        · subst hij; simpa [h0, EntryCodec.pair] using this
        · simpa [h0, Fin.val_inj, hij, Matrix.one_apply_ne hij, EntryCodec.pair] using this

/-- **The order-one Schur leaf meets the Schur leaf contract** with errors $0$, for orders at most
$1$: a block of order at most $1$ is upper triangular, kept, with the identity accumulator. -/
theorem identityLeaf_randomSchurLeafContract {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (law : ℕ → Measure ℝ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) :
    Schur.RandomSchurLeafContract law 0 0 0 1 Nmax ps T (identityLeaf (O := O) (Q := Q)) I := by
  intro d w p ub B hd _
  refine PWrites.of_writes le_rfl fun μ τ ⟨hB, _, hl, hroom, hap⟩ => ?_
  have hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
      (Store.inBlock ub.1 ub.2 (2 * (d * d))) := by
    simpa using hap.disj_getD_of_lt (i := 0) (j := 2) (by omega) (by simp)
  refine (identityLeaf_writes hS h0 (fun _ => h1) hroom).mono le_sup_right
    fun μ' hfr ⟨_, hU⟩ => ?_
  exact ⟨1, B, ⟨hB.of_eqOff hfr hwu.symm, hU⟩, fun i j hji => absurd hji (by omega),
    IsTrackedUnitarySimilar.refl 1 B⟩

/-- The order-one Schur leaf terminates on every tape, with its accumulator exactly unitary on
orders at most $1$ (`NLAlib.ShiftedQR.TerminatingLeafRoutine` at $\varepsilon_L = 0$). -/
theorem identityLeaf_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (ps : List ℝ) (T : ℕ) :
    TerminatingLeafRoutine 0 1 ps T (identityLeaf (O := O) (Q := Q)) I :=
  fun B _ hB _ hl hroom hwu _ =>
    (identityLeaf_writes hS h0 (fun _ => h1) hroom).mono le_sup_right fun _ hfr ⟨_, hU⟩ =>
      ⟨B, 1, 1, hB.of_eqOff hfr hwu.symm, hU, hasOrthonormalCols_one, by simp⟩

end NLAlib.SmallEig
