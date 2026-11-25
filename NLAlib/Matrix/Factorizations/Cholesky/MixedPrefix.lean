/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightPrefix
public import NLAlib.Matrix.Perturbation.CholeskyRange

/-!
# Stored prefixes for finite-range Cholesky

The stored residual stays close to the exact Gaussian state. Completed factor columns
retain their uniform entry error, positive diagonal and literal upper zeros. The invariant
records values of actual stored words and contains no execution or safety oracle.

## Main results

* `NLAlib.Cholesky.IsMixedPrefix.initial`: the copied and initialized words.
* `NLAlib.Cholesky.IsMixedPrefix.succ`: a committed approximate column extends the prefix.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K : Type} {N : ℕ}

/-- Actual residual and factor words with propagated residual and committed-column errors. -/
def IsMixedPrefix (dec : K → ℝ) (zero : K) (u η B μ e : ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (R L : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ rw lw : ℕ → ℕ → K,
    s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw ∧
    s.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw ∧
    (∀ i j : Fin N, |dec (rw i j) - gaussState A k i j| ≤
      choleskyMixedSchurErrorBound u η B μ k) ∧
    (∀ i j : Fin N, j.val < k → |dec (lw i j) - choleskyLower A i j| ≤ e) ∧
    (∀ j : Fin N, j.val < k → 0 < dec (lw j j)) ∧
    (∀ i j : Fin N, i < j → lw i j = zero)

variable [Inhabited K]

/-- Copied input and a literal-filled factor establish the numerical prefix at zero.
No exact arithmetic law is required. -/
theorem IsMixedPrefix.initial {M : Machine K} {dec : K → ℝ} {u η B μ e : ℝ}
    {R L : ℕ × ℕ} {s : Store K} {as : List K}
    (hR : s.readBlock R.1 R.2 (N * N) = some as)
    (hL : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) :
    IsMixedPrefix dec (M.lit 0) u η B μ e (decodeMatrix dec N N as) 0 R L s := by
  refine ⟨fun i j => vec as (j * N + i), fun _ _ => M.lit 0,
    Store.holdsMat_of_readBlock rfl hR, ?_, ?_, fun _ _ h => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
  · intro i hi j hj
    have hh := Store.holdsMat_of_readBlock (L := ⟨L.1, L.2, N, N, N⟩) rfl hL i hi j hj
    simpa only [vec,
      List.getD_replicate (α := K) (x := M.lit 0) (h := Idx.add_lt_mul hj hi)] using hh
  · intro i j
    rw [gaussState_zero, decodeMatrix_apply, sub_self, abs_zero]
    rfl

/-- A column suffix with bounded error and positive root extends the stored factor prefix.
The next residual error is established independently by the actual Schur update. -/
theorem IsMixedPrefix.succ {dec : K → ℝ} {zero : K} {u η B μ e : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L : ℕ × ℕ} {s : Store K}
    (k : Fin N) (rw lw : ℕ → ℕ → K) (ys : List K)
    (hR : s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw)
    (hL : s.HoldsMat ⟨L.1, L.2, N, N, N⟩
      (fun i j => if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j))
    (hres : ∀ i j : Fin N, |dec (rw i j) - gaussState A (k.val + 1) i j| ≤
      choleskyMixedSchurErrorBound u η B μ (k.val + 1))
    (hfac : ∀ i j : Fin N, j.val < k.val → |dec (lw i j) - choleskyLower A i j| ≤ e)
    (hdiag : ∀ j : Fin N, j.val < k.val → 0 < dec (lw j j))
    (hupper : ∀ i j : Fin N, i < j → lw i j = zero)
    (hzero : dec zero = 0) (he : 0 ≤ e)
    (hy : ∀ i : Fin N, k ≤ i → |dec (vec ys (i.val - k.val)) - choleskyLower A i k| ≤ e)
    (hypos : 0 < dec (vec ys 0)) :
    IsMixedPrefix dec zero u η B μ e A (k.val + 1) R L s := by
  refine ⟨rw, fun i j => if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j,
    hR, hL, hres, ?_, ?_, ?_⟩
  · intro i j hj
    change |dec (if j.val = k.val ∧ k.val ≤ i.val then vec ys (i.val - k.val) else lw i j) -
      choleskyLower A i j| ≤ e
    by_cases hjk : j.val < k.val
    · rw [if_neg (fun h => hjk.ne h.1)]
      exact hfac i j hjk
    · have hjk : j = k := Fin.ext (by omega)
      subst j
      by_cases hki : k ≤ i
      · rw [if_pos ⟨rfl, hki⟩]
        exact hy i hki
      · rw [if_neg (fun h => hki h.2), hupper i k (lt_of_not_ge hki), hzero,
          isLowerTriangular_choleskyLower A (lt_of_not_ge hki), sub_self, abs_zero]
        exact he
  · intro j hj
    change 0 < dec (if j.val = k.val ∧ k.val ≤ j.val then vec ys (j.val - k.val) else lw j j)
    by_cases hjk : j.val < k.val
    · rw [if_neg (fun h => hjk.ne h.1)]
      exact hdiag j hjk
    · have hjk : j = k := Fin.ext (by omega)
      subst j
      simpa only [and_self, le_refl, if_true, Nat.sub_self] using hypos
  · intro i j hij
    change (if j.val = k.val ∧ k.val ≤ i.val then vec ys (i.val - k.val) else lw i j) = zero
    rw [if_neg (by intro h; have hlt : i.val < j.val := hij; omega)]
    exact hupper i j hij

/-- The completed stored prefix yields the actual factor words, triangular shape,
positive diagonal and uniform entry error. -/
theorem IsMixedPrefix.read_factor {dec : K → ℝ} {zero : K} {u η B μ e : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L : ℕ × ℕ} {s : Store K}
    (hzero : dec zero = 0) (h : IsMixedPrefix dec zero u η B μ e A N R L s) :
    ∃ ls : List K, s.readBlock L.1 L.2 (N * N) = some ls ∧
      (decodeMatrix dec N N ls).IsLowerTriangular ∧
      (∀ i : Fin N, 0 < decodeMatrix dec N N ls i i) ∧
      (∀ i j : Fin N, |decodeMatrix dec N N ls i j - choleskyLower A i j| ≤ e) ∧
      (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = zero) := by
  obtain ⟨rw, lw, hR, hL, hres, hfac, hdiag, hupper⟩ := h
  obtain ⟨ls, hls, -, hdata⟩ := hL.readBlock rfl
  have hd (i j : Fin N) : decodeMatrix dec N N ls i j = dec (lw i j) := by
    rw [decodeMatrix_apply, hdata i i.isLt j j.isLt]
  refine ⟨ls, hls, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hd, hupper i j hij, hzero]
  · intro i
    rw [hd]
    exact hdiag i i.isLt
  · intro i j
    rw [hd]
    exact hfac i j j.isLt
  · intro i j hij
    rw [hdata i i.isLt j j.isLt]
    exact hupper i j hij

end NLAlib.Cholesky
