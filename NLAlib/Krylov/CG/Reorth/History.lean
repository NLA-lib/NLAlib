/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Interface

/-!
# Initialized residual history for full reorthogonalization

Only the initialized prefix of the basis is read. Appending the current residual extends
that prefix by one column; future allocated columns can remain uninitialized.

## Main results

* `NLAlib.Krylov.CG.Reorth.StoresHistory`: the stored initialized residual prefix.
* `NLAlib.Krylov.CG.Reorth.storesHistory_snoc`: extend it by a newly written column.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {K : Type} [Inhabited K]

omit [Inhabited K] in
private theorem readBlock_append {s : Store K} {b o n m : ℕ} {xs ys : List K}
    (hx : s.readBlock b o n = some xs) (hy : s.readBlock b (o + n) m = some ys) :
    s.readBlock b o (n + m) = some (xs ++ ys) := by
  obtain ⟨hxl, hxg⟩ := Store.readBlock_eq_some_iff.mp hx
  obtain ⟨hyl, hyg⟩ := Store.readBlock_eq_some_iff.mp hy
  refine Store.readBlock_eq_some_iff.mpr ⟨by simp [hxl, hyl], fun j hj => ?_⟩
  by_cases hn : j < n
  · rw [List.getElem?_append_left (by omega), hxg j hn]
  · rw [List.getElem?_append_right (by omega), hxl]
    have e : o + j = o + n + (j - n) := by omega
    rw [e, hyg (j - n) (by omega)]

/-- An initialized prefix stores precisely the first `k` residual vectors. -/
def StoresHistory (dec : K → ℝ) (n : ℕ) (Q : ℕ × ℕ)
    (v : ℕ → Fin n → ℝ) (k : ℕ) (μ : Mem K) : Prop :=
  ∃ qs, μ.store.readBlock Q.1 Q.2 (k * n) = some qs ∧ ∀ j < k, column dec n qs j = v j

/-- No history cells need initialization before the first active round. -/
theorem storesHistory_zero (dec : K → ℝ) (n : ℕ) (Q : ℕ × ℕ)
    (v : ℕ → Fin n → ℝ) (μ : Mem K) : StoresHistory dec n Q v 0 μ :=
  ⟨[], by simp, fun _ h => (Nat.not_lt_zero _ h).elim⟩

/-- A new column extends the initialized history without reading any later cells. -/
theorem storesHistory_snoc {dec : K → ℝ} {n k : ℕ} {Q : ℕ × ℕ}
    {v : ℕ → Fin n → ℝ} {μ : Mem K} {qs rs : List K}
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hrs : μ.store.readBlock Q.1 (Q.2 + k * n) n = some rs)
    (hprev : ∀ j < k, column dec n qs j = v j) (hcur : decv dec n rs = v k) :
    StoresHistory dec n Q v (k + 1) μ := by
  have hlen := Store.length_of_readBlock hqs
  refine ⟨qs ++ rs, by simpa only [Nat.add_mul, Nat.one_mul] using readBlock_append hqs hrs,
    fun j hj => ?_⟩
  by_cases h : j < k
  · rw [← hprev j h]
    funext i
    exact congrArg dec (vec_append_left (by rw [hlen]; exact Idx.add_lt_mul h i.isLt) rs)
  · have e : j = k := by omega
    subst j
    rw [← hcur]
    funext i
    exact congrArg dec (by simpa only [hlen] using vec_append_right qs rs i)

end NLAlib.Krylov.CG.Reorth
