/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Reduce

/-!
# Total guarded normalization

The executable test reads the actual real norm square. Zero residuals are preserved;
nonzero residuals are divided by the embedded positive real norm. The mathematical
residual identity supplies the nonzero divisor without a successful-execution premise.

## Main results

* `NLAlib.MGS.writes_normalizeGuard` executes the stored norm-square decision.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  [Has CmpTst Tst] {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- The guard uses the actual stored squared norm and returns the corresponding
normalized vector. Its total execution includes both the zero and nonzero branches. -/
theorem writes_normalizeGuard (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n : ℕ} {v t : ℕ × ℕ} (w : Fin n → 𝕜) (d : 𝕜) (hl : m.Live [v, t])
    (hv : m.store.readBlock v.1 v.2 n = some (List.ofFn w))
    (hd : m.store.readBlock t.1 (t.2 + 1) 1 = some [d])
    (hzero : m.store.get t.1 t.2 = some 0)
    (htv : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock v.1 v.2 n))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ normalizeGuard.body (Env.frame [n] [v, t])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (if RCLike.re d = 0 then List.ofFn w else
          List.ofFn fun i : Fin n => w i / RCLike.ofReal (Real.sqrt (RCLike.re d)))) m := by
  classical
  have hg : m.store.get t.1 (t.2 + 1) = some d := by
    simpa using Store.get_of_readBlock hd Nat.zero_lt_one (0 : 𝕜)
  have htest := hC.test_eq (d := []) (x := (t.1, t.2 + 1)) (y := t) hg hzero
  have hsub : Store.inBlock t.1 (t.2 + 1) 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  unfold normalizeGuard
  dsimp only
  by_cases he : RCLike.re d = 0
  · refine writes_ite rfl rfl (by simpa [he] using htest) ?_
    exact (Writes.skip ⟨rfl, by simpa [he] using hv⟩).mono bot_le (fun _ _ h => h)
  · refine writes_ite rfl rfl (by simpa [he] using htest) ?_
    refine Writes.seq_le (writes_call_fn1 (hS .sqrt) (xs := [[d]])
      rfl rfl rfl rfl rfl trivial
      (by simp only [Mem.live_append, Mem.live_cons, Mem.live_nil];
          exact ⟨⟨hl t (by simp), trivial⟩, hl t (by simp), trivial⟩)
      (by simp [Machine.fn, Mem.readBlocks, hd]) rfl rfl (by omega))
      (hsub.trans le_sup_left) ?_
    intro m₁ hfr ⟨hp, hr⟩
    have hv₁ := hfr.keep (Store.readsOnly_readBlock v.1 v.2 n (List.ofFn w))
      (htv.mono hsub le_rfl) hv
    have hl₁ := hl.congr hfr.length_eq
    refine (RCLikeBlas.writes_scal hB rfl rfl rfl
      (by simp only [Mem.live_cons, Mem.live_nil];
          exact ⟨hl₁ t (by simp), hl₁ v (by simp), hl₁ v (by simp), trivial⟩)
      hr hv₁ (htv.mono hsub le_rfl) (Or.inr rfl)
      (by simpa only [hfr.len_eq] using hz)).mono le_sup_right ?_
    intro m₂ _ ⟨hp₂, hv₂⟩
    exact ⟨hp₂.trans hp, by simpa [he, RCLikeBlas.machine,
      List.getD_eq_getElem?_getD] using hv₂⟩

/-- Compute the actual Hermitian norm square and perform the guarded normalization.
The statement covers every vector, including zero, with no execution-success premise. -/
theorem writes_normalize (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n : ℕ} {v t : ℕ × ℕ} (w : Fin n → 𝕜) (hl : m.Live [v, t])
    (hv : m.store.readBlock v.1 v.2 n = some (List.ofFn w))
    (htv : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock v.1 v.2 n))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ normalize.body (Env.frame [n] [v, t])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (if RCLike.re (star w ⬝ᵥ w) = 0 then List.ofFn w else
          List.ofFn fun i : Fin n =>
            w i / RCLike.ofReal (Real.sqrt (RCLike.re (star w ⬝ᵥ w))))) m := by
  have ht₀ : Store.inBlock t.1 t.2 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have ht₁ : Store.inBlock t.1 (t.2 + 1) 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  unfold normalize
  dsimp only
  refine Writes.seq_le (RCLikeBlas.writes_dot hB rfl rfl rfl
    (by simp only [Mem.live_cons, Mem.live_nil];
        exact ⟨hl v (by simp), hl v (by simp), hl t (by simp), trivial⟩)
    hv hv (htv.mono ht₁ le_rfl) (htv.mono ht₁ le_rfl) (by omega)) (ht₁.trans le_sup_left) ?_
  intro m₁ hfr₁ ⟨hp₁, hd₁⟩
  have hv₁ := hfr₁.keep (Store.readsOnly_readBlock v.1 v.2 n (List.ofFn w))
    (htv.mono ht₁ le_rfl) hv
  have hd₁' : m₁.store.readBlock t.1 (t.2 + 1) 1 = some [star w ⬝ᵥ w] := by
    simpa only [RCLikeBlas.dot_ofFn, dotProduct, Pi.star_apply] using hd₁
  refine Writes.seq_le (writes_call_const (hS (.lit 0)) rfl trivial
    (by change t.2 < m₁.store.len t.1; rw [hfr₁.len_eq]; omega)) (ht₀.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hz₂⟩
  have hv₂ := hfr₂.keep (Store.readsOnly_readBlock v.1 v.2 n (List.ofFn w))
    (htv.mono ht₀ le_rfl) hv₁
  have hd₂ := hfr₂.keep (Store.readsOnly_readBlock t.1 (t.2 + 1) 1 [star w ⬝ᵥ w])
    (Fp.disj_inBlock_of_le (by omega)) hd₁'
  have hl₂ := hl.congr (hfr₂.length_eq.trans hfr₁.length_eq)
  refine ((writes_normalizeGuard hS hB hC w (star w ⬝ᵥ w) hl₂ hv₂ hd₂
    (by simpa [RCLikeBlas.machine] using hz₂) htv
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using ht)
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using hz)).in_frame
      rfl rfl hl₂).mono le_rfl ?_
  intro m₃ _ ⟨hp₃, hv₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hv₃⟩

/-- A Gram–Schmidt residual normalizes to its intended column at every rank. The
zero-coefficient case returns the zero column, and the other case has a nonzero divisor. -/
theorem writes_normalize_residual (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {n : ℕ} {v t : ℕ × ℕ} (q : Fin n → 𝕜) (ρ : 𝕜) (hρ : 0 ≤ ρ)
    (hzero : ρ = 0 → q = 0) (hunit : ρ ≠ 0 → star q ⬝ᵥ q = 1)
    (hl : m.Live [v, t])
    (hv : m.store.readBlock v.1 v.2 n = some (List.ofFn (ρ • q)))
    (htv : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock v.1 v.2 n))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ normalize.body (Env.frame [n] [v, t])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn q)) m := by
  refine (writes_normalize hS hB hC (ρ • q) hl hv htv ht hz).mono le_rfl ?_
  intro m' _ ⟨hp, hv'⟩
  refine ⟨hp, ?_⟩
  have he := congrArg (List.ofFn (n := n)) (normalize_residual q ρ hρ hzero hunit)
  by_cases hz : RCLike.re (star (ρ • q) ⬝ᵥ (ρ • q)) = 0
  · rw [if_pos hz] at hv' he
    exact hv'.trans (congrArg some he)
  · rw [if_neg hz] at hv' he
    exact hv'.trans (congrArg some he)

end NLAlib.MGS
