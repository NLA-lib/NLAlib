/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingFrames

/-!
# Initialization for rounded pivoted LU

The existing full driver copies the input into a distinct residual workspace, then initializes
both factor blocks with actual scalar zero literals. These operations succeed for arbitrary
word carriers and charge monoids and preserve the complete store outside their three blocks.

## Main results

* `NLAlib.Computation.PLURounding.exec_initialize`: copied decoded input and zero factors.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Readable decoded input and writable separate residual/factor blocks suffice for the
actual initialization to succeed under standard relative-error semantics with every scalar
result in range. The residual contains the copied input, both decoded factors are zero,
and only the three full declared blocks may change. No index or roundoff upper-bound
assumption is needed. [GolubVanLoan2013, §3.2]. -/
theorem exec_initialize {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (A S L U : ℕ) (ao lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : HoldsDecoded st.store dec p A ao.eval M)
    (hS : Writable st.store p S 0 (n.eval * n.eval))
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hAS : A ≠ S) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (do
        copyv p A ao S 0 (n * n)
        forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
        forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, (b ≠ S ∨ n.eval * n.eval ≤ idx) →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      HoldsDecoded out.store dec p S 0 M ∧
      HoldsDecoded out.store dec p L lo.eval (0 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ∧
      HoldsDecoded out.store dec p U uo.eval (0 : Matrix (Fin n.eval) (Fin n.eval) ℝ) := by
  classical
  choose Mw hMw hdMw using hM
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw
  have hraw : Holds st.store p A ao.eval Mw := hMw
  obtain ⟨W, hWs, hflat, -, -⟩ := hraw.exists_array
  have hx : ∀ i < (n * n).eval, ∃ w, st.store.read p A (ao.eval + i) = some w := by
    intro i hi
    have ht : i < W.size := by rw [hWs]; simpa only [IExp.eval_mul] using hi
    exact ⟨W[i], (hflat i (by simpa only [IExp.eval_mul] using hi)).trans
      (Array.getElem?_eq_getElem ht)⟩
  obtain ⟨copied, hcopy, hcsh, hcread, hcfr⟩ := exec_copyv_block I p st (n * n) A S ao 0
    hx hAS (by simpa only [Writable, IExp.eval_mul, IExp.eval_zero] using hS)
  have hCM : HoldsDecoded copied.store dec p S 0 M := by
    intro i j
    refine ⟨Mw i j, ?_, hdMw i j⟩
    have hh := hcread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
    simpa only [Nat.add_assoc, IExp.eval_zero] using hh.trans
      (by simpa only [Nat.add_assoc] using hMw i j)
  obtain ⟨z, hz⟩ := h.lit_ok p 0 trivial
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, hd⟩ := h.lit_err p 0 z hz
    simpa only [Rat.cast_zero, zero_mul] using hd
  obtain ⟨sl, hlrun, hlsh, hlread, hlfr⟩ := exec_forRange_literal_zero I p z hz copied
    (n * n) L lo (by simpa only [Writable, IExp.eval_mul] using hL.of_shape_eq hcsh)
  let lower : St P K C :=
    { copied with store := sl, cnt := copied.cnt + (n * n).eval • I.charge (.lit p) }
  obtain ⟨su, hurun, hush, huread, hufr⟩ := exec_forRange_literal_zero I p z hz lower
    (n * n) U uo
    (by simpa only [Writable, IExp.eval_mul, lower] using hU.of_shape_eq (hlsh.trans hcsh))
  let out : St P K C :=
    { lower with store := su, cnt := lower.cnt + (n * n).eval • I.charge (.lit p) }
  refine ⟨out, ?_, hush.trans (hlsh.trans hcsh), ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := copyv p A ao S 0 (n * n)) (fun _ => rfl), hcopy,
      Option.bind_some, exec_run_bind I
        (b := forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)) (fun _ => rfl),
      hlrun, Option.bind_some]
    exact hurun
  · intro q b idx hbS hbL hbU
    rw [hufr q b idx (Or.inr (by simpa only [IExp.eval_mul] using hbU)),
      hlfr q b idx (Or.inr (by simpa only [IExp.eval_mul] using hbL)),
      hcfr q b idx (by simpa only [IExp.eval_zero, IExp.eval_mul, Nat.zero_add,
        Nat.not_lt_zero, false_or] using hbS)]
  · intro i j
    obtain ⟨w, hw, hd⟩ := hCM i j
    refine ⟨w, ?_, hd⟩
    rw [hufr p S _ (Or.inr (Or.inl hSU)), hlfr p S _ (Or.inr (Or.inl hSL))]
    exact hw
  · intro i j
    refine ⟨z, ?_, by simpa only [Matrix.zero_apply] using hdz⟩
    rw [hufr p L _ (Or.inr (Or.inl hLU))]
    simpa only [lower, Nat.add_assoc] using hlread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
  · intro i j
    refine ⟨z, ?_, by simpa only [Matrix.zero_apply] using hdz⟩
    simpa only [out, Nat.add_assoc] using huread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)

end NLAlib.Computation.PLURounding
