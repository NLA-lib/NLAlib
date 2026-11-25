/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Contract
public import NLAlib.Computation.RoutineFrames

/-!
# Reciprocal scaling under an arithmetic error contract

The actual vector kernel succeeds when its decoded divisor is nonzero and each exact quotient
is in range. A generic one-word-per-iteration frame gives the entire vector block write.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_rscl`: actual successful reciprocal scaling with
  per-entry arithmetic errors and the full output block frame.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C) {dec : P → K → ℝ}

/-- The actual reciprocal-scaling kernel succeeds under an arithmetic error contract
when each exact quotient is in range. It writes precisely the vector block and supplies one
error witness per division, with arbitrary word carriers and charge monoids. The nonzero
divisor must not alias a vector cell. -/
theorem IsArithErrSem.exec_rscl {err : P → BinOp → ℝ → ℝ → Prop} {safe : P → ℝ → Prop}
    (h : IsArithErrSem err dec safe I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo n : IExp ℕ) (av : ℝ) (xs : ℕ → ℝ) (hav : av ≠ 0)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i)
    (hsafe : ∀ i < n.eval, safe p (xs i / av)) :
    ∃ st', ∃ W : ℕ → K, exec I (rscl p a x xo n).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, err p .div (xs i / av) (dec p (W i)) := by
  obtain ⟨wa, hwa, hva⟩ := ha
  obtain ⟨out, W, hr, hw, hW⟩ := exists_exec_loop_writeBlock I (n := n) p x xo.eval
    (fun k w => err p .div (xs k / av) (dec p w)) (fun k hk ys σ hsize _ hwrite => by
      obtain ⟨wx, hwx, hvx⟩ := hx k hk
      have hx' : σ.store.read p x (xo.eval + k) = some wx :=
        (Store.read_of_writeBlock_eq_some_of_ne hwrite (Or.inr (Or.inr (by omega)))).trans hwx
      have hdis : a.buf ≠ x ∨ a.idx.eval < xo.eval ∨ xo.eval + ys.size ≤ a.idx.eval := by
        by_cases hb : a.buf = x
        · right
          by_contra hh
          push Not at hh
          have hn : a.idx.eval - xo.eval < n.eval := by omega
          have hn' := hax hb (a.idx.eval - xo.eval) hn
          omega
        · exact Or.inl hb
      have ha' : σ.store.read p a.buf a.idx.eval = some wa :=
        (Store.read_of_writeBlock_eq_some_of_ne hwrite hdis).trans hwa
      obtain ⟨z, hz⟩ := h.bin_ok p .div wx wa trivial (fun _ => by rwa [hva])
        (by simpa only [BinOp.realOp, hvx, hva] using hsafe k hk)
      obtain ⟨len, hshape, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some hx'
      obtain ⟨store, hs, hrun, -, -, -⟩ := exec_scalar_bin I p σ .div
        ⟨x, xo + .var k⟩ ⟨x, xo + .var k⟩ a wx wa z
        (by simpa only [IExp.eval_add, IExp.eval_var] using hx') ha' hz
        ⟨len, hshape, by simpa only [IExp.eval_add, IExp.eval_var] using hlt⟩
      refine ⟨_, z, hrun, ?_, ?_⟩
      · simpa only [IExp.eval_add, IExp.eval_var] using hs
      · simpa only [BinOp.realOp, hvx, hva] using h.bin_err p .div wx wa z trivial hz)
  let words : ℕ → K := fun k => if hk : k < n.eval then W ⟨k, hk⟩ else wa
  have hwords : (List.range n.eval).toArray.map words = Array.ofFn W := by
    apply Array.ext
    · simp
    · intro i hi hi'
      simp only [Array.size_map, List.size_toArray, List.length_range] at hi
      simp [words, hi]
  refine ⟨out, words, ?_, hwords ▸ hw, ?_⟩
  · rw [run_rscl, exec_seq_skip, exec_named, exec_seq_skip]
    exact hr
  · intro i hi
    simpa only [words, dif_pos hi] using hW ⟨i, hi⟩

end NLAlib.Computation
