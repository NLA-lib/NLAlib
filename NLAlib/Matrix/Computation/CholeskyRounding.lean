/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Cholesky
public import NLAlib.Computation.BLAS.RoundingErrors

/-!
# Rounded execution of a Cholesky column

The actual stored column routine first computes a rounded square root of its positive Schur
pivot and then divides the lower column by that computed diagonal. The scalar model gives
local relative errors for these instructions and ensures the diagonal remains positive when
the unit roundoff is below one. The result includes successful execution and the complete
two-block output frame. It makes no claim of full rounded factorization stability.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_choleskyColumn`: rounded success and local error relations.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A positive decoded Schur pivot suffices for the actual Cholesky column routine to succeed
in the standard scalar model with every value in range and unit roundoff $u_p<1$.
Its diagonal word $d$ decodes to a positive value with relative error at most $u_p$ from
$\sqrt a$. Each lower entry has relative error at most $u_p$ from division of the original
entry by the computed diagonal. The only store effects are the diagonal singleton and vector
block writes, in that order. Output blocks may share a buffer when disjoint; the pivot may
alias either input or output, and the vector may be empty. Arithmetic charges are arbitrary.
These are local instruction errors from [Higham2002, §2.2], not a full factorization bound. -/
theorem IsRelErrSem.exec_choleskyColumn {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (pivot diag : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ)
    (a : ℝ) (xs : ℕ → ℝ) (ha : 0 < a) (hu : u p < 1)
    (hp : ∃ v, st.store.read p pivot.buf pivot.idx.eval = some v ∧ dec p v = a)
    (hx : ∀ i < n.eval, ∃ v, st.store.read p x (xo.eval + i) = some v ∧ dec p v = xs i)
    (hd : Writable st.store p diag.buf diag.idx.eval 1)
    (hdis : blockDisjoint (diag.buf, diag.idx.eval, 1) (x, xo.eval, n.eval) = true) :
    ∃ (out : St P K C) (d : K) (W : ℕ → K),
      exec I (choleskyColumn p pivot diag x xo n).run st = some out ∧
      st.store.writeBlocks p [(diag.buf, diag.idx.eval, 1), (x, xo.eval, n.eval)]
        [#[d], (List.range n.eval).toArray.map W] = some out.store ∧
      0 < dec p d ∧ RelErr (u p) (Real.sqrt a) (dec p d) ∧
      ∀ i < n.eval, RelErr (u p) (xs i / dec p d) (dec p (W i)) := by
  obtain ⟨v, hp, hda⟩ := hp
  obtain ⟨d, hroot⟩ := h.sqrt_ok p v (by rw [hda]; exact ha.le)
  obtain ⟨δ, hδ, hdd⟩ := h.sqrt_err p v d hroot
  rw [hda] at hdd
  have hdpos : 0 < dec p d := by
    rw [hdd]
    apply mul_pos (Real.sqrt_pos.mpr ha)
    have := (abs_le.mp hδ).1
    linarith
  obtain ⟨len, hlen, hlt⟩ := hd 0 (by omega)
  obtain ⟨mid, hm⟩ := Store.exists_write_eq_some_of_getElem?_shape d hlen (by simpa using hlt)
  have hne : ∀ i < n.eval, x ≠ diag.buf ∨ xo.eval + i ≠ diag.idx.eval := by
    intro i hi
    have hh := blockDisjoint_iff.mp hdis
    dsimp only at hh
    omega
  have hx' : ∀ i < n.eval, ∃ v, mid.read p x (xo.eval + i) = some v ∧ dec p v = xs i := by
    intro i hi
    obtain ⟨w, hw, hdw⟩ := hx i hi
    exact ⟨w, (Store.read_of_write_eq_some_of_ne hm (hne i hi)).trans hw, hdw⟩
  let ready : St P K C :=
    { st with store := mid, cnt := st.cnt + I.charge (.un p .sqrt) }
  obtain ⟨out, W, hr, hw, hW⟩ := h.exec_rscl I p ready diag x xo n (dec p d) xs hdpos.ne'
    ⟨d, Store.read_of_write_eq_some hm, rfl⟩ hx'
    (fun he i hi => ((hne i hi).resolve_left (fun hne => hne he.symm)).symm)
  have hm' : st.store.writeBlock p diag.buf diag.idx.eval #[d] = some mid := by
    simpa [Store.writeBlock] using hm
  refine ⟨out, d, W, ?_, ?_, hdpos, ⟨δ, hδ, hdd⟩, hW⟩
  · change exec I (.seq (.seq (.instr (.un p .sqrt diag pivot))
      (rscl p diag x xo n).run) .skip) st = some out
    rw [exec_seq_skip]
    exact (exec_seq_instr_un I hp hroot hm).trans hr
  · exact Store.writeBlocks_pair_eq_some_iff.mpr
      ⟨by simp, by simp, mid, hm', hw⟩

end NLAlib.Computation
