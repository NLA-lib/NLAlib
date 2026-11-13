/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Frames

/-!
# Guarded vector normalization

The actual branch fills its destination with zeros at zero norm. Otherwise it copies the
source and divides by the stored nonzero norm. Execution retains every other cell and all
usage fields, with a componentwise bound covering both alternatives. Zero dimension and
zero vectors are included. Direct-index zero initialization has the same execution as the
zero-offset form for every interpretation, including failed executions.

## Main results

* `exec_normalize_branch`: exact normalized vector, storage frame and operation budget.
* `exec_normalize_branch_var_eq`: direct-index and zero-offset branch execution equality.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι : Type} [DecidableEq P]

private theorem exec_copyv_rscl_frame (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (src dst : ℕ)
    (soff doff : IExp ℕ) (a : Cell ℕ ℕ) (r : ℝ) (xs : ℕ → ℝ) (hr : r ≠ 0)
    (ha : st.store.read tag a.buf a.idx.eval = some r)
    (hx : ∀ i < n.eval, st.store.read tag src (soff.eval + i) = some (xs i))
    (hdisjoint : src ≠ dst) (had : a.buf ≠ dst)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[dst]? = some (tag, len) ∧ doff.eval + i < len) :
    ∃ out, exec I (do copyv tag src soff dst doff n; rscl tag a dst doff n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag dst (doff.eval + i) = some (xs i / r)) ∧
      (∀ q b i, (b ≠ dst ∨ i < doff.eval ∨ doff.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + n.eval • Finsupp.single (.copy tag) 1 +
        n.eval • Finsupp.single (.bin tag .div) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨mid, hcopy, hsh, hread, hframe, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_copyv_frame I hc tag st n src dst soff doff xs hx hdisjoint hshape
  have ha' : mid.store.read tag a.buf a.idx.eval = some r :=
    (hframe tag a.buf a.idx.eval (Or.inl had)).trans ha
  obtain ⟨out, hdiv, hsh', hread', hframe', hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_rscl_frame I hI hc tag mid n a dst doff r xs hr ha' hread had
  refine ⟨out, ?_, hsh'.trans hsh, hread', ?_, hpos'.trans hpos,
    hcur'.trans hcur, hcurW'.trans hcurW, ?_, hpeak'.trans hpeak, hpeakW'.trans hpeakW⟩
  · rw [exec_run_bind I (b := copyv tag src soff dst doff n) (fun _ => rfl),
      hcopy, Option.bind_some]
    exact hdiv
  · intro q b i hi
    exact (hframe' q b i hi).trans (hframe q b i hi)
  · rw [hcnt', hcnt]

/-- The actual zero-test and guarded normalization execute successfully from the stored exact
norm and writable destination. Inputs, norm and zero cells occupy distinct buffers. The output
is the source divided by its Euclidean norm, with total real division giving zero at breakdown.
The branch retains every cell outside its destination window, changes no usage fields, and
counts at most one comparison and, per entry, one literal, copy and division. -/
theorem exec_normalize_branch (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (buf : Fin 4 → ℕ) (hbuf : Function.Injective buf)
    (n soff doff ni zi : IExp ℕ) (xs : ℕ → ℝ)
    (hx : ∀ i < n.eval, st.store.read tag (buf 0) (soff.eval + i) = some (xs i))
    (hnorm : st.store.read tag (buf 2) ni.eval =
      some ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖)
    (hzero : st.store.read tag (buf 3) zi.eval = some 0)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf 1]? = some (tag, len) ∧ doff.eval + i < len) :
    ∃ out, exec I (ifThenElse tag .eq ⟨buf 2, ni⟩ ⟨buf 3, zi⟩
        (forRange n fun i => ins (.lit tag ⟨buf 1, doff + .var i⟩ 0))
        (do copyv tag (buf 0) soff (buf 1) doff n
            rscl tag ⟨buf 2, ni⟩ (buf 1) doff n)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag (buf 1) (doff.eval + i) =
        some (xs i / ‖WithLp.toLp 2 (fun j : Fin n.eval => xs j)‖)) ∧
      (∀ q b i, (b ≠ buf 1 ∨ i < doff.eval ∨ doff.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + Finsupp.single (.cmp tag) 1 + n.eval •
        (Finsupp.single (.lit tag) 1 + Finsupp.single (.copy tag) 1 +
          Finsupp.single (.bin tag .div) 1) ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  let r := ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
  let st₀ : St P ℝ (OpCount P ι) :=
    { st with cnt := st.cnt + Finsupp.single (OpKind.cmp tag) 1 }
  have hcmp : cmpStep I tag .eq ⟨buf 2, ni⟩ ⟨buf 3, zi⟩ st =
      some (decide (r = 0), st₀) := by
    simp only [cmpStep, hnorm, hzero, Option.bind_some, hI, exactSem,
      Option.map_some, hc.charge_eq, r, st₀]
  by_cases hr : r = 0
  · obtain ⟨s', hrun, hsh, hread, hframe⟩ :=
      exec_forRange_zero I hI tag st₀ n (buf 1) doff hshape
    let out : St P ℝ (OpCount P ι) := { st₀ with
      store := s'
      cnt := st₀.cnt + n.eval • Finsupp.single (OpKind.lit tag) 1 }
    refine ⟨out, ?_, hsh, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
    · change exec I (.seq (.ite tag .eq _ _ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp]
      simpa only [hr, decide_true, Option.bind_some, Bool.true_eq, ite_true, out, hc.charge_eq]
        using hrun
    · intro i hi
      change s'.read tag (buf 1) (doff.eval + i) = some (xs i / r)
      simpa only [hr, div_zero] using hread i hi
    · intro q b i hi
      exact hframe q b i (Or.inr hi)
    · change (st.cnt + _) + n.eval • _ ≤ _
      intro k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_add]
      omega
  · obtain ⟨out, hrun, hsh, hread, hframe, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
      exec_copyv_rscl_frame I hI hc tag st₀ n (buf 0) (buf 1) soff doff ⟨buf 2, ni⟩
        r xs hr hnorm hx (hbuf.ne (by decide)) (hbuf.ne (by decide)) hshape
    refine ⟨out, ?_, hsh, hread, hframe, hpos, hcur, hcurW, ?_, hpeak, hpeakW⟩
    · change exec I (.seq (.ite tag .eq _ _ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp]
      simpa only [hr, decide_false, Option.bind_some, Bool.false_eq_true, ite_false] using hrun
    · rw [hcnt]
      change (st.cnt + _) + n.eval • _ + n.eval • _ ≤ _
      intro k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_add]
      omega

variable {K C : Type} [AddMonoid C]

/-- The actual direct-index initial zero branch has the same execution as the generic
zero-offset branch. Both successful and failed executions, charges and memory are equal. -/
theorem exec_normalize_branch_var_eq (I : Interp P ι K C) (tag : P) (st : St P K C)
    (n : IExp ℕ) (src dst : ℕ) (soff : IExp ℕ) (norm zero : Cell ℕ ℕ) :
    exec I (ifThenElse tag .eq norm zero
        (forRange n fun i => ins (.lit tag ⟨dst, .var i⟩ 0)) (do
          copyv tag src soff dst 0 n
          rscl tag norm dst 0 n)).run st =
      exec I (ifThenElse tag .eq norm zero
        (forRange n fun i => ins (.lit tag ⟨dst, 0 + .var i⟩ 0)) (do
          copyv tag src soff dst 0 n
          rscl tag norm dst 0 n)).run st := by
  change exec I (.seq (.ite tag .eq norm zero _ _) .skip) st =
    exec I (.seq (.ite tag .eq norm zero _ _) .skip) st
  rw [exec_seq_skip, exec_seq_skip, exec_ite, exec_ite]
  congr 1
  funext r
  split_ifs
  · exact exec_forRange_zero_var_eq I tag r.2 n dst
  · rfl

end NLAlib.Computation
