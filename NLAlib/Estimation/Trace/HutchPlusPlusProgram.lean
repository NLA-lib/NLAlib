/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.SparseCompile
public import NLAlib.Estimation.Trace.HutchPlusPlusTargets
public import NLAlib.Matrix.Factorizations.GramSchmidtProgram

/-!
# Hutch++ as a program

`NLAlib.hutchppProg` (in `NLAlib/Estimation/Trace/HutchPlusPlusProgramTree.lean`) is Hutch++ as a
program over memory buffers: it draws an $N \times k$ sketch and $N \times \ell$ probes from the
tape, forms $\mathbf{Y} = \mathbf{A}\mathbf{S}$ with one oracle call, orthonormalises
$\mathbf{Y}$ in place by rank-revealing modified Gram–Schmidt, projects the probes in place, forms
$\mathbf{A}[\mathbf{Q}\ \mathbf{G}']$ with a second call, and writes
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\operatorname{tr}(\mathbf{G}'^{\mathsf{H}}\mathbf{A}\mathbf{G}')/\ell$ into its output cell.

Under exact arithmetic it computes `NLAlib.hutchpp` of the matrices drawn from the tape, with 2
loads, $2k + \ell$ matrix-vector products, the operation counts `NLAlib.hutchppCount` and
$2N(k + \ell) + 4$ cells of memory besides its output, for every matrix and every tape. With the
law of the tape, the tail bound of Gaussian Hutch++ transfers to the program with no new
probability. With the oracle implemented by a dense matrix or by a matrix in coordinate form, the
substitution theorem gives the totals in arithmetic operations and memory, in the stored-entries
model. Each is first proved for the program family, then for the tree the target is about,
through the tree's instantiation equation: the targets of
`NLAlib/Estimation/Trace/HutchPlusPlusTargets.lean` are proved here. The sparse tree is compiled
from a pattern of any length, by an induction through the entries of
`NLAlib.Computation.cooImpl`. Design: `docs/design/Computation.md` (§5, §6, "Guarantees", F8).

## Main results

* `NLAlib.matrixFree_hutchppProg`, `NLAlib.matrixFreeProb_hutchppProg`,
  `NLAlib.storedEntries_substOracle_hutchppProg_denseImpl`,
  `NLAlib.storedEntries_substOracle_hutchppProg_cooImpl`: the results for the program families.
* `NLAlib.hutchppProg.toStmt_compiled`, `NLAlib.hutchppProg.toStmt_compiledDense`,
  `NLAlib.hutchppProg.toStmt_compiledCoo`: the trees instantiate to the families.
* `NLAlib.hutchppProg.exists_compile_coo`: the sparse family compiles for every pattern.
* `NLAlib.matrixFreeHutchpp`, `NLAlib.matrixFreeProbHutchpp`, `NLAlib.storedEntriesDenseHutchpp`,
  `NLAlib.storedEntriesCooHutchpp`: the targets `NLAlib.MatrixFreeHutchpp`,
  `NLAlib.MatrixFreeProbHutchpp`, `NLAlib.StoredEntriesDenseHutchpp`,
  `NLAlib.StoredEntriesCooHutchpp`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

section Statements

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- Column `c` of a matrix as a vector, zero past the last column. -/
private def colOf {N m : ℕ} (M : Matrix (Fin N) (Fin m) 𝕜) (c : ℕ) : Fin N → 𝕜 :=
  fun a => if h : c < m then M a ⟨c, h⟩ else 0

/-- The end of `hutchppProg`: `out ← out + t[1] / ℓ`. -/
private theorem exec_hutchpp_finish (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (t ℓ : ℕ) (hℓ : 0 < ℓ)
    (st : St P 𝕜 (OpCount P ι)) (x y : 𝕜) (h0t : 0 ≠ t) (ht1 : st.store.read p t 1 = some x)
    (hout : st.store.read p 0 0 = some y) (ht0 : ∃ s, st.store.write p t 0 0 = some s) :
    ∃ st', exec I (ins (.litIdx p ⟨t, 0⟩ (.const ℓ)) >>= fun _ =>
        ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩) >>= fun _ =>
        ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 1⟩)).run st = some st' ∧
      st'.store.read p 0 0 = some (y + x / ℓ) ∧ st'.store.shape = st.store.shape ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.cnt = st.cnt + (Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.bin p .div) 1 +
        Finsupp.single (OpKind.bin p .add) 1) ∧ st'.peak = st.peak := by
  obtain ⟨u₀, hu₀⟩ := ht0
  obtain ⟨s6, hs6⟩ := Store.exists_write_eq_some_of_shape_eq rfl hu₀ (((ℓ : ℕ) : ℚ) : 𝕜)
  have hℓ' : (((ℓ : ℕ) : ℚ) : 𝕜) ≠ 0 := by
    rw [Rat.cast_natCast]; exact Nat.cast_ne_zero.mpr hℓ.ne'
  have ht1' : s6.read p t 1 = some x := by
    rw [Store.read_of_write_eq_some_of_ne hs6 (Or.inr Nat.one_ne_zero)]; exact ht1
  obtain ⟨s7, hs7⟩ := Store.exists_write_eq_some_of_read_eq_some
    (v := x / (((ℓ : ℕ) : ℚ) : 𝕜)) ht1'
  have hout7 : s7.read p 0 0 = some y := by
    rw [Store.read_of_write_eq_some_of_ne hs7 (Or.inl h0t),
      Store.read_of_write_eq_some_of_ne hs6 (Or.inl h0t), hout]
  obtain ⟨s8, hs8⟩ := Store.exists_write_eq_some_of_read_eq_some
    (v := y + x / (((ℓ : ℕ) : ℚ) : 𝕜)) hout7
  have e6 : exec I (ins (.litIdx p ⟨t, 0⟩ (.const ℓ))).run st =
      some { st with store := s6, cnt := st.cnt + I.charge (.lit p) } :=
    (exec_seq_instr_litIdx I (by rw [hI]; rfl) hs6).trans (exec_skip I _)
  have e7 : exec I (ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)).run
      { st with store := s6, cnt := st.cnt + I.charge (.lit p) } =
      some { st with store := s7, cnt := st.cnt + I.charge (.lit p) + I.charge (.bin p .div) } :=
    (exec_seq_instr_bin I ht1' (Store.read_of_write_eq_some hs6)
      (by rw [hI]; exact if_neg hℓ') hs7).trans (exec_skip I _)
  have e8 : exec I (ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 1⟩)).run
      { st with store := s7, cnt := st.cnt + I.charge (.lit p) + I.charge (.bin p .div) } =
      some { st with
        store := s8
        cnt := st.cnt + I.charge (.lit p) + I.charge (.bin p .div) + I.charge (.bin p .add) } :=
    (exec_seq_instr_bin I hout7 (Store.read_of_write_eq_some hs7) (by rw [hI]; rfl)
      hs8).trans (exec_skip I _)
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [e6, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [e7, Option.bind_some, e8]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · change s8.read p 0 0 = _
    rw [Store.read_of_write_eq_some hs8, Rat.cast_natCast]
  · change s8.shape = _
    rw [Store.shape_of_write_eq_some hs8, Store.shape_of_write_eq_some hs7,
      Store.shape_of_write_eq_some hs6]
  · simp only [hc.charge_eq, add_assoc]

/-- The two traces of `hutchppProg`, from the products `B = W` and `C = A W`. -/
private theorem exec_hutchpp_traces (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) {N k ℓ : ℕ} (hℓ : 0 < ℓ) (p : P) (B t C : ℕ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜)
    (st : St P 𝕜 (OpCount P ι))
    (hB : ∀ (a : Fin N) (c : Fin (k + ℓ)), st.store.read p B (N * c + a) = some (W a c))
    (hC : ∀ (a : Fin N) (c : Fin (k + ℓ)), st.store.read p C (N * c + a) = some ((A * W) a c))
    (hout : st.store.read p 0 0 = some 0)
    (ht0 : ∃ s, st.store.write p t 0 0 = some s) (ht1 : ∃ s, st.store.write p t 1 0 = some s)
    (htB : t ≠ B) (htC : t ≠ C) (h0B : 0 ≠ B) (h0C : 0 ≠ C) (h0t : 0 ≠ t) :
    ∃ st', exec I
        (forRange (.const k) (fun j => dot p ⟨t, 0⟩ B (.const N * .var j) C (.const N * .var j)
          (.const N) >>= fun _ => ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.lit p ⟨t, 1⟩ 0) >>= fun _ =>
        forRange (.const ℓ) (fun j => dot p ⟨t, 0⟩ B (.const N * (.const k + .var j)) C
          (.const N * (.const k + .var j)) (.const N) >>= fun _ =>
            ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.litIdx p ⟨t, 0⟩ (.const ℓ)) >>= fun _ =>
        ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩) >>= fun _ =>
        ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 1⟩)).run st = some st' ∧
      st'.store.read p 0 0 =
        some ((0 + ∑ j ∈ Finset.range k, star (colOf W j) ⬝ᵥ colOf (A * W) j) +
          (0 + ∑ j ∈ Finset.range ℓ, star (colOf W (k + j)) ⬝ᵥ colOf (A * W) (k + j)) / ℓ) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.cnt = st.cnt + (k • (N • (Finsupp.single (OpKind.un p .conj) 1 +
          Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
          Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 +
        ℓ • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + (Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.bin p .div) 1 + Finsupp.single (OpKind.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) := by
  obtain ⟨u₀, hu₀⟩ := ht0
  obtain ⟨st3, h3, hacc3, hfr3, hsh3, hpos3, hcur3, -, hcnt3, hpeak3, -⟩ :=
    exec_forRange_dot_add I hI hc p B C t ⟨0, .const 0⟩ (.const k) (fun j => .const N * .var j)
      0
      (fun j => by simp) (fun j => colOf W j) (fun j => colOf (A * W) j) st 0
      (fun j hj a => by
        simp only [IExp.eval_const] at hj
        rw [zero_add, hB a ⟨j, by omega⟩]; simp [colOf, show j < k + ℓ by omega])
      (fun j hj a => by
        simp only [IExp.eval_const] at hj
        rw [zero_add, hC a ⟨j, by omega⟩]; simp [colOf, show j < k + ℓ by omega])
      hout htB htC h0B h0C (fun h => absurd h h0t) ⟨u₀, hu₀⟩
  obtain ⟨u₁, hu₁⟩ := ht1
  obtain ⟨s4, hs4⟩ := Store.exists_write_eq_some_of_shape_eq hsh3 hu₁ ((0 : ℚ) : 𝕜)
  have hlit2 : exec I (ins (.lit p ⟨t, 1⟩ 0)).run st3 =
      some { st3 with store := s4, cnt := st3.cnt + I.charge (.lit p) } :=
    (exec_seq_instr_lit I (by rw [hI]; rfl) hs4).trans (exec_skip I _)
  set st4 : St P 𝕜 (OpCount P ι) := { st3 with store := s4, cnt := st3.cnt + I.charge (.lit p) }
  have hfr4 : ∀ q b i, b ≠ t → (b = 0 → i ≠ 0) → st4.store.read q b i = st.store.read q b i :=
    fun q b i hbt hb0 => by
      change s4.read q b i = _
      rw [Store.read_of_write_eq_some_of_ne hs4 (Or.inl hbt), hfr3 q b i hbt hb0]
  have hsh4 : st4.store.shape = st.store.shape := (Store.shape_of_write_eq_some hs4).trans hsh3
  obtain ⟨st5, h5, hacc5, hfr5, hsh5, hpos5, hcur5, -, hcnt5, hpeak5, -⟩ :=
    exec_forRange_dot_add I hI hc p B C t ⟨t, 1⟩ (.const ℓ)
      (fun j => .const N * (.const k + .var j)) k
      (fun j => by simp) (fun j => colOf W (k + j)) (fun j => colOf (A * W) (k + j)) st4
      ((0 : ℚ) : 𝕜)
      (fun j hj a => by
        simp only [IExp.eval_const] at hj
        rw [hfr4 p B _ (Ne.symm htB) (fun h => absurd h.symm h0B), hB a ⟨k + j, by omega⟩]
        simp [colOf, show k + j < k + ℓ by omega])
      (fun j hj a => by
        simp only [IExp.eval_const] at hj
        rw [hfr4 p C _ (Ne.symm htC) (fun h => absurd h.symm h0C), hC a ⟨k + j, by omega⟩]
        simp [colOf, show k + j < k + ℓ by omega])
      (Store.read_of_write_eq_some hs4) htB htC htB htC (fun _ => Nat.one_ne_zero)
      (Store.exists_write_eq_some_of_shape_eq hsh4 hu₀ 0)
  simp only [IExp.eval_const, Rat.cast_zero] at hacc3 hacc5 hcnt3 hcnt5
  obtain ⟨st6, h6, hout6, hsh6, hpos6, hcur6, hcnt6, hpeak6⟩ :=
    exec_hutchpp_finish I hI hc p t ℓ hℓ st5 _ _ h0t hacc5 (by
      rw [hfr5 p 0 0 h0t (fun h => absurd h h0t)]
      change s4.read p 0 0 = _
      rw [Store.read_of_write_eq_some_of_ne hs4 (Or.inl h0t)]
      exact hacc3) (Store.exists_write_eq_some_of_shape_eq (hsh5.trans hsh4) hu₀ 0)
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h3, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [hlit2, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h5, Option.bind_some]
  refine ⟨st6, h6, hout6, hsh6.trans (hsh5.trans hsh4), hpos6.trans (hpos5.trans hpos3),
    hcur6.trans (hcur5.trans hcur3), ?_, ?_⟩
  · rw [hcnt6, hcnt5]
    simp only [st4, hcnt3, hc.charge_eq, add_assoc]
  · change st3.cur = st.cur at hcur3
    change st5.peak ≤ Function.update st3.peak p (max (st3.peak p) (st3.cur p + 1)) at hpeak5
    rw [hpeak6, hcur3] at *
    refine hpeak5.trans fun q => ?_
    have h3q := hpeak3 q
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self] at h3q ⊢
      omega
    · simp only [Function.update_of_ne hq] at h3q ⊢
      exact h3q

/-- The tail of `hutchppProg`: the second oracle call and the two traces. -/
private theorem exec_hutchpp_tail {N k ℓ : ℕ} (hℓ : 0 < ℓ) (A : Matrix (Fin N) (Fin N) 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (o : ι) (B t C : ℕ) (W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜)
    (st : St P 𝕜 (OpCount P ι))
    (hW : ∀ (a : Fin N) (c : Fin (k + ℓ)), st.store.read p B (N * c + a) = some (W a c))
    (hC : ∀ i < N * (k + ℓ), ∃ v s, st.store.write p C (0 + i) v = some s)
    (hout : ∃ s, st.store.write p 0 0 0 = some s)
    (ht0 : ∃ s, st.store.write p t 0 0 = some s) (ht1 : ∃ s, st.store.write p t 1 0 = some s)
    (hBC : C ≠ B) (htB : t ≠ B) (htC : t ≠ C) (h0B : 0 ≠ B) (h0C : 0 ≠ C) (h0t : 0 ≠ t) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (stmt (.apply o p C 0 B 0 (.const k + .const ℓ)) >>= fun _ =>
        ins (.lit p ⟨0, .const 0⟩ 0) >>= fun _ =>
        forRange (.const k) (fun j => dot p ⟨t, 0⟩ B (.const N * .var j) C (.const N * .var j)
          (.const N) >>= fun _ => ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.lit p ⟨t, 1⟩ 0) >>= fun _ =>
        forRange (.const ℓ) (fun j => dot p ⟨t, 0⟩ B (.const N * (.const k + .var j)) C
          (.const N * (.const k + .var j)) (.const N) >>= fun _ =>
            ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.litIdx p ⟨t, 0⟩ (.const ℓ)) >>= fun _ =>
        ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩) >>= fun _ =>
        ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 1⟩)).run st = some st' ∧
      st'.store.read p 0 0 =
        some ((0 + ∑ j ∈ Finset.range k, star (colOf W j) ⬝ᵥ colOf (A * W) j) +
          (0 + ∑ j ∈ Finset.range ℓ, star (colOf W (k + j)) ⬝ᵥ colOf (A * W) (k + j)) / ℓ) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.cnt = st.cnt + (Finsupp.single (OpKind.load p o) 1 +
        (k + ℓ) • Finsupp.single (OpKind.matvec p o) 1 + Finsupp.single (OpKind.lit p) 1 +
        k • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        ℓ • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.bin p .div) 1 + Finsupp.single (OpKind.bin p .add) 1) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ with hIdef
  have hI : I.sem = exactSem := rfl
  have hc : IsUnitCharge I := fun _ => rfl
  obtain ⟨s1, hs1⟩ := Store.exists_writeBlock_eq_some_of_write (s := st.store) (p := p) (b := C)
    (off := 0) (xs := flatten (A * W)) fun i hi => hC i (by rwa [size_flatten] at hi)
  have hC1 : ∀ (a : Fin N) (c : Fin (k + ℓ)), s1.read p C (N * c + a) = some ((A * W) a c) :=
    fun a c => by
      rw [show N * (c : ℕ) + a = 0 + ((a : ℕ) + N * c) by ring,
        Store.read_of_writeBlock_eq_some_of_lt hs1
          (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt a.2 c.2), getElem?_flatten]
  have hsh1 := Store.shape_of_writeBlock_eq_some hs1
  have happ : exec I (stmt (.apply o p C 0 B 0 (.const k + .const ℓ))).run st = some { st with
      store := s1
      cnt := st.cnt + (Finsupp.single (OpKind.load p o) 1 +
        (k + ℓ) • Finsupp.single (OpKind.matvec p o) 1) } := by
    rw [show (stmt (ι := ι) (.apply o p C 0 B 0 (.const k + .const ℓ))).run =
      .seq (.apply o p C 0 B 0 (.const k + .const ℓ)) .skip from rfl, exec_seq_skip]
    exact exec_apply_exactInterp (m := k + ℓ) A ξ o p C B _ rfl st W hBC hW hs1
  set st1 : St P 𝕜 (OpCount P ι) := { st with
      store := s1
      cnt := st.cnt + (Finsupp.single (OpKind.load p o) 1 +
        (k + ℓ) • Finsupp.single (OpKind.matvec p o) 1) } with hst1
  obtain ⟨s₀, hs₀⟩ := hout
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_shape_eq hsh1 hs₀ ((0 : ℚ) : 𝕜)
  have hlit : exec I (ins (.lit p ⟨0, .const 0⟩ 0)).run st1 =
      some { st1 with store := s2, cnt := st1.cnt + I.charge (.lit p) } :=
    (exec_seq_instr_lit I (by rw [hI]; rfl) hs2).trans (exec_skip I _)
  set st2 : St P 𝕜 (OpCount P ι) := { st1 with store := s2, cnt := st1.cnt + I.charge (.lit p) }
  have hsh2 : st2.store.shape = st.store.shape := (Store.shape_of_write_eq_some hs2).trans hsh1
  obtain ⟨st3, h3, hout3, hsh3, hpos3, hcur3, hcnt3, hpeak3⟩ :=
    exec_hutchpp_traces I hI hc hℓ p B t C A W st2
      (fun a c => by
        change s2.read p B _ = _
        rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inl (Ne.symm h0B)),
          Store.read_of_writeBlock_eq_some_of_ne hs1 (Or.inl (Ne.symm hBC)), hW a c])
      (fun a c => by
        change s2.read p C _ = _
        rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inl (Ne.symm h0C)), hC1 a c])
      (by change s2.read p 0 0 = _; rw [Store.read_of_write_eq_some hs2, Rat.cast_zero])
      (let ⟨_, h⟩ := ht0; Store.exists_write_eq_some_of_shape_eq hsh2 h 0)
      (let ⟨_, h⟩ := ht1; Store.exists_write_eq_some_of_shape_eq hsh2 h 0)
      htB htC h0B h0C h0t
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [happ, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [hlit, Option.bind_some]
  refine ⟨st3, h3, hout3, hsh3.trans hsh2, hpos3, hcur3, ?_, hpeak3⟩
  rw [hcnt3]
  simp only [st2, st1, hc.charge_eq, add_assoc]

omit [DecidableEq P] in
/-- A block of columns of `W` holding `M`: the sum of the column quadratic forms of `A` is
`tr(Mᴴ A M)`. -/
private theorem sum_colOf_eq_trace {N n m : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (W : Matrix (Fin N) (Fin n) 𝕜) (M : Matrix (Fin N) (Fin m) 𝕜) (c0 : ℕ) (hm : c0 + m ≤ n)
    (hW : ∀ (a : Fin N) (j : Fin m), W a ⟨c0 + j, by omega⟩ = M a j) :
    ∑ j ∈ Finset.range m, star (colOf W (c0 + j)) ⬝ᵥ colOf (A * W) (c0 + j) =
      (Mᴴ * A * M).trace := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => star (colOf W (c0 + j)) ⬝ᵥ colOf (A * W) (c0 + j)),
    Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : c0 + j < n := by omega
  rw [Matrix.diag, Matrix.mul_assoc]
  simp only [colOf, hj, dif_pos, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, hW]

omit [DecidableEq P] in
/-- The value the program computes is Hutch++. -/
private theorem hutchpp_eq_colOf {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (S : Matrix (Fin N) (Fin k) 𝕜) (G : Matrix (Fin N) (Fin ℓ) 𝕜)
    (W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜)
    (hWQ : ∀ (a : Fin N) (c : Fin k), W a ⟨c, by omega⟩ = gramSchmidtQ (A * S) a c)
    (hWG : ∀ (a : Fin N) (j : Fin ℓ), W a ⟨k + j, by omega⟩ =
      ((1 - gramSchmidtQ (A * S) * (gramSchmidtQ (A * S))ᴴ) * G : Matrix (Fin N) (Fin ℓ) 𝕜) a j) :
    (0 + ∑ j ∈ Finset.range k, star (colOf W j) ⬝ᵥ colOf (A * W) j) +
      (0 + ∑ j ∈ Finset.range ℓ, star (colOf W (k + j)) ⬝ᵥ colOf (A * W) (k + j)) / ℓ =
      hutchpp A S G := by
  set Q := gramSchmidtQ (A * S)
  rw [hutchpp_eq_of_mul_conjTranspose_self_eq_rangeProjector (gramSchmidtQ_mul_conjTranspose _) G,
    girardHutchinson, Fintype.card_fin, zero_add, zero_add,
    sum_colOf_eq_trace A W ((1 - Q * Qᴴ) * G) k le_rfl hWG]
  have h1 := sum_colOf_eq_trace A W Q 0 (by omega) fun a c => by simpa using hWQ a c
  simp only [zero_add] at h1
  rw [h1]
  congr 2
  have hP : (1 - Q * Qᴴ)ᴴ = 1 - Q * Qᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_mul, hP]
  simp only [Matrix.mul_assoc]
  rfl

omit [RCLike 𝕜] [DecidableEq P] in
private theorem run_alloc_bind (p : P) (len : IExp ℕ) (f : ℕ → Builder P ι ℕ ℕ Unit) :
    (Builder.alloc p len >>= f).run = .alloc p len fun b => (f b).run := rfl

/-- The sketch of `hutchppProg`: `S` drawn into a scoped buffer, then `B ← A S`. -/
private theorem exec_hutchpp_sketch {N k : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (o : ι) (d : Dist) (B : ℕ) (st : St P 𝕜 (OpCount P ι))
    (hB : B < st.store.size) (hBw : ∀ i < N * k, ∃ v s, st.store.write p B (0 + i) v = some s) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (scope (Builder.alloc p (.const N * .const k) >>= fun S =>
          forRange (.const N * .const k) (fun i => ins (.draw p d ⟨S, .var i⟩)) >>= fun _ =>
          stmt (.apply o p B 0 S 0 (.const k)))).run st = some st' ∧
      (∀ (a : Fin N) (c : Fin k), st'.store.read p B (N * c + a) =
        some ((A * tapeMatrix (ξ d) (st.pos d) N k : Matrix (Fin N) (Fin k) 𝕜) a c)) ∧
      (∀ q b i, (b = B → N * k ≤ i) → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos d (st.pos d + N * k) ∧ st'.cur = st.cur ∧
      st'.cnt = st.cnt + ((N * k) • Finsupp.single (OpKind.draw p d) 1 +
        (Finsupp.single (OpKind.load p o) 1 + k • Finsupp.single (OpKind.matvec p o) 1)) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + N * k)) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  set Smat : Matrix (Fin N) (Fin k) 𝕜 := tapeMatrix (ξ d) (st.pos d) N k
  set x : P × Array (Option 𝕜) := (p, Array.replicate (N * k) none)
  rw [show ∀ X : Builder P ι ℕ ℕ Unit, (scope X).run = .seq X.run .skip from fun _ => rfl,
    exec_seq_skip, run_alloc_bind, exec_alloc]
  obtain ⟨st1, h1, hrd1, hfr1, hsh1, hpos1, hcur1, hpeak1, -, -, hcnt1⟩ :=
    exec_forRange_draw I p d st.store.size 0 (.const N * .const k) (fun i => .var i)
      (fun i => by simp)
      { st with
        store := st.store.push (p, Array.replicate (IExp.const N * IExp.const k).eval none)
        cur := Function.update st.cur p (st.cur p + (IExp.const N * IExp.const k).eval)
        peak := Function.update st.peak p
          (max (st.peak p) (st.cur p + (IExp.const N * IExp.const k).eval))
        curW := st.curW + (IExp.const N * IExp.const k).eval * I.width p
        peakW := max st.peakW (st.curW + (IExp.const N * IExp.const k).eval * I.width p) }
      (fun i hi => ⟨0, _, Store.write_push_size (by simpa using hi)⟩)
  have hBw1 : ∀ i < N * k, ∃ v s, st1.store.write p B (0 + i) v = some s := fun i hi => by
    obtain ⟨v, s, hs⟩ := hBw i hi
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsh1
      (show Store.write (st.store.push _) p B (0 + i) v = some (s.push x) by
        rw [Store.write_push_of_lt hB, hs]; rfl) v
    exact ⟨v, s', hs'⟩
  obtain ⟨s2, hs2⟩ := Store.exists_writeBlock_eq_some_of_write (s := st1.store) (p := p) (b := B)
    (off := 0) (xs := flatten (A * Smat)) fun i hi => hBw1 i (by rwa [size_flatten] at hi)
  have happ := exec_apply_exactInterp (m := k) A ξ o p B st.store.size (.const k) rfl st1 Smat
    (Nat.ne_of_lt hB) (fun a c => by
      have := hrd1 (N * c + a) (by
        simp only [IExp.eval_mul, IExp.eval_const]
        rw [Nat.add_comm]; exact Nat.add_mul_lt_mul_of_lt_of_lt a.2 c.2)
      rw [zero_add] at this
      rw [this]
      simp only [I, exactInterp, Smat, tapeMatrix, Matrix.of_apply]
      congr 3
      omega) hs2
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h1, Option.bind_some, show ∀ X : Stmt P ι ℕ ℕ, (stmt (ι := ι) X).run = .seq X .skip from
    fun _ => rfl, exec_seq_skip, happ]
  have hsz1 : st1.store.size = st.store.size + 1 := by
    rw [Store.size_eq_of_shape_eq hsh1]; simp
  have hsh2 := Store.shape_of_writeBlock_eq_some hs2
  have hsz2 : s2.size = st.store.size + 1 := by rw [Store.size_eq_of_shape_eq hsh2, hsz1]
  refine ⟨_, rfl, fun a c => ?_, fun q b i hb => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Store.read s2.pop p B _ = _
    rw [Store.read_pop_of_lt (by omega), show N * (c : ℕ) + a = 0 + ((a : ℕ) + N * c) by ring,
      Store.read_of_writeBlock_eq_some_of_lt hs2
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt a.2 c.2), getElem?_flatten]
  · change Store.read s2.pop q b i = _
    by_cases hbs : b < st.store.size
    · rw [Store.read_pop_of_lt (by omega), Store.read_of_writeBlock_eq_some_of_ne hs2 (by
          by_cases h : b = B
          · exact Or.inr (Or.inr (by rw [size_flatten]; simpa using hb h))
          · exact Or.inl h),
        hfr1 q b i (fun h => absurd h (Nat.ne_of_lt hbs)), Store.read_push_of_lt hbs]
    · rw [Store.read_eq_none_of_size_le (by simp; omega),
        Store.read_eq_none_of_size_le (by omega)]
  · change Store.shape s2.pop = _
    simp only [Store.shape, Array.map_pop] at hsh2 hsh1 ⊢
    rw [hsh2, hsh1]
    simp
  · change st1.pos = _
    rw [hpos1]
    simp
  · change Function.update st1.cur p (st1.cur p - _) = _
    rw [hcur1]
    simp
  · change st1.cnt + _ = _
    rw [hcnt1]
    simp [I, exactInterp, add_assoc]
  · change st1.peak = _
    rw [hpeak1]
    simp

/-- The middle of `hutchppProg`: the projection of the probes, then the tail in a fresh buffer
`C`. -/
private theorem exec_hutchpp_mid {N k ℓ : ℕ} (hℓ : 0 < ℓ) (A : Matrix (Fin N) (Fin N) 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (o : ι) (B t : ℕ) (Q : Matrix (Fin N) (Fin k) 𝕜)
    (G : Matrix (Fin N) (Fin ℓ) 𝕜) (st : St P 𝕜 (OpCount P ι))
    (hQ : ∀ (a : Fin N) (c : Fin k), st.store.read p B (N * c + a) = some (Q a c))
    (hG : ∀ (a : Fin N) (j : Fin ℓ), st.store.read p B (N * (k + j) + a) = some (G a j))
    (hout : ∃ s, st.store.write p 0 0 0 = some s)
    (ht0 : ∃ s, st.store.write p t 0 0 = some s) (ht1 : ∃ s, st.store.write p t 1 0 = some s)
    (htB : t ≠ B) (h0B : 0 ≠ B) (h0t : 0 ≠ t) (hB : B < st.store.size)
    (ht : t < st.store.size) (h0 : 0 < st.store.size) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (forRange (.const ℓ) (fun j => orthAgainst p (.const N) B (.const k) B
          (.const N * (.const k + .var j)) ⟨t, 0⟩) >>= fun _ =>
        Builder.alloc p (.const N * (.const k + .const ℓ)) >>= fun C =>
        stmt (.apply o p C 0 B 0 (.const k + .const ℓ)) >>= fun _ =>
        ins (.lit p ⟨0, .const 0⟩ 0) >>= fun _ =>
        forRange (.const k) (fun j => dot p ⟨t, 0⟩ B (.const N * .var j) C (.const N * .var j)
          (.const N) >>= fun _ => ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.lit p ⟨t, 1⟩ 0) >>= fun _ =>
        forRange (.const ℓ) (fun j => dot p ⟨t, 0⟩ B (.const N * (.const k + .var j)) C
          (.const N * (.const k + .var j)) (.const N) >>= fun _ =>
            ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)) >>= fun _ =>
        ins (.litIdx p ⟨t, 0⟩ (.const ℓ)) >>= fun _ =>
        ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩) >>= fun _ =>
        ins (.bin p .add ⟨0, .const 0⟩ ⟨0, .const 0⟩ ⟨t, 1⟩)).run st = some st' ∧
      st'.store.read p 0 0 = some (
        let W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜 := Matrix.of fun a c =>
          if h : (c : ℕ) < k then Q a ⟨c, h⟩ else mgsSweep (colOf Q) (colOf G (c - k)) k a
        (0 + ∑ j ∈ Finset.range k, star (colOf W j) ⬝ᵥ colOf (A * W) j) +
          (0 + ∑ j ∈ Finset.range ℓ, star (colOf W (k + j)) ⬝ᵥ colOf (A * W) (k + j)) / ℓ) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.cnt = st.cnt + (ℓ • (k • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1))) +
        (Finsupp.single (OpKind.load p o) 1 +
        (k + ℓ) • Finsupp.single (OpKind.matvec p o) 1 + Finsupp.single (OpKind.lit p) 1 +
        k • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        ℓ • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
          Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.bin p .div) 1 + Finsupp.single (OpKind.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + N * (k + ℓ) + 1)) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  have hI : I.sem = exactSem := rfl
  have hc : IsUnitCharge I := fun _ => rfl
  set W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜 := Matrix.of fun a c =>
    if h : (c : ℕ) < k then Q a ⟨c, h⟩ else mgsSweep (colOf Q) (colOf G (c - k)) k a with hWdef
  obtain ⟨st1, h1, hsw1, hfr1, hsh1, hpos1, hcur1, -, hcnt1, hpeak1, -⟩ :=
    exec_forRange_orthAgainst I hI hc p B t (.const ℓ) (colOf Q) (fun j => colOf G j) st
      (fun i hi a => by rw [hQ a ⟨i, hi⟩]; simp [colOf, hi])
      (fun j hj a => by
        simp only [IExp.eval_const] at hj
        rw [hG a ⟨j, hj⟩]; simp [colOf, hj]) htB ht0
  have hsz1 : st1.store.size = st.store.size := Store.size_eq_of_shape_eq hsh1
  set C := st1.store.size with hC
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h1, Option.bind_some, run_alloc_bind, exec_alloc]
  have hwr : ∀ {b i : ℕ}, b < st.store.size → (∃ s, st.store.write p b i 0 = some s) →
      ∃ s, Store.write (st1.store.push (p, Array.replicate (IExp.const N *
        (IExp.const k + IExp.const ℓ)).eval none)) p b i 0 = some s := fun hb ⟨s₀, hs₀⟩ => by
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsh1 hs₀ 0
    exact ⟨_, by rw [Store.write_push_of_lt (by omega), hs']; rfl⟩
  obtain ⟨st2, h2, hout2, hsh2, hpos2, hcur2, hcnt2, hpeak2⟩ := exec_hutchpp_tail hℓ A ξ p o B t C W
    { st1 with
      store := st1.store.push (p, Array.replicate (IExp.const N *
        (IExp.const k + IExp.const ℓ)).eval none)
      cur := Function.update st1.cur p (st1.cur p + (IExp.const N *
        (IExp.const k + IExp.const ℓ)).eval)
      peak := Function.update st1.peak p (max (st1.peak p) (st1.cur p + (IExp.const N *
        (IExp.const k + IExp.const ℓ)).eval))
      curW := st1.curW + (IExp.const N * (IExp.const k + IExp.const ℓ)).eval * I.width p
      peakW := max st1.peakW (st1.curW + (IExp.const N *
        (IExp.const k + IExp.const ℓ)).eval * I.width p) }
    (fun a c => by
      change Store.read (st1.store.push _) p B _ = _
      rw [Store.read_push_of_lt (by omega)]
      by_cases hck : (c : ℕ) < k
      · rw [hfr1 p B _ (fun _ => by
            have := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hck)
            rw [Nat.mul_succ] at this; omega) (Ne.symm htB), hQ a ⟨c, hck⟩]
        simp [W, hck]
      · have hj : (c : ℕ) - k < ℓ := by omega
        rw [show N * (c : ℕ) + a = N * (k + ((c : ℕ) - k)) + a by congr 2; omega,
          hsw1 _ (by simpa using hj) a]
        simp [W, hck])
    (fun i hi => ⟨0, _, Store.write_push_size (by simp; omega)⟩)
    (hwr h0 hout) (hwr ht ht0) (hwr ht ht1) (by omega) htB (by omega) h0B (by omega) h0t
  rw [h2]
  have hsz2 : st2.store.size = st.store.size + 1 := by
    rw [Store.size_eq_of_shape_eq hsh2]; simpa using hsz1
  refine ⟨_, rfl, ?_, ?_, hpos2.trans hpos1, ?_, ?_, ?_⟩
  · change Store.read st2.store.pop p 0 0 = _
    rw [Store.read_pop_of_lt (by omega), hout2]
  · change Store.shape st2.store.pop = _
    simp only [Store.shape, Array.map_pop] at hsh2 hsh1 ⊢
    rw [hsh2]
    simp [hsh1]
  · change Function.update st2.cur p (st2.cur p - _) = _
    rw [hcur2]
    simp [hcur1]
  · rw [hcnt2]
    change st1.cnt + _ = _
    rw [hcnt1]
    simp only [IExp.eval_const, add_assoc]
  · change st2.peak ≤ _
    refine hpeak2.trans fun q => ?_
    have h1q := hpeak1 q
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, IExp.eval_mul, IExp.eval_add, IExp.eval_const,
        hcur1] at h1q ⊢
      omega
    · simp only [Function.update_of_ne hq] at h1q ⊢
      exact h1q

omit [DecidableEq P] in
/-- The sweep against the Gram–Schmidt columns is the residual projection. -/
private theorem mgsSweep_colOf_gramSchmidtQ {N k : ℕ} (Y : Matrix (Fin N) (Fin k) 𝕜)
    (g : Fin N → 𝕜) (a : Fin N) :
    mgsSweep (colOf (gramSchmidtQ Y)) g k a =
      ((1 - gramSchmidtQ Y * (gramSchmidtQ Y)ᴴ) *ᵥ g) a := by
  set Q := gramSchmidtQ Y
  have hcol : ∀ i (h : i < k), colOf Q i = Q.col ⟨i, h⟩ := fun i h => by
    ext b; simp [colOf, h, Matrix.col]
  rw [mgsSweep_eq_sub_sum]
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.sub_apply, ← Matrix.mulVec_mulVec]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => (star (colOf Q i) ⬝ᵥ g) • colOf Q i) k,
      Finset.sum_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol i i.2]
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  · intro i hi j hj
    rw [hcol i hi, hcol j (hj.trans hi)]
    have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self Y) ⟨i, hi⟩) ⟨j, hj.trans hi⟩
    rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ (by simp [Fin.ext_iff]; omega)] at h
    rw [← h, dotProduct]
    rfl

omit [RCLike 𝕜] [DecidableEq P] in
private theorem hutchppCount_eq (p : P) (o : ι) (d : Dist) (N k ℓ : ℕ) :
    ((N * k) • Finsupp.single (OpKind.draw p d) 1 +
      (Finsupp.single (OpKind.load p o) 1 + k • Finsupp.single (OpKind.matvec p o) 1) +
    (N * ℓ) • Finsupp.single (OpKind.draw p d) 1 + gramSchmidtCount p N k +
    (ℓ • (k • (N • (Finsupp.single (OpKind.un p .conj) 1 +
      Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
      Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
      N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1))) +
    (Finsupp.single (OpKind.load p o) 1 +
      (k + ℓ) • Finsupp.single (OpKind.matvec p o) 1 + Finsupp.single (OpKind.lit p) 1 +
      k • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
      ℓ • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
      Finsupp.single (OpKind.bin p .div) 1 + Finsupp.single (OpKind.bin p .add) 1)) : OpCount P ι) =
    hutchppCount p o d N k ℓ := by
  have hg : gramSchmidtCount (ι := ι) p N k =
      (2 * N * k.choose 2 + N * k) • Finsupp.single (OpKind.bin p .mul) 1 +
      (2 * N * k.choose 2 + N * k) • Finsupp.single (OpKind.bin p .add) 1 +
      (N * k.choose 2 + N * k) • Finsupp.single (OpKind.un p .conj) 1 +
      k.choose 2 • Finsupp.single (OpKind.un p .neg) 1 +
      (k.choose 2 + 2 * k) • Finsupp.single (OpKind.lit p) 1 +
      k • Finsupp.single (OpKind.cmp p) 1 + k • Finsupp.single (OpKind.un p .sqrt) 1 +
      (N * k) • Finsupp.single (OpKind.bin p .div) 1 := by
    simp only [gramSchmidtCount, Finsupp.smul_single_one]
  have hh : hutchppCount (ι := ι) p o d N k ℓ =
      2 • Finsupp.single (OpKind.load p o) 1 + (2 * k + ℓ) • Finsupp.single (OpKind.matvec p o) 1 +
      (N * (k + ℓ)) • Finsupp.single (OpKind.draw p d) 1 +
      (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ) •
        Finsupp.single (OpKind.bin p .mul) 1 +
      (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ + k + ℓ + 1) •
        Finsupp.single (OpKind.bin p .add) 1 +
      (N * k + 1) • Finsupp.single (OpKind.bin p .div) 1 +
      k • Finsupp.single (OpKind.un p .sqrt) 1 +
      (N * k.choose 2 + 2 * N * k + N * k * ℓ + N * ℓ) • Finsupp.single (OpKind.un p .conj) 1 +
      (k.choose 2 + k * ℓ) • Finsupp.single (OpKind.un p .neg) 1 +
      (k.choose 2 + 3 * k + k * ℓ + ℓ + 3) • Finsupp.single (OpKind.lit p) 1 +
      k • Finsupp.single (OpKind.cmp p) 1 := by
    simp only [hutchppCount, Finsupp.smul_single_one]
  rw [hg, hh]
  module

/-- The front of `hutchppProg`: the sketch, the probes and Gram–Schmidt. -/
private theorem exec_hutchpp_front {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (o : ι) (d : Dist) (B : ℕ) (st : St P 𝕜 (OpCount P ι))
    (hB : B < st.store.size) (hpos : st.pos d = 0)
    (hBw : ∀ i < N * (k + ℓ), ∃ v s, st.store.write p B (0 + i) v = some s) :
    ∃ st1 st2 st3,
      exec (exactInterp (fun _ => A) ξ)
        (scope (Builder.alloc p (.const N * .const k) >>= fun S =>
          forRange (.const N * .const k) (fun i => ins (.draw p d ⟨S, .var i⟩)) >>= fun _ =>
          stmt (.apply o p B 0 S 0 (.const k)))).run st = some st1 ∧
      exec (exactInterp (fun _ => A) ξ) (forRange (.const N * .const ℓ) (fun i =>
        ins (.draw p d ⟨B, .const N * .const k + .var i⟩))).run st1 = some st2 ∧
      exec (exactInterp (fun _ => A) ξ) (gramSchmidtProg p (.const N) (.const k) B).run st2 =
        some st3 ∧
      (∀ (a : Fin N) (c : Fin k), st3.store.read p B (N * c + a) =
        some (gramSchmidtQ (A * tapeMatrix (ξ d) 0 N k) a c)) ∧
      (∀ (a : Fin N) (j : Fin ℓ), st3.store.read p B (N * (k + j) + a) =
        some (tapeMatrix (ξ d) (N * k) N ℓ a j)) ∧
      (∀ q b i, b ≠ B → st3.store.read q b i = st.store.read q b i) ∧
      st3.store.shape = st.store.shape ∧ st3.cur = st.cur ∧
      st3.cnt ≤ st.cnt + ((N * k) • Finsupp.single (OpKind.draw p d) 1 +
        (Finsupp.single (OpKind.load p o) 1 + k • Finsupp.single (OpKind.matvec p o) 1) +
        (N * ℓ) • Finsupp.single (OpKind.draw p d) 1 + gramSchmidtCount p N k) ∧
      st3.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + N * k + 3)) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  have hI : I.sem = exactSem := rfl
  have hc : IsUnitCharge I := fun _ => rfl
  have hle : N * k ≤ N * (k + ℓ) := Nat.mul_le_mul_left N (Nat.le_add_right k ℓ)
  obtain ⟨st1, h1, hAS, hfr1, hsh1, hpos1, hcur1, hcnt1, hpeak1⟩ :=
    exec_hutchpp_sketch (k := k) A ξ p o d B st hB fun i hi => hBw i (by omega)
  rw [hpos] at hAS
  have hw1 : ∀ {i v}, i < N * (k + ℓ) → ∃ s, st1.store.write p B (0 + i) v = some s :=
    fun {i v} hi => by
      obtain ⟨v', s, hs⟩ := hBw i hi
      exact Store.exists_write_eq_some_of_shape_eq hsh1 hs v
  obtain ⟨st2, h2, hrd2, hfr2, hsh2, hpos2, hcur2, hpeak2, -, -, hcnt2⟩ :=
    exec_forRange_draw I p d B (N * k) (.const N * .const ℓ)
      (fun i => .const N * .const k + .var i)
      (fun i => rfl) st1 fun i hi => ⟨0, by
        change i < N * ℓ at hi
        have := hw1 (i := N * k + i) (v := 0) (by rw [Nat.mul_add]; omega)
        rwa [zero_add] at this⟩
  have hp1 : st1.pos d = N * k := by rw [hpos1]; simp [hpos]
  have hM : Holds st2.store p B 0 (A * tapeMatrix (ξ d) 0 N k) := fun a c => by
    rw [hfr2 p B _ (fun _ => Or.inl (by
        have := Nat.add_mul_lt_mul_of_lt_of_lt a.2 c.2; omega)),
      show 0 + (a : ℕ) + N * c = N * c + a by ring, hAS a c]
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_write (s := st2.store) (p := p) (b := B)
    (off := 0) (xs := flatten (gramSchmidtQ (A * tapeMatrix (ξ d) 0 N k))) fun j hj => by
      rw [size_flatten] at hj
      obtain ⟨s, hs⟩ := hw1 (i := j) (v := 0) (by omega)
      exact ⟨0, Store.exists_write_eq_some_of_shape_eq hsh2 hs 0⟩
  obtain ⟨st3, h3, hst3, -, hcur3, -, hcnt3, hpeak3, -⟩ :=
    exec_gramSchmidtProg I hI hc p st2 B _ hM s₁ hs₁
  refine ⟨st1, st2, st3, h1, h2, h3, fun a c => ?_, fun a j => ?_, fun q b i hb => ?_, ?_,
    hcur3.trans (hcur2.trans hcur1), ?_, ?_⟩
  · rw [hst3, show N * (c : ℕ) + a = 0 + ((a : ℕ) + N * c) by ring,
      Store.read_of_writeBlock_eq_some_of_lt hs₁
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt a.2 c.2), getElem?_flatten]
  · have hj := Nat.mul_le_mul_left N (Nat.succ_le_of_lt j.2)
    rw [Nat.mul_succ] at hj
    rw [hst3, Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inr (Or.inr (by
        rw [size_flatten]; nlinarith))),
      show N * (k + (j : ℕ)) + a = N * k + (N * j + a) by ring, hrd2 _ (by simp; omega), hp1]
    simp only [I, exactInterp, tapeMatrix, Matrix.of_apply]
    congr 3
    omega
  · rw [hst3, Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inl hb),
      hfr2 q b i (fun h => absurd h hb), hfr1 q b i (fun h => absurd h hb)]
  · rw [hst3, Store.shape_of_writeBlock_eq_some hs₁, hsh2, hsh1]
  · refine hcnt3.trans ?_
    rw [hcnt2, hcnt1]
    simp only [hc.charge_eq, IExp.eval_mul, IExp.eval_const, add_assoc]
    exact le_rfl
  · rw [hcur2, hcur1, hpeak2, hpeak1] at hpeak3
    refine hpeak3.trans fun q => ?_
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      omega
    · simp [Function.update_of_ne hq]

omit [DecidableEq P] in
/-- The value the middle of the program computes, for the Gram–Schmidt basis of the sketch. -/
private theorem hutchpp_eq_of_mgsSweep {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (S : Matrix (Fin N) (Fin k) 𝕜) (G : Matrix (Fin N) (Fin ℓ) 𝕜) :
    (let W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜 := Matrix.of fun a c =>
        if h : (c : ℕ) < k then gramSchmidtQ (A * S) a ⟨c, h⟩
        else mgsSweep (colOf (gramSchmidtQ (A * S))) (colOf G (c - k)) k a;
      (0 + ∑ j ∈ Finset.range k, star (colOf W j) ⬝ᵥ colOf (A * W) j) +
        (0 + ∑ j ∈ Finset.range ℓ, star (colOf W (k + j)) ⬝ᵥ colOf (A * W) (k + j)) / ℓ) =
      hutchpp A S G := by
  refine hutchpp_eq_colOf A S G _ (fun a c => by simp [c.2]) fun a j => ?_
  have h := mgsSweep_colOf_gramSchmidtQ (A * S) (colOf G j) a
  simp only [Matrix.of_apply, show ¬ (k + (j : ℕ) < k) by omega, dif_neg, not_false_eq_true,
    show k + (j : ℕ) - k = j by omega]
  rw [h]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, colOf]

/-- The realisation of `hutchppProg` (the proof of `NLAlib.matrixFree_hutchppProg`). -/
private theorem runsWithin_hutchppProg (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ} (hℓ : 0 < ℓ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (fun _ => A) ξ)
      ((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run)
      (inputState p [Array.replicate 1 none]) (hutchppCount p o d N k ℓ)
      (fun q => if q = p then 2 * N * (k + ℓ) + 4 else 0)
      (fun st => st.store.read p 0 0 =
        some (hutchpp A (tapeMatrix (ξ d) 0 N k) (tapeMatrix (ξ d) (N * k) N ℓ))) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  set st0 : St P 𝕜 (OpCount P ι) := inputState p [Array.replicate 1 none] with hst0
  set Q := gramSchmidtQ (A * tapeMatrix (ξ d) 0 N k)
  set Gm : Matrix (Fin N) (Fin ℓ) 𝕜 := tapeMatrix (ξ d) (N * k) N ℓ
  have hsz0 : st0.store.size = 1 := rfl
  obtain ⟨s00, hs00⟩ : ∃ s, st0.store.write p 0 0 0 = some s :=
    ⟨#[(p, #[some 0])], by simp [Store.write, hst0, inputState]⟩
  rw [show (hutchppProg (ι := ι) (VB := ℕ) (VI := ℕ) p o d (.const N) (.const k) (.const ℓ)
      ⟨0, .const 0⟩) = Builder.alloc p (.const N * (.const k + .const ℓ)) >>= _ from rfl,
    RunsWithin, run_alloc_bind, exec_alloc]
  obtain ⟨st1, st2, st3, h1, h2, h3, hQ3, hG3, hfr3, hsh3, hcur3, hcnt3, hpeak3⟩ :=
    exec_hutchpp_front (ℓ := ℓ) A ξ p o d st0.store.size { st0 with
      store := st0.store.push (p, Array.replicate
        (IExp.const N * (IExp.const k + IExp.const ℓ)).eval none)
      cur := Function.update st0.cur p
        (st0.cur p + (IExp.const N * (IExp.const k + IExp.const ℓ)).eval)
      peak := Function.update st0.peak p
        (max (st0.peak p) (st0.cur p + (IExp.const N * (IExp.const k + IExp.const ℓ)).eval))
      curW := st0.curW + (IExp.const N * (IExp.const k + IExp.const ℓ)).eval * I.width p
      peakW := max st0.peakW
        (st0.curW + (IExp.const N * (IExp.const k + IExp.const ℓ)).eval * I.width p) }
      (by simp) rfl (fun i hi => ⟨0, _, Store.write_push_size (by simp; omega)⟩)
  rw [exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h1, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h2, Option.bind_some, exec_run_bind I]
  on_goal 2 => exact fun _ => rfl
  rw [h3, Option.bind_some, run_alloc_bind, exec_alloc]
  have hsz3 : st3.store.size = 2 := by rw [Store.size_eq_of_shape_eq hsh3]; simp [hsz0]
  have hw3 : ∀ {b i : ℕ}, b < 2 → (∃ s, Store.write (st0.store.push (p, Array.replicate
      (IExp.const N * (IExp.const k + IExp.const ℓ)).eval none)) p b i 0 = some s) →
      ∃ s, Store.write (st3.store.push (p, Array.replicate (IExp.eval 2) none)) p b i 0 =
        some s := fun hb ⟨s₀, hs₀⟩ => by
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsh3 hs₀ 0
    exact ⟨_, by rw [Store.write_push_of_lt (by omega), hs']; rfl⟩
  obtain ⟨st4, h4, hout4, hsh4, -, -, hcnt4, hpeak4⟩ := exec_hutchpp_mid hℓ A ξ p o
    st0.store.size st3.store.size Q Gm { st3 with
      store := st3.store.push (p, Array.replicate (IExp.eval 2) none)
      cur := Function.update st3.cur p (st3.cur p + IExp.eval 2)
      peak := Function.update st3.peak p (max (st3.peak p) (st3.cur p + IExp.eval 2))
      curW := st3.curW + IExp.eval 2 * I.width p
      peakW := max st3.peakW (st3.curW + IExp.eval 2 * I.width p) }
    (fun a c => by
      change Store.read (st3.store.push _) p _ _ = _
      rw [Store.read_push_of_lt (by omega)]; exact hQ3 a c)
    (fun a j => by
      change Store.read (st3.store.push _) p _ _ = _
      rw [Store.read_push_of_lt (by omega)]; exact hG3 a j)
    (hw3 (by omega) ⟨_, by rw [Store.write_push_of_lt (by omega), hs00]; rfl⟩)
    ⟨_, Store.write_push_size (by simp)⟩ ⟨_, Store.write_push_size (by simp)⟩
    (by omega) (by omega) (by omega) (by simp [hsz3, hsz0]) (by simp [hsz3]) (by simp)
  rw [h4]
  have hsz4 : st4.store.size = 3 := by rw [Store.size_eq_of_shape_eq hsh4]; simp [hsz3]
  refine ⟨_, rfl, ?_, fun q => ?_, ?_⟩
  · change st4.cnt ≤ _
    exact hcnt4.trans_le ((add_le_add hcnt3 le_rfl).trans (le_of_eq (by
      rw [← hutchppCount_eq p o d N k ℓ]; exact add_assoc _ _ _)))
  · change st4.peak q + 0 ≤ _
    have hle : N * k ≤ N * (k + ℓ) := Nat.mul_le_mul_left N (Nat.le_add_right k ℓ)
    have h2N : 2 * N * (k + ℓ) = 2 * (N * (k + ℓ)) := by ring
    have h4q := hpeak4 q
    have h3q := hpeak3 q
    change st3.cur = Function.update st0.cur p (st0.cur p + N * (k + ℓ)) at hcur3
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, IExp.eval_ofNat, hcur3] at h4q h3q ⊢
      simp only [hst0, inputState, if_true, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Array.size_replicate, add_zero, IExp.eval_mul, IExp.eval_add,
        IExp.eval_const] at h4q h3q ⊢
      omega
    · simp only [Function.update_of_ne hq] at h4q h3q ⊢
      simp only [hst0, inputState, if_neg hq] at h4q h3q ⊢
      omega
  · change Store.read st4.store.pop.pop p 0 0 = _
    rw [Store.read_pop_of_lt (by simp [hsz4]), Store.read_pop_of_lt (by omega), hout4]
    exact congrArg some (hutchpp_eq_of_mgsSweep A _ Gm)

/-- Hutch++ as a program computes Hutch++, for the program family, in the matrix-free model on
families: for all $N$, $k$ and $\ell \ge 1$, every $N \times N$ matrix $\mathbf{A}$ over
$\Bbbk$ (every oracle name means $\mathbf{A}$) and every tape $\xi$, under exact arithmetic, the
program run from a single declared output cell succeeds within the counts
`hutchppCount p o d N k ℓ` and $2N(k + \ell) + 4$ cells besides the output, and its output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of `d` from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major. The sizes are $N$ and $n = (k, \ell)$. No hypothesis on the rank of
$\mathbf{A}\mathbf{S}$. The proof of `NLAlib.matrixFreeHutchpp`. -/
theorem matrixFree_hutchppProg (p : P) (o : ι) (d : Dist) :
    ProgFamily.MatrixFree (𝕜 := 𝕜) (r := 2) (b := 1) p
      (fun _ _ N n h => (hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run)
      (fun _ n => 0 < n 1) (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun N n _ A ξ st => st.store.read p 0 0 = some
        (hutchpp A (tapeMatrix (ξ d) 0 N (n 0)) (tapeMatrix (ξ d) (N * n 0) N (n 1)))) :=
  fun _ _ hℓ _ A ξ => runsWithin_hutchppProg p o d hℓ A ξ

/-- The deviation of Hutch++ as a program, for the program family, in the probabilistic
matrix-free model on families: let the tape have the law of the tape (`tapeLaw`: the tape of the
Gaussian distribution an i.i.d. sequence of standard Gaussians, independent of the others),
$k \ge 1$, $\ell \ge 1$. If
$\delta > 0$ and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$k \ge 25 \cdot 1^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then for every real
$N \times N$ matrix $\mathbf{A}$ and every $\tau \ge 0$, with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, the probability that the program
fails to compute, within the counts `hutchppCount` and $2N(k + \ell) + 4$ cells, a value $v$ with
$\lvert \operatorname{tr}\mathbf{A} - v \rvert < \tau$ is
at most <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 5\cdot 1/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 5\cdot 1/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. The sizes are $N$ and $n = (k, \ell)$. From
`NLAlib.matrixFree_hutchppProg`, the tape laws and the Gaussian tail
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`, through
`NLAlib.Computation.measureReal_not_runsWithin_le`. The proof of
`NLAlib.matrixFreeProbHutchpp`. -/
theorem matrixFreeProb_hutchppProg (p : P) (o : ι) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    ProgFamily.MatrixFreeProb (𝕜 := ℝ) (r := 2) (b := 1) p
      (fun _ _ N n h => (hutchppProg p o .gaussian N (n 0) (n 1) ⟨h 0, 0⟩).run)
      (fun _ n => 0 < n 0 ∧ 0 < n 1 ∧ subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o .gaussian N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun _ _ _ A st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)
      (fun _ n _ A => δ + 2 * Real.exp (-(hansonWrightConstant *
        min (n 1 * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (n 1 * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r)))))) := by
  rintro N n ⟨hk, hℓ, hs⟩ - A Ω _ μ ξ hξ
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.mpr inferInstance
  have : NeZero (n 0) := ⟨Nat.pos_iff_ne_zero.mp hk⟩
  have hg : HasLaw (fun ω => ξ ω .gaussian) (iidSequence (gaussianReal 0 1)) μ :=
    hasLaw_apply_of_hasLaw_tapeLaw hξ .gaussian
  have h := measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix A
    (hasLaw_tapeMatrix_of_hasLaw_iidSequence hg 0 N (n 0))
    (hasLaw_tapeMatrix_of_hasLaw_iidSequence hg (N * n 0) N (n 1))
    (indepFun_tapeMatrix_of_hasLaw_iidSequence hg N (n 0) (n 1)) hδ (by simpa using hs) hτ
  refine measureReal_not_runsWithin_le (G := fun v => |A.trace - v| < τ)
    (fun ω => runsWithin_hutchppProg p o .gaussian hℓ A (ξ ω)) ?_
  simpa only [not_lt, Fintype.card_fin] using h

/-- Dense Hutch++, for the program family, in the stored-entries model on families: with the
oracle calls served by `NLAlib.Computation.denseImpl` from $N^2$ stored entries $v$,
column-major, so that the matrix is $\mathbf{A} = (v_{i + Nj})_{i, j}$, under exact arithmetic
and $\ell \ge 1$, for every tape the substituted program computes
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of `d` from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, with the counts `hutchppCount` in which each matrix-vector product is replaced by
$N^2$ multiplications, additions and reads and $N$ literals and each load costs nothing, and
$2N(k + \ell) + 5 + N^2$ cells of memory besides its output. From
`NLAlib.matrixFree_hutchppProg` through
`NLAlib.Computation.ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl`. The proof of
`NLAlib.storedEntriesDenseHutchpp`. -/
theorem storedEntries_substOracle_hutchppProg_denseImpl (p : P) (o : ι) (d : Dist) :
    ProgFamily.StoredEntries (𝕜 := 𝕜) (r := 2) (b := 1) p
      (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (denseImpl N))
      (fun _ n => 0 < n 1) (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N _ => N * N) (fun N n => substCount (denseCost N) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then N * N else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (Matrix.of fun (i j : Fin N) => vals (i + N * j)) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1)))) :=
  fun N n hv x vals ξ =>
    ((matrixFree_hutchppProg p o d).storedEntries_substOracle_denseImpl N n hv x vals ξ).mono
      le_rfl le_rfl fun _ ⟨_, h1, h2, _⟩ => by beta_reduce; rw [h2]; exact h1

/-- Sparse Hutch++, for the program family, in the stored-entries model on families: with the
oracle calls served by `NLAlib.Computation.cooImpl` for a public pattern with positions in
$[0, N)^2$ (unrolled into the program, its index storage not counted) and `nnz` stored values
$v$, so that the matrix is `cooMatrix pattern v`, under exact arithmetic and $\ell \ge 1$, for
every tape the substituted program computes $\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$,
where $\mathbf{S}$ is the $N \times k$ matrix drawn from the tape of `d` from position $0$ and
$\mathbf{G}$ the $N \times \ell$ matrix drawn after it, with the counts `hutchppCount` in which
each matrix-vector product is replaced by `nnz` multiplications, additions and reads and $N$
literals and each load costs nothing, and $2N(k + \ell) + 5 + \mathit{nnz}$ cells of memory
besides its output. From `NLAlib.matrixFree_hutchppProg` through
`NLAlib.Computation.ProgFamily.MatrixFree.storedEntries_substOracle_cooImpl`. -/
theorem storedEntries_substOracle_hutchppProg_cooImpl (p : P) (o : ι) (d : Dist)
    (pattern : List (ℕ × ℕ)) :
    ProgFamily.StoredEntries (𝕜 := 𝕜) (r := 2) (b := 1) p
      (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern))
      (fun N n => 0 < n 1 ∧ ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => pattern.length)
      (fun N n => substCount (cooCost N pattern.length) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then pattern.length else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (cooMatrix pattern vals) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1)))) :=
  fun N n hv x vals ξ =>
    ((matrixFree_hutchppProg p o d).storedEntries_substOracle_cooImpl pattern N n hv x vals
      ξ).mono le_rfl le_rfl fun _ ⟨_, h1, h2, _⟩ => by beta_reduce; rw [h2]; exact h1

end Statements

/-! ### The registered trees and the targets -/

section Targets

variable {P ι : Type}

/-- The registered tree of Hutch++ instantiates, at every size, to the statement of the program
family. -/
theorem hutchppProg.toStmt_compiled (p : P) (o : ι) (d : Dist) (N : ℕ)
    (n : Fin 2 → ℕ) :
    (hutchppProg.compiled p o d).toStmt N n = ProgFamily.inst (r := 2) (b := 1)
      (fun _ _ N n h => (hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run) N n :=
  rfl

/-- The registered tree of dense Hutch++ instantiates, at every size, to the statement of the
program family with its oracle calls served by `NLAlib.Computation.denseImpl`. -/
theorem hutchppProg.toStmt_compiledDense (p : P) (o : ι) (d : Dist) (N : ℕ)
    (n : Fin 2 → ℕ) :
    (hutchppProg.compiledDense p o d).toStmt N n = ProgFamily.inst (r := 2) (b := 1)
      (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (denseImpl N)) N n :=
  rfl

/-! The sparse tree: an induction on the statement, with an induction on the pattern through the
entries of `cooImpl`, shows that the COO family compiles for every pattern and instantiates to
the family. -/

/-- The sparse family compiles, for every pattern: Hutch++ with its oracle calls served by
`NLAlib.Computation.cooImpl`, compiled at symbolic sizes, is some first-order program, and that
program instantiates at every size $N$, $n$ to the statement of the family there. By induction
on the statement, with an induction on the pattern through the entries of `cooImpl`. -/
theorem hutchppProg.exists_compile_coo (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ)) :
    ∃ c, ProgFamily.compile (r := 2) (b := 1) (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern)) =
      some c ∧ ∀ N n, c.toStmt N n = ProgFamily.inst (r := 2) (b := 1) (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern)) N n := by
  obtain ⟨c, hc, hc'⟩ := exists_compile_substOracle_cooImpl pattern _ (by norm_num : 0 < 3)
    (hutchppProg.compiled p o d) (Option.some_get _).symm
  exact ⟨c, hc, fun N n => (hc' _ _ N rfl).trans (congrArg
    (Stmt.substOracle (cooImpl (.const N) pattern)) (hutchppProg.toStmt_compiled p o d N n))⟩

/-- The tree of sparse Hutch++ instantiates, at every size, to the statement of the program
family with its oracle calls served by `NLAlib.Computation.cooImpl`. -/
theorem hutchppProg.toStmt_compiledCoo (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ))
    (N : ℕ) (n : Fin 2 → ℕ) :
    (hutchppProg.compiledCoo p o d pattern).toStmt N n = ProgFamily.inst (r := 2) (b := 1)
      (fun _ _ N n h =>
        ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern)) N n := by
  obtain ⟨c, hc, hc'⟩ := hutchppProg.exists_compile_coo p o d pattern
  rw [hutchppProg.compiledCoo, hc, Option.getD_some, hc']


/-- **Hutch++ as a program computes Hutch++**, in the matrix-free model: for every type of tags
with decidable equality, every type of oracle names, every tag $p$, oracle name $o$ and
distribution $d$ and every `RCLike` field $\Bbbk$, for all $N$, $k$ and $\ell \ge 1$, every
$N \times N$ matrix $\mathbf{A}$ over $\Bbbk$ (every oracle name means $\mathbf{A}$) and every
tape $\xi$, under exact arithmetic, the registered tree `hutchppProg.compiled p o d` run from a
single declared output cell succeeds within the counts `hutchppCount p o d N k ℓ` and
$2N(k + \ell) + 4$ cells besides the output, and its output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of $d$ from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major. No hypothesis on the rank of $\mathbf{A}\mathbf{S}$.
[MeyerMuscoMuscoWoodruff2021, Algorithm 1]; there with the costs stated in matrix-vector
products only.
Result: hutchpp-program -/
theorem matrixFreeHutchpp : MatrixFreeHutchpp := fun _ _ _ p o d _ _ =>
  (matrixFree_hutchppProg p o d).prog _ (hutchppProg.toStmt_compiled p o d)

/-- **The deviation of Hutch++ as a program**, in the probabilistic matrix-free model: for every
type of tags with decidable equality, every type of oracle names, every tag $p$ and oracle name
$o$ and every rank $r$, let the tape have the law of the tape (`tapeLaw`: the tape of the
Gaussian distribution an i.i.d. sequence of standard Gaussians, independent of the others),
$k \ge 1$, $\ell \ge 1$. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$k \ge 25 \cdot 1^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then for every real
$N \times N$ matrix $\mathbf{A}$ and every $\tau \ge 0$, with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, the probability that the
registered tree `hutchppProg.compiled p o .gaussian` fails to compute, within the counts
`hutchppCount` and $2N(k + \ell) + 4$ cells, a value $v$ with
$\lvert \operatorname{tr}\mathbf{A} - v \rvert < \tau$ is
at most <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 5\cdot 1/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 5\cdot 1/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. The sizes are $N$ and $n = (k, \ell)$. The output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$ of the Gaussian matrices it draws.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]; there with unspecified constants
and for the algorithm, not a program.
Result: hutchpp-program-tail -/
theorem matrixFreeProbHutchpp : MatrixFreeProbHutchpp := fun _ _ _ p o r _ hδ _ hτ =>
  (matrixFreeProb_hutchppProg p o r hδ hτ).prog _ (hutchppProg.toStmt_compiled p o .gaussian)

/-- **Dense Hutch++**, in the stored-entries model: for every type of tags with decidable
equality, every type of oracle names, every tag $p$, oracle name $o$ and distribution $d$ and
every `RCLike` field $\Bbbk$, with the oracle calls served by `NLAlib.Computation.denseImpl` from
$N^2$ stored entries $v$, column-major, so that the matrix is
$\mathbf{A} = (v_{i + Nj})_{i, j}$, under exact arithmetic and $\ell \ge 1$, for every tape the
registered tree `hutchppProg.compiledDense p o d` computes
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of $d$ from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major, with the counts `hutchppCount` in which each matrix-vector product
is replaced by $N^2$ multiplications, additions and reads and $N$ literals and each load costs
nothing, and $2N(k + \ell) + 5 + N^2$ cells of memory besides its output. No printed source.
Result: hutchpp-program-dense -/
theorem storedEntriesDenseHutchpp : StoredEntriesDenseHutchpp := fun _ _ _ p o d _ _ =>
  (storedEntries_substOracle_hutchppProg_denseImpl p o d).prog _
    (hutchppProg.toStmt_compiledDense p o d)

/-- **Sparse Hutch++**, in the stored-entries model: for every type of tags with decidable
equality, every type of oracle names, every tag $p$, oracle name $o$ and distribution $d$, every
public pattern and every `RCLike` field $\Bbbk$, with the oracle calls served by
`NLAlib.Computation.cooImpl` for the pattern, its positions in $[0, N)^2$ (unrolled into the
program, its index storage not counted), and `nnz` stored values $v$, so that the matrix is
`cooMatrix pattern v`, under exact arithmetic and $\ell \ge 1$, for every tape the tree
`hutchppProg.compiledCoo p o d pattern` computes
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of $d$ from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major, with the counts `hutchppCount` in which each matrix-vector product
is replaced by `nnz` multiplications, additions and reads and $N$ literals and each load costs
nothing, and $2N(k + \ell) + 5 + \mathit{nnz}$ cells of memory besides its output. No printed
source.
Result: hutchpp-program-sparse -/
theorem storedEntriesCooHutchpp : StoredEntriesCooHutchpp := fun _ _ _ p o d pattern _ _ =>
  (storedEntries_substOracle_hutchppProg_cooImpl p o d pattern).prog _
    (hutchppProg.toStmt_compiledCoo p o d pattern)

/-- **The Hutch++ target is not vacuous** (`docs/design/Computation-Hardening.md`, §2.2): for
every $N_0$ there are tags, oracle names, a distribution and a field (`Unit`, `Unit`, the
Gaussian, $\mathbb{R}$) and sizes $N = N_0 + 1$, $n = (1, 1)$ meeting the size condition
$\ell \ge 1$, the declared input type `Unit` inhabited. The witness of
`NLAlib.MatrixFreeHutchpp` (`scripts/Targets.lean`, item 7). No printed source. -/
theorem matrixFreeHutchpp_nonVacuous : ∀ N₀ : ℕ, ∃ (P ι : Type) (_ : DecidableEq P) (p : P)
    (o : ι) (d : Dist) (𝕜 : Type) (_ : RCLike 𝕜),
    MatrixFree.NonVacuous (𝕜 := 𝕜) p (hutchppProg.compiled p o d) (fun _ n => 0 < n 1)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun N n _ A ξ st => st.store.read p 0 0 = some
        (hutchpp A (tapeMatrix (ξ d) 0 N (n 0)) (tapeMatrix (ξ d) (N * n 0) N (n 1)))) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), (), .gaussian, ℝ, inferInstance, N₀ + 1,
    fun _ => 1, Nat.le_succ N₀, Nat.one_pos, ⟨()⟩⟩

/-- **The probabilistic Hutch++ target is not vacuous** (`docs/design/Computation-Hardening.md`,
§2.2): for every $N_0$ there are tags and oracle names (`Unit`), the rank $r = 1$,
$\delta = 1/2$, $\tau = 1$ and sizes $N = N_0 + 1$, $n = (k, 1)$ with
$k = \lceil\mathsf{subgaussianEmbeddingDim}(1, 1, 1/2, \delta/2)\rceil + 1$, meeting the size
condition, the declared input type `Unit` inhabited. The witness of
`NLAlib.MatrixFreeProbHutchpp` (`scripts/Targets.lean`, item 7). No printed source. -/
theorem matrixFreeProbHutchpp_nonVacuous : ∀ N₀ : ℕ, ∃ (P ι : Type) (_ : DecidableEq P) (p : P)
    (o : ι) (r : ℕ) (δ : ℝ) (_ : 0 < δ) (τ : ℝ) (_ : 0 ≤ τ),
    MatrixFreeProb.NonVacuous (𝕜 := ℝ) p (hutchppProg.compiled p o .gaussian)
      (fun _ n => 0 < n 0 ∧ 0 < n 1 ∧ subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o .gaussian N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun _ _ _ A st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)
      (fun _ n _ A => δ + 2 * Real.exp (-(hansonWrightConstant *
        min (n 1 * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (n 1 * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r))))))
      N₀ := by
  intro N₀
  set k := ⌈subgaussianEmbeddingDim 1 1 (1 / 2) ((1 / 2 : ℝ) / 2)⌉₊ + 1
  refine ⟨Unit, Unit, inferInstance, (), (), 1, 1 / 2, by norm_num, 1, zero_le_one, N₀ + 1,
    ![k, 1], Nat.le_succ N₀, ⟨Nat.succ_pos _, Nat.one_pos, ?_⟩, ⟨()⟩⟩
  simp only [Matrix.cons_val_zero, k, Nat.cast_add, Nat.cast_one]
  exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one)

/-- **The dense Hutch++ target is not vacuous** (`docs/design/Computation-Hardening.md`, §2.2):
for every $N_0$ there are tags, oracle names, a distribution and a field (`Unit`, `Unit`, the
Gaussian, $\mathbb{R}$) and sizes $N = N_0 + 1$, $n = (1, 1)$ meeting the size condition
$\ell \ge 1$, the declared input type `Unit` inhabited. The witness of
`NLAlib.StoredEntriesDenseHutchpp` (`scripts/Targets.lean`, item 7). No printed source. -/
theorem storedEntriesDenseHutchpp_nonVacuous : ∀ N₀ : ℕ, ∃ (P ι : Type) (_ : DecidableEq P)
    (p : P) (o : ι) (d : Dist) (𝕜 : Type) (_ : RCLike 𝕜),
    StoredEntries.NonVacuous (𝕜 := 𝕜) p (hutchppProg.compiledDense p o d) (fun _ n => 0 < n 1)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun N _ => N * N)
      (fun N n => substCount (denseCost N) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then N * N else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (Matrix.of fun (i j : Fin N) => vals (i + N * j)) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1)))) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), (), .gaussian, ℝ, inferInstance, N₀ + 1,
    fun _ => 1, Nat.le_succ N₀, Nat.one_pos, ⟨()⟩⟩

/-- **The sparse Hutch++ target is not vacuous** (`docs/design/Computation-Hardening.md`, §2.2):
for every $N_0$ there are tags, oracle names, a distribution, the one-entry pattern
$[(0, 0)]$ and a field (`Unit`, `Unit`, the Gaussian, $\mathbb{R}$) and sizes $N = N_0 + 1$,
$n = (1, 1)$ meeting the size condition ($\ell \ge 1$, the pattern in $[0, N)^2$), the declared
input type `Unit` inhabited. The witness of `NLAlib.StoredEntriesCooHutchpp`
(`scripts/Targets.lean`, item 7). No printed source. -/
theorem storedEntriesCooHutchpp_nonVacuous : ∀ N₀ : ℕ, ∃ (P ι : Type) (_ : DecidableEq P)
    (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ)) (𝕜 : Type) (_ : RCLike 𝕜),
    StoredEntries.NonVacuous (𝕜 := 𝕜) p (hutchppProg.compiledCoo p o d pattern)
      (fun N n => 0 < n 1 ∧ ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => pattern.length)
      (fun N n => substCount (cooCost N pattern.length) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then pattern.length else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (cooMatrix pattern vals) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1)))) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), (), .gaussian, [(0, 0)], ℝ, inferInstance, N₀ + 1,
    fun _ => 1, Nat.le_succ N₀, ⟨Nat.one_pos, by simp⟩, ⟨()⟩⟩

end Targets

end NLAlib
