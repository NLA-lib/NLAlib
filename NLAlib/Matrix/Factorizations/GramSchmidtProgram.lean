/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Order.Basic
public import NLAlib.Matrix.Factorizations.GramSchmidtTargets

/-!
# Gram–Schmidt as a program

In-place rank-revealing modified Gram–Schmidt on the $k$ columns of an $N \times k$ buffer
(`NLAlib.gramSchmidtProg`, in `NLAlib/Matrix/Factorizations/GramSchmidtProgramTree.lean`):
column $j$ is reduced against the earlier columns one at a time (`NLAlib.orthAgainst`,
the sweep `NLAlib.mgsSweep`), then normalised, or left zero when its squared norm is exactly zero.
In exact arithmetic the program computes `NLAlib.gramSchmidtQ` with no rank hypothesis (D6):
modified and classical Gram–Schmidt agree (`NLAlib.mgsSweep_eq_sub_sum`), and a column that
depends on the earlier ones is reduced to zero. The counts `NLAlib.gramSchmidtCount`
are those of a matrix of full column rank; each zero column saves one square root and $N$
divisions, and the realisation is an upper bound. This file proves the target
`NLAlib.MatrixFreeGramSchmidt` (in `NLAlib/Matrix/Factorizations/GramSchmidtTargets.lean`) about
the registered tree `NLAlib.gramSchmidtProg.compiled`. Design: `docs/design/Computation.md`
(D6, §5, F8).

## Main results

* `NLAlib.exec_orthAgainst`: the sweep computes `NLAlib.mgsSweep`.
* `NLAlib.exec_forRange_orthAgainst`: a loop of sweeps against the same columns.
* `NLAlib.exec_gramSchmidtProg`: the program computes `NLAlib.gramSchmidtQ` from any
  state.
* `NLAlib.matrixFree_gramSchmidtProg`: the realisation from its input, for the program family.
* `NLAlib.gramSchmidtProg.toStmt_compiled`: the registered tree instantiates to the family.
* `NLAlib.matrixFreeGramSchmidt`: the target `NLAlib.MatrixFreeGramSchmidt`.
-/
@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

open Computation Computation.Builder

section Specs

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

omit [RCLike 𝕜] [DecidableEq P] in
private theorem orthAgainst_run (p : P) (N Q : ℕ) (k : IExp ℕ) (v : ℕ) (vo : IExp ℕ)
    (r : Cell ℕ ℕ) :
    (orthAgainst (ι := ι) p (.const N) Q k v vo r).run = .seq (.loop k fun i =>
      (dot p r Q (IExp.const N * IExp.var i) v vo (.const N) >>= fun _ => ins (.un p .neg r r) >>=
        fun _ => axpy p r Q (IExp.const N * IExp.var i) v vo (.const N)).run) .skip := rfl

omit [DecidableEq P] in
private theorem sum_range_star_mul_dite {N : ℕ} (f g : Fin N → 𝕜) :
    ∑ a ∈ Finset.range N, star (if h : a < N then f ⟨a, h⟩ else 0) *
      (if h : a < N then g ⟨a, h⟩ else 0) = star f ⬝ᵥ g := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => star (if h : a < N then f ⟨a, h⟩ else 0) *
    (if h : a < N then g ⟨a, h⟩ else 0))]
  simp [dotProduct]

private theorem col_lt {N c j a : ℕ} (hc : c < j) (ha : a < N) : N * c + a < N * j := by
  have := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hc)
  rw [Nat.mul_succ] at this
  omega

/-- One sweep step of `orthAgainst`, against column `i`. -/
private theorem exec_orthAgainst_step (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι)) {N : ℕ}
    (Q : ℕ) (k : IExp ℕ) (v : ℕ) (vo : IExp ℕ) (r : Cell ℕ ℕ) (V : ℕ → Fin N → 𝕜)
    (w : Fin N → 𝕜) (hQ : ∀ i < k.eval, ∀ a : Fin N, st.store.read p Q (N * i + a) = some (V i a))
    (hvQ : v = Q → N * k.eval ≤ vo.eval) (hrv : r.buf = v → N = 0) (hrQ : r.buf = Q → N = 0)
    (hr : ∃ s, st.store.write p r.buf r.idx.eval 0 = some s) (i : ℕ) (hi : i < k.eval)
    (st' : St P 𝕜 (OpCount P ι))
    (hv' : ∀ a : Fin N, st'.store.read p v (vo.eval + a) = some (mgsSweep V w i a))
    (hfr : ∀ q b j, (b = v → j < vo.eval ∨ vo.eval + N ≤ j) → (b = r.buf → j ≠ r.idx.eval) →
      st'.store.read q b j = st.store.read q b j)
    (hsh : st'.store.shape = st.store.shape) :
    ∃ st'', exec I (dot p r Q (IExp.const N * IExp.var i) v vo (.const N) >>= fun _ =>
        ins (.un p .neg r r) >>= fun _ =>
          axpy p r Q (IExp.const N * IExp.var i) v vo (.const N)).run st' =
        some st'' ∧
      (∀ a : Fin N, st''.store.read p v (vo.eval + a) = some (mgsSweep V w (i + 1) a)) ∧
      (∀ q b j, (b = v → j < vo.eval ∨ vo.eval + N ≤ j) → (b = r.buf → j ≠ r.idx.eval) →
        st''.store.read q b j = st.store.read q b j) ∧
      st''.store.shape = st.store.shape ∧ st''.pos = st'.pos ∧ st''.cur = st'.cur ∧
      st''.curW = st'.curW ∧
      st''.cnt = st'.cnt + (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) ∧
      st''.peak ≤ Function.update st'.peak p (max (st'.peak p) (st'.cur p + 1)) ∧
      st''.peakW ≤ max st'.peakW (st'.curW + I.width p) := by
  set u := mgsSweep V w i with hu
  set xs : ℕ → 𝕜 := fun a => if h : a < N then V i ⟨a, h⟩ else 0 with hxs
  set ys : ℕ → 𝕜 := fun a => if h : a < N then u ⟨a, h⟩ else 0 with hys
  set c := ∑ a ∈ Finset.range N, star (xs a) * ys a with hcdef
  have hc' : c = star (V i) ⬝ᵥ u := sum_range_star_mul_dite _ _
  have hNi : ∀ a < N, N * i + a < N * k.eval := fun a ha => by
    have := Nat.add_mul_lt_mul_of_lt_of_lt ha hi
    omega
  have hrQ' : ∀ a < N, r.buf ≠ Q := fun a ha h => by have := hrQ h; omega
  have hrv' : ∀ a < N, r.buf ≠ v := fun a ha h => by have := hrv h; omega
  have hQ' : ∀ a < N, st'.store.read p Q (N * i + a) = some (xs a) := fun a ha => by
    rw [hfr p Q _ (fun h => Or.inl ((hNi a ha).trans_le (hvQ h.symm)))
      (fun h => absurd h.symm (hrQ' a ha)),
      hQ i hi ⟨a, ha⟩]
    simp [xs, ha]
  have hy' : ∀ a < N, st'.store.read p v (vo.eval + a) = some (ys a) := fun a ha => by
    rw [hv' ⟨a, ha⟩]
    simp [ys, ha]
  obtain ⟨s₀, hs₀⟩ := hr
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ c
  obtain ⟨st1, h1, hst1, hpos1, hcur1, hcurW1, hcnt1, hpeak1, hpeakW1⟩ :=
    exec_dot I hI hc p st' r Q (IExp.const N * IExp.var i) v vo (.const N) xs ys (by exact hQ') hy'
      (fun h i hi => absurd h (hrQ' i hi)) (fun h i hi => absurd h (hrv' i hi)) s1 hs1
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_write_eq_some hs1 (-c)
  have hs2₁ : s1.write p r.buf r.idx.eval (-c) = some s2 := by
    rw [Store.write_of_write_eq_some hs1]; exact hs2
  have hneg : exec I (ins (.un p .neg r r)).run st1 =
      some { st1 with store := s2, cnt := st1.cnt + I.charge (.un p .neg) } :=
    (exec_seq_instr_un I (by rw [hst1]; exact Store.read_of_write_eq_some hs1) (by rw [hI]; rfl)
      (by rw [hst1]; exact hs2₁)).trans (exec_skip I _)
  have hx2 : ∀ a < N, s2.read p Q (N * i + a) = some (xs a) := fun a ha => by
    rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inl (Ne.symm (hrQ' a ha))), hQ' a ha]
  have hy2 : ∀ a < N, s2.read p v (vo.eval + a) = some (ys a) := fun a ha => by
    rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inl (Ne.symm (hrv' a ha))), hy' a ha]
  obtain ⟨s3, hs3⟩ := Store.exists_writeBlock_eq_some (s := s2) (b := v) (off := vo.eval)
    (xs := (List.range N).toArray.map fun a => -c * xs a + ys a)
    (fun j hj => ⟨ys j, hy2 j (by simpa using hj)⟩)
  obtain ⟨st3, h3, hst3, hpos3, hcur3, hcurW3, hcnt3, hpeak3, hpeakW3⟩ :=
    exec_axpy I hI hc p { st1 with store := s2, cnt := st1.cnt + I.charge (.un p .neg) } r Q
      (IExp.const N * IExp.var i) v vo (.const N) (-c) xs ys (Store.read_of_write_eq_some hs2)
      (by exact hx2) hy2
      (fun h i hi => absurd h (hrv' i hi))
      (fun h a ha b _ he => absurd he (by
        simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_var]
        have := hNi a ha; have := hvQ h.symm; omega)) s3 hs3
  rw [exec_run_bind I (b := dot p r Q (IExp.const N * IExp.var i) v vo (.const N)) (fun _ => rfl),
    h1,
    Option.bind_some, exec_run_bind I (b := ins (.un p .neg r r)) (fun _ => rfl), hneg,
    Option.bind_some]
  refine ⟨st3, h3, fun a => ?_, fun q b j hb hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst3, Store.read_of_writeBlock_eq_some_of_lt hs3 (by simp)]
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range a.2,
      Option.map_some, Option.some.injEq, xs, ys, a.2, dif_pos, mgsSweep, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hu]
    rw [hc']
    ring
  · rw [hst3, Store.read_of_writeBlock_eq_some_of_ne hs3 ?_, Store.read_of_write_eq_some_of_ne hs2,
      hfr q b j hb hr]
    · by_cases h : b = r.buf
      · exact Or.inr (hr h)
      · exact Or.inl h
    · by_cases h : b = v
      · rcases hb h with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (by simpa using h'))
      · exact Or.inl h
  · rw [hst3, Store.shape_of_writeBlock_eq_some hs3, Store.shape_of_write_eq_some hs2, hsh]
  · rw [hpos3, ← hpos1]
  · rw [hcur3, ← hcur1]
  · rw [hcurW3, ← hcurW1]
  · rw [hcnt3]
    simp only [hcnt1, hc.charge_eq, add_assoc, IExp.eval_const]
  · rw [hpeak3]
    dsimp only
    rw [hpeak1, hcur1]
    exact Function.update_max_le_update_max le_rfl
  · rw [hpeakW3]
    dsimp only
    rw [hpeakW1, hcurW1]
    omega

private theorem exec_orthAgainst_of_imp (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι)) {N : ℕ}
    (Q : ℕ) (k : IExp ℕ) (v : ℕ) (vo : IExp ℕ) (r : Cell ℕ ℕ) (V : ℕ → Fin N → 𝕜)
    (w : Fin N → 𝕜) (hQ : ∀ i < k.eval, ∀ a : Fin N, st.store.read p Q (N * i + a) = some (V i a))
    (hv : ∀ a : Fin N, st.store.read p v (vo.eval + a) = some (w a))
    (hvQ : v = Q → N * k.eval ≤ vo.eval) (hrv : r.buf = v → N = 0)
    (hrQ : r.buf = Q → N = 0)
    (hr : ∃ s, st.store.write p r.buf r.idx.eval 0 = some s) :
    ∃ st', exec I (orthAgainst p (.const N) Q k v vo r).run st = some st' ∧
      (∀ a : Fin N, st'.store.read p v (vo.eval + a) = some (mgsSweep V w k.eval a)) ∧
      (∀ q b i, (b = v → i < vo.eval ∨ vo.eval + N ≤ i) → (b = r.buf → i ≠ r.idx.eval) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + k.eval • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  rw [orthAgainst_run, exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun i st' =>
      (∀ a : Fin N, st'.store.read p v (vo.eval + a) = some (mgsSweep V w i a)) ∧
      (∀ q b j, (b = v → j < vo.eval ∨ vo.eval + N ≤ j) → (b = r.buf → j ≠ r.idx.eval) →
        st'.store.read q b j = st.store.read q b j) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.curW = st.curW ∧
      st'.cnt = st.cnt + i • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p))
    ⟨hv, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, by simp,
      le_update_self_iff.2 (le_max_left _ _), le_max_left _ _⟩ ?_
  intro i hi st' ⟨hv', hfr, hsh, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  obtain ⟨st'', h, hv'', hfr'', hsh'', hpos'', hcur'', hcurW'', hcnt'', hpeak'', hpeakW''⟩ :=
    exec_orthAgainst_step I hI hc p st Q k v vo r V w hQ hvQ hrv hrQ hr i hi st' hv' hfr hsh
  refine ⟨st'', h, hv'', hfr'', hsh'', hpos''.trans hpos, hcur''.trans hcur,
    hcurW''.trans hcurW, by rw [hcnt'', hcnt, succ_nsmul, add_assoc],
    hpeak''.trans (by rw [hcur]; exact Function.update_max_le_update_max hpeak), hpeakW''.trans ?_⟩
  rw [hcurW]
  exact max_le hpeakW (le_max_right _ _)

/-- **The sweep computes the modified Gram–Schmidt sweep** under exact arithmetic: if columns
$i < k$ of the buffer $Q$ hold $\mathbf{v}_i$, the cells of $\mathbf{v}$ hold $\mathbf{w}$ and lie
after those columns when in the same buffer, and the cell $r$ is writable and in neither, the run
leaves `mgsSweep V w k` in the cells of $\mathbf{v}$, changes no other cell but $r$ and no buffer's
tag or length, keeps the tape and the current memory, raises the peak by at most one cell, and
counts, $k$ times over, $N$ conjugations, $2N$ multiplications, $2N$ additions, one literal and
one negation.
[GolubVanLoan2013, §5.2.8]. -/
theorem exec_orthAgainst (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι)) {N : ℕ}
    (Q : ℕ) (k : IExp ℕ) (v : ℕ) (vo : IExp ℕ) (r : Cell ℕ ℕ) (V : ℕ → Fin N → 𝕜)
    (w : Fin N → 𝕜) (hQ : ∀ i < k.eval, ∀ a : Fin N, st.store.read p Q (N * i + a) = some (V i a))
    (hv : ∀ a : Fin N, st.store.read p v (vo.eval + a) = some (w a))
    (hvQ : v = Q → N * k.eval ≤ vo.eval) (hrv : r.buf ≠ v) (hrQ : r.buf ≠ Q)
    (hr : ∃ s, st.store.write p r.buf r.idx.eval 0 = some s) :
    ∃ st', exec I (orthAgainst p (.const N) Q k v vo r).run st = some st' ∧
      (∀ a : Fin N, st'.store.read p v (vo.eval + a) = some (mgsSweep V w k.eval a)) ∧
      (∀ q b i, (b = v → i < vo.eval ∨ vo.eval + N ≤ i) → (b = r.buf → i ≠ r.idx.eval) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + k.eval • (N • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1 + Finsupp.single (.un p .neg) 1 +
        N • (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) :=
  exec_orthAgainst_of_imp I hI hc p st Q k v vo r V w hQ hv hvQ (fun h => absurd h hrv)
    (fun h => absurd h hrQ) hr

/-- A loop of sweeps: for $j < \ell$, `orthAgainst` sweeps column $k + j$ of the $N$-row
buffer `B` against its first $k$ columns, with the coefficient in the scratch cell `t[0]`. If
these columns hold $\mathbf{q}_0, \dots, \mathbf{q}_{k-1}$ and column $k + j$ holds
$\mathbf{g}_j$, the run leaves in column $k + j$ the sweep of $\mathbf{g}_j$ against them
(`NLAlib.mgsSweep`; the projection $(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{g}_j$
when they are orthonormal), changes no cell of the first $k$ columns or outside `B` and the
scratch buffer, keeps the shape, the tape and the current memory, raises the peaks by at most
one cell at tag $p$, and counts $\ell$ sweeps. -/
theorem exec_forRange_orthAgainst (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) {N k : ℕ} (B t : ℕ) (ℓE : IExp ℕ)
    (Q G : ℕ → Fin N → 𝕜) (st : St P 𝕜 (OpCount P ι))
    (hQ : ∀ i < k, ∀ a : Fin N, st.store.read p B (N * i + a) = some (Q i a))
    (hG : ∀ j < ℓE.eval, ∀ a : Fin N, st.store.read p B (N * (k + j) + a) = some (G j a))
    (htB : t ≠ B) (ht : ∃ s, st.store.write p t 0 0 = some s) :
    ∃ st', exec I (forRange ℓE fun j => orthAgainst p (.const N) B (.const k) B
        (.const N * (.const k + .var j)) ⟨t, 0⟩).run st = some st' ∧
      (∀ j < ℓE.eval, ∀ a : Fin N,
        st'.store.read p B (N * (k + j) + a) = some (mgsSweep Q (G j) k a)) ∧
      (∀ q b i, (b = B → i < N * k) → b ≠ t → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.curW = st.curW ∧
      st'.cnt = st.cnt + ℓE.eval • (k • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1))) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  rw [show (forRange (ι := ι) ℓE fun j => orthAgainst p (.const N) B (.const k) B
      (.const N * (.const k + .var j)) ⟨t, 0⟩).run = .seq (.loop ℓE fun j =>
        (orthAgainst p (.const N) B (.const k) B (.const N * (.const k + .var j))
          ⟨t, 0⟩).run) .skip from rfl, exec_seq_skip]
  obtain ⟨s₀, hs₀⟩ := ht
  refine exists_exec_loop_eq_some_of_forall I (fun j st' =>
      (∀ j' < j, ∀ a : Fin N,
        st'.store.read p B (N * (k + j') + a) = some (mgsSweep Q (G j') k a)) ∧
      (∀ q b i, (b = B → i < N * k ∨ N * (k + j) ≤ i) → b ≠ t →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.curW = st.curW ∧
      st'.cnt = st.cnt + j • (k • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1))) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p))
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by simp, fun q => by
        by_cases hq : q = p
        · subst hq; simp
        · simp [Function.update_of_ne hq], le_max_left _ _⟩ ?_
    |>.imp fun st' h => ⟨h.1, h.2.1, fun q b i hb hbt => h.2.2.1 q b i (fun h' => Or.inl (hb h'))
      hbt, h.2.2.2⟩
  intro j hj st' ⟨hsw, hfr, hsh, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  obtain ⟨st'', h, hv'', hfr'', hsh'', hpos'', hcur'', hcurW'', hcnt'', hpeak'', hpeakW''⟩ :=
    exec_orthAgainst I hI hc p st' B (.const k) B (.const N * (.const k + .var j)) ⟨t, 0⟩ Q (G j)
      (fun i hi a => by
        rw [hfr p B _ (fun _ => Or.inl (col_lt (N := N) hi a.2)) (Ne.symm htB), hQ i hi a])
      (fun a => by
        change st'.store.read p B (N * (k + j) + a) = _
        rw [hfr p B _ (fun _ => Or.inr (by omega)) (Ne.symm htB), hG j hj a])
      (fun _ => by
        simp only [IExp.eval_mul, IExp.eval_add, IExp.eval_const, IExp.eval_var]
        exact Nat.mul_le_mul_left N (Nat.le_add_right k j)) htB htB
      (Store.exists_write_eq_some_of_shape_eq hsh hs₀ 0)
  refine ⟨st'', h, fun j' hj' a => ?_, fun q b i hb hbt => ?_, hsh''.trans hsh,
    hpos''.trans hpos, hcur''.trans hcur, hcurW''.trans hcurW,
    by simp only [hcnt'', hcnt, succ_nsmul, add_assoc, IExp.eval_const], ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | rfl
    · rw [hfr'' p B _ (fun _ => Or.inl (col_lt (N := N) (j := k + j) (by omega) a.2))
        (fun h => absurd h.symm htB),
        hsw j' h' a]
    · exact hv'' a
  · have hmono := Nat.mul_le_mul_left N (Nat.le_add_right k j)
    have hsucc : N * (k + j) + N = N * (k + (j + 1)) := by rw [← Nat.add_assoc, Nat.mul_succ]
    rw [hfr'' q b i (fun h => ?_) (fun h => absurd h hbt), hfr q b i (fun h => ?_) hbt]
    · rcases hb h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by omega)
    · change i < N * (k + j) ∨ N * (k + j) + N ≤ i
      rcases hb h with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · rw [hcur] at hpeak''
    refine hpeak''.trans fun q => ?_
    by_cases hq : q = p
    · subst hq
      have := hpeak q
      simp only [Function.update_self] at this ⊢
      omega
    · have := hpeak q
      simp only [Function.update_of_ne hq] at this ⊢
      exact this
  · rw [hcurW] at hpeakW''
    exact hpeakW''.trans (max_le hpeakW (le_max_right _ _))

omit [RCLike 𝕜] [DecidableEq P] in
private theorem gramSchmidtCount_succ (p : P) (N j : ℕ) :
    gramSchmidtCount (ι := ι) p N (j + 1) = gramSchmidtCount p N j +
      (j • (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1 +
        Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) +
      (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1) +
      Finsupp.single (OpKind.lit p) 1 + (Finsupp.single (OpKind.cmp p) 1 +
      Finsupp.single (OpKind.un p .sqrt) 1 +
      N • Finsupp.single (OpKind.bin p .div) 1)) := by
  have h : ∀ j, gramSchmidtCount (ι := ι) p N j =
      (2 * N * j.choose 2 + N * j) • Finsupp.single (OpKind.bin p .mul) 1 +
      (2 * N * j.choose 2 + N * j) • Finsupp.single (OpKind.bin p .add) 1 +
      (N * j.choose 2 + N * j) • Finsupp.single (OpKind.un p .conj) 1 +
      j.choose 2 • Finsupp.single (OpKind.un p .neg) 1 +
      (j.choose 2 + 2 * j) • Finsupp.single (OpKind.lit p) 1 +
      j • Finsupp.single (OpKind.cmp p) 1 + j • Finsupp.single (OpKind.un p .sqrt) 1 +
      (N * j) • Finsupp.single (OpKind.bin p .div) 1 := fun j => by
    simp only [gramSchmidtCount, Finsupp.smul_single_one]
  rw [h, h, Nat.choose_succ_succ', Nat.choose_one_right]
  module

private theorem col_ge {N c j a : ℕ} (hc : j + 1 ≤ c) : N * j + N ≤ N * c + a := by
  have := Nat.mul_le_mul_left N hc
  rw [Nat.mul_succ] at this
  omega

/-- The normalisation of a swept column `ρ q`, with its squared norm in `t[1]` and `0` in
`t[0]`. -/
private theorem exec_gramSchmidt_normalize (I : Interp P ι 𝕜 (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (p : P) {N : ℕ}
    (Y t : ℕ) (jE : IExp ℕ) (st3 : St P 𝕜 (OpCount P ι)) (q : Fin N → 𝕜) (ρ : 𝕜) (hρ : 0 ≤ ρ)
    (hq : ρ = 0 → q = 0) (hq1 : ρ ≠ 0 → star q ⬝ᵥ q = 1) (hYt : Y = t → N = 0)
    (hcol : ∀ a : Fin N, st3.store.read p Y (jE.eval + a) = some (ρ * q a))
    (ht1 : st3.store.read p t 1 = some (star (ρ • q) ⬝ᵥ (ρ • q)))
    (ht0 : st3.store.read p t 0 = some 0) :
    ∃ st4, exec I (ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ())
        (ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩) >>= fun _ => rscl p ⟨t, 1⟩ Y jE (IExp.const N))).run st3 =
        some st4 ∧
      (∀ a : Fin N, st4.store.read p Y (jE.eval + a) = some (q a)) ∧
      (∀ q' b i, (b = Y → i < jE.eval ∨ jE.eval + N ≤ i) → b ≠ t →
        st4.store.read q' b i = st3.store.read q' b i) ∧
      st4.store.shape = st3.store.shape ∧ st4.pos = st3.pos ∧ st4.cur = st3.cur ∧
      st4.curW = st3.curW ∧
      st4.cnt ≤ st3.cnt + (Finsupp.single (OpKind.cmp p) 1 + Finsupp.single (OpKind.un p .sqrt) 1 +
        N • Finsupp.single (OpKind.bin p .div) 1) ∧
      st4.peak = st3.peak ∧ st4.peakW = st3.peakW := by
  set d := star (ρ • q) ⬝ᵥ (ρ • q) with hd
  have hrun : (ifThenElse (ι := ι) p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ())
      (ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩) >>= fun _ => rscl p ⟨t, 1⟩ Y jE (IExp.const N))).run =
      .seq (.ite p .eq ⟨t, 1⟩ ⟨t, 0⟩ .skip (ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩) >>= fun _ =>
        rscl p ⟨t, 1⟩ Y jE (IExp.const N)).run) .skip := rfl
  have hcmp : ∀ r : Bool, (d = 0 ↔ r = true) → cmpStep I p .eq ⟨t, 1⟩ ⟨t, 0⟩ st3 =
      some (r, { st3 with cnt := st3.cnt + I.charge (.cmp p) }) := by
    intro r hr
    unfold cmpStep
    dsimp only [IExp.eval_one, IExp.eval_zero]
    rw [ht1, ht0, hI]
    simp only [exactSem, Option.map_some]
    cases r <;> simpa using hr
  rw [hrun, exec_seq_skip, exec_ite]
  by_cases hρ0 : ρ = 0
  · have hd0 : d = 0 := by simp [hd, hρ0]
    rw [hcmp true (by simp [hd0]), Option.bind_some, if_pos rfl]
    refine ⟨_, exec_skip I _, fun a => ?_, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, ?_, rfl,
      rfl⟩
    · rw [hcol a, hρ0, hq hρ0]
      simp
    · rw [hc.charge_eq]
      exact add_le_add (le_refl _) (le_add_right le_self_add)
  obtain ⟨r, hr0, hrρ⟩ := RCLike.nonneg_iff_exists_ofReal.mp hρ
  have hd' : d = ((r ^ 2 : ℝ) : 𝕜) := by
    rw [hd, star_smul, smul_dotProduct, dotProduct_smul, hq1 hρ0, ← hrρ]
    simp [pow_two]
  have hdne : d ≠ 0 := by
    rw [hd']
    have : r ≠ 0 := fun h => hρ0 (by rw [← hrρ, h, RCLike.ofReal_zero])
    exact_mod_cast pow_ne_zero 2 this
  have hsq : ((√(RCLike.re d) : ℝ) : 𝕜) = ρ := by
    rw [hd', RCLike.ofReal_re, Real.sqrt_sq hr0, hrρ]
  have hdnn : (0 : 𝕜) ≤ d := by
    rw [hd']
    exact RCLike.ofReal_nonneg.mpr (sq_nonneg r)
  rw [hcmp false (by simp [hdne]), Option.bind_some, if_neg Bool.false_ne_true]
  rw [exec_run_bind I (b := ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)) (fun _ => rfl)]
  obtain ⟨s4, hs4⟩ := Store.exists_write_eq_some_of_read_eq_some (v := ρ) ht1
  rw [show (ins (ι := ι) (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)).run =
    .seq (.instr (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)) .skip from rfl]
  rw [(exec_seq_instr_un I (by exact ht1) (by rw [hI]; exact (if_pos hdnn).trans (by rw [hsq]))
    (by exact hs4)).trans (exec_skip I _), Option.bind_some]
  have hYt' : ∀ a < N, Y ≠ t := fun a ha h => by have := hYt h; omega
  have hx : ∀ a < N, s4.read p Y (jE.eval + a) =
      some (if h : a < N then ρ * q ⟨a, h⟩ else 0) := fun a ha => by
    rw [Store.read_of_write_eq_some_of_ne hs4 (Or.inl (hYt' a ha)), hcol ⟨a, ha⟩]
    simp [ha]
  obtain ⟨s5, hs5⟩ := Store.exists_writeBlock_eq_some (s := s4) (b := Y) (off := jE.eval)
    (xs := (List.range N).toArray.map fun a => (if h : a < N then ρ * q ⟨a, h⟩ else 0) / ρ)
    (fun j hj => ⟨_, hx j (by simpa using hj)⟩)
  obtain ⟨st5, h5, hst5, hpos5, hcur5, hcurW5, hcnt5, hpeak5, hpeakW5⟩ :=
    exec_rscl I hI hc p { st3 with
        store := s4
        cnt := st3.cnt + I.charge (.cmp p) + I.charge (.un p .sqrt) } ⟨t, 1⟩ Y jE (IExp.const N) ρ
      _ hρ0 (Store.read_of_write_eq_some hs4) (by exact hx)
      (fun h i hi => absurd (hYt h.symm) (by simp only [IExp.eval_const] at hi; omega))
      s5 hs5
  refine ⟨st5, h5, fun a => ?_, fun q' b i hb hbt => ?_, ?_, hpos5, hcur5, hcurW5, ?_, hpeak5,
    hpeakW5⟩
  · rw [hst5, Store.read_of_writeBlock_eq_some_of_lt hs5 (by simp)]
    simp [a.2, mul_div_cancel_left₀ _ hρ0]
  · rw [hst5, Store.read_of_writeBlock_eq_some_of_ne hs5 ?_,
      Store.read_of_write_eq_some_of_ne hs4 (Or.inl hbt)]
    by_cases h : b = Y
    · rcases hb h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (by simpa using h'))
    · exact Or.inl h
  · rw [hst5, Store.shape_of_writeBlock_eq_some hs5, Store.shape_of_write_eq_some hs4]
  · rw [hcnt5]
    dsimp only
    simp only [hc.charge_eq, IExp.eval_const, add_assoc, le_refl]

/-- The sweep of column `j` against the earlier columns, its squared norm into `t[1]`, and `0`
into `t[0]`. -/
private theorem exec_gramSchmidt_reduce (I : Interp P ι 𝕜 (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (p : P) (Y t : ℕ)
    {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜) (j : ℕ) (hj : j < k) (hYt : Y = t → N = 0)
    (st' : St P 𝕜 (OpCount P ι))
    (hQ : ∀ (a : Fin N) (c : Fin k), (c : ℕ) < j →
      st'.store.read p Y (N * c + a) = some (gramSchmidtQ M a c))
    (hM : ∀ a : Fin N, st'.store.read p Y (N * j + a) = some (M a ⟨j, hj⟩))
    (ht0 : ∃ s, st'.store.write p t 0 0 = some s) (ht1 : ∃ s, st'.store.write p t 1 0 = some s) :
    ∃ st1 st2 st3,
      exec I (orthAgainst p (.const N) Y (.var j) Y (IExp.const N * IExp.var j) ⟨t, 0⟩).run
        st' = some st1 ∧
      exec I (dot p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) Y (IExp.const N * IExp.var j)
        (.const N)).run st1 = some st2 ∧
      exec I (ins (.lit p ⟨t, 0⟩ 0)).run st2 = some st3 ∧
      (∀ a : Fin N, st3.store.read p Y ((IExp.const N * IExp.var j).eval + a) =
        some (gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩ * (gramSchmidtQ M).col ⟨j, hj⟩ a)) ∧
      st3.store.read p t 1 =
        some (star (gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨j, hj⟩) ⬝ᵥ
          (gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨j, hj⟩)) ∧
      st3.store.read p t 0 = some 0 ∧
      (∀ q b i, (b = Y → i < N * j ∨ N * j + N ≤ i) → b ≠ t →
        st3.store.read q b i = st'.store.read q b i) ∧
      st3.store.shape = st'.store.shape ∧ st3.pos = st'.pos ∧ st3.cur = st'.cur ∧
      st3.curW = st'.curW ∧
      st3.cnt = st'.cnt + (j • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) +
      (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1) +
      Finsupp.single (OpKind.lit p) 1) ∧
      st3.peak ≤ Function.update st'.peak p (max (st'.peak p) (st'.cur p + 1)) ∧
      st3.peakW ≤ max st'.peakW (st'.curW + I.width p) := by
  set u := gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨j, hj⟩ with hu
  set Vc : ℕ → Fin N → 𝕜 := fun c a => if h : c < k then gramSchmidtQ M a ⟨c, h⟩ else 0
  obtain ⟨st1, h1, hv1, hfr1, hsh1, hpos1, hcur1, hcurW1, hcnt1, hpeak1, hpeakW1⟩ :=
    exec_orthAgainst_of_imp I hI hc p st' Y (.var j) Y (IExp.const N * IExp.var j) ⟨t, 0⟩ Vc
      (M.col ⟨j, hj⟩) (fun i hi a => by
        rw [hQ a ⟨i, (show i < j from hi).trans hj⟩ hi]
        simp [Vc, (show i < j from hi).trans hj]) (fun a => by exact hM a) (fun _ => le_rfl)
      (fun h => hYt h.symm) (fun h => hYt h.symm) ht0
  have hYt' : ∀ a < N, Y ≠ t := fun a ha h => by have := hYt h; omega
  have hv1' : ∀ a < N, st1.store.read p Y (N * j + a) =
      some (if h : a < N then u ⟨a, h⟩ else 0) := fun a ha => by
    rw [show N * j + a = (IExp.const N * IExp.var j).eval + (⟨a, ha⟩ : Fin N) from rfl, hv1]
    simp only [ha, dif_pos]
    exact congrArg some (congrFun (mgsSweep_gramSchmidtQ_col M ⟨j, hj⟩) _)
  obtain ⟨s₀, hs₀⟩ := ht1
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_shape_eq hsh1 hs₀
    (∑ a ∈ Finset.range N, star (if h : a < N then u ⟨a, h⟩ else 0) *
      (if h : a < N then u ⟨a, h⟩ else 0))
  obtain ⟨st2, h2, hst2, hpos2, hcur2, hcurW2, hcnt2, hpeak2, hpeakW2⟩ :=
    exec_dot I hI hc p st1 ⟨t, 1⟩ Y (IExp.const N * IExp.var j) Y (IExp.const N * IExp.var j)
      (.const N) _ _ (by exact hv1') (by exact hv1')
      (fun h i hi => absurd (hYt h.symm) (by simp only [IExp.eval_const] at hi; omega))
      (fun h i hi => absurd (hYt h.symm) (by simp only [IExp.eval_const] at hi; omega)) s2 hs2
  obtain ⟨s₀', hs₀'⟩ := ht0
  obtain ⟨s3, hs3⟩ := Store.exists_write_eq_some_of_shape_eq (s' := st2.store)
    (by rw [hst2, Store.shape_of_write_eq_some hs2, hsh1]) hs₀' ((0 : ℚ) : 𝕜)
  have h3 : exec I (ins (.lit p ⟨t, 0⟩ 0)).run st2 =
      some { st2 with store := s3, cnt := st2.cnt + I.charge (.lit p) } :=
    (exec_seq_instr_lit I (by rw [hI]; rfl) (by exact hs3)).trans (exec_skip I _)
  refine ⟨st1, st2, _, h1, h2, h3, fun a => ?_, ?_, ?_, fun q b i hb hbt => ?_, ?_,
    hpos2.trans hpos1, hcur2.trans hcur1, hcurW2.trans hcurW1, ?_, ?_, ?_⟩
  · change s3.read p Y (N * j + a) = _
    rw [Store.read_of_write_eq_some_of_ne hs3 (Or.inl (hYt' a a.2)), hst2,
      Store.read_of_write_eq_some_of_ne hs2 (Or.inl (hYt' a a.2)), hv1' a a.2]
    simp [u]
  · change s3.read p t 1 = _
    rw [Store.read_of_write_eq_some_of_ne hs3 (Or.inr Nat.one_ne_zero), hst2,
      Store.read_of_write_eq_some hs2, sum_range_star_mul_dite]
  · change s3.read p t 0 = _
    rw [Store.read_of_write_eq_some hs3, Rat.cast_zero]
  · change s3.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hs3 (Or.inl hbt), hst2,
      Store.read_of_write_eq_some_of_ne hs2 (Or.inl hbt), hfr1 q b i hb (fun h => absurd h hbt)]
  · change s3.shape = _
    rw [Store.shape_of_write_eq_some hs3, hst2, Store.shape_of_write_eq_some hs2, hsh1]
  · change st2.cnt + I.charge (.lit p) = _
    simp only [hcnt2, hcnt1, hc.charge_eq, IExp.eval_const, IExp.eval_var, add_assoc]
  · change st2.peak ≤ _
    rw [hpeak2, hcur1]
    exact Function.update_max_le_update_max hpeak1
  · change st2.peakW ≤ _
    rw [hpeakW2, hcurW1]
    exact max_le (hpeakW1.trans (le_refl _)) (le_max_right _ _)

/-- One column of `gramSchmidtProg`: sweep, norm, normalisation. -/
private theorem exec_gramSchmidt_col (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (Y t : ℕ) {N k : ℕ}
    (M : Matrix (Fin N) (Fin k) 𝕜) (j : ℕ) (hj : j < k) (hYt : Y = t → N = 0)
    (st' : St P 𝕜 (OpCount P ι))
    (hQ : ∀ (a : Fin N) (c : Fin k), (c : ℕ) < j →
      st'.store.read p Y (N * c + a) = some (gramSchmidtQ M a c))
    (hM : ∀ (a : Fin N) (c : Fin k), j ≤ (c : ℕ) →
      st'.store.read p Y (N * c + a) = some (M a c))
    (ht0 : ∃ s, st'.store.write p t 0 0 = some s) (ht1 : ∃ s, st'.store.write p t 1 0 = some s) :
    ∃ st'', exec I (orthAgainst p (.const N) Y (.var j) Y (IExp.const N * IExp.var j) ⟨t, 0⟩ >>=
        fun _ => dot p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) Y (IExp.const N * IExp.var j)
          (.const N) >>= fun _ => ins (.lit p ⟨t, 0⟩ 0) >>= fun _ =>
        ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) (ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩) >>= fun _ =>
          rscl p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) (.const N))).run st' = some st'' ∧
      (∀ (a : Fin N) (c : Fin k), (c : ℕ) < j + 1 →
        st''.store.read p Y (N * c + a) = some (gramSchmidtQ M a c)) ∧
      (∀ (a : Fin N) (c : Fin k), j + 1 ≤ (c : ℕ) →
        st''.store.read p Y (N * c + a) = some (M a c)) ∧
      (∀ q b i, (b = Y → N * k ≤ i) → b ≠ t → st''.store.read q b i = st'.store.read q b i) ∧
      st''.store.shape = st'.store.shape ∧ st''.pos = st'.pos ∧ st''.cur = st'.cur ∧
      st''.curW = st'.curW ∧
      st''.cnt ≤ st'.cnt + (j • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.un p .neg) 1 +
        N • (Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1)) +
      (N • (Finsupp.single (OpKind.un p .conj) 1 + Finsupp.single (OpKind.bin p .mul) 1 +
        Finsupp.single (OpKind.bin p .add) 1) + Finsupp.single (OpKind.lit p) 1) +
      Finsupp.single (OpKind.lit p) 1 + (Finsupp.single (OpKind.cmp p) 1 +
      Finsupp.single (OpKind.un p .sqrt) 1 +
      N • Finsupp.single (OpKind.bin p .div) 1)) ∧
      st''.peak ≤ Function.update st'.peak p (max (st'.peak p) (st'.cur p + 1)) ∧
      st''.peakW ≤ max st'.peakW (st'.curW + I.width p) := by
  obtain ⟨st1, st2, st3, h1, h2, h3, hcol3, ht13, ht03, hfr3, hsh3, hpos3, hcur3, hcurW3, hcnt3,
    hpeak3, hpeakW3⟩ := exec_gramSchmidt_reduce I hI hc p Y t M j hj hYt st' hQ
      (fun a => hM a ⟨j, hj⟩ le_rfl) ht0 ht1
  obtain ⟨st4, h4, hcol4, hfr4, hsh4, hpos4, hcur4, hcurW4, hcnt4, hpeak4, hpeakW4⟩ :=
    exec_gramSchmidt_normalize I hI hc p Y t (IExp.const N * IExp.var j) st3
      ((gramSchmidtQ M).col ⟨j, hj⟩) (gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩)
      (gramSchmidtR_apply_self_nonneg M _) (fun h => (gramSchmidtQ_col_eq_zero_iff M _).mpr h)
      (fun h => by rw [dotProduct_gramSchmidtQ_col, if_pos rfl, if_neg h]) hYt hcol3 ht13 ht03
  rw [exec_run_bind I (b := orthAgainst p (.const N) Y (.var j) Y (IExp.const N * IExp.var j)
      ⟨t, 0⟩) (fun _ => rfl), h1, Option.bind_some,
    exec_run_bind I (b := dot p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) Y
      (IExp.const N * IExp.var j) (.const N)) (fun _ => rfl), h2, Option.bind_some,
    exec_run_bind I (b := ins (.lit p ⟨t, 0⟩ 0)) (fun _ => rfl), h3, Option.bind_some]
  have hYt' : ∀ a < N, Y ≠ t := fun a ha h => by have := hYt h; omega
  have hfr : ∀ q b i, (b = Y → i < N * j ∨ N * j + N ≤ i) → b ≠ t →
      st4.store.read q b i = st'.store.read q b i := fun q b i hb hbt => by
    rw [hfr4 q b i hb hbt, hfr3 q b i hb hbt]
  refine ⟨st4, h4, fun a c hc' => ?_, fun a c hc' => ?_, fun q b i hb hbt =>
    hfr q b i (fun h => Or.inr ?_) hbt, hsh4.trans hsh3, hpos4.trans hpos3, hcur4.trans hcur3,
    hcurW4.trans hcurW3, hcnt4.trans (le_of_eq (by rw [hcnt3, add_assoc])), hpeak4 ▸ hpeak3,
    hpeakW4 ▸ hpeakW3⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | heq
    · rw [hfr p Y _ (fun _ => Or.inl (col_lt hlt a.2)) (hYt' a a.2), hQ a c hlt]
    · obtain rfl : c = ⟨j, hj⟩ := Fin.ext heq
      exact hcol4 a
  · rw [hfr p Y _ (fun _ => Or.inr (col_ge hc')) (hYt' a a.2), hM a c (by omega)]
  · have := Nat.mul_le_mul_left N (show j + 1 ≤ k from hj)
    rw [Nat.mul_succ] at this
    have := hb h
    omega

/-- The final store of `gramSchmidtProg`, once its scratch buffer is popped. -/
private theorem pop_eq_of_gramSchmidt {N k : ℕ} {M : Matrix (Fin N) (Fin k) 𝕜} {p : P} {Y : ℕ}
    {s s' s₁ : Store P 𝕜} {arr : Array (Option 𝕜)} (hM : Holds s p Y 0 M)
    (h₁ : s.writeBlock p Y 0 (flatten (gramSchmidtQ M)) = some s₁)
    (hQ : ∀ (a : Fin N) (c : Fin k), (c : ℕ) < k →
      s'.read p Y (N * c + a) = some (gramSchmidtQ M a c))
    (hfr : ∀ q b i, (b = Y → N * k ≤ i) → b ≠ s.size → s'.read q b i = s.read q b i)
    (hsh : s'.shape = Store.shape (s.push (p, arr))) : s'.pop = s₁ := by
  have hsz : s'.size = s.size + 1 := by
    rw [Store.size_eq_of_shape_eq hsh]; simp
  have hsz1 : s₁.size = s.size :=
    Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some h₁)
  refine Store.ext_of_shape_eq ?_ fun q b i => ?_
  · change (s'.pop.map _) = _
    rw [Store.shape_of_writeBlock_eq_some h₁, Array.map_pop]
    change s'.shape.pop = _
    rw [hsh]
    simp [Store.shape]
  by_cases hb : b < s.size
  · rw [Store.read_pop_of_lt (by omega)]
    by_cases hY : b = Y ∧ i < N * k
    · obtain ⟨rfl, hi⟩ := hY
      have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
      have hck : i / N < k := Nat.div_lt_of_lt_mul hi
      have hi' : i = N * (i / N) + i % N := (Nat.div_add_mod i N).symm
      by_cases hq : q = p
      · rw [hq]
        have hblk : s₁.read p b (0 + i) = (flatten (gramSchmidtQ M))[i]? :=
          Store.read_of_writeBlock_eq_some_of_lt h₁ (by rw [size_flatten]; exact hi)
        rw [zero_add] at hblk
        set a : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩
        set c : Fin k := ⟨i / N, hck⟩
        calc s'.read p b i = s'.read p b (N * c + a) := by
              congr 1
            _ = some (gramSchmidtQ M a c) := hQ a c hck
            _ = (flatten (gramSchmidtQ M))[(a : ℕ) + N * c]? := (getElem?_flatten _ a c).symm
            _ = (flatten (gramSchmidtQ M))[i]? := by
              congr 1
              simp only [a, c]
              omega
            _ = s₁.read p b i := hblk.symm
      · obtain ⟨len, hlen, -⟩ := Store.exists_getElem?_shape_of_read_eq_some
          (hM ⟨i % N, Nat.mod_lt _ hN⟩ ⟨i / N, hck⟩)
        rw [Store.read_eq_none_of_getElem?_shape_of_ne (n := len) (by
            rw [hsh]; simp only [Store.shape, Array.map_push, Array.getElem?_push]
            rw [if_neg (by rw [Array.size_map]; omega)]; exact hlen) hq,
          Store.read_eq_none_of_getElem?_shape_of_ne (n := len)
            (by rw [Store.shape_of_writeBlock_eq_some h₁]; exact hlen) hq]
    · rw [hfr q b i (fun h => by_contra fun h' => hY ⟨h, by omega⟩) (by omega),
        Store.read_of_writeBlock_eq_some_of_ne h₁ (by
          by_cases h : b = Y
          · exact Or.inr (Or.inr (by rw [size_flatten]; exact by_contra fun h' => hY ⟨h, by omega⟩))
          · exact Or.inl h)]
  · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le (by omega)]

omit [RCLike 𝕜] [DecidableEq P] in
private theorem gramSchmidtProg_run (p : P) (N k Y : ℕ) :
    (gramSchmidtProg (ι := ι) (VB := ℕ) (VI := ℕ) p (.const N) (.const k) Y).run =
      .seq (.alloc p 2 fun t =>
      .seq (.loop (.const k) fun j =>
        (orthAgainst p (.const N) Y (.var j) Y (IExp.const N * IExp.var j) ⟨t, 0⟩ >>=
        fun _ => dot p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) Y (IExp.const N * IExp.var j)
          (.const N) >>= fun _ => ins (.lit p ⟨t, 0⟩ 0) >>= fun _ =>
        ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) (ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩) >>= fun _ =>
          rscl p ⟨t, 1⟩ Y (IExp.const N * IExp.var j) (.const N))).run) .skip) .skip := rfl

/-- **Gram–Schmidt as a program computes `gramSchmidtQ`** from any state, under exact arithmetic:
if the buffer $Y$ holds the $N \times k$ matrix $\mathbf{M}$ from offset $0$, the run writes
`gramSchmidtQ M` over it and nothing else, keeps the tape and the current memory, raises the peak
by at most three cells and $3$ cell widths, and counts at most `gramSchmidtCount p N k`.
No rank hypothesis: a column that depends on the earlier ones becomes zero.
[GolubVanLoan2013, §5.2.8]. -/
theorem exec_gramSchmidtProg (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι)) (Y : ℕ)
    {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜) (hM : Holds st.store p Y 0 M) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p Y 0 (flatten (gramSchmidtQ M)) = some s₁) :
    ∃ st', exec I (gramSchmidtProg p (.const N) (.const k) Y).run st = some st' ∧
      st'.store = s₁ ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + gramSchmidtCount p N k ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 3)) ∧
      st'.peakW ≤ max st.peakW (st.curW + 3 * I.width p) := by
  have hmap : ∀ {α β : Type} {o : Option α} {f : α → β} {Q : α → Prop} {R : β → Prop},
      (∃ a, o = some a ∧ Q a) → (∀ a, Q a → R (f a)) → ∃ b, o.map f = some b ∧ R b := by
    rintro α β o f Q R ⟨a, rfl, ha⟩ hQR
    exact ⟨f a, rfl, hQR a ha⟩
  set t := st.store.size with ht
  have hYt : 0 < k → Y = t → N = 0 := fun hk h => by
    by_contra hN
    have := Store.lt_size_of_read_eq_some (hM ⟨0, Nat.pos_of_ne_zero hN⟩ ⟨0, hk⟩)
    omega
  have hS0 : ∀ i < 2, ∃ s, Store.write (st.store.push (p, Array.replicate 2 none)) p t i 0 =
      some s := fun i hi => ⟨_, Store.write_push_size (by simpa using hi)⟩
  rw [gramSchmidtProg_run, exec_seq_skip, exec_alloc, exec_seq_skip]
  refine hmap (exists_exec_loop_eq_some_of_forall I (fun j st' =>
      (∀ (a : Fin N) (c : Fin k), (c : ℕ) < j →
        st'.store.read p Y (N * c + a) = some (gramSchmidtQ M a c)) ∧
      (∀ (a : Fin N) (c : Fin k), j ≤ (c : ℕ) → st'.store.read p Y (N * c + a) = some (M a c)) ∧
      (∀ q b i, (b = Y → N * k ≤ i) → b ≠ t → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = Store.shape (st.store.push (p, Array.replicate 2 none)) ∧
      st'.pos = st.pos ∧ st'.cur = Function.update st.cur p (st.cur p + 2) ∧
      st'.curW = st.curW + 2 * I.width p ∧ st'.cnt ≤ st.cnt + gramSchmidtCount p N j ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 3)) ∧
      st'.peakW ≤ max st.peakW (st.curW + 3 * I.width p)) ?_ ?_) ?_
  · refine ⟨fun a c hc => absurd hc (Nat.not_lt_zero _), fun a c _ => ?_,
      fun q b i _ hbt => Store.read_push_of_ne hbt, rfl, rfl, rfl, rfl, le_self_add, ?_, ?_⟩
    · have hYlt := Store.lt_size_of_read_eq_some (hM a c)
      change Store.read (st.store.push _) p Y _ = _
      rw [Store.read_push_of_lt hYlt, show N * c + a = 0 + a + N * c by ring]
      exact hM a c
    · change Function.update st.peak p (max (st.peak p) (st.cur p + 2)) ≤ _
      intro q
      by_cases hq : q = p
      · subst hq
        simp only [Function.update_self]
        omega
      · simp [Function.update_of_ne hq]
    · change max st.peakW (st.curW + 2 * I.width p) ≤ _
      exact max_le_max le_rfl (by nlinarith)
  · intro j hj st' ⟨hQ, hMj, hfr, hsh, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
    obtain ⟨s₀, hs₀⟩ := hS0 0 (by norm_num)
    obtain ⟨s₁', hs₁'⟩ := hS0 1 (by norm_num)
    obtain ⟨st'', h, hQ'', hM'', hfr'', hsh'', hpos'', hcur'', hcurW'', hcnt'', hpeak'',
      hpeakW''⟩ := exec_gramSchmidt_col I hI hc p Y t M j hj
        (hYt (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)) st'
        hQ hMj
        (Store.exists_write_eq_some_of_shape_eq hsh hs₀ 0)
        (Store.exists_write_eq_some_of_shape_eq hsh hs₁' 0)
    have hc1 : st'.cur p + 1 = st.cur p + 3 := by rw [hcur]; simp
    refine ⟨st'', h, hQ'', hM'', fun q b i hb hbt => (hfr'' q b i hb hbt).trans (hfr q b i hb hbt),
      hsh''.trans hsh, hpos''.trans hpos, hcur''.trans hcur, hcurW''.trans hcurW, ?_,
      ?_, ?_⟩
    · rw [gramSchmidtCount_succ, ← add_assoc]
      exact hcnt''.trans (add_le_add hcnt le_rfl)
    · rw [hc1] at hpeak''
      exact hpeak''.trans (Function.update_max_le_update_max hpeak)
    · refine hpeakW''.trans (max_le hpeakW ?_)
      rw [hcurW]
      exact le_max_of_le_right (by ring_nf; exact le_rfl)
  · intro stL ⟨hQ, _, hfr, hsh, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
    exact ⟨pop_eq_of_gramSchmidt hM h₁ hQ hfr hsh, hpos, by rw [hcur]; simp, by rw [hcurW]; simp,
      hcnt, hpeak, hpeakW⟩

/-- The realisation of `gramSchmidtProg` from its input, under the exact interpretation of any
oracle and tape (the proof of `NLAlib.matrixFree_gramSchmidtProg`). -/
private theorem runsWithin_gramSchmidtProg (p : P) {N k : ℕ} (Y : Matrix (Fin N) (Fin k) 𝕜)
    (A : ι → Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (P := P) A ξ)
      ((gramSchmidtProg p (.const N) (.const k) 0).run)
      (inputState p [(flatten Y).map some]) (gramSchmidtCount p N k)
      (fun q => if q = p then N * k + 3 else 0)
      (fun st => Holds st.store p 0 0 (gramSchmidtQ Y)) := by
  set st0 : St P 𝕜 (OpCount P ι) := inputState p [(flatten Y).map some] with hst0
  have hread : ∀ i < N * k, st0.store.read p 0 i = (flatten Y)[i]? := fun i hi => by
    simp [hst0, inputState, Store.read, hi, size_flatten]
  have hY : Holds st0.store p 0 0 Y := fun i j => by
    rw [zero_add, hread _ (Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2), getElem?_flatten]
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some (s := st0.store) (p := p) (b := 0) (off := 0)
    (xs := flatten (gramSchmidtQ Y)) fun i hi => by
      rw [size_flatten] at hi
      rw [zero_add, hread i hi, Array.getElem?_eq_getElem (by rw [size_flatten]; exact hi)]
      exact ⟨_, rfl⟩
  obtain ⟨st', h, hst, -, -, -, hcnt, hpeak, -⟩ :=
    exec_gramSchmidtProg (exactInterp (P := P) A ξ) rfl (fun _ => rfl) p st0 0 Y hY s₁ hs₁
  refine ⟨st', h, hcnt, fun q => ?_, ?_⟩
  · have hq := hpeak q
    change st'.peak q + 0 ≤ _
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, hst0, inputState, if_true, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Array.size_map, size_flatten, add_zero] at hq ⊢
      omega
    · simp only [Function.update_of_ne hqp, hst0, inputState, if_neg hqp] at hq ⊢
      omega
  · intro i j
    rw [hst, zero_add, show (i : ℕ) + N * j = 0 + ((i : ℕ) + N * j) from (zero_add _).symm,
      Store.read_of_writeBlock_eq_some_of_lt hs₁
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2), getElem?_flatten]

/-- The realisation of `NLAlib.gramSchmidtProg` for the program family, in the matrix-free
model on families: for every $N$ and $k$ and every $N \times k$ matrix $\mathbf{Y}$, held
column-major in the one declared buffer, under exact arithmetic (for every oracle and tape, which
the program does not use), the program runs within the counts `gramSchmidtCount p N k` and
$Nk + 3$ cells, and leaves `gramSchmidtQ Y` in the buffer. The proof of
`NLAlib.matrixFreeGramSchmidt`. -/
theorem matrixFree_gramSchmidtProg (p : P) :
    ProgFamily.MatrixFree (𝕜 := 𝕜) (ι := ι) (r := 1) (b := 1) p
      (fun _ _ N n h => (gramSchmidtProg p N (n 0) (h 0)).run)
      (fun _ _ => True) (fun N n => Matrix (Fin N) (Fin (n 0)) 𝕜)
      (fun _ _ Y => ![(flatten Y).map some]) (fun N n => gramSchmidtCount p N (n 0))
      (fun N n q => if q = p then N * n 0 + 3 else 0)
      (fun _ _ Y _ _ st => Holds st.store p 0 0 (gramSchmidtQ Y)) :=
  fun _ _ _ Y A ξ => runsWithin_gramSchmidtProg p Y (fun _ => A) ξ

end Specs

/-- The registered tree of Gram–Schmidt instantiates, at every size, to the statement of the
program family. -/
theorem gramSchmidtProg.toStmt_compiled {P ι : Type} (p : P) (N : ℕ) (n : Fin 1 → ℕ) :
    (gramSchmidtProg.compiled (ι := ι) p).toStmt N n =
      ProgFamily.inst (r := 1) (b := 1) (fun _ _ N n h => (gramSchmidtProg p N (n 0) (h 0)).run)
        N n :=
  rfl

/-- **Gram–Schmidt as a program**, in the matrix-free model: for every type of tags with
decidable equality, every type of oracle names, every tag $p$ and every `RCLike` field $\Bbbk$,
for every $N$ and $k$ and every $N \times k$ matrix $\mathbf{Y}$ over $\Bbbk$, held column-major
in the one declared buffer, under exact arithmetic (for every oracle and tape, which the program
does not use), the registered tree `gramSchmidtProg.compiled p` runs within the counts
`gramSchmidtCount p N k` and $Nk + 3$ cells, and leaves
$\mathsf{gramSchmidtQ}(\mathbf{Y})$ in the buffer.
[GolubVanLoan2013, §5.2.8]; here rank-revealing, with no rank hypothesis.
Result: gram-schmidt-program -/
theorem matrixFreeGramSchmidt : MatrixFreeGramSchmidt := fun _ _ _ p _ _ =>
  (matrixFree_gramSchmidtProg p).prog _ (gramSchmidtProg.toStmt_compiled p)

/-- **The Gram–Schmidt target is not vacuous** (`docs/design/Computation-Hardening.md`, §2.2):
for every $N_0$ there are tags, oracle names and a field (`Unit`, `Unit`, $\mathbb{R}$) and sizes
$N = N_0 + 1$, $n = (1)$ (no size condition), the declared input type of $N \times 1$ matrices
inhabited. The witness of `NLAlib.MatrixFreeGramSchmidt` (`scripts/Targets.lean`, item 7).
No printed source. -/
theorem matrixFreeGramSchmidt_nonVacuous : ∀ N₀ : ℕ, ∃ (P ι : Type) (_ : DecidableEq P) (p : P)
    (𝕜 : Type) (_ : RCLike 𝕜),
    MatrixFree.NonVacuous (𝕜 := 𝕜) p (gramSchmidtProg.compiled (ι := ι) p) (fun _ _ => True)
      (fun N n => Matrix (Fin N) (Fin (n 0)) 𝕜)
      (fun _ _ Y => ![(flatten Y).map some]) (fun N n => gramSchmidtCount p N (n 0))
      (fun N n q => if q = p then N * n 0 + 3 else 0)
      (fun _ _ Y _ _ st => Holds st.store p 0 0 (gramSchmidtQ Y)) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), ℝ, inferInstance, N₀ + 1, fun _ => 1, Nat.le_succ N₀,
    trivial, ⟨0⟩⟩

end NLAlib
