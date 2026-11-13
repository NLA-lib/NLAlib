/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ScalarFrames
public import NLAlib.Computation.BLAS.Frames
public import NLAlib.Krylov.LinearSystems.CGProgramDirection
public import NLAlib.Krylov.LinearSystems.CGRecurrence

/-!
# Realizing the approved concrete CG program

Store-layout invariants and exact execution composition for the registered canonical program.
The context below describes actual initialized cells and buffer shapes only; it assumes no
local arithmetic defects, successful trajectory or desired output theorem.

## Main results

The store context preserves the matrix, input and scalar constants through
framed writes. Whole-program exact realization is built from actual kernel executions.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P K : Type} [DecidableEq P]

/-- Layout after the three workspace allocations; oracle access reserves an empty matrix slot. -/
def workspaceShape (tag : P) (N : ℕ) (storedMatrix : Bool := true) : Array (P × ℕ) :=
  #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1),
    (tag, if storedMatrix then N * N else 0), (tag, N), (tag, 9)]

/-- Initialized cells in the canonical CG workspace, expressed through the interpretation
decoder. The default stored-matrix specialization keeps the canonical dense layout and all its
matrix reads; oracle access reserves a zero-capacity slot instead. This is a store invariant,
with no arithmetic-error or trajectory assumptions. -/
structure StoreContext (tag : P) (dec : P → K → ℝ) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag : ℝ) (store : Store P K) (storedMatrix : Bool := true) : Prop where
  /-- Exact declared and scoped buffer shape. -/
  shape : store.shape = workspaceShape tag N storedMatrix
  /-- Loaded matrix entries when this implementation stores its matrix. -/
  matrix : if storedMatrix then HoldsDecoded store dec tag 5 0 A else True
  /-- Preserved right-hand side cells. -/
  input : ∀ i : Fin N, ∃ w, store.read tag 0 i = some w ∧ dec tag w = b i
  /-- Actual decoded iterate cells. -/
  iterate : ∀ i : Fin N, ∃ w, store.read tag 1 i = some w ∧ dec tag w = v.x i
  /-- Actual decoded residual cells. -/
  residual : ∀ i : Fin N, ∃ w, store.read tag 2 i = some w ∧ dec tag w = v.r i
  /-- Actual decoded search-direction cells. -/
  direction : ∀ i : Fin N, ∃ w, store.read tag 3 i = some w ∧ dec tag w = v.p i
  /-- Cached residual pairing, kept independently during the update. -/
  squaredResidual : ∃ w, store.read tag 7 0 = some w ∧ dec tag w = ν
  /-- Actual stop-status cell. -/
  statusValue : ∃ w, store.read tag 4 0 = some w ∧ dec tag w = status
  /-- Persistent decoded zero comparison value. -/
  zero : ∃ w, store.read tag 7 6 = some w ∧ dec tag w = 0
  /-- Persistent positive stop-status value. -/
  positive : ∃ w, store.read tag 7 7 = some w ∧ dec tag w = flag
  /-- Persistent negative breakdown-status value. -/
  negative : ∃ w, store.read tag 7 8 = some w ∧ dec tag w = -flag

variable {storedMatrix : Bool}

private def baseCell (buf idx : ℕ) : Prop :=
  buf = 0 ∨ buf = 5 ∨ (buf = 7 ∧ (idx = 6 ∨ idx = 7 ∨ idx = 8))

private theorem read_decoded_of_frame {tag : P} {dec : P → K → ℝ}
    {old next : Store P K} {buf idx : ℕ} {value : ℝ}
    (hframe : next.read tag buf idx = old.read tag buf idx)
    (h : ∃ w, old.read tag buf idx = some w ∧ dec tag w = value) :
    ∃ w, next.read tag buf idx = some w ∧ dec tag w = value := by
  obtain ⟨w, hw, hdec⟩ := h
  exact ⟨w, hframe.trans hw, hdec⟩

private theorem StoreContext.of_state_frame
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v v' : CGState ℝ (Fin N)} {ν ν' status status' flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape)
    (hframe : ∀ buf idx, baseCell buf idx → next.read tag buf idx = old.read tag buf idx)
    (hx : ∀ i : Fin N, ∃ w, next.read tag 1 i = some w ∧ dec tag w = v'.x i)
    (hr : ∀ i : Fin N, ∃ w, next.read tag 2 i = some w ∧ dec tag w = v'.r i)
    (hp : ∀ i : Fin N, ∃ w, next.read tag 3 i = some w ∧ dec tag w = v'.p i)
    (hν : ∃ w, next.read tag 7 0 = some w ∧ dec tag w = ν')
    (hstatus : ∃ w, next.read tag 4 0 = some w ∧ dec tag w = status') :
    StoreContext tag dec N A b v' ν' status' flag next storedMatrix := by
  refine ⟨hshape.trans h.shape, ?_, ?_, hx, hr, hp, hν, hstatus, ?_, ?_, ?_⟩
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i j
      exact read_decoded_of_frame (hframe 5 _ (Or.inr (Or.inl rfl))) (h.matrix i j)
  · intro i
    exact read_decoded_of_frame (hframe 0 i (Or.inl rfl)) (h.input i)
  · exact read_decoded_of_frame
      (hframe 7 6 (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))) h.zero
  · exact read_decoded_of_frame
      (hframe 7 7 (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩))) h.positive
  · exact read_decoded_of_frame
      (hframe 7 8 (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩))) h.negative

/-- Writes outside persistent CG cells preserve their actual decoded store context. -/
theorem StoreContext.preserve_frame
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν status flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape)
    (hframe : ∀ buf idx, (buf ≤ 5 ∨ (buf = 7 ∧
      (idx = 0 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8))) →
      next.read tag buf idx = old.read tag buf idx) :
    StoreContext tag dec N A b v ν status flag next storedMatrix := by
  apply h.of_state_frame hshape
  · intro buf idx hb
    rcases hb with rfl | rfl | ⟨rfl, hi⟩
    · exact hframe 0 idx (Or.inl (by norm_num))
    · exact hframe 5 idx (Or.inl le_rfl)
    · exact hframe 7 idx (Or.inr ⟨rfl, Or.inr hi⟩)
  · intro i
    exact read_decoded_of_frame (hframe 1 i (Or.inl (by norm_num))) (h.iterate i)
  · intro i
    exact read_decoded_of_frame (hframe 2 i (Or.inl (by norm_num))) (h.residual i)
  · intro i
    exact read_decoded_of_frame (hframe 3 i (Or.inl (by norm_num))) (h.direction i)
  · exact read_decoded_of_frame (hframe 7 0 (Or.inr ⟨rfl, Or.inl rfl⟩)) h.squaredResidual
  · exact read_decoded_of_frame (hframe 4 0 (Or.inl (by norm_num))) h.statusValue

private theorem baseCell_ne_vector {buf idx slot : ℕ} (hs : 1 ≤ slot) (hs' : slot ≤ 4)
    (hb : baseCell buf idx) : buf ≠ slot := by
  rcases hb with rfl | rfl | ⟨rfl, _⟩ <;> omega

/-- An actual scalar scratch write preserves all decoded persistent CG cells. -/
theorem StoreContext.preserve_scalar_write
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν status flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    {idx : ℕ} (hi : 1 ≤ idx) (hi' : idx ≤ 5) {word : K}
    (hw : old.write tag 7 idx word = some next) :
    StoreContext tag dec N A b v ν status flag next storedMatrix := by
  apply h.preserve_frame (Store.shape_of_write_eq_some hw)
  intro buf j hcell
  apply Store.read_of_write_eq_some_of_ne hw
  rcases hcell with hb | ⟨rfl, hj⟩
  · exact Or.inl (by omega)
  · exact Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> omega)

/-- A framed actual iterate write replaces only the decoded iterate. -/
theorem StoreContext.replace_iterate
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν status flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape) (xnew : Fin N → ℝ)
    (hframe : ∀ buf idx, buf ≠ 1 → next.read tag buf idx = old.read tag buf idx)
    (hnew : ∀ i : Fin N, ∃ w, next.read tag 1 i = some w ∧ dec tag w = xnew i) :
    StoreContext tag dec N A b ⟨xnew, v.r, v.p⟩ ν status flag next storedMatrix := by
  apply h.of_state_frame hshape
  · intro buf idx hb
    exact hframe buf idx (baseCell_ne_vector (by norm_num) (by norm_num) hb)
  · exact hnew
  · intro i
    exact read_decoded_of_frame (hframe 2 i (by norm_num)) (h.residual i)
  · intro i
    exact read_decoded_of_frame (hframe 3 i (by norm_num)) (h.direction i)
  · exact read_decoded_of_frame (hframe 7 0 (by norm_num)) h.squaredResidual
  · exact read_decoded_of_frame (hframe 4 0 (by norm_num)) h.statusValue

/-- A framed actual residual write replaces only the decoded residual. -/
theorem StoreContext.replace_residual
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν status flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape) (xnew : Fin N → ℝ)
    (hframe : ∀ buf idx, buf ≠ 2 → next.read tag buf idx = old.read tag buf idx)
    (hnew : ∀ i : Fin N, ∃ w, next.read tag 2 i = some w ∧ dec tag w = xnew i) :
    StoreContext tag dec N A b ⟨v.x, xnew, v.p⟩ ν status flag next storedMatrix := by
  apply h.of_state_frame hshape
  · intro buf idx hb
    exact hframe buf idx (baseCell_ne_vector (by norm_num) (by norm_num) hb)
  · intro i
    exact read_decoded_of_frame (hframe 1 i (by norm_num)) (h.iterate i)
  · exact hnew
  · intro i
    exact read_decoded_of_frame (hframe 3 i (by norm_num)) (h.direction i)
  · exact read_decoded_of_frame (hframe 7 0 (by norm_num)) h.squaredResidual
  · exact read_decoded_of_frame (hframe 4 0 (by norm_num)) h.statusValue

/-- Framed actual register writes replace cache and status while retaining vectors. -/
theorem StoreContext.replace_registers
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν ν' status status' flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape)
    (hframe : ∀ buf idx, (buf ≠ 7 ∨ idx ≠ 0) → (buf ≠ 4 ∨ idx ≠ 0) →
      next.read tag buf idx = old.read tag buf idx)
    (hν : ∃ w, next.read tag 7 0 = some w ∧ dec tag w = ν')
    (hstatus : ∃ w, next.read tag 4 0 = some w ∧ dec tag w = status') :
    StoreContext tag dec N A b v ν' status' flag next storedMatrix := by
  apply h.of_state_frame hshape
  · intro buf idx hb
    rcases hb with rfl | rfl | ⟨rfl, hi⟩
    · exact hframe 0 idx (Or.inl (by norm_num)) (Or.inl (by norm_num))
    · exact hframe 5 idx (Or.inl (by norm_num)) (Or.inl (by norm_num))
    · exact hframe 7 idx (Or.inr (by rcases hi with rfl | rfl | rfl <;> norm_num))
        (Or.inl (by norm_num))
  · intro i
    exact read_decoded_of_frame
      (hframe 1 i (Or.inl (by norm_num)) (Or.inl (by norm_num))) (h.iterate i)
  · intro i
    exact read_decoded_of_frame
      (hframe 2 i (Or.inl (by norm_num)) (Or.inl (by norm_num))) (h.residual i)
  · intro i
    exact read_decoded_of_frame
      (hframe 3 i (Or.inl (by norm_num)) (Or.inl (by norm_num))) (h.direction i)
  · exact hν
  · exact hstatus

/-- The actual first two kernels of an active exact CG step produce the stored matrix-vector
product and curvature pairing. Every persistent CG cell and cached residual is preserved. -/
theorem exec_exact_curvature {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store) :
    ∃ out, exec I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν status 1 out.store ∧
      (∀ i : Fin N, out.store.read tag 6 i = some ((A *ᵥ v.p) i)) ∧
      out.store.read tag 7 2 = some (v.p ⬝ᵥ (A *ᵥ v.p)) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • Finsupp.single (.lit tag) 1 + (N * N) •
        (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) +
        (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
          Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  have hA : Holds st.store tag 5 0 A := by
    intro i j
    obtain ⟨w, hw, rfl⟩ := h.matrix i j
    exact hw
  have hp : ∀ i : Fin N, st.store.read tag 3 (0 + i) = some (v.p i) := by
    intro i
    obtain ⟨w, hw, rfl⟩ := h.direction i
    simpa only [zero_add] using hw
  obtain ⟨s, hs, hsh, hv, hf, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    Computation.exec_gemv_frame I hI hc tag st N 5 3 6 0 A v.p hA hp
      (by norm_num) (by norm_num) (fun i hi => ⟨N, by simp [h.shape, workspaceShape], hi⟩)
  have hctx : StoreContext tag (fun _ x => x) N A b v ν status 1 s.store := by
    apply h.preserve_frame hsh
    intro buf idx hcell
    apply hf tag buf idx (Or.inl ?_)
    rcases hcell with hb | ⟨rfl, _⟩ <;> omega
  have hp' : ∀ i : Fin N, s.store.read tag 3 (0 + i) = some (v.p i) := by
    intro i
    obtain ⟨w, hw, rfl⟩ := hctx.direction i
    simpa only [zero_add] using hw
  obtain ⟨scratch, hwrite⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (show s.store.shape[7]? = some (tag, 9) by simp [hctx.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  obtain ⟨out, hout, hshape, hμ, hframe, hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    Computation.exec_dot_frame I hI hc tag s N ⟨7, 2⟩ 3 6 0 0 v.p (A *ᵥ v.p)
      hp' (by simpa only [IExp.eval_zero, zero_add] using hv) (by norm_num) (by norm_num)
      ⟨0, scratch, hwrite⟩
  refine ⟨out, ?_, ?_, ?_, hμ, hpos'.trans hpos, hcur'.trans hcur,
    hcurW'.trans hcurW, by rw [hcnt', hcnt], ?_, ?_⟩
  · rw [exec_run_bind I (b := gemv tag (.const N) (.const N) 5 0 3 0 6 0)
      (fun _ => rfl), hs, Option.bind_some, hout]
  · apply hctx.preserve_frame hshape
    intro buf idx hcell
    apply hframe tag buf idx
    change buf ≠ 7 ∨ idx ≠ 2
    rcases hcell with hb | ⟨rfl, hj⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num)
  · intro i
    exact (hframe tag 6 i (Or.inl (by norm_num))).trans (hv i)
  · rw [hpeak', hpeak, hcur]
    simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
  · rw [hpeakW', hpeakW, hcurW, max_assoc, max_self]

/-- Given the actual nonzero stored curvature, the canonical division and iterate axpy
execute and update the physical iterate by the exact line-search coefficient. -/
theorem exec_exact_iterate_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status μ : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hμ : st.store.read tag 7 2 = some μ) (hne : μ ≠ 0) :
    ∃ out, exec I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b
        ⟨fun i => v.x i + (ν / μ) * v.p i, v.r, v.p⟩ ν status 1 out.store storedMatrix ∧
      out.store.read tag 7 3 = some (ν / μ) ∧
      (∀ i : Fin N, out.store.read tag 6 i = st.store.read tag 6 i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + Finsupp.single (.bin tag .div) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨word, hν, hword⟩ := h.squaredResidual
  change word = ν at hword
  subst word
  obtain ⟨store, hw, hrun, hshape, hγ, hframe⟩ := exec_scalar_bin I tag st .div
    ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩ ν μ (ν / μ) hν hμ
    (by rw [hI]; exact if_neg hne)
    ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  let mid : St P ℝ (OpCount P ι) :=
    { st with store := store, cnt := st.cnt + I.charge (.bin tag .div) }
  have hctx : StoreContext tag (fun _ x => x) N A b v ν status 1 mid.store storedMatrix :=
    h.preserve_scalar_write (by norm_num) (by norm_num) hw
  have hp : ∀ i : Fin N, mid.store.read tag 3 (0 + i) = some (v.p i) := by
    intro i
    obtain ⟨word, hw, rfl⟩ := hctx.direction i
    simpa only [zero_add] using hw
  have hx : ∀ i : Fin N, mid.store.read tag 1 (0 + i) = some (v.x i) := by
    intro i
    obtain ⟨word, hw, rfl⟩ := hctx.iterate i
    simpa only [zero_add] using hw
  obtain ⟨out, hout, hsh, hv, hf, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    Computation.exec_axpy_frame I hI hc tag mid N ⟨7, 3⟩ 3 1 0 0 (ν / μ)
      v.p v.x hγ hp hx (by norm_num) (by norm_num)
  refine ⟨out, ?_, ?_, ?_, ?_, hpos, hcur, hcurW, ?_, hpeak, hpeakW⟩
  · rw [exec_run_bind I (b := Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩))
      (fun _ => rfl), hrun, Option.bind_some]
    exact hout
  · apply hctx.replace_iterate hsh (fun i => v.x i + (ν / μ) * v.p i)
    · intro buf idx hb
      exact hf tag buf idx (Or.inl hb)
    · intro i
      exact ⟨_, by simpa only [IExp.eval_zero, zero_add] using hv i, rfl⟩
  · exact (hf tag 7 3 (Or.inl (by norm_num))).trans hγ
  · intro i
    exact (hf tag 6 i (Or.inl (by norm_num))).trans
      (hframe tag 6 i (Or.inr (Or.inl (by norm_num))))
  · simpa only [mid, hc.charge_eq] using hcnt

/-- The canonical negation and residual axpy execute on the actual stored product vector.
The cached old residual pairing is retained until the subsequent direction quotient. -/
theorem exec_exact_residual_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status γ : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hγ : st.store.read tag 7 3 = some γ)
    (hs : ∀ i : Fin N, st.store.read tag 6 i = some (sv i)) :
    ∃ out, exec I (do
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b
        ⟨v.x, fun i => v.r i - γ * sv i, v.p⟩ ν status 1 out.store storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + Finsupp.single (.un tag .neg) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨store, hw, hrun, hshape, hneg, hframe⟩ := exec_scalar_un I tag st .neg
    ⟨7, 5⟩ ⟨7, 3⟩ γ (-γ) hγ (by rw [hI]; rfl)
    ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  let mid : St P ℝ (OpCount P ι) :=
    { st with store := store, cnt := st.cnt + I.charge (.un tag .neg) }
  have hctx : StoreContext tag (fun _ x => x) N A b v ν status 1 mid.store storedMatrix :=
    h.preserve_scalar_write (by norm_num) (by norm_num) hw
  have hs' : ∀ i : Fin N, mid.store.read tag 6 (0 + i) = some (sv i) := by
    intro i
    simpa only [zero_add] using
      (hframe tag 6 i (Or.inr (Or.inl (by norm_num)))).trans (hs i)
  have hr : ∀ i : Fin N, mid.store.read tag 2 (0 + i) = some (v.r i) := by
    intro i
    obtain ⟨word, hw, rfl⟩ := hctx.residual i
    simpa only [zero_add] using hw
  obtain ⟨out, hout, hsh, hv, hf, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    Computation.exec_axpy_frame I hI hc tag mid N ⟨7, 5⟩ 6 2 0 0 (-γ)
      sv v.r hneg hs' hr (by norm_num) (by norm_num)
  refine ⟨out, ?_, ?_, hpos, hcur, hcurW, ?_, hpeak, hpeakW⟩
  · rw [exec_run_bind I (b := Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩))
      (fun _ => rfl), hrun, Option.bind_some]
    exact hout
  · apply hctx.replace_residual hsh (fun i => v.r i - γ * sv i)
    · intro buf idx hb
      exact hf tag buf idx (Or.inl hb)
    · intro i
      exact ⟨_, by simpa only [IExp.eval_zero, zero_add, neg_mul, sub_eq_add_neg] using hv i,
        rfl⟩
  · simpa only [mid, hc.charge_eq] using hcnt

/-- The actual four-instruction/kernel primal update changes the iterate and residual using
one stored curvature. Both vector operations occur before the next residual pairing. -/
theorem exec_exact_primal_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status μ : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hμ : st.store.read tag 7 2 = some μ) (hne : μ ≠ 0)
    (hs : ∀ i : Fin N, st.store.read tag 6 i = some ((A *ᵥ v.p) i)) :
    ∃ out, exec I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b
        ⟨fun i => v.x i + (ν / μ) * v.p i,
          fun i => v.r i - (ν / μ) * (A *ᵥ v.p) i, v.p⟩ ν status 1 out.store storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + Finsupp.single (.bin tag .div) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.un tag .neg) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨mid, hrun, hctx, hγ, hs', hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_iterate_update I hI hc tag st N A b v ν status μ h hμ hne
  obtain ⟨out, hout, hctx', hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_exact_residual_update I hI hc tag mid N A b
      ⟨fun i => v.x i + (ν / μ) * v.p i, v.r, v.p⟩ ν status (ν / μ) (A *ᵥ v.p)
      hctx hγ (fun i => (hs' i).trans (hs i))
  have hcompose : ExecutionComposable I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  refine ⟨out, ?_, hctx', hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW,
    by rw [hcnt', hcnt], ?_, ?_⟩
  · change exec I ((do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)) >>= fun _ => do
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)).run st = _
    rw [hcompose, hrun, Option.bind_some, hout]
  · rw [hpeak', hpeak, hcur]
    simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
  · rw [hpeakW', hpeakW, hcurW, max_assoc, max_self]
/-- The updated residual is paired before the direction quotient, using the cached old
pairing as the denominator. No residual norm or square-root operation is inserted. -/
theorem exec_exact_direction_quotient {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix) (hne : ν ≠ 0) :
    ∃ out, exec I (do
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν status 1 out.store storedMatrix ∧
      out.store.read tag 7 1 = some (v.r ⬝ᵥ v.r) ∧
      out.store.read tag 7 4 = some ((v.r ⬝ᵥ v.r) / ν) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) + Finsupp.single (.bin tag .div) 1 ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  have hr : ∀ i : Fin N, st.store.read tag 2 (0 + i) = some (v.r i) := by
    intro i
    obtain ⟨word, hw, rfl⟩ := h.residual i
    simpa only [zero_add] using hw
  obtain ⟨scratch, hwrite⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (show st.store.shape[7]? = some (tag, 9) by simp [h.shape, workspaceShape])
    (show 1 < 9 by norm_num)
  obtain ⟨mid, hrun, hshape, hnew, hframe, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    Computation.exec_dot_frame I hI hc tag st N ⟨7, 1⟩ 2 2 0 0 v.r v.r hr hr
      (by norm_num) (by norm_num) ⟨0, scratch, hwrite⟩
  have hctx : StoreContext tag (fun _ x => x) N A b v ν status 1 mid.store storedMatrix := by
    apply h.preserve_frame hshape
    intro buf idx hcell
    apply hframe tag buf idx
    change buf ≠ 7 ∨ idx ≠ 1
    rcases hcell with hb | ⟨rfl, hj⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num)
  obtain ⟨word, hν, hword⟩ := hctx.squaredResidual
  change word = ν at hword
  subst word
  obtain ⟨store, hw, hout, hsh, hδ, hf⟩ := exec_scalar_bin I tag mid .div
    ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩ (v.r ⬝ᵥ v.r) ν ((v.r ⬝ᵥ v.r) / ν) hnew hν
    (by rw [hI]; exact if_neg hne)
    ⟨9, by simp [hctx.shape, workspaceShape], by norm_num⟩
  refine ⟨{ mid with store := store, cnt := mid.cnt + I.charge (.bin tag .div) }, ?_,
    hctx.preserve_scalar_write (by norm_num) (by norm_num) hw,
    (hf tag 7 1 (Or.inr (Or.inr (by norm_num)))).trans hnew, hδ, hpos, hcur,
    hcurW, ?_, hpeak, hpeakW⟩
  · rw [exec_run_bind I (b := dot tag ⟨7, 1⟩ 2 0 2 0 (.const N))
      (fun _ => rfl), hrun, Option.bind_some]
    exact hout
  · simp only [hc.charge_eq, hcnt]

private def extendVector {N : ℕ} (v : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N then v ⟨i, hi⟩ else 0

/-- The published inline multiplication/addition loop updates the actual direction cells,
while retaining the old cached residual pairing, the new residual and the right-hand side. -/
theorem exec_exact_direction_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status δ : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hδ : st.store.read tag 7 4 = some δ) :
    ∃ out, exec I (Builder.forRange (.const N) fun i => do
      Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
      Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b
        ⟨v.x, v.r, fun i => v.r i + δ * v.p i⟩ ν status 1 out.store storedMatrix ∧
      (∀ idx, idx ≠ 2 → out.store.read tag 7 idx = st.store.read tag 7 idx) ∧
      out = { st with store := out.store, cnt := st.cnt +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) } := by
  have hp : ∀ i < N, st.store.read tag 3 i = some (extendVector v.p i) := by
    intro i hi
    obtain ⟨word, hw, hword⟩ := h.direction ⟨i, hi⟩
    change word = v.p ⟨i, hi⟩ at hword
    simpa only [extendVector, dif_pos hi, hword] using hw
  have hr : ∀ i < N, st.store.read tag 2 i = some (extendVector v.r i) := by
    intro i hi
    obtain ⟨word, hw, hword⟩ := h.residual ⟨i, hi⟩
    change word = v.r ⟨i, hi⟩ at hword
    simpa only [extendVector, dif_pos hi, hword] using hw
  obtain ⟨scratch, hwrite⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (show st.store.shape[7]? = some (tag, 9) by simp [h.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  obtain ⟨out, hout, hsh, hstate, hf, hv⟩ :=
    exec_cg_direction_update_of_sem_eq_exactSem I tag hI st ⟨7, 4⟩ ⟨7, 2⟩ 3 2
      (.const N) δ (extendVector v.p) (extendVector v.r) hδ hp hr
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨0, scratch, hwrite⟩
  have hframe : ∀ buf idx, buf ≠ 3 → (buf ≠ 7 ∨ idx ≠ 2) →
      out.store.read tag buf idx = st.store.read tag buf idx := by
    intro buf idx hp ht
    exact hf tag buf idx (Or.inr (Or.inl hp)) (Or.inr ht)
  refine ⟨out, hout, ?_, fun idx hi => hframe 7 idx (by norm_num) (Or.inr hi), ?_⟩
  · apply h.of_state_frame hsh
    · intro buf idx hb
      rcases hb with rfl | rfl | ⟨rfl, hi⟩
      · exact hframe 0 idx (by norm_num) (Or.inl (by norm_num))
      · exact hframe 5 idx (by norm_num) (Or.inl (by norm_num))
      · exact hframe 7 idx (by norm_num) (Or.inr (by
          rcases hi with rfl | rfl | rfl <;> norm_num))
    · intro i
      exact read_decoded_of_frame (dec := fun _ x => x)
        (hframe 1 i (by norm_num) (Or.inl (by norm_num))) (h.iterate i)
    · intro i
      exact read_decoded_of_frame (dec := fun _ x => x)
        (hframe 2 i (by norm_num) (Or.inl (by norm_num))) (h.residual i)
    · intro i
      exact ⟨_, by simpa only [IExp.eval_const, extendVector, dif_pos i.isLt] using hv i i.isLt,
        rfl⟩
    · exact read_decoded_of_frame (dec := fun _ x => x)
        (hframe 7 0 (by norm_num) (Or.inr (by norm_num))) h.squaredResidual
    · exact read_decoded_of_frame (dec := fun _ x => x)
        (hframe 4 0 (by norm_num) (Or.inl (by norm_num))) h.statusValue
  · simpa only [IExp.eval_const, hc.charge_eq] using hstate

/-- The residual cache is overwritten only after the direction has consumed its old value.
This is the actual final scalar copy of an active step. -/
theorem exec_exact_cache_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν νnext status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hnext : st.store.read tag 7 1 = some νnext) :
    ∃ out, exec I (Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v νnext status 1 out.store storedMatrix ∧
      out = { st with store := out.store, cnt := st.cnt + I.charge (.copy tag) } := by
  obtain ⟨store, hw, hrun, hshape, hν, hf⟩ := exec_scalar_copy I tag st
    ⟨7, 0⟩ ⟨7, 1⟩ νnext hnext ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  refine ⟨{ st with store := store, cnt := st.cnt + I.charge (.copy tag) }, hrun, ?_, rfl⟩
  apply h.replace_registers hshape
  · intro buf idx hcell _
    exact hf tag buf idx (Or.inr hcell)
  · exact ⟨νnext, hν, rfl⟩
  · exact read_decoded_of_frame (dec := fun _ x => x)
      (hf tag 4 0 (Or.inr (Or.inl (by norm_num)))) h.statusValue

/-- An exact zero-cache guard records successful termination; otherwise it leaves the
previous status untouched. The result includes the actual branch-dependent copy charge. -/
theorem exec_exact_zero_guard {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (tag : P) (st : St P ℝ (OpCount P ι)) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix) :
    ∃ out, exec I (Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν
        (if ν = 0 then 1 else status) 1 out.store storedMatrix ∧
      out = { st with store := out.store, cnt := st.cnt + I.charge (.cmp tag) +
        (if ν = 0 then I.charge (.copy tag) else 0) } := by
  classical
  have hν : st.store.read tag 7 0 = some ν := by
    obtain ⟨word, hw, hword⟩ := h.squaredResidual
    simpa only [hword] using hw
  have hz : st.store.read tag 7 6 = some 0 := by
    obtain ⟨word, hw, hword⟩ := h.zero
    simpa only [hword] using hw
  have hp : st.store.read tag 7 7 = some 1 := by
    obtain ⟨word, hw, hword⟩ := h.positive
    simpa only [hword] using hw
  have hsem : I.sem.cmp tag .eq ν 0 = some (decide (ν = 0)) := by rw [hI]; rfl
  have hcmp : cmpStep I tag .eq ⟨7, 0⟩ ⟨7, 6⟩ st =
      some (decide (ν = 0), { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hν, hz, Option.bind_some,
      hsem, Option.map_some]
  let mid : St P ℝ (OpCount P ι) := { st with cnt := st.cnt + I.charge (.cmp tag) }
  by_cases hzero : ν = 0
  · obtain ⟨store, hw, hrun, hshape, hstatus, hf⟩ := exec_scalar_copy I tag mid
      ⟨4, 0⟩ ⟨7, 7⟩ 1 hp ⟨1, by simp [mid, h.shape, workspaceShape], by norm_num⟩
    refine ⟨{ mid with store := store, cnt := mid.cnt + I.charge (.copy tag) }, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .eq ⟨7, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hzero, decide_true, Bool.true_eq, ↓reduceIte] using hrun
    · rw [if_pos hzero]
      apply h.replace_registers hshape
      · intro buf idx _ hcell
        exact hf tag buf idx (Or.inr hcell)
      · exact read_decoded_of_frame (dec := fun _ x => x)
          (hf tag 7 0 (Or.inr (Or.inl (by norm_num)))) h.squaredResidual
      · exact ⟨1, hstatus, rfl⟩
    · simp only [mid, if_pos hzero]
  · refine ⟨mid, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .eq ⟨7, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hzero, decide_false, Bool.false_eq_true, ↓reduceIte, Builder.run_pure]
        using exec_skip I mid
    · simpa only [if_neg hzero] using h
    · simp only [mid, if_neg hzero, add_zero]

/-- The direction update consumes its coefficient before overwriting the residual cache,
then records zero termination. This is the full canonical tail, with exact branch counts. -/
theorem exec_exact_direction_tail {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν νnext status δ : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix)
    (hδ : st.store.read tag 7 4 = some δ) (hnext : st.store.read tag 7 1 = some νnext) :
    ∃ out, exec I (do
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag (fun _ x => x) N A b
        ⟨v.x, v.r, fun i => v.r i + δ * v.p i⟩ νnext
        (if νnext = 0 then 1 else status) 1 out.store storedMatrix ∧
      out = { st with store := out.store, cnt := st.cnt +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.copy tag) 1 + Finsupp.single (.cmp tag) 1 +
        (if νnext = 0 then Finsupp.single (.copy tag) 1 else 0) } := by
  obtain ⟨dir, hdir, hctx, hf, hdirstate⟩ :=
    exec_exact_direction_update I hI hc tag st N A b v ν status δ h hδ
  obtain ⟨cache, hcache, hctx', hcachestate⟩ := exec_exact_cache_update I tag dir N A b
    ⟨v.x, v.r, fun i => v.r i + δ * v.p i⟩ ν νnext status hctx
    ((hf 1 (by norm_num)).trans hnext)
  obtain ⟨out, hout, hctx'', houtstate⟩ := exec_exact_zero_guard I hI tag cache N A b
    ⟨v.x, v.r, fun i => v.r i + δ * v.p i⟩ νnext status hctx'
  refine ⟨out, ?_, hctx'', ?_⟩
  · rw [exec_run_bind I (b := Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)) (fun _ => rfl),
      hdir, Option.bind_some,
      exec_run_bind I (b := Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)) (fun _ => rfl),
      hcache, Option.bind_some, hout]
  · calc
      out = { cache with store := out.store, cnt := cache.cnt + I.charge (.cmp tag) +
        (if νnext = 0 then I.charge (.copy tag) else 0) } := houtstate
      _ = _ := by rw [hcachestate, hdirstate]; simp only [hc.charge_eq]

/-- The full search-direction phase pairs the new residual, divides by the old cache,
updates the direction, then stores the new cache and zero status, in the approved order. -/
theorem exec_exact_search_update {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix) (hne : ν ≠ 0) :
    ∃ out, exec I (do
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag (fun _ x => x) N A b
        ⟨v.x, v.r, fun i => v.r i + ((v.r ⬝ᵥ v.r) / ν) * v.p i⟩ (v.r ⬝ᵥ v.r)
        (if v.r ⬝ᵥ v.r = 0 then 1 else status) 1 out.store storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) + Finsupp.single (.bin tag .div) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.copy tag) 1 + Finsupp.single (.cmp tag) 1 +
        (if v.r ⬝ᵥ v.r = 0 then Finsupp.single (.copy tag) 1 else 0) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨mid, hrun, hctx, hnew, hδ, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_direction_quotient I hI hc tag st N A b v ν status h hne
  obtain ⟨out, hout, hctx', hstate⟩ := exec_exact_direction_tail I hI hc tag mid N A b v
    ν (v.r ⬝ᵥ v.r) status ((v.r ⬝ᵥ v.r) / ν) hctx hδ hnew
  have hcompose : ExecutionComposable I (do
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  refine ⟨out, ?_, hctx', (congrArg St.pos hstate).trans hpos,
    (congrArg St.cur hstate).trans hcur, (congrArg St.curW hstate).trans hcurW,
    ?_, (congrArg St.peak hstate).trans hpeak, (congrArg St.peakW hstate).trans hpeakW⟩
  · change exec I ((do
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)) >>= fun _ => do
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = _
    rw [hcompose, hrun, Option.bind_some, hout]
  · exact (congrArg St.cnt hstate).trans (by rw [hcnt])

/-- The entire inner body under positive curvature realizes one mathematical CG step.
The physical vector cells, cached residual and terminal status are all tied to that step. -/
theorem exec_exact_positive_body {ι : Type} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 st.store storedMatrix)
    (hμ : st.store.read tag 7 2 = some (v.p ⬝ᵥ (A *ᵥ v.p)))
    (hne : v.p ⬝ᵥ (A *ᵥ v.p) ≠ 0) (hr : v.r ⬝ᵥ v.r ≠ 0)
    (hs : ∀ i : Fin N, st.store.read tag 6 i = some ((A *ᵥ v.p) i)) :
    ∃ out, exec I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag (fun _ x => x) N A b (cgStep A v)
        ((cgStep A v).r ⬝ᵥ (cgStep A v).r)
        (if (cgStep A v).r ⬝ᵥ (cgStep A v).r = 0 then 1 else status) 1 out.store storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + Finsupp.single (.bin tag .div) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.un tag .neg) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
          Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1) +
        Finsupp.single (.bin tag .div) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.copy tag) 1 + Finsupp.single (.cmp tag) 1 +
        (if (cgStep A v).r ⬝ᵥ (cgStep A v).r = 0 then Finsupp.single (.copy tag) 1 else 0) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨mid, hrun, hctx, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_primal_update I hI hc tag st N A b v (v.r ⬝ᵥ v.r) status
      (v.p ⬝ᵥ (A *ᵥ v.p)) h hμ hne hs
  obtain ⟨out, hout, hctx', hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_exact_search_update I hI hc tag mid N A b
      ⟨fun i => v.x i + ((v.r ⬝ᵥ v.r) / (v.p ⬝ᵥ (A *ᵥ v.p))) * v.p i,
        fun i => v.r i - ((v.r ⬝ᵥ v.r) / (v.p ⬝ᵥ (A *ᵥ v.p))) * (A *ᵥ v.p) i, v.p⟩
      (v.r ⬝ᵥ v.r) status hctx hr
  have hcompose : ExecutionComposable I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl))))
  refine ⟨out, ?_, ?_, hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW, ?_, ?_, ?_⟩
  · change exec I ((do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)) >>= fun _ => _).run st = _
    rw [hcompose, hrun, Option.bind_some]
    exact hout
  · simpa only [cgStep_eq] using hctx'
  · simpa only [cgStep_eq] using hcnt'.trans (by rw [hcnt])
  · rw [hpeak', hpeak, hcur]
    simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
  · rw [hpeakW', hpeakW, hcurW, max_assoc, max_self]

/-- A rejected nonpositive curvature records breakdown without performing either division
or changing any CG vector or the cached residual. Division failure is a separate execution
outcome and is not used to represent this status. -/
theorem exec_exact_rejection {ι : Type} (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store storedMatrix) :
    ∃ out, exec I (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩)).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν (-1) 1 out.store storedMatrix ∧
      out = { st with store := out.store, cnt := st.cnt + I.charge (.copy tag) } := by
  have hn : st.store.read tag 7 8 = some (-1) := by
    obtain ⟨word, hw, hword⟩ := h.negative
    simpa only [hword] using hw
  obtain ⟨store, hw, hrun, hshape, hstatus, hf⟩ := exec_scalar_copy I tag st
    ⟨4, 0⟩ ⟨7, 8⟩ (-1) hn ⟨1, by simp [h.shape, workspaceShape], by norm_num⟩
  refine ⟨{ st with store := store, cnt := st.cnt + I.charge (.copy tag) }, hrun, ?_, rfl⟩
  apply h.replace_registers hshape
  · intro buf idx _ hcell
    exact hf tag buf idx (Or.inr hcell)
  · exact read_decoded_of_frame (dec := fun _ x => x)
      (hf tag 7 0 (Or.inr (Or.inl (by norm_num)))) h.squaredResidual
  · exact ⟨-1, hstatus, rfl⟩

/-- A framed actual direction update may overwrite its scalar multiplication scratch while
retaining the residual, iterate, old cache and stop status. -/
theorem StoreContext.replace_direction
    {tag : P} {dec : P → K → ℝ} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {ν status flag : ℝ}
    {old next : Store P K} (h : StoreContext tag dec N A b v ν status flag old storedMatrix)
    (hshape : next.shape = old.shape) (pnew : Fin N → ℝ)
    (hframe : ∀ buf idx, buf ≠ 3 → (buf ≠ 7 ∨ idx ≠ 2) →
      next.read tag buf idx = old.read tag buf idx)
    (hnew : ∀ i : Fin N, ∃ w, next.read tag 3 i = some w ∧ dec tag w = pnew i) :
    StoreContext tag dec N A b ⟨v.x, v.r, pnew⟩ ν status flag next storedMatrix := by
  apply h.of_state_frame hshape
  · intro buf idx hb
    rcases hb with rfl | rfl | ⟨rfl, hi⟩
    · exact hframe 0 idx (by norm_num) (Or.inl (by norm_num))
    · exact hframe 5 idx (by norm_num) (Or.inl (by norm_num))
    · exact hframe 7 idx (by norm_num) (Or.inr (by
        rcases hi with rfl | rfl | rfl <;> norm_num))
  · intro i
    exact read_decoded_of_frame (dec := dec)
      (hframe 1 i (by norm_num) (Or.inl (by norm_num))) (h.iterate i)
  · intro i
    exact read_decoded_of_frame (dec := dec)
      (hframe 2 i (by norm_num) (Or.inl (by norm_num))) (h.residual i)
  · exact hnew
  · exact read_decoded_of_frame (dec := dec)
      (hframe 7 0 (by norm_num) (Or.inr (by norm_num))) h.squaredResidual
  · exact read_decoded_of_frame (dec := dec)
      (hframe 4 0 (by norm_num) (Or.inl (by norm_num))) h.statusValue

end NLAlib.CGImplementation
