/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BlockSchurUpdate
public import NLAlib.Matrix.Computation.MatrixBlockUpdate

/-!
# A packed GEMM update of the full residual's trailing block

The routine first gathers both panel factors and the trailing residual into one scoped packed
workspace. It calls the block Schur update once and scatters only the trailing result. Every
source word is saved before any residual output write, so source buffers may alias.

## Main results

* `NLAlib.Computation.exec_trailingSchurUpdate`: actual exact execution, the complete residual
  block write and the trailing-panel product formula with all exterior entries preserved.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Update the residual after a panel beginning at `start` with `width` columns: save its
lower panel, upper panel and trailing residual, then apply one packed GEMM-backed Schur update
and scatter the result. All sources are gathered before any residual write, permitting source
aliases. Scratch is scoped, and width-zero or empty trailing blocks perform no arithmetic.
[GolubVanLoan2013, §3.6].
Algorithm: trailing-schur-update -/
def trailingSchurUpdate {P ι VB VI : Type} (p : P) (size start width : IExp VI)
    (L U R : VB) (lo uo ro : IExp VI) : Builder P ι VB VI Unit := scope do
  let finish := start + width
  let m := size - finish
  let work ← alloc p (m * width + width * m + m * m)
  gatherMatrixBlock p m width size L lo finish start work 0
  gatherMatrixBlock p width m size U uo start finish work (m * width)
  gatherMatrixBlock p m m size R ro finish finish work (m * width + width * m)
  blockSchurUpdate p m width m work work work 0 (m * width) (m * width + width * m)
  scatterMatrixBlock p m m size work (m * width + width * m) R ro finish finish

/-- The scoped full trailing-block update composes with any continuation. -/
theorem executionComposable_trailingSchurUpdate {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (size start width : IExp ℕ) (L U R : ℕ)
    (lo uo ro : IExp ℕ) :
    ExecutionComposable I (trailingSchurUpdate p size start width L U R lo uo ro) :=
  executionComposable_single I (fun _ => rfl)

namespace TrailingSchurUpdate

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem exec_gather (I : Interp P ι K C) (p : P) (st : St P K C)
    (size start width m : IExp ℕ) (L U R work : ℕ) (lo uo ro : IExp ℕ)
    (MA : Matrix (Fin m.eval) (Fin width.eval) K)
    (MB : Matrix (Fin width.eval) (Fin m.eval) K)
    (MC : Matrix (Fin m.eval) (Fin m.eval) K)
    (hL : ∀ i j, st.store.read p L
      (lo.eval + (start + width).eval + i.val + size.eval * (start.eval + j.val)) = some (MA i j))
    (hU : ∀ i j, st.store.read p U
      (uo.eval + start.eval + i.val + size.eval * ((start + width).eval + j.val)) = some (MB i j))
    (hR : ∀ i j, st.store.read p R
      (ro.eval + (start + width).eval + i.val + size.eval * ((start + width).eval + j.val)) =
        some (MC i j))
    (hLw : 0 < m.eval * width.eval → L ≠ work)
    (hUw : 0 < width.eval * m.eval → U ≠ work) (hRw : 0 < m.eval * m.eval → R ≠ work)
    (hw : st.store.shape[work]? =
      some (p, m.eval * width.eval + width.eval * m.eval + m.eval * m.eval))
    (htop : st.store.size ≤ work + 1) :
    ∃ out, exec I (do
      gatherMatrixBlock p m width size L lo (start + width) start work 0
      gatherMatrixBlock p width m size U uo start (start + width) work (m * width)
      gatherMatrixBlock p m m size R ro (start + width) (start + width) work
        (m * width + width * m)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b i, b ≠ work → out.store.read q b i = st.store.read q b i) ∧
      out.store.pop = st.store.pop ∧ Holds out.store p work 0 MA ∧
      Holds out.store p work (m.eval * width.eval) MB ∧
      Holds out.store p work (m.eval * width.eval + width.eval * m.eval) MC := by
  obtain ⟨s₁, WL, hWL, hr₁, hw₁, hA⟩ := exec_gatherMatrixBlock I p st m width size L lo
    (start + width) start work 0 MA hLw hL
    (fun i hi => ⟨_, hw, by simp only [IExp.eval_zero]; omega⟩)
  have hsh₁ := Store.shape_of_writeBlock_eq_some hw₁
  obtain ⟨s₂, WU, hWU, hr₂, hw₂, hB⟩ := exec_gatherMatrixBlock I p s₁ width m size U uo
    start (start + width) work (m * width) MB hUw (by
      intro i j
      rw [Store.read_of_writeBlock_eq_some_of_ne hw₁
        (Or.inl (hUw (Nat.mul_pos (Nat.zero_lt_of_lt i.isLt) (Nat.zero_lt_of_lt j.isLt))))]
      exact hU i j)
    (fun i hi => ⟨_, hsh₁ ▸ hw, by simp only [IExp.eval_mul]; omega⟩)
  have hsh₂ := (Store.shape_of_writeBlock_eq_some hw₂).trans hsh₁
  obtain ⟨s₃, WC, hWC, hr₃, hw₃, hC⟩ := exec_gatherMatrixBlock I p s₂ m m size R ro
    (start + width) (start + width) work (m * width + width * m) MC hRw (by
      intro i j
      have hn := hRw (Nat.mul_pos (Nat.zero_lt_of_lt i.isLt) (Nat.zero_lt_of_lt j.isLt))
      rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hn),
        Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hn)]
      exact hR i j)
    (fun i hi => ⟨_, hsh₂ ▸ hw, by simp only [IExp.eval_add, IExp.eval_mul]; omega⟩)
  have hsh₃ := (Store.shape_of_writeBlock_eq_some hw₃).trans hsh₂
  refine ⟨s₃, ?_, hsh₃, ?_, ?_, ?_, ?_, hC⟩
  · rw [exec_run_bind I
      (b := gatherMatrixBlock p m width size L lo (start + width) start work 0) (fun _ => rfl),
      hr₁, Option.bind_some, exec_run_bind I
      (b := gatherMatrixBlock p width m size U uo start (start + width) work (m * width))
      (fun _ => rfl), hr₂, Option.bind_some]
    exact hr₃
  · intro q b i hb
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inl hb),
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hb),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hb)]
  · exact (Store.pop_of_writeBlock_top hw₃ (by
      rw [Store.size_eq_of_shape_eq hsh₂]; exact htop)).trans
      ((Store.pop_of_writeBlock_top hw₂ (by
        rw [Store.size_eq_of_shape_eq hsh₁]; exact htop)).trans
        (Store.pop_of_writeBlock_top hw₁ htop))
  · intro i j
    have hidx := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inr (Or.inl (by
      simp only [IExp.eval_add, IExp.eval_mul]; omega))),
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inr (Or.inl (by
        simp only [IExp.eval_mul]; omega)))]
    exact hA i j
  · intro i j
    have hidx := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inr (Or.inl (by
      simp only [IExp.eval_add, IExp.eval_mul]; omega)))]
    exact hB i j

private theorem exec_prepare (I : Interp P ι K C) (p : P) (initial : Store P K)
    (st : St P K C) (size start width m : IExp ℕ) (L U R : ℕ) (lo uo ro : IExp ℕ)
    (MA : Matrix (Fin m.eval) (Fin width.eval) K)
    (MB : Matrix (Fin width.eval) (Fin m.eval) K)
    (MC : Matrix (Fin m.eval) (Fin m.eval) K)
    (M : Matrix (Fin size.eval) (Fin size.eval) K)
    (hL : ∀ i j, initial.read p L
      (lo.eval + (start + width).eval + i.val + size.eval * (start.eval + j.val)) = some (MA i j))
    (hU : ∀ i j, initial.read p U
      (uo.eval + start.eval + i.val + size.eval * ((start + width).eval + j.val)) = some (MB i j))
    (hC : ∀ i j, initial.read p R
      (ro.eval + (start + width).eval + i.val + size.eval * ((start + width).eval + j.val)) =
        some (MC i j))
    (hM : Holds initial p R ro.eval M)
    (hst : st.store = initial.push
      (p, Array.replicate (m.eval * width.eval + width.eval * m.eval + m.eval * m.eval) none)) :
    ∃ out, exec I (do
      gatherMatrixBlock p m width size L lo (start + width) start initial.size 0
      gatherMatrixBlock p width m size U uo start (start + width) initial.size (m * width)
      gatherMatrixBlock p m m size R ro (start + width) (start + width) initial.size
        (m * width + width * m)).run st = some out ∧
      out.store.shape = st.store.shape ∧ out.store.pop = initial ∧
      Holds out.store p R ro.eval M ∧ Holds out.store p initial.size 0 MA ∧
      Holds out.store p initial.size (m.eval * width.eval) MB ∧
      Holds out.store p initial.size (m.eval * width.eval + width.eval * m.eval) MC := by
  obtain ⟨out, hr, hsh, hfr, hpop, hA, hB, hC'⟩ := exec_gather I p st size start width m
    L U R initial.size lo uo ro MA MB MC
    (by intro i j; rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hL i j))];
        exact hL i j)
    (by intro i j; rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hU i j))];
        exact hU i j)
    (by intro i j; rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hC i j))];
        exact hC i j)
    (by
      intro hn
      have hm : 0 < m.eval := by nlinarith
      have hw : 0 < width.eval := by nlinarith
      exact Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hL ⟨0, hm⟩ ⟨0, hw⟩)))
    (by
      intro hn
      have hm : 0 < m.eval := by nlinarith
      have hw : 0 < width.eval := by nlinarith
      exact Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hU ⟨0, hw⟩ ⟨0, hm⟩)))
    (by
      intro hn
      have hm : 0 < m.eval := by nlinarith
      exact Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hC ⟨0, hm⟩ ⟨0, hm⟩)))
    (by rw [hst]; exact Store.getElem?_shape_push_size initial p _)
    (by rw [hst]; simp only [Array.size_push]; omega)
  refine ⟨out, hr, hsh, ?_, ?_, hA, hB, hC'⟩
  · rw [hpop, hst]
    exact Array.pop_push
  · intro i j
    rw [hfr p R _ (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hM i j))), hst,
      Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hM i j))]
    exact hM i j

private theorem exec_body {𝕜 : Type} [RCLike 𝕜]
    (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (initial : Store P 𝕜)
    (st : St P 𝕜 (OpCount P ι)) (size start width m : IExp ℕ) (L U R : ℕ)
    (lo uo ro : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin width.eval) 𝕜)
    (MB : Matrix (Fin width.eval) (Fin m.eval) 𝕜) (MC : Matrix (Fin m.eval) (Fin m.eval) 𝕜)
    (M : Matrix (Fin size.eval) (Fin size.eval) 𝕜)
    (hL : ∀ i j, initial.read p L
      (lo.eval + (start + width).eval + i.val + size.eval * (start.eval + j.val)) = some (MA i j))
    (hU : ∀ i j, initial.read p U
      (uo.eval + start.eval + i.val + size.eval * ((start + width).eval + j.val)) = some (MB i j))
    (hC : ∀ i j, initial.read p R
      (ro.eval + (start + width).eval + i.val + size.eval * ((start + width).eval + j.val)) =
        some (MC i j))
    (hM : Holds initial p R ro.eval M) (htail : (start + width).eval + m.eval ≤ size.eval)
    (hst : st.store = initial.push
      (p, Array.replicate (m.eval * width.eval + width.eval * m.eval + m.eval * m.eval) none)) :
    ∃ (out : St P 𝕜 (OpCount P ι)) (W : Array 𝕜) (M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜),
      W.size = size.eval * size.eval ∧ exec I (do
        gatherMatrixBlock p m width size L lo (start + width) start initial.size 0
        gatherMatrixBlock p width m size U uo start (start + width) initial.size (m * width)
        gatherMatrixBlock p m m size R ro (start + width) (start + width) initial.size
          (m * width + width * m)
        blockSchurUpdate p m width m initial.size initial.size initial.size 0 (m * width)
          (m * width + width * m)
        scatterMatrixBlock p m m size initial.size (m * width + width * m) R ro
          (start + width) (start + width)).run st = some out ∧
      initial.writeBlock p R ro.eval W = some out.store.pop ∧ Holds out.store.pop p R ro.eval M' ∧
      (∀ i j, M' (Fin.castLE htail (Fin.natAdd (start + width).eval i))
        (Fin.castLE htail (Fin.natAdd (start + width).eval j)) = (MC - MA * MB) i j) ∧
      ∀ i j, (i.val < (start + width).eval ∨ (start + width).eval + m.eval ≤ i.val ∨
        j.val < (start + width).eval ∨ (start + width).eval + m.eval ≤ j.val) → M' i j = M i j := by
  obtain ⟨ready, hr₁, hsh, hpop, hMr, hA, hB, hC'⟩ :=
    exec_prepare I p initial st size start width m L U R lo uo ro MA MB MC M hL hU hC hM hst
  have hsize : ready.store.size = initial.size + 1 := by
    rw [Store.size_eq_of_shape_eq hsh, hst, Array.size_push]
  obtain ⟨updated, hr₂, hw₂, hC''⟩ := exec_blockSchurUpdate I hI hc p ready m width m
    initial.size initial.size initial.size 0 (m * width) (m * width + width * m) MA MB MC hA hB hC'
  have hsize' : updated.store.size = initial.size + 1 :=
    (Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some hw₂)).trans hsize
  have hpop' : updated.store.pop = initial :=
    (Store.pop_of_writeBlock_top hw₂ (by rw [hsize])).trans hpop
  have hMu : Holds updated.store p R ro.eval M := by
    intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂
      (Or.inl (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hM i j))))]
    exact hMr i j
  obtain ⟨out, W, M', hWs, hr₃, hw₃, hM', hcoords, houter⟩ :=
    exec_scatterMatrixBlock_into_matrix I p updated size m m initial.size
      (m * width + width * m) R ro (start + width) (start + width) M (MC - MA * MB)
      htail htail hMu hC'' (fun hn => by
        have hRlt := hM.writable.lt_size (by
          have hm : 0 < m.eval := by nlinarith
          have hN : 0 < size.eval := by omega
          exact Nat.mul_pos hN hN)
        exact Nat.ne_of_gt hRlt)
  have hwrite := Store.writeBlock_pop_of_lt hw₃ (fun hn => by
    have hRlt := hM.writable.lt_size (by simpa only [hWs] using hn)
    omega)
  rw [hpop'] at hwrite
  refine ⟨out, W, M', hWs, ?_, hwrite, ?_, hcoords, houter⟩
  · have hcomp : ExecutionComposable I (do
      gatherMatrixBlock p m width size L lo (start + width) start initial.size 0
      gatherMatrixBlock p width m size U uo start (start + width) initial.size (m * width)
      gatherMatrixBlock p m m size R ro (start + width) (start + width) initial.size
        (m * width + width * m)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    exact (hcomp (fun _ => do
      blockSchurUpdate p m width m initial.size initial.size initial.size 0 (m * width)
        (m * width + width * m)
      scatterMatrixBlock p m m size initial.size (m * width + width * m) R ro
        (start + width) (start + width)) st).trans (by
      rw [hr₁, Option.bind_some, exec_run_bind I
        (b := blockSchurUpdate p m width m initial.size initial.size initial.size 0 (m * width)
          (m * width + width * m)) (fun _ => rfl), hr₂, Option.bind_some]
      exact hr₃)
  · intro i j
    rw [Store.read_pop_of_lt (by
      have hRlt := Store.lt_size_of_read_eq_some (hM i j)
      have hsz := Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some hw₃)
      omega)]
    exact hM' i j

end TrailingSchurUpdate

/-- The actual trailing-panel update succeeds in exact arithmetic with standard charges.
It writes one full residual matrix block, subtracts the product of the saved lower and upper
panel factors on every trailing entry, and retains every exterior entry. All three original
source buffers may alias because they are gathered before any residual write. Zero-width
panels and empty trailing blocks are supported, including an empty matrix with invalid
buffer handles. [GolubVanLoan2013, §3.6]. -/
theorem exec_trailingSchurUpdate {𝕜 P ι : Type} [RCLike 𝕜] [DecidableEq P]
    (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P 𝕜 (OpCount P ι)) (size start width : IExp ℕ) (L U R : ℕ)
    (lo uo ro : IExp ℕ) (F G M : Matrix (Fin size.eval) (Fin size.eval) 𝕜)
    (hsw : start.eval + width.eval ≤ size.eval)
    (hF : Holds st.store p L lo.eval F) (hG : Holds st.store p U uo.eval G)
    (hM : Holds st.store p R ro.eval M) :
    ∃ (out : St P 𝕜 (OpCount P ι)) (W : Array 𝕜)
      (M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜),
      W.size = size.eval * size.eval ∧
      exec I (trailingSchurUpdate p size start width L U R lo uo ro).run st = some out ∧
      st.store.writeBlock p R ro.eval W = some out.store ∧ Holds out.store p R ro.eval M' ∧
      (∀ i j, start.eval + width.eval ≤ i.val → start.eval + width.eval ≤ j.val →
        M' i j = M i j - ∑ t : Fin width.eval,
          F i (Fin.castLE hsw (Fin.natAdd start.eval t)) *
            G (Fin.castLE hsw (Fin.natAdd start.eval t)) j) ∧
      ∀ i j, (i.val < start.eval + width.eval ∨ j.val < start.eval + width.eval) →
        M' i j = M i j := by
  let finish := start + width
  let m := size - finish
  have htail : finish.eval + m.eval ≤ size.eval := by
    change start.eval + width.eval + (size.eval - (start.eval + width.eval)) ≤ size.eval
    omega
  let tail : Fin m.eval → Fin size.eval := fun i => Fin.castLE htail (Fin.natAdd finish.eval i)
  let panel : Fin width.eval → Fin size.eval := fun t => Fin.castLE hsw (Fin.natAdd start.eval t)
  let MA : Matrix (Fin m.eval) (Fin width.eval) 𝕜 := fun i t => F (tail i) (panel t)
  let MB : Matrix (Fin width.eval) (Fin m.eval) 𝕜 := fun t j => G (panel t) (tail j)
  let MC : Matrix (Fin m.eval) (Fin m.eval) 𝕜 := fun i j => M (tail i) (tail j)
  obtain ⟨out, hr, W, M', hWs, hw, hM', hcoords, houter⟩ := exists_exec_alloc I p
    (m * width + width * m + m * m) (fun work => (do
      gatherMatrixBlock p m width size L lo finish start work 0
      gatherMatrixBlock p width m size U uo start finish work (m * width)
      gatherMatrixBlock p m m size R ro finish finish work (m * width + width * m)
      blockSchurUpdate p m width m work work work 0 (m * width) (m * width + width * m)
      scatterMatrixBlock p m m size work (m * width + width * m) R ro finish finish).run) st
    (fun s => ∃ (W : Array 𝕜) (M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜),
      W.size = size.eval * size.eval ∧ st.store.writeBlock p R ro.eval W = some s ∧
      Holds s p R ro.eval M' ∧ (∀ i j, M' (tail i) (tail j) = (MC - MA * MB) i j) ∧
      ∀ i j, (i.val < finish.eval ∨ finish.eval + m.eval ≤ i.val ∨
        j.val < finish.eval ∨ finish.eval + m.eval ≤ j.val) → M' i j = M i j)
    (fun σ hσ => by
      obtain ⟨out, W, M', hsize, hexec, hwrite, hM', hcoords, houter⟩ :=
        TrailingSchurUpdate.exec_body I hI hc p st.store σ size start width m L U R lo uo ro
          MA MB MC M (by
            intro i j
            simpa [MA, tail, panel, finish, Fin.castLE, Fin.natAdd, Nat.add_assoc] using
              (hF (tail i) (panel j)))
          (by
            intro i j
            simpa [MB, tail, panel, finish, Fin.castLE, Fin.natAdd, Nat.add_assoc] using
              (hG (panel i) (tail j)))
          (by
            intro i j
            simpa [MC, tail, finish, Fin.castLE, Fin.natAdd, Nat.add_assoc] using
              (hM (tail i) (tail j)))
          hM htail (by simpa only [IExp.eval_add, IExp.eval_mul] using hσ)
      exact ⟨out, hexec, W, M', hsize, hwrite, hM', hcoords, houter⟩)
  refine ⟨out, W, M', hWs, ?_, hw, hM', ?_, ?_⟩
  · change exec I (.seq (.alloc p (m * width + width * m + m * m) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j hi hj
    change finish.eval ≤ i.val at hi
    change finish.eval ≤ j.val at hj
    let ii : Fin m.eval := ⟨i.val - finish.eval, by
      have hh := i.isLt
      change i.val - finish.eval < size.eval - finish.eval
      omega⟩
    let jj : Fin m.eval := ⟨j.val - finish.eval, by
      have hh := j.isLt
      change j.val - finish.eval < size.eval - finish.eval
      omega⟩
    have hti : tail ii = i := by
      apply Fin.ext
      change finish.eval + (i.val - finish.eval) = i.val
      omega
    have htj : tail jj = j := by
      apply Fin.ext
      change finish.eval + (j.val - finish.eval) = j.val
      omega
    have he := hcoords ii jj
    rw [hti, htj] at he
    rw [he, Matrix.sub_apply, Matrix.mul_apply]
    simp only [MC, MA, MB, hti, htj, panel]
  · intro i j hout
    exact houter i j (by
      rcases hout with hi | hj
      · exact Or.inl hi
      · exact Or.inr (Or.inr (Or.inl hj)))

end NLAlib.Computation
