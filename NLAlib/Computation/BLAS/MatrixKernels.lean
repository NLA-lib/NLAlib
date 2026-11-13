/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS

/-!
# Specifications of the BLAS matrix kernels

The level-2 and level-3 kernels `NLAlib.Computation.gemv` ($\mathbf{y} \leftarrow
\mathbf{A}\mathbf{x}$), `NLAlib.Computation.ger` (the rank-one update
$\mathbf{A} \leftarrow \mathbf{A} + a\,\mathbf{x}\mathbf{y}^{\mathsf{H}}$) and
`NLAlib.Computation.gemm` ($\mathbf{C} \leftarrow \mathbf{A}\mathbf{B}$, one `gemv` per
column) take their operands as matrices held column-major (`NLAlib.Computation.Holds`) and write
their result as a vector or as a matrix flattened column-major. Each specification has the six
parts of the level-1 kernels in `NLAlib/Computation/BLAS.lean`: value, tape, memory in cells and
in bits, and counts.
The runs carry the frame invariant `NLAlib.Computation.Store.BlockFrame` through their loops.
Design: `docs/design/Computation.md` (D13, D17, §4).

## Main results

* `NLAlib.Computation.exec_gemv`, `NLAlib.Computation.exec_ger`, `NLAlib.Computation.exec_gemm`:
  the specifications.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.Computation

open Builder

section Steps

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-! ### Steps of the runs -/

namespace Level2

omit [RCLike 𝕜] in
/-- The destination buffer of a block write of $L$ cells exists when $L > 0$, and the block
fits in it. -/
private theorem blockFacts {s s₁ : Store P 𝕜} {p : P} {dst dOff L : ℕ} {Y : Array 𝕜}
    (hs₁ : s.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L) :
    (0 < L → dst < s.size) ∧ ∀ m < L, ∃ n, s.shape[dst]? = some (p, n) ∧ dOff + m < n :=
  ⟨fun h => Store.lt_size_of_writeBlock_eq_some hs₁ (hYs ▸ h),
    fun _ hm => Store.exists_getElem?_shape_of_writeBlock_eq_some hs₁ (hYs ▸ hm)⟩


section GemvSteps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T A x y L : ℕ}
  {m n ao xo yo : IExp ℕ}

private theorem exec_gemvStep (hsem : I.sem = exactSem) (hc : IsUnitCharge I)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j : ℕ} {a xj w : 𝕜}
    (h : Store.BlockFrame s₀ p T y yo.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1))
    (hyT : y ≠ T)
    (hi : i < L) (hy : ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (hA : σ.store.read p A (ao.eval + i + m.eval * j) = some a)
    (hx : σ.store.read p x (xo.eval + j) = some xj) (hw : g i = some w) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨T, 0⟩ ⟨A, ao + .var i + m * .var j⟩
        ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩
          ⟨T, 0⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T y yo.eval L s' (Function.update g i (some (w + a * xj))) := by
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some (a * xj) hT one_pos
  have h₁' := h.write_scratch (fun _ => hyT) h₁
  obtain ⟨k, hysh, hylt⟩ := hy
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (w + a * xj) hysh hylt
  refine ⟨s₂, ?_, h₁'.write_of_lt hi h₂⟩
  have rw₁ : s₁.read p y (yo.eval + i) = some w := by rw [h₁'.2.2 _ hi, hw]
  simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
    IExp.eval_zero, hA, hx, hsem, hc.charge_eq, h₁, Option.bind_some, Option.map_some,
    Store.read_of_write_eq_some h₁, rw₁, exactSem, h₂]
  simp only [add_assoc]

private structure GemvCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T A x y : ℕ) (m n ao xo yo : ℕ) (a : ℕ → ℕ → 𝕜) (xv : ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : IsUnitCharge I
  scratch : s₀.shape[T]? = some (p, 1)
  y_ne : 0 < m → y ≠ T
  y_shape : ∀ i < m, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo + i < k
  A_read : ∀ i < m, ∀ j < n, s₀.read p A (ao + i + m * j) = some (a i j)
  A_out : ∀ i < m, ∀ j < n, A ≠ T ∧ ¬(p = p ∧ A = y ∧ yo ≤ ao + i + m * j ∧
    ao + i + m * j < yo + m)
  x_read : ∀ j < n, s₀.read p x (xo + j) = some (xv j)
  x_out : ∀ j < n, x ≠ T ∧ ¬(p = p ∧ x = y ∧ yo ≤ xo + j ∧ xo + j < yo + m)

variable {a : ℕ → ℕ → 𝕜} {xv : ℕ → 𝕜}

private theorem exec_gemvRow
    (hC : GemvCtx I s₀ p T A x y m.eval n.eval ao.eval xo.eval yo.eval a xv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store g)
    (hg : ∀ i < m.eval, g i = some (∑ j' ∈ Finset.range j, a i j' * xv j')) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
        Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧
        ∀ i < m.eval, g' i = some (∑ j' ∈ Finset.range (j + 1), a i j' * xv j') := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧
      ∀ i < m.eval, g' i = some (∑ j' ∈ Finset.range (if i < i' then j + 1 else j),
        a i j' * xv j')) ⟨σ.store, g, by simp, h, by simpa using hg⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ =>
      ⟨hrun, s', g', hσ, hI, fun i hi => by simpa [hi] using hrow i hi⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨hAT, hAout⟩ := hC.A_out i' hi' j hj
  obtain ⟨hxT, hxout⟩ := hC.x_out j hj
  obtain ⟨s'', hrun, hI'⟩ := exec_gemvStep hC.sem hC.charge hI hC.scratch
    (hC.y_ne (by omega)) hi' (hC.y_shape i' hi')
    ((hI.read_of_ne hAT hAout).trans (hC.A_read i' hi' j hj))
    ((hI.read_of_ne hxT hxout).trans (hC.x_read j hj)) (by simpa using hrow i' hi')
  refine ⟨_, hrun, s'', _, ?_, hI', fun i hi => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp [Finset.sum_range_succ]
    · rw [Function.update_of_ne hii, hrow i hi]
      have : (i < i' + 1) = (i < i') := by
        apply propext
        omega
      simp only [this]

private theorem exec_gemvCols
    (hC : GemvCtx I s₀ p T A x y m.eval n.eval ao.eval xo.eval yo.eval a xv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store g) (hg : ∀ i < m.eval, g i = some 0) :
    ∃ σ', exec I (.loop n fun j => .seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) .skip) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + n.eval • (m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧
        ∀ i < m.eval, g' i = some (∑ j ∈ Finset.range n.eval, a i j * xv j) := by
  refine exists_exec_loop_eq_some_of_forall I (fun j' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + j' • (m.eval • (.single (.bin p .mul) 1 +
        .single (.bin p .add) 1)) } ∧ Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧
      ∀ i < m.eval, g' i = some (∑ j ∈ Finset.range j', a i j * xv j))
    ⟨σ.store, g, by simp, h, by simpa using hg⟩ ?_
  rintro j hj σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow'⟩ := exec_gemvRow hC hj hI hrow
  refine ⟨_, by rw [exec_seq_skip, hrun], s'', g'', ?_, hI', hrow'⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

private theorem exec_gemvZero (hsem : I.sem = exactSem) (hc : IsUnitCharge I)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (hy : ∀ i < m.eval, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (h : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store g) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.lit p ⟨y, yo + .var i⟩ 0)) .skip) σ =
        some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval • .single (.lit p) 1 } ∧
        Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧ ∀ i < m.eval, g' i = some 0 := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • .single (.lit p) 1 } ∧
      Store.BlockFrame s₀ p T y yo.eval m.eval s' g' ∧ ∀ i < i', g' i = some 0)
    ⟨σ.store, g, by simp, h, by simp⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ => ⟨hrun, s', g', hσ, hI, hrow⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨k, hysh, hylt⟩ := hy i' hi'
  obtain ⟨s'', hw⟩ := hI.exists_write_eq_some 0 hysh hylt
  refine ⟨{ σ' with store := s'', cnt := σ'.cnt + .single (.lit p) 1 }, ?_, s'', _, ?_,
    hI.write_of_lt hi' hw, fun i hi => ?_⟩
  · simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_var, hsem, hc.charge_eq,
      exactSem,
      Rat.cast_zero, Option.bind_some, hw, Option.map_some]
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp
    · rw [Function.update_of_ne hii]
      exact hrow i (by omega)

end GemvSteps

section GerSteps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T A x y : ℕ}
  {m n ao xo yo : IExp ℕ}

private structure GerCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T A x y : ℕ) (a : Cell ℕ ℕ) (m n ao xo yo : ℕ) (av : 𝕜) (xv yv : ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : IsUnitCharge I
  scratch : s₀.shape[T]? = some (p, 2)
  A_ne : 0 < m * n → A ≠ T
  A_shape : ∀ k < m * n, ∃ l, s₀.shape[A]? = some (p, l) ∧ ao + k < l
  a_read : s₀.read p a.buf a.idx.eval = some av
  a_out : a.buf ≠ T ∧ ¬(p = p ∧ a.buf = A ∧ ao ≤ a.idx.eval ∧ a.idx.eval < ao + m * n)
  x_read : ∀ i < m, s₀.read p x (xo + i) = some (xv i)
  x_out : ∀ i < m, x ≠ T ∧ ¬(p = p ∧ x = A ∧ ao ≤ xo + i ∧ xo + i < ao + m * n)
  y_read : ∀ j < n, s₀.read p y (yo + j) = some (yv j)
  y_out : ∀ j < n, y ≠ T ∧ ¬(p = p ∧ y = A ∧ ao ≤ yo + j ∧ yo + j < ao + m * n)

variable {a : Cell ℕ ℕ} {av : 𝕜} {xv yv : ℕ → 𝕜} {M : ℕ → ℕ → 𝕜}

private theorem exec_gerStep
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j : ℕ} {c₀ w : 𝕜} (hi : i < m.eval)
    (hj : j < n.eval) (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some c₀) (hw : g (i + m.eval * j) = some w) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s'
        (Function.update g (i + m.eval * j) (some (w + xv i * c₀))) ∧
      s'.read p T 0 = some c₀ := by
  have hk : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
  have hAT := hC.A_ne (by omega)
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some (xv i * c₀) hC.scratch (by omega : 1 < 2)
  have h₁' := h.write_scratch (fun _ => hAT) h₁
  obtain ⟨l, hAsh, hAlt⟩ := hC.A_shape _ hk
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (w + xv i * c₀) hAsh hAlt
  refine ⟨s₂, ?_, h₁'.write_of_lt hk h₂, ?_⟩
  · have rx : σ.store.read p x (xo.eval + i) = some (xv i) :=
      (h.read_of_ne (hC.x_out i hi).1 (hC.x_out i hi).2).trans (hC.x_read i hi)
    have rA : s₁.read p A (ao.eval + i + m.eval * j) = some w := by
      rw [Nat.add_assoc, h₁'.2.2 _ hk, hw]
    rw [← Nat.add_assoc] at h₂
    simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
      IExp.eval_zero, IExp.eval_one, rx, ht, hC.sem, hC.charge.charge_eq, h₁, Option.bind_some,
      Option.map_some, Store.read_of_write_eq_some h₁, rA, exactSem, h₂]
    simp only [add_assoc]
  · rw [Store.read_of_write_eq_some_of_ne h₂ (Or.inl (Ne.symm hAT)),
      Store.read_of_write_eq_some_of_ne h₁ (Or.inr (by omega)), ht]

private def gerVal (M : ℕ → ℕ → 𝕜) (av : 𝕜) (xv yv : ℕ → 𝕜) (i j : ℕ) (b : Prop)
    [Decidable b] : Option 𝕜 :=
  some (if b then M i j + xv i * (av * star (yv j)) else M i j)

private theorem exec_gerRow
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some (av * star (yv j)))
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M av xv yv i j' (j' < j)) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M av xv yv i j' (j' < j + 1) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      s'.read p T 0 = some (av * star (yv j)) ∧ ∀ i < m.eval, ∀ j' < n.eval,
        g' (i + m.eval * j') = gerVal M av xv yv i j' (j' < j ∨ (j' = j ∧ i < i')))
    ⟨σ.store, g, by simp, h, ht, by simpa using hg⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, _, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      rw [hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, ht', hrow⟩
  replace hI : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  replace ht' : σ'.store.read p T 0 = some (av * star (yv j)) := hσ ▸ ht'
  have hw := hrow i' hi' j hj
  simp only [gerVal, lt_irrefl, false_or, and_false, if_false] at hw
  obtain ⟨s'', hrun, hI', ht''⟩ := exec_gerStep hC hi' hj hI ht' hw
  refine ⟨_, hrun, s'', _, ?_, hI', ht'', fun i hi j' hj' => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases he : i = i' ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := he
      simp [gerVal]
    · rw [Function.update_of_ne (fun h' => he
        ((Nat.add_mul_eq_add_mul_iff_of_lt hi hi').mp h')), hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)

private theorem exec_gerCol
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M av xv yv i j' (j' < j)) :
    ∃ σ', exec I (.seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (.single (.un p .conj) 1 +
          .single (.bin p .mul) 1 + m.eval •
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M av xv yv i j' (j' < j + 1) := by
  obtain ⟨hyT, hyout⟩ := hC.y_out j hj
  have ry : σ.store.read p y (yo.eval + j) = some (yv j) :=
    (h.read_of_ne hyT hyout).trans (hC.y_read j hj)
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some (star (yv j)) hC.scratch (by omega : 0 < 2)
  have h₁' := h.write_scratch hC.A_ne h₁
  have ra : s₁.read p a.buf a.idx.eval = some av :=
    (h₁'.read_of_ne hC.a_out.1 hC.a_out.2).trans hC.a_read
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (av * star (yv j)) hC.scratch (by omega : 0 < 2)
  have h₂' := h₁'.write_scratch hC.A_ne h₂
  obtain ⟨σ'', hrun, s'', g'', hσ'', hI'', hrow''⟩ := exec_gerRow (M := M) hC hj (σ := { σ with
      store := s₂, cnt := σ.cnt + .single (.un p .conj) 1 + .single (.bin p .mul) 1 }) h₂'
    (Store.read_of_write_eq_some h₂) hg
  refine ⟨σ'', ?_, s'', g'', ?_, hI'', hrow''⟩
  · rw [exec_seq_instr_un I (s := s₁) ry (by rw [hC.sem]; rfl) h₁,
      exec_seq_instr_bin I (s := s₂) ra (Store.read_of_write_eq_some h₁) (by rw [hC.sem]; rfl)
        h₂, exec_seq_skip]
    simp only [hC.charge.charge_eq]
    exact hrun
  · rw [hσ'']
    simp only [add_assoc]

private theorem exec_gerCols
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = some (M i j')) :
    ∃ σ', exec I (.loop n fun j => .seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + n.eval •
          (.single (.un p .conj) 1 + .single (.bin p .mul) 1 + m.eval •
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          some (M i j' + xv i * (av * star (yv j'))) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun j σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + j • (.single (.un p .conj) 1 + .single (.bin p .mul) 1 +
        m.eval • (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') = gerVal M av xv yv i j' (j' < j))
    ⟨σ.store, g, by simp, h, fun i hi j' hj' => by simp [gerVal, hg i hi j' hj']⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      simpa [gerVal, hj'] using hrow i hi j' hj'⟩
  rintro j hj σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow'⟩ := exec_gerCol hC hj hI hrow
  refine ⟨_, hrun, s'', g'', ?_, hI', hrow'⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

end GerSteps

end Level2

end Steps

/-! ### Specifications under exact arithmetic -/

section Specs

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]
  (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc

/-- **`gemv` computes $\mathbf{A}\mathbf{x}$**: if buffer $A$ holds the $m \times n$ matrix
$\mathbf{A}$ from $\mathit{ao}$, the cells of $\mathbf{x}$ hold $\mathbf{x}$, and the cells of
$\mathbf{y}$ overlap neither, the run writes $\mathbf{A}\mathbf{x}$ into the cells of
$\mathbf{y}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $m$ literals and $mn$ multiplications and additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_gemv (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) 𝕜) (xv : Fin n.eval → 𝕜)
    (hA : Holds st.store p A ao.eval M)
    (hx : ∀ j : Fin n.eval, st.store.read p x (xo.eval + j) = some (xv j))
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval (Array.ofFn (M *ᵥ xv)) = some s₁) :
    ∃ st', exec I (gemv p m n A ao x xo y yo).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  obtain ⟨hylt, hyshape⟩ := Level2.blockFacts (L := m.eval) h₁ (by simp)
  rw [run_gemv, exec_seq_skip, exec_named, exec_seq]
  obtain ⟨σ₁, h0, s₁', g₁, rfl, hI₁, hz⟩ := Level2.exec_gemvZero (I := I) (s₀ := st.store)
    (T := st.store.size) (σ := st) hI hc hyshape ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hsz : s₁'.size = st.store.size := by
    simpa [Store.size_shape] using congrArg Array.size hI₁.1
  rw [h0, Option.bind_some, exec_alloc, exec_seq_skip]
  dsimp only
  rw [hsz]
  have hC : Level2.GemvCtx I (st.store.push (p, Array.replicate (1 : IExp ℕ).eval none)) p
      st.store.size A x y m.eval n.eval ao.eval xo.eval yo.eval
      (fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
      (fun j => if h : j < n.eval then xv ⟨j, h⟩ else 0) :=
    { sem := hI
      charge := hc
      scratch := Store.getElem?_shape_push_size _ _ _
      y_ne := fun h => Nat.ne_of_lt (hylt h)
      y_shape := fun i hi => by
        rw [Store.getElem?_shape_push_of_lt _ (hylt (by omega))]
        exact hyshape i hi
      A_read := fun i hi j hj => by
        have := hA ⟨i, hi⟩ ⟨j, hj⟩
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some this), this]
        simp [hi, hj]
      A_out := fun i hi j hj => by
        have hlt : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hA ⟨i, hi⟩ ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyA rfl with h | h <;> omega
      x_read := fun j hj => by
        have := hx ⟨j, hj⟩
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some this), this]
        simp [hj]
      x_out := fun j hj => by
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hx ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyx rfl with h | h <;> omega }
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Level2.exec_gemvCols hC
    (σ := { st with
      store := s₁'.push (p, Array.replicate (1 : IExp ℕ).eval none)
      cnt := st.cnt + m.eval • .single (.lit p) 1
      cur := Function.update st.cur p (st.cur p + (1 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (1 : IExp ℕ).eval))
      curW := st.curW + (1 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (1 : IExp ℕ).eval * I.width p) })
    (hI₁.push _ hylt) hz
  rw [hF, Option.map_some]
  refine ⟨_, rfl, hIF.pop_eq h₁ (by simp) fun i hi => ?_, rfl, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hgF i hi, Array.getElem?_ofFn]
    simp only [hi, dif_pos, Option.some.injEq, Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp [j.2]
  · funext q
    by_cases hq : q = p <;> simp [hq]
  · simp
  · simp only [mul_smul, add_assoc]
  · simp
  · simp

/-- **`ger` computes $\mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ in place**: if buffer $A$
holds the $m \times n$ matrix $\mathbf{A}$ from $\mathit{ao}$, the cells of $a$, $\mathbf{x}$
and $\mathbf{y}$ hold $a$, $\mathbf{x}$, $\mathbf{y}$ and lie outside the block of $\mathbf{A}$,
the run writes $\mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ into the block and nothing else,
keeps the tape and the current memory, raises the peak by two cells, and counts $n$
conjugations, $n + mn$ multiplications and $mn$ additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_ger (m n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (av : 𝕜) (xv : Fin m.eval → 𝕜) (yv : Fin n.eval → 𝕜)
    (M : Matrix (Fin m.eval) (Fin n.eval) 𝕜) (hA : Holds st.store p A ao.eval M)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin m.eval, st.store.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j : Fin n.eval, st.store.read p y (yo.eval + j) = some (yv j))
    (haA : a.buf = A → a.idx.eval < ao.eval ∨ ao.eval + m.eval * n.eval ≤ a.idx.eval)
    (hxA : x = A → xo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ xo.eval)
    (hyA : y = A → yo.eval + n.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p A ao.eval (flatten (M + av • Matrix.vecMulVec xv (star yv))) =
      some s₁) :
    ∃ st', exec I (ger p m n a x xo y yo A ao).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1) + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 2)) ∧
      st'.peakW = max st.peakW (st.curW + 2 * I.width p) := by
  obtain ⟨hAlt, hAshape⟩ := Level2.blockFacts (L := m.eval * n.eval) h₁ (by simp [size_flatten])
  rw [run_ger, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  set s₀ : Store P 𝕜 := st.store.push (p, Array.replicate (2 : IExp ℕ).eval none) with hs₀
  have hC : Level2.GerCtx I s₀ p st.store.size A x y a m.eval n.eval ao.eval xo.eval yo.eval av
      (fun i => if h : i < m.eval then xv ⟨i, h⟩ else 0)
      (fun j => if h : j < n.eval then yv ⟨j, h⟩ else 0) :=
    { sem := hI
      charge := hc
      scratch := Store.getElem?_shape_push_size _ _ _
      A_ne := fun h => Nat.ne_of_lt (hAlt h)
      A_shape := fun k hk => by
        rw [hs₀, Store.getElem?_shape_push_of_lt _ (hAlt (by omega))]
        exact hAshape k hk
      a_read := by rw [hs₀, Store.read_push_of_lt (Store.lt_size_of_read_eq_some ha), ha]
      a_out := by
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some ha), ?_⟩
        rintro ⟨-, h, h₁, h₂⟩
        rcases haA h with h | h <;> omega
      x_read := fun i hi => by
        rw [hs₀, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hx ⟨i, hi⟩)), hx ⟨i, hi⟩]
        simp [hi]
      x_out := fun i hi => by
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hx ⟨i, hi⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hxA rfl with h | h <;> omega
      y_read := fun j hj => by
        rw [hs₀, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hy ⟨j, hj⟩)), hy ⟨j, hj⟩]
        simp [hj]
      y_out := fun j hj => by
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hy ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyA rfl with h | h <;> omega }
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Level2.exec_gerCols
    (M := fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) hC
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (2 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (2 : IExp ℕ).eval))
      curW := st.curW + (2 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (2 : IExp ℕ).eval * I.width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ fun i hi j hj => by
      have := hA ⟨i, hi⟩ ⟨j, hj⟩
      rw [← Nat.add_assoc, hs₀, Store.read_push_of_lt (Store.lt_size_of_read_eq_some this), this]
      simp [hi, hj]
  rw [hF, Option.map_some]
  refine ⟨_, rfl, hIF.pop_eq h₁ (by simp [size_flatten]) fun k hk => ?_, rfl, ?_,
    ?_, ?_, ?_, ?_⟩
  · have hm : 0 < m.eval := Nat.pos_of_ne_zero fun h => by simp [h] at hk
    have hi : k % m.eval < m.eval := Nat.mod_lt _ hm
    have hj : k / m.eval < n.eval := Nat.div_lt_of_lt_mul hk
    rw [← Nat.mod_add_div k m.eval, hgF _ hi _ hj, getElem?_flatten _ ⟨_, hi⟩ ⟨_, hj⟩]
    simp [hi, hj, Matrix.vecMulVec_apply, mul_left_comm]
  · funext q
    by_cases hq : q = p <;> simp [hq]
  · simp
  · simp only [smul_add, mul_smul, add_assoc]
  · simp
  · simp

/-- One column of `gemm`: the `gemv` of column $c$, from a store with the frame invariant of the
block of $\mathbf{C}$. -/
private theorem exec_gemm_step (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ)
    (C : ℕ) (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (MB : Matrix (Fin n.eval) (Fin l.eval) 𝕜) (hA : Holds st.store p A ao.eval MA)
    (hB : Holds st.store p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hCsh : ∀ k < m.eval * l.eval, ∃ N, st.store.shape[C]? = some (p, N) ∧ co.eval + k < N)
    {c : ℕ} (hcl : c < l.eval) (σ : St P 𝕜 (OpCount P ι)) (g : ℕ → Option 𝕜)
    (hD : Store.BlockFrame st.store p st.store.size C co.eval (m.eval * l.eval) σ.store g)
    (hg : ∀ k < m.eval * c, g k = (flatten (MA * MB))[k]?) :
    ∃ σ', exec I (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run σ = some σ' ∧
      σ'.pos = σ.pos ∧ σ'.cur = σ.cur ∧ σ'.curW = σ.curW ∧
      σ'.cnt = σ.cnt + (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      σ'.peak = Function.update σ.peak p (max (σ.peak p) (σ.cur p + 1)) ∧
      σ'.peakW = max σ.peakW (σ.curW + I.width p) ∧
      ∃ g', Store.BlockFrame st.store p st.store.size C co.eval (m.eval * l.eval) σ'.store g' ∧
        ∀ k < m.eval * (c + 1), g' k = (flatten (MA * MB))[k]? := by
  have hmc : m.eval * c + m.eval ≤ m.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hnc : n.eval * c + n.eval ≤ n.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hA' : Holds σ.store p A ao.eval MA := fun i j => by
    have hk := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
    refine (hD.read_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hA i j))) ?_).trans (hA i j)
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCA h.symm with h | h <;> omega
  have hx : ∀ j : Fin n.eval, σ.store.read p B ((bo + n * .var c).eval + j) =
      some (MB j ⟨c, hcl⟩) := fun j => by
    have hk := Nat.add_mul_lt_mul_of_lt_of_lt j.2 hcl
    simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]
    rw [show bo.eval + n.eval * c + j = bo.eval + j + n.eval * c by omega]
    refine (hD.read_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hB j ⟨c, hcl⟩))) ?_).trans
      (hB j ⟨c, hcl⟩)
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCB h.symm with h | h <;> omega
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := σ.store) (p := p)
    (b := C)
    (off := (co + m * .var c).eval) (xs := Array.ofFn (MA *ᵥ fun j => MB j ⟨c, hcl⟩))
    fun i hi => by
      obtain ⟨N, hN, hlt⟩ := hCsh (m.eval * c + i) (by simp at hi; omega)
      exact ⟨N, hD.1 ▸ hN, by simp; omega⟩
  obtain ⟨σ', hrun, hst, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ := exec_gemv I hI hc p σ m n A ao
    B (bo + n * .var c) C (co + m * .var c) MA (fun j => MB j ⟨c, hcl⟩) hA' hx
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    s₁ hs₁
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] at hs₁
  refine ⟨σ', hrun, hpos, hcur, hcurW, hcnt, hpeak, hpeakW, _,
    hst ▸ hD.writeBlock hs₁ (by simp; omega), fun k hk => ?_⟩
  by_cases hkc : k < m.eval * c
  · rw [if_neg (by omega), hg k hkc]
  · have hi : k - m.eval * c < m.eval := by rw [Nat.mul_succ] at hk; omega
    rw [if_pos (by simp; omega), show k = (k - m.eval * c) + m.eval * c by omega,
      Nat.add_sub_cancel, getElem?_flatten _ ⟨_, hi⟩ ⟨c, hcl⟩, Array.getElem?_ofFn]
    simp [hi, Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- **`gemm` computes $\mathbf{A}\mathbf{B}$**: if buffers $A$ and $B$ hold the $m \times n$ and
$n \times l$ matrices $\mathbf{A}$, $\mathbf{B}$ from $\mathit{ao}$, $\mathit{bo}$, and the block
of $\mathbf{C}$ overlaps neither, the run writes $\mathbf{A}\mathbf{B}$ into the block of
$\mathbf{C}$ and nothing else, keeps the tape and the current memory, raises the peak by at
most one cell, and counts $lm$ literals and $lnm$ multiplications and additions.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_gemm (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ) (C : ℕ)
    (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (MB : Matrix (Fin n.eval) (Fin l.eval) 𝕜) (hA : Holds st.store p A ao.eval MA)
    (hB : Holds st.store p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (s₁ : Store P 𝕜) (h₁ : st.store.writeBlock p C co.eval (flatten (MA * MB)) = some s₁) :
    ∃ st', exec I (gemm p m n l A ao B bo C co).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + l.eval • (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  obtain ⟨hClt, hCsh⟩ := Level2.blockFacts (L := m.eval * l.eval) h₁ (by simp [size_flatten])
  rw [run_gemm, exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (n := l)
    (body := fun c => (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run)
    (fun c σ => σ.pos = st.pos ∧ σ.cur = st.cur ∧
      σ.curW = st.curW ∧ σ.cnt = st.cnt + c • (m.eval • Finsupp.single (.lit p) 1 +
        (n.eval * m.eval) • (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      σ.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      σ.peakW ≤ max st.peakW (st.curW + I.width p) ∧
      ∃ g, Store.BlockFrame st.store p st.store.size C co.eval (m.eval * l.eval) σ.store g ∧
        ∀ k < m.eval * c, g k = (flatten (MA * MB))[k]?)
    ⟨rfl, rfl, rfl, by simp, fun q => ?_, le_max_left _ _, _,
      ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, by simp⟩ ?_).imp ?_
  · by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · rintro c hcl σ ⟨hpos, hcur, hcurW, hcnt, hpeak, hpeakW, g, hD, hg⟩
    obtain ⟨σ', hrun, hpos', hcur', hcurW', hcnt', hpeak', hpeakW', g', hD', hg'⟩ :=
      exec_gemm_step I hI hc p st m n l A ao B bo C co MA MB hA hB hCA hCB hCsh hcl σ g hD hg
    refine ⟨σ', hrun, hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW, ?_, fun q => ?_,
      ?_, g', hD', hg'⟩
    · rw [hcnt', hcnt, succ_nsmul, add_assoc]
    · rw [hpeak', hcur]
      by_cases hq : q = p
      · rw [hq, Function.update_self, Function.update_self]
        exact max_le ((hpeak p).trans_eq (Function.update_self _ _ _)) (le_max_right _ _)
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact (hpeak q).trans_eq (Function.update_of_ne hq _ _)
    · rw [hpeakW', hcurW]
      exact max_le hpeakW (le_max_right _ _)
  · rintro σ ⟨hrun, hpos, hcur, hcurW, hcnt, hpeak, hpeakW, g, hD, hg⟩
    refine ⟨hrun, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
    have := (hD.push (p, Array.replicate 1 none) hClt).pop_eq h₁ (by simp [size_flatten]) hg
    simpa using this

end Specs

end NLAlib.Computation
