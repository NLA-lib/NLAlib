/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Model

/-!
# The dense implementation of an oracle

A dense $N \times N$ matrix held as read-only data of size $N^2$ at a tag, column-major, and
counted as constant memory (D14). `NLAlib.Computation.denseImpl` serves an oracle call column by
column, as `gemm` on read-only data: it zeroes the destination column and, for each entry
$(i, j)$, reads $\mathbf{A}_{i,j}$, multiplies it by source entry $j$ and adds it into destination
entry $i$. Each matrix-vector product costs $N^2$ multiplications, additions and reads and $N$
literals (`NLAlib.Computation.denseCost`), with one scratch cell. The certificate
`NLAlib.Computation.implementsOracle_denseImpl` makes it a valid substitution for the exact
oracle (through `NLAlib.Computation.RunsWithin.substOracle`). The implementation is generic in its
sizes: it takes no host data. Design: `docs/design/Computation.md` (D4, D14).

## Main definitions

* `NLAlib.Computation.denseImpl`, `NLAlib.Computation.denseInterp`,
  `NLAlib.Computation.denseCost`.

## Main results

* `NLAlib.Computation.implementsOracle_denseImpl`: the certificate.
* `NLAlib.Computation.ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl`: a matrix-free
  result gives the stored-entries result of the program served by `denseImpl`.
-/

@[expose] public section

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The dense implementation of an oracle call**: for each of the `cols` columns, zero the
destination column, then for each $j$ and $i$ read entry $i + Nj$ of the read-only data, multiply
it by source entry $j$ and add it into destination entry $i$. One scratch cell. -/
def denseImpl {VB VI : Type} (N : IExp VI) (_o : ι) (p : P) (dst : VB) (dOff : IExp VI)
    (src : VB) (sOff : IExp VI) (cols : IExp VI) : Stmt P ι VB VI :=
  Builder.run <| Builder.named "dense_apply"
      [.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols] do
    let t ← Builder.alloc p 1
    Builder.forRange cols fun c => do
      Builder.forRange N fun i => Builder.ins (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)
      Builder.forRange N fun j => Builder.forRange N fun i => do
        Builder.stmt (.rom p ⟨t, 0⟩ (.var i + N * .var j))
        Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .var j + N * .var c⟩)
        Builder.ins (.bin p .add ⟨dst, dOff + .var i + N * .var c⟩
          ⟨dst, dOff + .var i + N * .var c⟩ ⟨t, 0⟩)

/-- The interpretation with $\mathbf{A}$ as read-only data of size $N^2$ at tag `p₀`,
column-major, and no oracle: the stored-entries interpretation `storedInterp` of the entries of
`flatten A`. -/
noncomputable def denseInterp {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p₀ : P) : Interp P ι 𝕜 (OpCount P ι) :=
  storedInterp (N * N) (fun e => (flatten A).getD e 0) ξ p₀

/-- The cost of the dense implementation: a matrix-vector product at tag $p$ is $N^2$
multiplications, additions and read-only reads and $N$ literals at $p$; a load costs nothing. -/
noncomputable def denseCost (N : ℕ) : OpKind P ι → OpCount P ι
  | .matvec p _ => Finsupp.single (.bin p .mul) (N * N) + Finsupp.single (.bin p .add) (N * N) +
      Finsupp.single (.rom p) (N * N) + Finsupp.single (.lit p) N
  | _ => 0

/-! ### The steps of the run -/

namespace Dense

section Steps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T dst src N L : ℕ}
  {dOff sOff : IExp ℕ}

/-- One step of the product: read $\mathbf{A}_{i,j}$, multiply by source entry $j$, add into
destination entry $i$. -/
private theorem exec_denseStep (hsem : I.sem = exactSem) (hc : IsUnitCharge I)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j c : ℕ} {a x w : 𝕜}
    (h : Store.BlockFrame s₀ p T dst dOff.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1))
    (hdT : dst ≠ T) (hsT : src ≠ T) (hm : i + N * c < L)
    (hdst : ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + (i + N * c) < n)
    (hrom : I.rom (i + N * j) = some a) (hx : s₀.read p src (sOff.eval + j + N * c) = some x)
    (hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
      sOff.eval + j + N * c < dOff.eval + L))
    (hw : g (i + N * c) = some w) :
    ∃ s', exec I (.seq (.rom p ⟨T, .const 0⟩ (.add (.var i) (.mul (.const N) (.var j))))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.var j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) .skip)))
        σ = some { σ with
          store := s', cnt := σ.cnt + (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval L s'
        (Function.update g (i + N * c) (some (w + a * x))) := by
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some a hT one_pos
  have h₁' := h.write_scratch (fun _ => hdT) h₁
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (a * x) hT one_pos
  have h₂' := h₁'.write_scratch (fun _ => hdT) h₂
  obtain ⟨n, hdsh, hdlt⟩ := hdst
  obtain ⟨s₃, h₃⟩ := h₂'.exists_write_eq_some (w + a * x) hdsh hdlt
  refine ⟨s₃, ?_, h₂'.write_of_lt hm h₃⟩
  have rx : s₁.read p src (sOff.eval + j + N * c) = some x := by
    rw [h₁'.read_of_ne hsT (by tauto), hx]
  have rw₂ : s₂.read p dst (dOff.eval + i + N * c) = some w := by
    rw [Nat.add_assoc, h₂'.2.2 _ hm, hw]
  rw [← Nat.add_assoc] at h₃
  simp only [exec, Instr.run, Instr.kind, IExp.eval, hrom, hsem, hc.charge_eq, h₁, Option.bind_some,
    Option.map_some, Store.read_of_write_eq_some h₁, rx, exactSem, h₂,
    Store.read_of_write_eq_some h₂, rw₂, h₃, Option.some.injEq]
  simp only [add_assoc]

/-- The facts about a dense oracle call that every step uses. -/
private structure DenseCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T dst src N cols : ℕ) (dOff sOff : IExp ℕ) (a x : ℕ → ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : IsUnitCharge I
  scratch : s₀.shape[T]? = some (p, 1)
  dst_ne : 0 < N * cols → dst ≠ T
  src_ne : 0 < N * cols → src ≠ T
  dst_shape : ∀ m < N * cols, ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + m < n
  rom_eq : ∀ i < N, ∀ j < N, I.rom (i + N * j) = some (a i j)
  src_read : ∀ c < cols, ∀ j < N, s₀.read p src (sOff.eval + j + N * c) = some (x c j)
  disj : dst ≠ src ∨ dOff.eval + N * cols ≤ sOff.eval ∨ sOff.eval + N * cols ≤ dOff.eval

variable {cols : ℕ} {a x : ℕ → ℕ → 𝕜} {G : ℕ → Option 𝕜}

/-- One sweep over the rows: add $\mathbf{A}_{i,j} x_j$ into every destination entry $i$. -/
private theorem exec_denseRow (hC : DenseCtx I s₀ p T dst src N cols dOff sOff a x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j c : ℕ} (hj : j < N) (hc : c < cols)
    (hcL : N * c + N ≤ N * cols) (h : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ.store g)
    (hg : ∀ i < N, g (i + N * c) = some (∑ j' ∈ Finset.range j, a i j' * x c j'))
    (hG : ∀ m < N * c, g m = G m) :
    ∃ σ', exec I (.loop (.const N) fun i =>
        .seq (.rom p ⟨T, .const 0⟩ (.add (.var i) (.mul (.const N) (.var j))))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.var j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) .skip)))
        σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + N • (.single (.rom p) 1 +
          .single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
        (∀ i < N, g' (i + N * c) = some (∑ j' ∈ Finset.range (j + 1), a i j' * x c j')) ∧
        ∀ m < N * c, g' m = G m := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g',
        σ' = { σ with store := s', cnt := σ.cnt + i' • (.single (.rom p) 1 +
          .single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
      (∀ i < N, g' (i + N * c) = some (∑ j' ∈ Finset.range (if i < i' then j + 1 else j),
        a i j' * x c j')) ∧ ∀ m < N * c, g' m = G m)
      ⟨σ.store, g, by simp, h, by simpa using hg, hG⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow, hG'⟩ =>
      ⟨hrun, s', g', hσ, hI, fun i hi => by simpa [hi] using hrow i hi, hG'⟩
  rintro i' (hi' : i' < N) σ' ⟨s, g', hσ, hI, hrow, hG'⟩
  replace hI : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ'.store g' := hσ ▸ hI
  have hm : i' + N * c < N * cols := by omega
  have hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
      sOff.eval + j + N * c < dOff.eval + N * cols) := by
    rcases hC.disj with h | h | h
    · exact fun h' => h h'.1.symm
    · omega
    · omega
  obtain ⟨s'', hrun, hI'⟩ := exec_denseStep hC.sem hC.charge hI hC.scratch
    (hC.dst_ne (by omega)) (hC.src_ne (by omega)) hm (hC.dst_shape _ hm) (hC.rom_eq i' hi' j hj)
    (hC.src_read c hc j hj) hsrc (by simpa using hrow i' hi')
  refine ⟨_, hrun, s'', _, ?_, hI', fun i hi => ?_, fun m hm' => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp [Finset.sum_range_succ]
    · rw [Function.update_of_ne (by omega), hrow i hi]
      have : (i < i' + 1) = (i < i') := by
        apply propext
        omega
      simp only [this]
  · rw [Function.update_of_ne (by omega), hG' m hm']

/-- The zero sweep: write $0$ into every destination entry of column `c`. -/
private theorem exec_denseZero (hC : DenseCtx I s₀ p T dst src N cols dOff sOff a x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {c : ℕ} (hcL : N * c + N ≤ N * cols)
    (h : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ.store g) (hG : ∀ m < N * c, g m = G m) :
    ∃ σ', exec I (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + N • .single (.lit p) 1 } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
        (∀ i < N, g' (i + N * c) = some 0) ∧
        ∀ m < N * c, g' m = G m := by
  refine exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g',
      σ' = { σ with store := s', cnt := σ.cnt + (i' • .single (.lit p) 1) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
      (∀ i < i', g' (i + N * c) = some 0) ∧ ∀ m < N * c, g' m = G m)
    ⟨σ.store, g, by simp, h, by simp, hG⟩ ?_
  rintro i' (hi' : i' < N) σ' ⟨s, g', hσ, hI, hrow, hG'⟩
  replace hI : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ'.store g' := hσ ▸ hI
  have hm : i' + N * c < N * cols := by omega
  obtain ⟨n, hdsh, hdlt⟩ := hC.dst_shape _ hm
  obtain ⟨s'', hw⟩ := hI.exists_write_eq_some 0 hdsh hdlt
  refine ⟨{ σ' with store := s'', cnt := σ'.cnt + .single (.lit p) 1 }, ?_, s'', _, ?_,
    hI.write_of_lt hm hw, fun i hi => ?_, fun m hm' => ?_⟩
  · rw [← Nat.add_assoc] at hw
    simp only [exec, Instr.run, Instr.kind, IExp.eval, hC.sem, hC.charge.charge_eq, exactSem,
      Rat.cast_zero, Option.bind_some, hw, Option.map_some]
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp
    · rw [Function.update_of_ne (by omega)]
      exact hrow i (by omega)
  · rw [Function.update_of_ne (by omega), hG' m hm']

/-- One column of the product: zero the destination column, then add each column of
$\mathbf{A}$ scaled by its source entry. -/
private theorem exec_denseCol (hC : DenseCtx I s₀ p T dst src N cols dOff sOff a x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {c : ℕ} (hc : c < cols)
    (h : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ.store g) (hG : ∀ m < N * c, g m = G m)
    (hY : ∀ i < N, G (i + N * c) = some (∑ j ∈ Finset.range N, a i j * x c j)) :
    ∃ σ', exec I (.seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (.seq (.loop (.const N) fun j => .seq (.loop (.const N) fun i =>
        .seq (.rom p ⟨T, .const 0⟩ (.add (.var i) (.mul (.const N) (.var j))))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.var j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) .skip)))
        .skip) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (N • .single (.lit p) 1 + N • (N •
          (.single (.rom p) 1 + .single (.bin p .mul) 1 + .single (.bin p .add) 1))) } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧ ∀ m < N * (c + 1), g' m = G m := by
  have hcL : N * c + N ≤ N * cols := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hc
  obtain ⟨σ₁, h₁, s₁, g₁, rfl, hI₁, hrow₁, hG₁⟩ := exec_denseZero hC hcL h hG
  rw [exec_seq_of_exec_eq_some I h₁, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun j' σ' => ∃ s' g',
      σ' = { σ with store := s', cnt := σ.cnt + (N • .single (.lit p) 1 +
        j' • (N • (.single (.rom p) 1 + .single (.bin p .mul) 1 + .single (.bin p .add) 1))) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
      (∀ i < N, g' (i + N * c) = some (∑ j ∈ Finset.range j', a i j * x c j)) ∧
      ∀ m < N * c, g' m = G m) ⟨s₁, g₁, by simp, hI₁, by simpa using hrow₁, hG₁⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow, hG'⟩ => ⟨hrun, s', g', hσ, hI, fun m hm => ?_⟩
  · rintro j (hj : j < N) σ' ⟨s, g', hσ, hI, hrow, hG'⟩
    replace hI : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ'.store g' := hσ ▸ hI
    obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow', hG''⟩ := exec_denseRow hC hj hc hcL hI hrow hG'
    refine ⟨_, by rw [exec_seq_skip, hrun], s'', g'', ?_, hI', hrow', hG''⟩
    subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hmc : m < N * c
    · exact hG' m hmc
    · have hi : m - N * c < N := by rw [Nat.mul_succ] at hm; omega
      have hm' : m = (m - N * c) + N * c := by omega
      rw [hm', hrow _ hi, hY _ hi]
      rfl

/-- All the columns of the product. -/
private theorem exec_denseCols {colsE : IExp ℕ}
    (hC : DenseCtx I s₀ p T dst src N colsE.eval dOff sOff a x) {σ : St P 𝕜 (OpCount P ι)}
    {g : ℕ → Option 𝕜} (h : Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) σ.store g)
    (hY : ∀ c < colsE.eval, ∀ i < N,
      G (i + N * c) = some (∑ j ∈ Finset.range N, a i j * x c j)) :
    ∃ σ', exec I (.loop colsE fun c => .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (.seq (.loop (.const N) fun j => .seq (.loop (.const N) fun i =>
        .seq (.rom p ⟨T, .const 0⟩ (.add (.var i) (.mul (.const N) (.var j))))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.var j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) .skip)))
        .skip) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + colsE.eval • (N • .single (.lit p) 1 +
          N • (N • (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1))) } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧
        ∀ m < N * colsE.eval, g' m = G m := by
  refine exists_exec_loop_eq_some_of_forall I (fun c' σ' => ∃ s' g',
      σ' = { σ with store := s', cnt := σ.cnt + c' • (N • .single (.lit p) 1 +
        N • (N • (.single (.rom p) 1 + .single (.bin p .mul) 1 + .single (.bin p .add) 1))) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧ ∀ m < N * c', g' m = G m)
    ⟨σ.store, g, by simp, h, by simp⟩ ?_
  rintro c hc σ' ⟨s, g', hσ, hI, hG'⟩
  replace hI : Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hG''⟩ := exec_denseCol hC hc hI hG' (hY c hc)
  refine ⟨_, hrun, s'', g'', ?_, hI', hG''⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

end Steps

/-- Entry $(i, c)$ of the product, as the sum the run computes. -/
private theorem getElem?_flatten_mul {N cols : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (X : Array 𝕜) :
    ∀ c < cols, ∀ i < N, (flatten (A * unflatten N cols X))[i + N * c]? =
      some (∑ j ∈ Finset.range N,
        (fun i j => if h : i < N ∧ j < N then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) i j *
          (fun c j => X[j + N * c]?.getD 0) c j) := by
  intro c hc i hi
  rw [getElem?_flatten _ ⟨i, hi⟩ ⟨c, hc⟩, Matrix.mul_apply]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [unflatten, hi, j.2, Array.getD_eq_getD_getElem?]

end Dense

/-- Entry $i + Nj$ of the read-only data of `denseInterp A` is $\mathbf{A}_{i,j}$. -/
private theorem rom_denseInterp {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p₀ : P) {i j : ℕ} (hi : i < N) (hj : j < N) :
    (denseInterp (ι := ι) A ξ p₀).rom (i + N * j) = some (A ⟨i, hi⟩ ⟨j, hj⟩) := by
  change (if i + N * j < N * N then some ((flatten A).getD (i + N * j) 0) else none) = _
  rw [if_pos (Nat.add_mul_lt_mul_of_lt_of_lt hi hj), Array.getD_eq_getD_getElem?,
    getElem?_flatten A ⟨i, hi⟩ ⟨j, hj⟩]
  rfl

/-- **The dense certificate**: `denseImpl` implements the exact oracle of $\mathbf{A}$ under
`denseInterp`, at the cost `denseCost` of each matrix-vector product, every other kind kept, with
one scratch cell and no bit scratch. No printed source.
Result: dense-oracle-certificate -/
theorem implementsOracle_denseImpl {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p₀ : P) :
    ImplementsOracle (exactInterp (P := P) (ι := ι) (fun _ => A) ξ) (denseInterp A ξ p₀)
      (fun o p dst dOff src sOff cols => denseImpl (.const N) o p dst dOff src sOff cols)
      (substKind (denseCost N)) (fun _ => 1) 0 := by
  intro o p dst dOff src sOff cols st X Y s₁ hdisj hX hY hs₁
  change dst ≠ src ∨ dOff.eval + N * cols.eval ≤ sOff.eval ∨
    sOff.eval + N * cols.eval ≤ dOff.eval at hdisj
  change st.store.readBlock p src sOff.eval (N * cols.eval) = some X at hX
  change matOracle A cols.eval X = some Y at hY
  unfold matOracle at hY
  split_ifs at hY with hXs
  cases hY
  have hXr := fun m (hm : m < N * cols.eval) => Store.read_of_readBlock_eq_some_of_lt hX hm
  set Y := flatten (A * unflatten N cols.eval X) with hYdef
  have hYs : Y.size = N * cols.eval := size_flatten _
  set s₀ : Store P 𝕜 := st.store.push (p, Array.replicate (IExp.const 1).eval none) with hs₀
  have hsrc : 0 < N * cols.eval → src < st.store.size := Store.lt_size_of_readBlock_eq_some hX
  have hdstlt : 0 < N * cols.eval → dst < st.store.size := fun h =>
    Store.lt_size_of_writeBlock_eq_some hs₁ (hYs ▸ h)
  have hdst : ∀ m < N * cols.eval, ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + m < n :=
    fun m hm => (Store.exists_getElem?_shape_of_writeBlock_eq_some hs₁ (hYs ▸ hm)).imp fun n h =>
      ⟨by rw [hs₀, Store.getElem?_shape_push_of_lt _ (hdstlt (by omega))]; exact h.1, h.2⟩
  have hC : Dense.DenseCtx (denseInterp (ι := ι) A ξ p₀) s₀ p st.store.size dst src N cols.eval
      dOff sOff
      (fun i j => if h : i < N ∧ j < N then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
      (fun c j => X[j + N * c]?.getD 0) :=
    { sem := rfl
      charge := fun _ => rfl
      scratch := Store.getElem?_shape_push_size _ _ _
      dst_ne := fun h => Nat.ne_of_lt (hdstlt h)
      src_ne := fun h => Nat.ne_of_lt (hsrc h)
      dst_shape := hdst
      rom_eq := fun i hi j hj => by
        rw [rom_denseInterp A ξ p₀ hi hj]
        simp [hi, hj]
      src_read := fun c hc j hj => by
        have hm : j + N * c < N * cols.eval := Nat.add_mul_lt_mul_of_lt_of_lt hj hc
        rw [hs₀, Store.read_push_of_lt (hsrc (by omega)), Nat.add_assoc, hXr _ hm,
          Array.getElem?_eq_getElem (by omega)]
        simp
      disj := hdisj }
  have hYc := Dense.getElem?_flatten_mul A X (cols := cols.eval)
  have hprog : denseImpl (P := P) (ι := ι) (.const N) o p dst dOff src sOff cols =
      .seq (.named "dense_apply" [.idx (.const N), .buf dst, .idx dOff, .buf src, .idx sOff,
        .idx cols] (.alloc p (.const 1) fun t => .seq (.loop cols fun c =>
      .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (.seq (.loop (.const N) fun j => .seq (.loop (.const N) fun i =>
        .seq (.rom p ⟨t, .const 0⟩ (.add (.var i) (.mul (.const N) (.var j))))
        (.seq (.instr (.bin p .mul ⟨t, .const 0⟩ ⟨t, .const 0⟩
          ⟨src, .add (.add sOff (.var j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ ⟨t, .const 0⟩)) .skip)))
        .skip) .skip)) .skip)) .skip := rfl
  beta_reduce
  rw [hprog, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Dense.exec_denseCols hC
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (IExp.const 1).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (IExp.const 1).eval))
      curW := st.curW + (IExp.const 1).eval * (denseInterp (ι := ι) A ξ p₀).width p
      peakW := max st.peakW (st.curW + (IExp.const 1).eval *
        (denseInterp (ι := ι) A ξ p₀).width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ hYc
  rw [hF, Option.map_some]
  refine ⟨_, rfl, hIF.pop_eq hs₁ hYs hgF, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [denseInterp, storedInterp]
  · refine le_of_eq (congrArg (st.cnt + ·) ?_)
    simp only [substKind, denseCost, zero_add, smul_add, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    abel
  · intro q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [denseInterp, storedInterp]

omit [DecidableEq P] in
/-- Entry $e < N^2$ of the flattened matrix with entries $v_{i + Nj}$ is $v_e$. -/
private theorem getD_flatten_of_lt {N : ℕ} (vals : ℕ → 𝕜) {e : ℕ} (he : e < N * N) :
    (flatten (Matrix.of fun (i j : Fin N) => vals (i + N * j))).getD e 0 = vals e := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
  have h := getElem?_flatten (Matrix.of fun (i j : Fin N) => vals (i + N * j))
    ⟨e % N, Nat.mod_lt _ hN⟩ ⟨e / N, Nat.div_lt_of_lt_mul he⟩
  simp only [Nat.mod_add_div, Matrix.of_apply] at h
  rw [Array.getD_eq_getD_getElem?, h]
  rfl

/-- **Matrix-free to dense**: a matrix-free result gives the stored-entries result for the
program with its oracle calls served by `denseImpl` from $N^2$ stored entries $v$, column-major:
the matrix is $(v_{i + Nj})_{i, j}$, each matrix-vector product costs $N^2$ multiplications,
additions and reads and $N$ literals and each load nothing (`denseCost`), and the memory grows by
one scratch cell and the $N^2$ stored entries. The final state has the store, tape positions and
current memory of a final state of the matrix-free run. No printed source.
Result: matrix-free-dense-substitution -/
theorem ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl {r b : ℕ} {p : P}
    {prog : ProgFamily P ι r b} {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜)}
    {cost : ℕ → (Fin r → ℕ) → OpCount P ι} {mem : ℕ → (Fin r → ℕ) → P → ℕ}
    {post : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 →
      (Dist → ℕ → ℝ) → St P 𝕜 (OpCount P ι) → Prop}
    (h : ProgFamily.MatrixFree p prog valid X inputs cost mem post) :
    ProgFamily.StoredEntries p (prog.substOracle fun _ _ N => denseImpl N) valid X inputs
      (fun N _ => N * N)
      (fun N n => substCount (denseCost N) (cost N n))
      (fun N n q => mem N n q + 1 + if q = p then N * N else 0)
      (fun N n x vals ξ st' => ∃ st, post N n x (Matrix.of fun i j => vals (i + N * j)) ξ st ∧
        st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur) := by
  intro N n hv x vals ξ
  have hI : denseInterp (ι := ι) (Matrix.of fun (i j : Fin N) => vals (i + N * j)) ξ p =
      storedInterp (N * N) vals ξ p := by
    simp only [denseInterp, storedInterp, Interp.mk.injEq, true_and, and_true]
    funext e
    split_ifs with he
    · rw [getD_flatten_of_lt vals he]
    · rfl
  rw [← hI]
  exact RunsWithin.substOracle
    (I := exactInterp (fun _ => Matrix.of fun (i j : Fin N) => vals (i + N * j)) ξ)
    (I' := denseInterp _ ξ p) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)
    (fun _ _ _ => rfl) (implementsOracle_denseImpl _ ξ p) rfl (fun _ => le_rfl) le_rfl
    (h N n hv x _ ξ)

end NLAlib.Computation
