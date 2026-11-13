/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Model

/-!
# The coordinate (COO) implementation of an oracle

A sparse matrix in coordinate form: a pattern of `nnz` positions $(i, j)$, unrolled into the
implementation as host data, and the values `vals`, held as read-only data of size `nnz` at a tag
and counted as constant memory (D14). `NLAlib.Computation.cooImpl` serves an oracle call column
by column: it zeroes the destination column and, for each stored entry, reads its value, multiplies
it by the source entry and adds it into the destination. Each matrix-vector product costs `nnz`
multiplications, additions and reads and $N$ literals (`NLAlib.Computation.cooCost`), with one
scratch cell. The certificate `NLAlib.Computation.implementsOracle_cooImpl` makes it a valid
substitution for the exact oracle of `NLAlib.Computation.cooMatrix` (through
`NLAlib.Computation.RunsWithin.substOracle`). The index storage of the pattern is host data and
is not counted. Design: `docs/design/Computation.md` (D4, D14).

## Main definitions

* `NLAlib.Computation.cooImpl`, `NLAlib.Computation.cooMatrix`, `NLAlib.Computation.cooInterp`,
  `NLAlib.Computation.cooCost`.

## Main results

* `NLAlib.Computation.implementsOracle_cooImpl`: the certificate.
* `NLAlib.Computation.ProgFamily.MatrixFree.storedEntries_substOracle_cooImpl`: a matrix-free
  result gives the stored-entries result of the program served by `cooImpl`.
-/

@[expose] public section

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The COO implementation of an oracle call**: for each of the `cols` columns, zero the
destination column, then for each entry $e$ of the pattern at position $(i, j)$ read value $e$ of
the read-only data, multiply it by source entry $j$ and add it into destination entry $i$. One
scratch cell. The pattern is host data, unrolled into the program. -/
def cooImpl {VB VI : Type} (N : IExp VI) (pattern : List (ℕ × ℕ)) (_o : ι) (p : P) (dst : VB)
    (dOff : IExp VI) (src : VB) (sOff : IExp VI) (cols : IExp VI) : Stmt P ι VB VI :=
  Builder.run <| Builder.named "coo_apply"
      [.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols] do
    let t ← Builder.alloc p 1
    Builder.forRange cols fun c => do
      Builder.forRange N fun i => Builder.ins (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)
      pattern.zipIdx.forM fun ((i, j), e) => do
        Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
        Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .const j + N * .var c⟩)
        Builder.ins (.bin p .add ⟨dst, dOff + .const i + N * .var c⟩
          ⟨dst, dOff + .const i + N * .var c⟩ ⟨t, 0⟩)

/-- The $N \times N$ matrix of a pattern and values: entry $(i, j)$ is the sum of the values of
the pattern entries at position $(i, j)$ (repeated positions add up). -/
def cooMatrix {N : ℕ} (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j => ∑ e ∈ Finset.range pattern.length,
    if pattern[e]? = some (i.1, j.1) then vals e else 0

/-- The interpretation with the COO values as read-only data of size `nnz` at tag `p₀`, and no
oracle: the stored-entries interpretation `storedInterp` of the first `nnz` values. -/
noncomputable def cooInterp (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) (p₀ : P) :
    Interp P ι 𝕜 (OpCount P ι) :=
  storedInterp pattern.length vals ξ p₀

/-- The cost of the COO implementation: a matrix-vector product at tag $p$ is `nnz`
multiplications, additions and read-only reads and $N$ literals at $p$; a load costs nothing. -/
noncomputable def cooCost (N nnz : ℕ) : OpKind P ι → OpCount P ι
  | .matvec p _ => Finsupp.single (.bin p .mul) nnz + Finsupp.single (.bin p .add) nnz +
      Finsupp.single (.rom p) nnz + Finsupp.single (.lit p) N
  | _ => 0

/-! ### The steps of the run -/

namespace Sparse

section Steps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T dst src N L : ℕ}
  {dOff sOff : IExp ℕ}

/-- One stored entry $(i, j)$ with value $a$: multiply it by source entry $j$, add into
destination entry $i$, then run `t`. -/
private theorem exec_cooStep (hsem : I.sem = exactSem) (hc : IsUnitCharge I)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j c e : ℕ} {a x w : 𝕜}
    (t : Stmt P ι ℕ ℕ)
    (h : Store.BlockFrame s₀ p T dst dOff.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1))
    (hdT : dst ≠ T) (hsT : src ≠ T) (hm : i + N * c < L)
    (hdst : ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + (i + N * c) < n)
    (hrom : I.rom e = some a) (hx : s₀.read p src (sOff.eval + j + N * c) = some x)
    (hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
      sOff.eval + j + N * c < dOff.eval + L))
    (hw : g (i + N * c) = some w) :
    ∃ s', exec I (.seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) t)))
        σ = exec I t { σ with
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
    Store.read_of_write_eq_some h₂, rw₂, h₃]
  simp only [add_assoc]

/-- The facts about a COO oracle call that every step uses. -/
private structure CooCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T dst src N cols : ℕ) (dOff sOff : IExp ℕ) (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜)
    (x : ℕ → ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : IsUnitCharge I
  scratch : s₀.shape[T]? = some (p, 1)
  dst_ne : 0 < N * cols → dst ≠ T
  src_ne : 0 < N * cols → src ≠ T
  dst_shape : ∀ m < N * cols, ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + m < n
  rom_eq : ∀ e < pattern.length, I.rom e = some (vals e)
  src_read : ∀ c < cols, ∀ j < N, s₀.read p src (sOff.eval + j + N * c) = some (x c j)
  disj : dst ≠ src ∨ dOff.eval + N * cols ≤ sOff.eval ∨ sOff.eval + N * cols ≤ dOff.eval
  pat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N

/-- The contribution of pattern entry `e` to destination row `i`. -/
private def cooTerm (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) (x : ℕ → 𝕜) (i e : ℕ) : 𝕜 :=
  match pattern[e]? with
  | some (i', j) => if i' = i then vals e * x j else 0
  | none => 0

variable {cols : ℕ} {pattern : List (ℕ × ℕ)} {vals : ℕ → 𝕜} {x : ℕ → ℕ → 𝕜}
  {G : ℕ → Option 𝕜}

/-- The zero sweep: write $0$ into every destination entry of column `c`. -/
private theorem exec_cooZero (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
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

/-- The stored entries from position `k₀` on, unrolled. -/
private theorem exec_cooEntries (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
    {c : ℕ} (hc : c < cols) (hcL : N * c + N ≤ N * cols)
    (F : (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ())))) :
    ∀ (l : List (ℕ × ℕ)) (k₀ : ℕ) (σ : St P 𝕜 (OpCount P ι)) (g : ℕ → Option 𝕜),
      (∀ e < l.length, pattern[k₀ + e]? = l[e]?) → k₀ + l.length = pattern.length →
      Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ.store g →
      (∀ i < N, g (i + N * c) =
        some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e)) →
      (∀ m < N * c, g m = G m) →
      ∃ σ', exec I (Builder.run (List.forM (l.zipIdx k₀) F)) σ = some σ' ∧
        ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + l.length • (.single (.rom p) 1 +
            .single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
          Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧
          (∀ i < N, g' (i + N * c) =
            some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) ∧
          ∀ m < N * c, g' m = G m
  | [], k₀, σ, g, _, hlen, h, hg, hG => by
    simp only [List.length_nil, add_zero] at hlen
    subst hlen
    exact ⟨σ, rfl, σ.store, g, by simp, h, hg, hG⟩
  | (i, j) :: l, k₀, σ, g, hl, hlen, h, hg, hG => by
    have hk₀ : pattern[k₀]? = some (i, j) := by simpa using hl 0 (by simp)
    obtain ⟨hi, hj⟩ := hC.pat (i, j) (List.mem_of_getElem? hk₀)
    have hk₀' : k₀ < pattern.length := (List.getElem?_eq_some_iff.mp hk₀).1
    have hm : i + N * c < N * cols := by omega
    have hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
        sOff.eval + j + N * c < dOff.eval + N * cols) := by
      rcases hC.disj with h | h | h
      · exact fun h' => h h'.1.symm
      · omega
      · omega
    obtain ⟨s', hrun, hI'⟩ := exec_cooStep hC.sem hC.charge
      (Builder.run (List.forM (l.zipIdx (k₀ + 1)) F)) h hC.scratch (hC.dst_ne (by omega))
      (hC.src_ne (by omega)) hm
      (hC.dst_shape _ hm) (hC.rom_eq k₀ hk₀') (hC.src_read c hc j hj) hsrc (hg i hi)
    have hrow' : ∀ i' < N, Function.update g (i + N * c)
        (some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e + vals k₀ * x c j))
        (i' + N * c) = some (∑ e ∈ Finset.range (k₀ + 1), cooTerm pattern vals (x c) i' e) := by
      intro i' hi'
      rw [Finset.sum_range_succ]
      by_cases hii : i' = i
      · subst hii
        simp [cooTerm, hk₀]
      · rw [Function.update_of_ne (by omega), hg i' hi']
        simp [cooTerm, hk₀, Ne.symm hii]
    have hG' : ∀ m < N * c, Function.update g (i + N * c)
        (some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e + vals k₀ * x c j)) m =
          G m := fun m hm' => by
      rw [Function.update_of_ne (by omega), hG m hm']
    obtain ⟨σ'', hrun', s'', g'', hσ'', hI'', hrow'', hG''⟩ := exec_cooEntries hC hc hcL F hF l
      (k₀ + 1) { σ with store := s', cnt := σ.cnt + (.single (.rom p) 1 +
        .single (.bin p .mul) 1 + .single (.bin p .add) 1) } _ (fun e he => by
        have := hl (e + 1) (by simp; omega)
        rw [show k₀ + 1 + e = k₀ + (e + 1) by omega, this]
        simp)
      (by simp at hlen; omega) hI' hrow' hG'
    refine ⟨σ'', ?_, s'', g'', ?_, hI'', hrow'', hG''⟩
    · rw [List.zipIdx_cons]
      change exec I (ContT.run (m := Id) (F ((i, j), k₀))
        fun _ => Builder.run (List.forM (l.zipIdx (k₀ + 1)) F)) σ = _
      rw [hF, hrun, hrun']
    · rw [hσ'']
      simp only [List.length_cons, succ_nsmul', add_assoc]

/-- One column of the product: zero the destination column, then run the stored entries. -/
private theorem exec_cooCol (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {c : ℕ} (hc : c < cols)
    (F : (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ()))))
    (h : Store.BlockFrame s₀ p T dst dOff.eval (N * cols) σ.store g) (hG : ∀ m < N * c, g m = G m)
    (hY : ∀ i < N, G (i + N * c) =
      some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) :
    ∃ σ', exec I (.seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx F))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (N • .single (.lit p) 1 +
          pattern.length • (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1)) } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * cols) s' g' ∧ ∀ m < N * (c + 1), g' m = G m := by
  have hcL : N * c + N ≤ N * cols := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hc
  obtain ⟨σ₁, h₁, s₁, g₁, rfl, hI₁, hrow₁, hG₁⟩ := exec_cooZero hC hcL h hG
  rw [exec_seq_of_exec_eq_some I h₁]
  obtain ⟨σ₂, h₂, s₂, g₂, rfl, hI₂, hrow₂, hG₂⟩ := exec_cooEntries hC hc hcL F hF pattern 0
    { σ with store := s₁, cnt := σ.cnt + N • .single (.lit p) 1 } g₁
    (by simp) (by simp) hI₁ (by simpa using hrow₁) hG₁
  refine ⟨_, h₂, s₂, g₂, by simp only [add_assoc], hI₂, fun m hm => ?_⟩
  by_cases hmc : m < N * c
  · exact hG₂ m hmc
  · have hi : m - N * c < N := by rw [Nat.mul_succ] at hm; omega
    have hm' : m = (m - N * c) + N * c := by omega
    rw [hm', hrow₂ _ hi, hY _ hi]

/-- All the columns of the product. -/
private theorem exec_cooCols {colsE : IExp ℕ}
    (hC : CooCtx I s₀ p T dst src N colsE.eval dOff sOff pattern vals x)
    (F : ℕ → (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ c i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F c ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ()))))
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) σ.store g)
    (hY : ∀ c < colsE.eval, ∀ i < N, G (i + N * c) =
      some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) :
    ∃ σ', exec I (.loop colsE fun c => .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx (F c)))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + colsE.eval • (N • .single (.lit p) 1 +
          pattern.length • (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1)) } ∧
        Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧
        ∀ m < N * colsE.eval, g' m = G m := by
  refine exists_exec_loop_eq_some_of_forall I (fun c' σ' => ∃ s' g',
      σ' = { σ with store := s', cnt := σ.cnt + c' • (N • .single (.lit p) 1 +
        pattern.length • (.single (.rom p) 1 +
        .single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
      Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧
      ∀ m < N * c', g' m = G m) ⟨σ.store, g, by simp, h, by simp⟩ ?_
  rintro c hc σ' ⟨s, g', hσ, hI, hG'⟩
  replace hI : Store.BlockFrame s₀ p T dst dOff.eval (N * colsE.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hG''⟩ :=
    exec_cooCol hC hc (F c) (hF c) hI hG' (hY c hc)
  refine ⟨_, hrun, s'', g'', ?_, hI', hG''⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

end Steps

/-- Entry $(i, c)$ of the product with the COO matrix, as the sum the run computes. -/
private theorem getElem?_flatten_cooMatrix_mul {N cols : ℕ} {pattern : List (ℕ × ℕ)}
    (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (vals : ℕ → 𝕜) (X : Array 𝕜) :
    ∀ c < cols, ∀ i < N,
      (flatten (cooMatrix (N := N) pattern vals * unflatten N cols X))[i + N * c]? =
      some (∑ e ∈ Finset.range pattern.length,
        cooTerm pattern vals ((fun c j => X[j + N * c]?.getD 0) c) i e) := by
  intro c hc i hi
  rw [getElem?_flatten _ ⟨i, hi⟩ ⟨c, hc⟩, Matrix.mul_apply]
  congr 1
  simp only [cooMatrix, unflatten, Matrix.of_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold cooTerm
  rcases he : pattern[e]? with _ | ⟨i', j⟩
  · simp
  · obtain ⟨-, hj⟩ := hpat (i', j) (List.mem_of_getElem? he)
    by_cases hii : i' = i
    · subst hii
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [Array.getD_eq_getD_getElem?]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (Prod.mk.inj (Option.some.inj h)).2.symm)
      · simp
    · simp [hii]

end Sparse

/-- **The COO certificate**: for a pattern with positions in $[0, N)^2$, `cooImpl` implements the
exact oracle of `cooMatrix pattern vals` under `cooInterp`, at the cost `cooCost` of each
matrix-vector product, every other kind kept, with one scratch cell and no bit scratch.
No printed source.
Result: coo-oracle-certificate -/
theorem implementsOracle_cooImpl {N : ℕ} (pattern : List (ℕ × ℕ))
    (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) (p₀ : P) :
    ImplementsOracle (exactInterp (P := P) (ι := ι) (fun _ => cooMatrix (N := N) pattern vals) ξ)
      (cooInterp pattern vals ξ p₀)
      (fun o p dst dOff src sOff cols => cooImpl (.const N) pattern o p dst dOff src sOff cols)
      (substKind (cooCost N pattern.length)) (fun _ => 1) 0 := by
  intro o p dst dOff src sOff cols st X Y s₁ hdisj hX hY hs₁
  change dst ≠ src ∨ dOff.eval + N * cols.eval ≤ sOff.eval ∨
    sOff.eval + N * cols.eval ≤ dOff.eval at hdisj
  change st.store.readBlock p src sOff.eval (N * cols.eval) = some X at hX
  change matOracle (cooMatrix pattern vals) cols.eval X = some Y at hY
  unfold matOracle at hY
  split_ifs at hY with hXs
  cases hY
  have hXr := fun m (hm : m < N * cols.eval) => Store.read_of_readBlock_eq_some_of_lt hX hm
  set Y := flatten (cooMatrix (N := N) pattern vals * unflatten N cols.eval X) with hYdef
  have hYs : Y.size = N * cols.eval := size_flatten _
  set s₀ : Store P 𝕜 := st.store.push (p, Array.replicate (IExp.const 1).eval none) with hs₀
  have hsrc : 0 < N * cols.eval → src < st.store.size := Store.lt_size_of_readBlock_eq_some hX
  have hdstlt : 0 < N * cols.eval → dst < st.store.size := fun h =>
    Store.lt_size_of_writeBlock_eq_some hs₁ (hYs ▸ h)
  have hdst : ∀ m < N * cols.eval, ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + m < n :=
    fun m hm => (Store.exists_getElem?_shape_of_writeBlock_eq_some hs₁ (hYs ▸ hm)).imp fun n h =>
      ⟨by rw [hs₀, Store.getElem?_shape_push_of_lt _ (hdstlt (by omega))]; exact h.1, h.2⟩
  have hC : Sparse.CooCtx (cooInterp (ι := ι) pattern vals ξ p₀) s₀ p st.store.size
      dst src N cols.eval dOff sOff pattern vals (fun c j => X[j + N * c]?.getD 0) :=
    { sem := rfl
      charge := fun _ => rfl
      scratch := Store.getElem?_shape_push_size _ _ _
      dst_ne := fun h => Nat.ne_of_lt (hdstlt h)
      src_ne := fun h => Nat.ne_of_lt (hsrc h)
      dst_shape := hdst
      rom_eq := fun e he => if_pos he
      src_read := fun c hc j hj => by
        have hm : j + N * c < N * cols.eval := Nat.add_mul_lt_mul_of_lt_of_lt hj hc
        rw [hs₀, Store.read_push_of_lt (hsrc (by omega)), Nat.add_assoc, hXr _ hm,
          Array.getElem?_eq_getElem (by omega)]
        simp
      disj := hdisj
      pat := hpat }
  have hYc := Sparse.getElem?_flatten_cooMatrix_mul hpat vals X (cols := cols.eval)
  let F : ℕ → ℕ → (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit := fun t c ((i, j), e) => do
    Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
    Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .const j + .const N * .var c⟩)
    Builder.ins (.bin p .add ⟨dst, dOff + .const i + .const N * .var c⟩
      ⟨dst, dOff + .const i + .const N * .var c⟩ ⟨t, 0⟩)
  have hprog : cooImpl (P := P) (ι := ι) (.const N) pattern o p dst dOff src sOff cols =
      .seq (.named "coo_apply" [.idx (.const N), .buf dst, .idx dOff, .buf src, .idx sOff,
        .idx cols] (.alloc p (.const 1) fun t => .seq (.loop cols fun c =>
      .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx (F t c)))) .skip)) .skip := rfl
  beta_reduce
  rw [hprog, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Sparse.exec_cooCols hC (F st.store.size)
    (fun _ _ _ _ _ => rfl)
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (IExp.const 1).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (IExp.const 1).eval))
      curW := st.curW + (IExp.const 1).eval *
        (cooInterp (ι := ι) pattern vals ξ p₀).width p
      peakW := max st.peakW (st.curW + (IExp.const 1).eval *
        (cooInterp (ι := ι) pattern vals ξ p₀).width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ hYc
  rw [hF, Option.map_some]
  refine ⟨_, rfl, hIF.pop_eq hs₁ hYs hgF, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [cooInterp, storedInterp]
  · refine le_of_eq (congrArg (st.cnt + ·) ?_)
    simp only [substKind, cooCost, zero_add, smul_add, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    abel
  · intro q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [cooInterp, storedInterp]

/-- **Matrix-free to sparse**: a matrix-free result gives the stored-entries result for the
program with its oracle calls served by `cooImpl` for a pattern with positions in $[0, N)^2$: the
`nnz` stored values are read-only data, the pattern is public (unrolled into the program, so the
program may depend on it, and its index storage is not counted), the matrix is
`cooMatrix pattern vals`, each matrix-vector product costs `nnz` multiplications, additions and
reads and $N$ literals and each load nothing (`cooCost`), and the memory grows by one scratch cell
and the `nnz` stored values. The final state has the store, tape positions and current memory of
a final state of the matrix-free run. No printed source.
Result: matrix-free-coo-substitution -/
theorem ProgFamily.MatrixFree.storedEntries_substOracle_cooImpl {r b : ℕ} {p : P}
    {prog : ProgFamily P ι r b} {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜)}
    {cost : ℕ → (Fin r → ℕ) → OpCount P ι} {mem : ℕ → (Fin r → ℕ) → P → ℕ}
    {post : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 →
      (Dist → ℕ → ℝ) → St P 𝕜 (OpCount P ι) → Prop}
    (h : ProgFamily.MatrixFree p prog valid X inputs cost mem post) (pattern : List (ℕ × ℕ)) :
    ProgFamily.StoredEntries p (prog.substOracle fun _ _ N => cooImpl N pattern)
      (fun N n => valid N n ∧ ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) X inputs
      (fun _ _ => pattern.length) (fun N n => substCount (cooCost N pattern.length) (cost N n))
      (fun N n q => mem N n q + 1 + if q = p then pattern.length else 0)
      (fun N n x vals ξ st' => ∃ st, post N n x (cooMatrix pattern vals) ξ st ∧
        st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur) := by
  rintro N n ⟨hv, hpat⟩ x vals ξ
  exact RunsWithin.substOracle (I := exactInterp (fun _ => cooMatrix (N := N) pattern vals) ξ)
    (I' := cooInterp pattern vals ξ p) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)
    (fun _ _ _ => rfl) (implementsOracle_cooImpl pattern hpat vals ξ p) rfl (fun _ => le_rfl) le_rfl
    (h N n hv x _ ξ)

end NLAlib.Computation
