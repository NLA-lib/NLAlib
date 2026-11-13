/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.CountTree

/-!
# The static count of the spectral bisection program

The counts of every successful run of the registered tree `NLAlib.eighProg.compiled` are bounded by
the static bound `NLAlib.eighCount`, the memory included: the scalar counts by the polynomial checks
of the tree, and the kernel counts by the tree of kernel calls.

## Main results

* `NLAlib.eighProg.cnt_le_of_exec_compiled`: the static bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K : Type}

/-! ### The tree of kernel calls -/

/-- A tree of kernel calls: the skeleton of a first-order tree that carries its kernel counts. -/
private inductive KernelTree (P ι : Type) : ℕ → Type
  | skip {ni : ℕ} : KernelTree P ι ni
  | seq {ni : ℕ} (a b : KernelTree P ι ni) : KernelTree P ι ni
  | loop {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι (ni + 1)) : KernelTree P ι ni
  | rep {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι ni) : KernelTree P ι ni
  | br {ni : ℕ} (a b : KernelTree P ι ni) : KernelTree P ι ni
  | bind {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι (ni + 1)) : KernelTree P ι ni
  | call {ni : ℕ} (o : ι) (p : P) (d : List (IExp (Fin ni))) : KernelTree P ι ni

/-- A sequence, an empty side dropped. -/
private def KernelTree.mkSeq {ni : ℕ} : KernelTree P ι ni → KernelTree P ι ni → KernelTree P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .seq a b

/-- A loop, dropped if its body is empty. -/
private def KernelTree.mkLoop {ni : ℕ} (n : IExp (Fin ni)) :
    KernelTree P ι (ni + 1) → KernelTree P ι ni
  | .skip => .skip
  | b => .loop n b

/-- A repetition, dropped if its body is empty. -/
private def KernelTree.mkRep {ni : ℕ} (n : IExp (Fin ni)) : KernelTree P ι ni → KernelTree P ι ni
  | .skip => .skip
  | b => .rep n b

/-- A branch, an empty side dropped. -/
private def KernelTree.mkBr {ni : ℕ} : KernelTree P ι ni → KernelTree P ι ni → KernelTree P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .br a b

/-- An index binder, dropped if its body is empty. -/
private def KernelTree.mkBind {ni : ℕ} (n : IExp (Fin ni)) :
    KernelTree P ι (ni + 1) → KernelTree P ι ni
  | .skip => .skip
  | b => .bind n b

/-- The kernel calls of a first-order tree (defined through the recursor of
`NLAlib.Computation.FStmt`). -/
private noncomputable def kernelTreeOf {nb ni : ℕ} (s : FStmt P ι nb ni) : KernelTree P ι ni :=
  FStmt.rec (motive := fun _ ni _ => KernelTree P ι ni)
    (skip := .skip)
    (seq := fun _ _ a b => a.mkSeq b)
    (instr := fun _ => .skip)
    (apply := fun _ _ _ _ _ _ _ => .skip)
    (rom := fun _ _ _ => .skip)
    (alloc := fun _ _ _ b => b)
    (loop := fun n _ b => .mkLoop n b)
    (whileFuel := fun f _ _ _ _ _ b => .mkRep f b)
    (ite := fun _ _ _ _ _ _ t e => t.mkBr e)
    (named := fun _ _ _ b => b)
    (kcall := fun o p d _ _ => .call o p d)
    (bindIdx := fun _ _ bd _ b => .mkBind bd b) s

private theorem kernelTreeOf_seq {nb ni : ℕ} (s t : FStmt P ι nb ni) :
    kernelTreeOf (.seq s t) = (kernelTreeOf s).mkSeq (kernelTreeOf t) := rfl

private theorem kernelTreeOf_loop {nb ni : ℕ} (n : IExp (Fin ni)) (b : FStmt P ι nb (ni + 1)) :
    kernelTreeOf (.loop n b) = .mkLoop n (kernelTreeOf b) := rfl

private theorem kernelTreeOf_whileFuel {nb ni : ℕ} (f : IExp (Fin ni)) (p : P) (c : CmpOp)
    (x y : Cell (Fin nb) (Fin ni)) (b : FStmt P ι nb ni) :
    kernelTreeOf (.whileFuel f p c x y b) = .mkRep f (kernelTreeOf b) := rfl

private theorem kernelTreeOf_ite {nb ni : ℕ} (p : P) (c : CmpOp) (x y : Cell (Fin nb) (Fin ni))
    (t e : FStmt P ι nb ni) :
    kernelTreeOf (.ite p c x y t e) = (kernelTreeOf t).mkBr (kernelTreeOf e) := rfl

private theorem kernelTreeOf_bindIdx {nb ni : ℕ} (p : P) (x : Cell (Fin nb) (Fin ni))
    (bd : IExp (Fin ni)) (b : FStmt P ι nb (ni + 1)) :
    kernelTreeOf (.bindIdx p x bd b) = .mkBind bd (kernelTreeOf b) := rfl

/-! #### The tree of kernel calls of the registered tree -/

/-- The index variable `i` of a context of `ni` variables. -/
private def ktVar {ni : ℕ} (i : ℕ) (h : i < ni := by decide) : IExp (Fin ni) := .var ⟨i, h⟩

/-- The kernel calls of the split of a node (depth $10$ variables). -/
private def splitCalls (p : P) (mm qr : ι) : KernelTree P ι 10 :=
  .seq (.call mm p [ktVar 5, ktVar 5, ktVar 5]) (.seq (.call qr p [ktVar 5, ktVar 5])
    (.seq (.call mm p [ktVar 5, ktVar 5, ktVar 5]) (.seq (.call qr p [ktVar 5, ktVar 5])
    (.seq (.call mm p [ktVar 8, ktVar 5, ktVar 5]) (.seq (.call mm p [ktVar 8, ktVar 5, ktVar 8])
    (.seq (.call mm p [.sub (ktVar 5) (ktVar 8), ktVar 5, ktVar 5])
      (.call mm p [.sub (ktVar 5) (ktVar 8), ktVar 5, .sub (ktVar 5) (ktVar 8)])))))))

/-- The split of a node, run at most once. -/
private def splitLoopCalls (p : P) (mm qr : ι) : KernelTree P ι 9 :=
  .loop (.sub (.const 1) (.sub (.const 1) (.mul (ktVar 8) (.sub (ktVar 5) (ktVar 8)))))
    (splitCalls p mm qr)

/-- The kernel calls of a node of the downward pass: the sign iteration and the split. -/
private def downNodeCalls (p : P) (mm qr : ι) : KernelTree P ι 8 :=
  .seq (.seq (.call mm p [ktVar 5, ktVar 5, ktVar 5])
      (.loop (ktVar 2) (.seq (.call mm p [ktVar 5, ktVar 5, ktVar 5])
        (.call mm p [ktVar 5, ktVar 5, ktVar 5]))))
    (.bind (ktVar 5) (splitLoopCalls p mm qr))

/-- The kernel calls of a slot of the downward pass. -/
private def downSlotCalls (p : P) (mm qr : ι) : KernelTree P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ktVar 5)))
    (.loop (.sub (.const 1) (.sub (.const 1) (.sub (ktVar 5) (.const 1)))) (downNodeCalls p mm qr))

/-- The kernel calls of the assembly of a split in the upward pass. -/
private def upSplitCalls (p : P) (mm : ι) : KernelTree P ι 10 :=
  .seq (.call mm p [ktVar 5, ktVar 9, ktVar 9])
    (.call mm p [ktVar 5, .sub (ktVar 5) (ktVar 9), .sub (ktVar 5) (ktVar 9)])

/-- The kernel calls of a node of the upward pass. -/
private def upNodeCalls (p : P) (mm : ι) : KernelTree P ι 8 :=
  .loop (.sub (.const 1) (.sub (.const 1)
    (.mul (.sub (.const 1) (.sub (ktVar 7) (.const 4)))
      (.sub (.const 1) (.sub (.const 4) (ktVar 7))))))
    (.bind (ktVar 5) (upSplitCalls p mm))

/-- The kernel calls of a slot of the upward pass. -/
private def upSlotCalls (p : P) (mm : ι) : KernelTree P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ktVar 5))) (.bind (.const 4) (upNodeCalls p mm))

/-- The kernel calls of `NLAlib.eighProg.compiled`. -/
private def eighKernelTree (p : P) (mm qr : ι) : KernelTree P ι 3 :=
  .seq (.loop (.add (ktVar 1) (.const 1)) (.loop (ktVar 0) (.bind (.sub (ktVar 0) (ktVar 4))
      (downSlotCalls p mm qr))))
    (.loop (.add (ktVar 1) (.const 1)) (.loop (ktVar 0) (.bind (.sub (ktVar 0) (ktVar 4))
      (upSlotCalls p mm))))

/-! #### The polynomial checks of the registered tree -/

/-- The polynomial environment of the sizes $(N, \ell_0, F)$. -/
private def sizePolys : Fin 3 → CostPoly :=
  fun v =>
    if v.val = 0 then [(1, 1, 0, 0)] else if v.val = 1 then [(1, 0, 1, 0)] else [(1, 0, 0, 1)]

/-- The check of a scalar class: degrees at most $(3, 1, 1)$ and coefficients summing to at most
$1024$. -/
private def checkScalar (p : CostPoly) : Bool :=
  p.all (fun e => e.2.1 ≤ 3 && e.2.2.1 ≤ 1 && e.2.2.2 ≤ 1) && decide ((p.map (·.1)).sum ≤ 1024)

/-- The check of the workspace: degrees at most $(2, 1, 0)$, coefficients of the terms without
$\ell_0$ summing to at most $192$, with $\ell_0$ to at most $64$. -/
private def checkCells (p : CostPoly) : Bool :=
  p.all (fun e => e.2.1 ≤ 2 && e.2.2.1 ≤ 1 && e.2.2.2 = 0) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum ≤ 192) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum ≤ 64)

private theorem checkCells_crudeCells_compiled :
    checkCells (crudeCells (eighProg.compiled () true false) sizePolys) = true := by
  decide +kernel

private theorem checkScalar_crudeCount_compiled :
    ∀ c ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32],
      checkScalar (crudeCount c (eighProg.compiled () true false) sizePolys) = true := by
  decide +kernel

private theorem crudeCount_compiled_eq_nil : ∀ c ∈ [3, 4, 5, 8, 14, 21, 31],
    crudeCount c (eighProg.compiled () true false) sizePolys = [] := by
  decide +kernel

/-! #### The kernel counts of a tree of kernel calls -/

/-- The static kernel count of a tree of kernel calls at the index values `ρ`, as
`NLAlib.Computation.FStmt.staticCost` counts it. -/
private noncomputable def KernelTree.count : {ni : ℕ} → KernelTree P ι ni → (Fin ni → ℕ) →
    OpCount P ι
  | _, .skip, _ => 0
  | _, .seq a b, ρ => a.count ρ + b.count ρ
  | _, .loop n b, ρ =>
      ((List.range (n.evalIn ρ)).map fun i => b.count (Fin.snoc (α := fun _ => ℕ) ρ i)).sum
  | _, .rep n b, ρ => n.evalIn ρ • b.count ρ
  | _, .br a b, ρ => a.count ρ ⊔ b.count ρ
  | _, .bind n b, ρ => (List.range (n.evalIn ρ + 1)).foldr
      (fun k c => b.count (Fin.snoc (α := fun _ => ℕ) ρ k) ⊔ c) 0
  | _, .call o p d, ρ => Finsupp.single (.kcall p o (d.map (·.evalIn ρ))) 1

private theorem foldr_sup_zero (l : List ℕ) :
    l.foldr (fun _ c => (0 : OpCount P ι) ⊔ c) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

private theorem count_mkSeq {ni : ℕ} (a b : KernelTree P ι ni) (ρ : Fin ni → ℕ) :
    (KernelTree.mkSeq a b).count ρ = a.count ρ + b.count ρ := by
  unfold KernelTree.mkSeq
  split <;> simp [KernelTree.count]

private theorem count_mkBr {ni : ℕ} (a b : KernelTree P ι ni) (ρ : Fin ni → ℕ) :
    (KernelTree.mkBr a b).count ρ = a.count ρ ⊔ b.count ρ := by
  unfold KernelTree.mkBr
  split <;> simp [KernelTree.count]

private theorem count_mkLoop {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι (ni + 1))
    (ρ : Fin ni → ℕ) : (KernelTree.mkLoop n b).count ρ = (KernelTree.loop n b).count ρ := by
  unfold KernelTree.mkLoop
  split <;> simp [KernelTree.count]

private theorem count_mkRep {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι ni)
    (ρ : Fin ni → ℕ) : (KernelTree.mkRep n b).count ρ = (KernelTree.rep n b).count ρ := by
  unfold KernelTree.mkRep
  split <;> simp [KernelTree.count]

private theorem count_mkBind {ni : ℕ} (n : IExp (Fin ni)) (b : KernelTree P ι (ni + 1))
    (ρ : Fin ni → ℕ) : (KernelTree.mkBind n b).count ρ = (KernelTree.bind n b).count ρ := by
  unfold KernelTree.mkBind
  split
  · simp only [KernelTree.count]; exact (foldr_sup_zero _).symm
  · rfl

private theorem sum_map_apply (l : List ℕ) (f : ℕ → OpCount P ι) (κ : OpKind P ι) :
    (l.map f).sum κ = (l.map fun i => f i κ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem count_supRange_eq {f : ℕ → StaticCost P ι} {g : ℕ → OpCount P ι} {m : ℕ}
    {κ : OpKind P ι} (h : ∀ k, (f k).count κ = g k κ) :
    (StaticCost.supRange m f).count κ = (List.range m).foldr (fun k c => g k ⊔ c) 0 κ := by
  unfold StaticCost.supRange
  induction List.range m with
  | nil => rfl
  | cons a l ih =>
    change ((f a).count ⊔ (l.foldr (fun k c => (f k).branch c) StaticCost.zero).count) κ =
      (g a ⊔ l.foldr (fun k c => g k ⊔ c) 0) κ
    rw [Finsupp.sup_apply, Finsupp.sup_apply, h, ih]

private theorem single_apply_eq_zero {k κ : OpKind P ι} (h : opKindClass k ≠ opKindClass κ) :
    (Finsupp.single k 1 : OpCount P ι) κ = 0 := by
  classical
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact h rfl

private theorem opKindClass_kind_ne (i : Instr P ℕ ℕ) : opKindClass (i.kind (ι := ι)) ≠ 9 := by
  cases i <;> simp only [Instr.kind, opKindClass] <;> first | decide | (split <;> decide)

/-! #### The polynomial checks -/

private theorem eval_le_sum_mul (N L F M : ℕ) (p : CostPoly)
    (h : ∀ e ∈ p, N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2 ≤ M) :
    p.eval N L F ≤ (p.map (·.1)).sum * M := by
  induction p with
  | nil => simp [CostPoly.eval]
  | cons a p ih =>
    have ih' := ih fun e he => h e (List.mem_cons_of_mem a he)
    simp only [CostPoly.eval, List.map_cons, List.sum_cons, add_mul] at ih' ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h a List.mem_cons_self)) ih'

private theorem pow_le_succ (L b : ℕ) (hb : b ≤ 1) : L ^ b ≤ L + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

private theorem eval_le_of_checkScalar (N L F : ℕ) (p : CostPoly) (h : checkScalar p = true) :
    p.eval N L F ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
  simp only [checkScalar, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  refine (eval_le_sum_mul N L F ((N + 1) ^ 3 * (L + 1) * (F + 1)) p fun e he => ?_).trans ?_
  · obtain ⟨⟨ha, hb⟩, hc⟩ := hall e he
    refine Nat.mul_le_mul (Nat.mul_le_mul ?_ (pow_le_succ L _ hb)) (pow_le_succ F _ hc)
    exact (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
  · calc (p.map (·.1)).sum * ((N + 1) ^ 3 * (L + 1) * (F + 1))
        ≤ 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1)) := Nat.mul_le_mul_right _ hsum
      _ ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
        have h1 : (L + 1) * (F + 1) ≤ (L + 2) * (F + 2) := Nat.mul_le_mul (by omega) (by omega)
        have h2 := Nat.mul_le_mul_left (1024 * (N + 1) ^ 3) h1
        calc 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1))
            = 1024 * (N + 1) ^ 3 * ((L + 1) * (F + 1)) := by ring
          _ ≤ 1024 * (N + 1) ^ 3 * ((L + 2) * (F + 2)) := h2
          _ = 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by ring

private theorem eval_le_of_checkCells (N L F : ℕ) (p : CostPoly) (h : checkCells p = true) :
    p.eval N L F ≤ 64 * (N + 1) ^ 2 * (L + 3) := by
  simp only [checkCells, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, h0⟩, h1⟩ := h
  have key : p.eval N L F ≤ (N + 1) ^ 2 * ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum +
      (p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum * L) := by
    clear h0 h1
    induction p with
    | nil => simp [CostPoly.eval]
    | cons a p ih =>
      have ih' := ih fun e he => hall e (List.mem_cons_of_mem a he)
      obtain ⟨⟨ha, hb⟩, hc⟩ := hall a List.mem_cons_self
      simp only [CostPoly.eval, List.map_cons, List.sum_cons] at ih' ⊢
      have hN : N ^ a.2.1 ≤ (N + 1) ^ 2 :=
        (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
      have hterm : a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) ≤
          (N + 1) ^ 2 * ((if a.2.2.1 = 0 then a.1 else 0) +
            (if a.2.2.1 = 0 then 0 else a.1) * L) := by
        rw [hc, pow_zero, mul_one]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
        · simp only [hb0, pow_zero, mul_one, if_true, zero_mul, add_zero]
          calc a.1 * N ^ a.2.1 ≤ a.1 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ hN
            _ = (N + 1) ^ 2 * a.1 := Nat.mul_comm _ _
        · simp only [hb1, pow_one, one_ne_zero, if_false, zero_add]
          calc a.1 * (N ^ a.2.1 * L) ≤ a.1 * ((N + 1) ^ 2 * L) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hN)
            _ = (N + 1) ^ 2 * (a.1 * L) := by ring
      calc a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) + CostPoly.eval N L F p
          ≤ _ + _ := Nat.add_le_add hterm ih'
        _ = _ := by ring
  refine key.trans ?_
  calc (N + 1) ^ 2 * (_ + _ * L) ≤ (N + 1) ^ 2 * (192 + 64 * L) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h0 (Nat.mul_le_mul_right _ h1))
    _ = 64 * (N + 1) ^ 2 * (L + 3) := by ring

/-! #### The kernel bound -/

/-- The kernel calls charged by `NLAlib.eighCount` for a node of size $k$ split at $k_+$. -/
private noncomputable def nodeCalls (p : P) (mm qr : ι) (F k kp : ℕ) : OpCount P ι :=
  (2 * F + 8) • Finsupp.single (.kcall p mm [k, k, k]) 1 +
    Finsupp.single (.kcall p qr [k, k]) 2 +
    Finsupp.single (.kcall p mm [kp, k, k]) 1 + Finsupp.single (.kcall p mm [kp, k, kp]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k - kp]) 1 +
    Finsupp.single (.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (.kcall p mm [k, k - kp, k - kp]) 1

/-- The kernel calls charged for a node of size $k$, every split. -/
private noncomputable def nodeCallsAll (p : P) (mm qr : ι) (F k : ℕ) : OpCount P ι :=
  ∑ kp ∈ Finset.range (k + 1), nodeCalls p mm qr F k kp

private theorem eighCount_eq (p : P) (mm qr : ι) (n L F : ℕ) :
    eighCount p mm qr n L F = ((eighScalarKinds (ι := ι) p).map fun κ =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)).sum +
      (2 * (L + 1) * n) • ∑ k ∈ Finset.range (n + 1), nodeCallsAll p mm qr F k := rfl

private theorem sum_map_range_le (m : ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ i < m, f i ≤ B) : ((List.range m).map f).sum ≤ m • B := by
  refine (List.sum_le_card_nsmul _ B ?_).trans_eq (by simp)
  simp only [List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩
  exact h i hi

private theorem sum_map_range_le_of_le_one {m : ℕ} (hm : m ≤ 1) (f : ℕ → OpCount P ι) :
    ((List.range m).map f).sum ≤ f 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp

private theorem foldr_sup_le (l : List ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ k ∈ l, f k ≤ B) : l.foldr (fun k c => f k ⊔ c) 0 ≤ B := by
  induction l with
  | nil => exact zero_le
  | cons a l ih =>
    exact sup_le (h a List.mem_cons_self) (ih fun k hk => h k (List.mem_cons_of_mem a hk))

private theorem foldr_sup_le_sum (m : ℕ) (f : ℕ → OpCount P ι) :
    (List.range m).foldr (fun k c => f k ⊔ c) 0 ≤ ∑ k ∈ Finset.range m, f k :=
  foldr_sup_le _ _ _ fun _ hk => Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hk))

private theorem count_splitCalls_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      (splitCalls p mm qr).count ρ ≤
      nodeCalls p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [splitCalls, KernelTree.count, ktVar, IExp.evalIn, List.map_cons, List.map_nil,
    nodeCalls]
  generalize ρ ⟨2, by decide⟩ = F
  generalize ρ ⟨5, by decide⟩ = k
  generalize ρ ⟨8, by decide⟩ = kp
  have e2 : Finsupp.single (OpKind.kcall p qr [k, k]) 2 =
      Finsupp.single (OpKind.kcall p qr [k, k]) 1 +
        Finsupp.single (OpKind.kcall p qr [k, k]) 1 := by
    rw [← Finsupp.single_add]
  rw [e2]
  refine (le_self_add (b := Finsupp.single (OpKind.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (OpKind.kcall p mm [k, k - kp, k - kp]) 1)).trans_eq ?_
  ext κ
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

private theorem count_splitLoopCalls_le (p : P) (mm qr : ι) (ρ : Fin 9 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      (splitLoopCalls p mm qr).count ρ ≤
      nodeCalls p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [splitLoopCalls, KernelTree.count]
  refine (add_le_add le_rfl (sum_map_range_le_of_le_one (Nat.sub_le _ _) _)).trans ?_
  exact count_splitCalls_le p mm qr (Fin.snoc ρ 0)

private theorem count_downNodeCalls_le (p : P) (mm qr : ι) (ρ : Fin 8 → ℕ) :
    (downNodeCalls p mm qr).count ρ ≤
      nodeCallsAll p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [downNodeCalls, KernelTree.count, ktVar, IExp.evalIn, List.map_cons, List.map_nil]
  set F := ρ ⟨2, by decide⟩
  set k := ρ ⟨5, by decide⟩
  set s := Finsupp.single (OpKind.kcall p mm [k, k, k]) (1 : ℕ)
  have h1 : s + ((List.range F).map fun _ => s + s).sum ≤ (2 * F + 6) • s := by
    rw [List.map_const', List.sum_replicate, List.length_range]
    have : s + F • (s + s) = (2 * F + 1) • s := by
      ext κ; simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact nsmul_le_nsmul_left zero_le (by omega)
  refine (add_le_add h1 le_rfl).trans ?_
  set c : ℕ → OpCount P ι := fun kp =>
    (splitLoopCalls p mm qr).count (Fin.snoc (α := fun _ => ℕ) ρ kp)
  have hX : ∀ kp, (2 * F + 6) • s + c kp ≤ nodeCalls p mm qr F k kp :=
    fun kp => count_splitLoopCalls_le p mm qr (Fin.snoc ρ kp)
  refine (add_le_add le_rfl (foldr_sup_le_sum _ _)).trans ?_
  unfold nodeCallsAll
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  calc (2 * F + 6) • s + (∑ i ∈ Finset.range k, c (i + 1) + c 0)
      = (∑ i ∈ Finset.range k, c (i + 1)) + ((2 * F + 6) • s + c 0) := by abel
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ => le_add_self.trans (hX (i + 1))) (hX 0)

private theorem count_downSlotCalls_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    (downSlotCalls p mm qr).count ρ ≤
      nodeCallsAll p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [downSlotCalls, KernelTree.count]
  refine (sum_map_range_le_of_le_one (Nat.sub_le _ _) _).trans ?_
  refine (sum_map_range_le_of_le_one (Nat.sub_le _ _) _).trans ?_
  exact count_downNodeCalls_le p mm qr _

private theorem count_upSplitCalls_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    (upSplitCalls p mm).count ρ ≤
      nodeCalls p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨9, by decide⟩) := by
  simp only [upSplitCalls, KernelTree.count, ktVar, IExp.evalIn, List.map_cons, List.map_nil,
    nodeCalls]
  rw [add_assoc _ (Finsupp.single _ 1) (Finsupp.single _ 1)]
  exact le_add_self

private theorem count_upSlotCalls_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    (upSlotCalls p mm).count ρ ≤
      nodeCallsAll p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [upSlotCalls, KernelTree.count]
  refine (sum_map_range_le_of_le_one (Nat.sub_le _ _) _).trans ?_
  refine foldr_sup_le _ _ _ fun c _ => ?_
  simp only [upNodeCalls, KernelTree.count]
  refine (sum_map_range_le_of_le_one (Nat.sub_le _ _) _).trans ?_
  refine foldr_sup_le _ _ _ fun kp hkp => ?_
  refine (count_upSplitCalls_le p mm qr _).trans ?_
  exact Finset.single_le_sum (f := fun kp => nodeCalls p mm qr _ _ kp) (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hkp))

/-- The kernel calls of the registered tree are at most those of `NLAlib.eighCount`. -/
private theorem count_eighKernelTree_le (p : P) (mm qr : ι) (N L F : ℕ) :
    (eighKernelTree p mm qr).count (Fin.cons N ![L, F]) ≤
      (2 * (L + 1) * N) • ∑ k ∈ Finset.range (N + 1), nodeCallsAll p mm qr F k := by
  set Gs := ∑ k ∈ Finset.range (N + 1), nodeCallsAll p mm qr F k
  have hG : ∀ k ≤ N, nodeCallsAll p mm qr F k ≤ Gs := fun k hk =>
    Finset.single_le_sum (f := fun k => nodeCallsAll p mm qr F k) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega))
  have hlev : ∀ (X : KernelTree P ι 6),
      (∀ ρ : Fin 6 → ℕ, ρ ⟨2, by decide⟩ = F → ρ ⟨5, by decide⟩ ≤ N → X.count ρ ≤ Gs) →
      (KernelTree.loop (.add (ktVar 1) (.const 1)) (.loop (ktVar 0)
        (.bind (.sub (ktVar 0) (ktVar 4)) X))).count (Fin.cons N ![L, F]) ≤ (L + 1) • N • Gs := by
    intro X hX
    simp only [KernelTree.count]
    refine sum_map_range_le _ _ _ fun d _ => ?_
    refine sum_map_range_le _ _ _ fun lo _ => ?_
    refine foldr_sup_le _ _ _ fun k hk => hX _ rfl ?_
    have := List.mem_range.mp hk
    simp only [IExp.evalIn, ktVar] at this
    change k ≤ N
    have h0 : (Fin.snoc (α := fun _ => ℕ) (Fin.snoc (α := fun _ => ℕ)
        (Fin.cons N ![L, F] : Fin 3 → ℕ) d) lo) ⟨0, by decide⟩ = N := rfl
    rw [h0] at this
    omega
  simp only [eighKernelTree, KernelTree.count]
  refine (add_le_add (hlev _ fun ρ hF hk => (count_downSlotCalls_le p mm qr ρ).trans (hF ▸ hG _ hk))
    (hlev _ fun ρ hF hk => (count_upSlotCalls_le p mm qr ρ).trans (hF ▸ hG _ hk))).trans_eq ?_
  rw [smul_smul, ← add_nsmul]
  congr 1
  ring

/-! #### Assembly -/

private theorem le_eval_sizePolys (N L F : ℕ) :
    ∀ v, (Fin.cons N ![L, F] : Fin 3 → ℕ) v ≤ (sizePolys v).eval N L F := by
  intro v
  fin_cases v <;> simp [sizePolys, CostPoly.eval]

private theorem le_eighCount (p : P) (mm qr : ι) (n L F : ℕ) {κ : OpKind P ι}
    (hκ : κ ∈ eighScalarKinds (ι := ι) p) :
    1024 * (F + 2) * (L + 2) * (n + 1) ^ 3 ≤ eighCount p mm qr n L F κ := by
  rw [eighCount_eq, Finsupp.add_apply]
  refine le_trans ?_ (Nat.le_add_right _ _)
  have h := List.single_le_sum (fun _ _ => zero_le) _
    (List.mem_map_of_mem (f := fun κ : OpKind P ι =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)) hκ)
  simpa using h κ

private theorem opKindClass_mem (p : P) (κ : OpKind P ι) (h9 : opKindClass κ ≠ 9)
    (ht : opKindTag κ = p) :
    opKindClass κ ∈ [3, 4, 5, 8, 14, 21, 31] ∨
      opKindClass κ ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32] ∧
        κ ∈ eighScalarKinds (ι := ι) p := by
  cases κ with
  | bin q b => obtain rfl : q = p := ht; cases b <;> simp [opKindClass, eighScalarKinds]
  | un q u => obtain rfl : q = p := ht; cases u <;> simp [opKindClass, eighScalarKinds]
  | draw q d => obtain rfl : q = p := ht; cases d <;> simp [opKindClass, eighScalarKinds]
  | kcall => exact absurd rfl h9
  | _ => simp only [opKindTag] at ht; subst ht; simp [opKindClass, eighScalarKinds]

private theorem eval_crudeCount_le_eighCount (p : P) (mm qr : ι) (N L F : ℕ) (κ : OpKind P ι)
    (h9 : opKindClass κ ≠ 9) (ht : opKindTag κ = p) :
    (crudeCount (opKindClass κ) (eighProg.compiled () true false) sizePolys).eval N L F ≤
      eighCount p mm qr N L F κ := by
  rcases opKindClass_mem p κ h9 ht with hz | ⟨hs, hk⟩
  · simp [crudeCount_compiled_eq_nil _ hz, CostPoly.eval]
  · exact (eval_le_of_checkScalar N L F _ (checkScalar_crudeCount_compiled _ hs)).trans
      (le_eighCount p mm qr N L F hk)

/-! #### Renaming the registered tree -/

/-- A tree of kernel calls with its tags renamed by `f` and its oracle names by `g`. -/
private def KernelTree.rename {P' ι' : Type} (f : P → P') (g : ι → ι') :
    {ni : ℕ} → KernelTree P ι ni → KernelTree P' ι' ni
  | _, .skip => .skip
  | _, .seq a b => .seq (a.rename f g) (b.rename f g)
  | _, .loop n b => .loop n (b.rename f g)
  | _, .rep n b => .rep n (b.rename f g)
  | _, .br a b => .br (a.rename f g) (b.rename f g)
  | _, .bind n b => .bind n (b.rename f g)
  | _, .call o p d => .call (g o) (f p) d

-- The registered tree is compared with the renamed one by evaluation, which needs a deeper
-- recursion than the default.
set_option maxRecDepth 100000 in
private theorem compiled_eq_mapTags (p : P) (mm qr : ι) : eighProg.compiled p mm qr =
    FStmt.mapTags (fun _ => p) (fun b => bif b then mm else qr) (eighProg.compiled () true false) :=
  rfl

private theorem crudeCount_mapTags {P' ι' : Type} (f : P → P') (g : ι → ι') (c : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → CostPoly),
      crudeCount c (FStmt.mapTags f g s) σ = crudeCount c s σ := by
  intro nb ni s
  induction s with
  | instr i => intro σ; cases i <;> rfl
  | _ => intro σ; simp only [FStmt.mapTags, crudeCount] at * <;> simp only [*]

private theorem crudeCells_mapTags {P' ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → CostPoly),
      crudeCells (FStmt.mapTags f g s) σ = crudeCells s σ := by
  intro nb ni s
  induction s with
  | _ => intro σ; simp only [FStmt.mapTags, crudeCells] at * <;> simp only [*]

private theorem tagsOf_mapTags {P' ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni), tagsOf (FStmt.mapTags f g s) = (tagsOf s).map f := by
  intro nb ni s
  induction s with
  | instr i => cases i <;> rfl
  | _ =>
    simp only [FStmt.mapTags, tagsOf, List.map_append, List.map_cons, List.map_nil] at * <;>
      simp only [*]

private theorem kernelTreeOf_mapTags {P' ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni),
      kernelTreeOf (FStmt.mapTags f g s) = (kernelTreeOf s).rename f g := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    simp only [FStmt.mapTags, kernelTreeOf_seq, ihs, iht]
    cases kernelTreeOf s <;> cases kernelTreeOf t <;> rfl
  | loop n b ih =>
    simp only [FStmt.mapTags, kernelTreeOf_loop, ih]
    cases kernelTreeOf b <;> rfl
  | whileFuel fu p c x y b ih =>
    simp only [FStmt.mapTags, kernelTreeOf_whileFuel, ih]
    cases kernelTreeOf b <;> rfl
  | ite p c x y t e iht ihe =>
    simp only [FStmt.mapTags, kernelTreeOf_ite, iht, ihe]
    cases kernelTreeOf t <;> cases kernelTreeOf e <;> rfl
  | bindIdx p x bd b ih =>
    simp only [FStmt.mapTags, kernelTreeOf_bindIdx, ih]
    cases kernelTreeOf b <;> rfl
  | alloc p len b ih => exact ih
  | named n a b ih => exact ih
  | _ => rfl

-- The tree of kernel calls of the registered tree is computed by evaluation, which needs a
-- deeper recursion than the default.
set_option maxRecDepth 100000 in
private theorem kernelTreeOf_compiled_unit :
    kernelTreeOf (eighProg.compiled () true false) = eighKernelTree () true false := rfl

private theorem kernelTreeOf_compiled (p : P) (mm qr : ι) :
    kernelTreeOf (eighProg.compiled p mm qr) = eighKernelTree p mm qr := by
  rw [compiled_eq_mapTags p mm qr, kernelTreeOf_mapTags, kernelTreeOf_compiled_unit]
  rfl

section

variable [DecidableEq P]

/-- The kernel counts are those of the tree of kernel calls. -/
private theorem count_staticCost_eq_count_kernelTreeOf (w : P → ℕ) (κ : OpKind P ι)
    (h9 : opKindClass κ = 9) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ),
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ = (kernelTreeOf s).count ρ κ := by
  have hz : ∀ k : OpKind P ι, opKindClass k ≠ 9 → (Finsupp.single k 1 : OpCount P ι) κ = 0 :=
    fun k hk => single_apply_eq_zero (h9 ▸ hk)
  intro nb ni s
  induction s with
  | skip => intro ρ; rfl
  | seq s t ihs iht =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, kernelTreeOf_seq, count_mkSeq,
      ihs, iht]
  | instr i => intro ρ; exact hz _ (opKindClass_kind_ne _)
  | apply o p d dOff s sOff cols =>
    intro ρ
    change _ = (0 : OpCount P ι) κ
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [hz _ (by simp [opKindClass]), hz _ (by simp [opKindClass])]
    simp
  | rom p d i => intro ρ; exact hz _ (by simp [opKindClass])
  | alloc p len body ih => exact ih
  | loop n body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, kernelTreeOf_loop, count_mkLoop,
      KernelTree.count, sum_map_apply, ih]
  | whileFuel fuel p c x y body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, kernelTreeOf_whileFuel, count_mkRep,
      KernelTree.count, ih, hz (.cmp p) (by simp [opKindClass]), zero_add]
  | ite p c x y t e iht ihe =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, kernelTreeOf_ite, count_mkBr, iht, ihe,
      hz (.cmp p) (by simp [opKindClass]), zero_add]
  | named name args body ih => exact ih
  | kcall o p dims ins outs => intro ρ; rfl
  | bindIdx p x bound body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply,
      hz (.toNat p) (by simp [opKindClass]), zero_add, kernelTreeOf_bindIdx, count_mkBind,
      KernelTree.count]
    exact count_supRange_eq fun k => ih _

private theorem count_le_eighCount (w : P → ℕ) (p : P) (mm qr : ι) (N L F : ℕ)
    (T : FStmt P ι 4 3) (hpr : kernelTreeOf T = eighKernelTree p mm qr)
    (hC : ∀ c, crudeCount c T sizePolys = crudeCount c (eighProg.compiled () true false) sizePolys)
    (htag : ∀ q ∈ tagsOf T, q = p) (κ : OpKind P ι) :
    (FStmt.staticCost (fun k => Finsupp.single k 1) w T (Fin.cons N ![L, F])).count κ ≤
      eighCount p mm qr N L F κ := by
  by_cases h9 : opKindClass κ = 9
  · rw [count_staticCost_eq_count_kernelTreeOf w κ h9, hpr, eighCount_eq, Finsupp.add_apply]
    exact (count_eighKernelTree_le p mm qr N L F κ).trans (Nat.le_add_left _ _)
  · by_cases ht : opKindTag κ = p
    · refine (count_staticCost_le_eval_crudeCount w κ N L F T _ sizePolys
        (le_eval_sizePolys N L F)).trans ?_
      rw [hC]
      exact eval_crudeCount_le_eighCount p mm qr N L F κ h9 ht
    · have := count_staticCost_le_zero_of_opKindTag_notMem_tagsOf w κ T (Fin.cons N ![L, F])
        fun hm => ht (htag _ hm)
      omega

private theorem cells_le_of_crudeCells_eq (charge : OpKind P ι → OpCount P ι) (w : P → ℕ)
    (p : P) (N L F : ℕ) (T : FStmt P ι 4 3)
    (hC : crudeCells T sizePolys = crudeCells (eighProg.compiled () true false) sizePolys)
    (htag : ∀ q ∈ tagsOf T, q = p) (q : P) :
    (FStmt.staticCost charge w T (Fin.cons N ![L, F])).cells q ≤
      if q = p then 64 * (N + 1) ^ 2 * (L + 3) else 0 := by
  split_ifs with hq
  · refine (cells_staticCost_le_eval_crudeCells charge w q N L F T _ sizePolys
      (le_eval_sizePolys N L F)).trans ?_
    rw [hC]
    exact eval_le_of_checkCells N L F _ checkCells_crudeCells_compiled
  · exact cells_staticCost_le_zero_of_notMem_tagsOf charge w q _ _ fun hm => hq (htag _ hm)

/-- The counts and the memory of the registered tree: under the standard charge (one per
operation), every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$
adds at most `NLAlib.eighCount p mm qr N ℓ₀ F` to the counts and raises the peak memory at tag `p`
by at most $64(N + 1)^2(\ell_0 + 3)$ cells above the current memory (by nothing at any other tag):
the arenas of $D + 1 = \ell_0 + 2$ levels and the scratch of one node, $O(N^2 \ell_0)$. No printed
source. -/
theorem eighProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : IsUnitCharge I) (p : P) (N ℓ₀ F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    st'.cnt ≤ st.cnt + eighCount p mm qr N ℓ₀ F ∧
      ∀ q, st'.peak q ≤ max (st.peak q)
        (st.cur q + if q = p then 64 * (N + 1) ^ 2 * (ℓ₀ + 3) else 0) := by
  have hb := (eighProg.compiled p mm qr).bounds_staticCost_of_exec_eq_some I N ![ℓ₀, F] h
  have hpr := kernelTreeOf_compiled p mm qr
  have hC : ∀ c, crudeCount c (eighProg.compiled p mm qr) sizePolys =
      crudeCount c (eighProg.compiled () true false) sizePolys := fun c => by
    rw [compiled_eq_mapTags p mm qr, crudeCount_mapTags]
  have hCc : crudeCells (eighProg.compiled p mm qr) sizePolys =
      crudeCells (eighProg.compiled () true false) sizePolys := by
    rw [compiled_eq_mapTags p mm qr, crudeCells_mapTags]
  have htag : ∀ q ∈ tagsOf (eighProg.compiled p mm qr), q = p := by
    rw [compiled_eq_mapTags p mm qr, tagsOf_mapTags]
    intro q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    rfl
  generalize eighProg.compiled p mm qr = T at hb hpr hC hCc htag
  have hcount := count_le_eighCount I.width p mm qr N ℓ₀ F T hpr hC htag
  rw [← hc.charge_eq] at hcount
  exact ⟨hb.count.trans (add_le_add le_rfl fun κ => hcount κ), fun q => (hb.peak q).trans
    (max_le_max le_rfl
      (add_le_add le_rfl (cells_le_of_crudeCells_eq I.charge I.width p N ℓ₀ F T hCc htag q)))⟩

end

end NLAlib
