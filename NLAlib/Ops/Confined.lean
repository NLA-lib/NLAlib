/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.BlockRel
public import NLAlib.Ops.Static

/-!
# Confined contracts, uniform models and charged resources

`NLAlib.Ops.AccessModel` accepts any contract for a primitive: a contract may depend on the
whole problem input, may read or write cells that are not operands of the call, and may be
given zero work. A certificate over such a model is a true statement about that model, and can
still mislead: a unit-cost primitive can write the answer.

This file names three properties that exclude this, as classes on the model, so that a
certificate can state them and a check can report them. They restrict no existing statement.

* A contract is **confined** (`NLAlib.Ops.Contract.Confined`) when it is in operand form
  (`NLAlib.Ops.BlockRel.spec`): it reads the operand blocks and the tape window, writes the
  output blocks, and the lengths of all of them are functions of the dimensions of the call,
  the key of its cost. A query is confined (`NLAlib.Ops.QueryContract.Confined`) when its
  result depends on the memory only through the blocks read at its operands.
* A model is **uniform** (`NLAlib.Ops.AccessModel.Uniform`) when its contracts do not depend on
  the sizes or the input. A model with a declared oracle, such as the application of an operator
  given as semantic data, is confined and not uniform.
* A model is **charged** (`NLAlib.Ops.AccessModel.Charged`) when every primitive, query and
  structural instruction has positive work.

## Main results

* `NLAlib.Ops.Contract.Confined.frame`: a confined call changes no buffer that is not an output
  operand.
* `NLAlib.Ops.AccessModel.Charged.size_le_work`: under a charged model the work of a count is at
  least its number of instructions.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- A block update leaves the other buffers of the store unchanged. -/
theorem Store.getElem?_updBlock_of_ne (s : Store K) {b b' : ℕ} (h : b ≠ b') (off : ℕ)
    (xs : List K) : (s.updBlock b off xs)[b']? = s[b']? := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [Store.updBlock, ih, Store.getElem?_upd, if_neg h]

/-- Writing blocks at the operands `zs` leaves every buffer that is not one of them unchanged. -/
theorem Mem.getElem?_updBlocks_of_ne (m : Mem K) {zs : List (ℕ × ℕ)} {b : ℕ}
    (h : ∀ z ∈ zs, z.1 ≠ b) (ys : List (List K)) :
    (m.updBlocks zs ys).store[b]? = m.store[b]? := by
  induction zs generalizing m ys with
  | nil => cases ys <;> rfl
  | cons z zs ih => cases ys with
    | nil => rfl
    | cons y ys =>
      rw [Mem.updBlocks_cons, ih _ fun z hz => h z (List.mem_cons_of_mem _ hz)]
      exact Store.getElem?_updBlock_of_ne _ (h z List.mem_cons_self) _ _

/-- **A confined contract**: a contract in operand form. It reads the operand blocks and the
tape window, writes the output blocks, and nothing else; the lengths of the blocks are functions
of the dimensions of the call. -/
def Contract.Confined (C : Contract K) : Prop :=
  ∃ (R : BlockRel K) (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop), C = R.spec adm

/-- A contract in operand form is confined. -/
theorem BlockRel.confined_spec (R : BlockRel K)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) : (R.spec adm).Confined :=
  ⟨R, adm, rfl⟩

/-- A confined call changes no buffer that is not an output operand. -/
theorem Contract.Confined.frame {C : Contract K} (hC : C.Confined) {md : Mode} {d : List ℕ}
    {ins outs : List (ℕ × ℕ)} {w : List K} {m m' : Mem K}
    (h : (C.spec md d ins outs w).post m m') {b : ℕ} (hb : ∀ z ∈ outs, z.1 ≠ b) :
    m'.store[b]? = m.store[b]? := by
  obtain ⟨R, adm, rfl⟩ := hC
  obtain ⟨xs, -, -, ys, -, -, rfl⟩ := h
  exact Mem.getElem?_updBlocks_of_ne m hb ys

/-- **A confined query**: the Boolean of a test and the number of an index use depend on the
memory only through the blocks read at the operands, whose lengths are functions of the
dimensions (one cell per operand for an index use). -/
def QueryContract.Confined (Q : QueryContract K) : Prop :=
  ∃ (lens : List ℕ → List ℕ)
    (T : List ℕ → List (ℕ × ℕ) → Option (List (List K)) → Option Bool → Prop)
    (X : List (ℕ × ℕ) → Option (List (List K)) → Option ℕ → Prop),
    (∀ d a m result, Q.test d a m result ↔ T d a (m.readBlocks a (lens d)) result) ∧
      ∀ a m result, Q.index a m result ↔ X a (m.readBlocks a (a.map fun _ => 1)) result

/-- A confined test gives the same verdicts on two memories with the same operand blocks. -/
theorem QueryContract.Confined.test_congr {Q : QueryContract K} (hQ : Q.Confined) :
    ∃ lens : List ℕ → List ℕ, ∀ (d : List ℕ) (a : List (ℕ × ℕ)) (m m' : Mem K)
      (result : Option Bool), m.readBlocks a (lens d) = m'.readBlocks a (lens d) →
        (Q.test d a m result ↔ Q.test d a m' result) := by
  obtain ⟨lens, T, X, hT, -⟩ := hQ
  exact ⟨lens, fun d a m m' result h => by rw [hT, hT, h]⟩

/-- **A uniform model**: the contracts of the primitives and of the queries do not depend on
the sizes or on the input. No primitive is an oracle for the semantic data. -/
class AccessModel.Uniform (M : AccessModel Op Tst P) : Prop where
  /-- The contract of a primitive is the same at every size and input. -/
  operation : ∀ d x d' x' o, M.operation d x o = M.operation d' x' o
  /-- The contract of a query is the same at every size and input. -/
  query : ∀ d x d' x' q, M.query d x q = M.query d' x' q

/-- **A confined model**: every primitive contract and every query contract is confined. -/
class AccessModel.Confined (M : AccessModel Op Tst P) : Prop where
  /-- Every primitive reads and writes its operand blocks only. -/
  operation : ∀ d x o, (M.operation d x o).Confined
  /-- Every query reads its operand blocks only. -/
  query : ∀ d x q, (M.query d x q).Confined

/-- **A charged model**: every primitive, query and structural instruction has positive work at
every list of dimensions. -/
class AccessModel.Charged (M : AccessModel Op Tst P) : Prop where
  /-- Every primitive has positive work. -/
  operation : ∀ o d, 0 < M.resources.operationWork o d
  /-- Every query has positive work. -/
  query : ∀ q d, 0 < M.resources.queryWork q d
  /-- Every structural instruction has positive work. -/
  core : ∀ k d, 0 < M.resources.coreWork k d

/-- The number of instructions of a count: primitives, structural instructions and queries. -/
noncomputable def Count.size : Count Op Tst →+ ℕ := Count.lift fun _ _ => 1

/-- Under a charged model the work of a count is at least its number of instructions. -/
theorem AccessModel.Charged.size_le_work (M : AccessModel Op Tst P) [hM : M.Charged]
    (c : Count (Op ⊕ Bookkeeping) Tst) : Count.size c ≤ M.resources.work c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Nat.add_le_add ha hb
  | single k n =>
    rw [Count.size, ResourceModel.work, Count.lift_single, Count.lift_single]
    refine Nat.mul_le_mul le_rfl ?_
    obtain ⟨(o | k) | q, d⟩ := k
    · exact hM.operation o d
    · exact hM.core k d
    · exact hM.query q d

end NLAlib.Ops
