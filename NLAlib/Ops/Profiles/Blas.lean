/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.Sum

/-!
# Profiles: the level-1 operations by sequential and by pairwise summation

Three tables of a signature over itself, each implementing some operations and keeping the rest:

## Main results

* `NLAlib.Ops.Blas.level1`: `dot`, `nrm2` over `sum`; `axpy`, `scal`, `copy` as loops;
* `NLAlib.Ops.Blas.sumSeq`: `sum` by sequential summation;
* `NLAlib.Ops.Blas.sumPairwise`: `sum` by pairwise summation, one level of the recursion.

Two profiles, by stacking:

* `NLAlib.Ops.Blas.seq = level1` over `sumSeq`, with `dot` error `(1 + u) ^ n - 1`;
* `NLAlib.Ops.Blas.pairwise k = level1` over the `k`-fold iterate of `sumPairwise`, with `dot`
  error `(1 + u) ^ (⌈log₂ n⌉ + 1) - 1` for the lengths `n` with `⌈log₂ n⌉ < k`.

Each has one certificate (`NLAlib.Ops.Blas.seq_certifies`,
`NLAlib.Ops.Blas.pairwise_certifies`) over the standard model of scalar arithmetic, assembled one
line per operation from the certificates of the implementations; the accounting certificates
are evaluations of static costs.
-/

@[expose] public section

namespace NLAlib.Ops.Blas

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op]

/-! ### Tables, costs and workspaces -/

/-- `dot`, `nrm2` over `sum`; `axpy`, `scal`, `copy` as loops; the rest kept. -/
def level1Table : Table Op Op Tst := fun o =>
  match Has.proj (G := Blas1Op) o with
  | some .dot => .inl dotSum
  | some .nrm2 => .inl nrm2Sum
  | some .axpy => .inl axpyLoop
  | some .scal => .inl scalLoop
  | some .copy => .inl copyLoop
  | _ => .inr o

/-- `sum` by sequential summation; the rest kept. -/
def sumSeqTable : Table Op Op Tst := fun o =>
  match Has.proj (G := Blas1Op) o with
  | some .sum => .inl sumSeq
  | _ => .inr o

/-- `sum` by pairwise summation (its tree calls `sum`); the rest kept. -/
def sumPairwiseTable : Table Op Op Tst := fun o =>
  match Has.proj (G := Blas1Op) o with
  | some .sum => .inl sumPairwise
  | _ => .inr o

/-- One call of a scalar operation. -/
noncomputable abbrev sc (a : ScalarOp) : Count Op Tst := Count.one (Has.inj a) []

/-- The cost of each operation of `level1Table`. -/
noncomputable def level1Cost (o : Op) (d : List ℕ) : Count Op Tst :=
  match Has.proj (G := Blas1Op) o, d with
  | some .dot, [n] => n • sc .mul + Count.one (Has.inj Blas1Op.sum) [n]
  | some .nrm2, [n] => n • sc .mul + (Count.one (Has.inj Blas1Op.sum) [n] + sc .sqrt)
  | some .axpy, [n] => n • (sc .mul + sc .add)
  | some .scal, [n] => n • sc .div
  | some .copy, [n] => n • sc .copy
  | _, _ => Count.one o d

/-- The cost of sequential summation: a literal, a copy if `n ≥ 1`, and `n - 1` additions. -/
noncomputable def sumSeqCost (o : Op) (d : List ℕ) : Count Op Tst :=
  match Has.proj (G := Blas1Op) o, d with
  | some .sum, [n] => sc (.lit 0) + ((1 - (1 - n)) • sc .copy + (n - 1) • sc .add)
  | _, _ => Count.one o d

/-- The cost of one level of pairwise summation. -/
noncomputable def sumPairwiseCost (o : Op) (d : List ℕ) : Count Op Tst :=
  match Has.proj (G := Blas1Op) o, d with
  | some .sum, [n] => (1 - n) • sc (.lit 0) + ((1 - (n - 1)) * (1 - (1 - n))) • sc .copy +
      (1 - (1 - n / 2)) • (Count.one (Has.inj Blas1Op.sum) [n / 2] +
        (Count.one (Has.inj Blas1Op.sum) [n - n / 2] + sc .add))
  | _, _ => Count.one o d

/-- The workspaces, given the workspace `wsum n` of `sum` at the length `n`. -/
def ws (wsum : ℕ → ℕ) (o : Op) (d : List ℕ) : ℕ :=
  match Has.proj (G := Blas1Op) o, d with
  | some .sum, [n] => wsum n
  | some .dot, [n] => n + wsum n
  | some .nrm2, [n] => n + wsum n
  | some .axpy, _ => 1
  | _, _ => 0

/-- The workspace of pairwise summation: two cells per level. -/
def pairWs (n : ℕ) : ℕ := 2 * Nat.clog 2 n

/-- `dot`, `nrm2` over `sum`; `axpy`, `scal`, `copy` as loops. -/
noncomputable def level1 (wsum : ℕ → ℕ) : Profile Op Op Tst :=
  { table := level1Table, cost := level1Cost, ws := ws wsum, wsLo := ws wsum }

/-- `sum` by sequential summation. -/
noncomputable def sumSeq : Profile Op Op Tst :=
  { table := sumSeqTable, cost := sumSeqCost, ws := ws 0, wsLo := ws 0 }

/-- `sum` by pairwise summation, one level. -/
noncomputable def sumPairwise : Profile Op Op Tst :=
  { table := sumPairwiseTable, cost := sumPairwiseCost, ws := ws pairWs, wsLo := ws pairWs }

/-- **The profile of sequential summation.** -/
noncomputable def seq : Profile Op Op Tst := (level1 0).over sumSeq

/-- **The profile of pairwise summation**, of depth `k`. -/
noncomputable def pairwise (k : ℕ) : Profile Op Op Tst := (level1 pairWs).over (sumPairwise.iter k)

omit [Apart Blas1Op ScalarOp Op] in
/-- Sequential BLAS leaves operations outside the BLAS1 group as primitives. -/
theorem seq_table_kept {o : Op} (ho : Has.proj (G := Blas1Op) o = none) :
    (seq (Op := Op) (Tst := Tst)).table o = .inr o := by
  simp [seq, Profile.over, level1, level1Table, sumSeq, sumSeqTable, Table.comp, ho]

omit [Apart Blas1Op ScalarOp Op] in
/-- Pairwise BLAS leaves operations outside the BLAS1 group as primitives at every depth. -/
theorem pairwise_table_kept (k : ℕ) {o : Op} (ho : Has.proj (G := Blas1Op) o = none) :
    (pairwise (Op := Op) (Tst := Tst) k).table o = .inr o := by
  have ht : (sumPairwise (Op := Op) (Tst := Tst)).table o = .inr o := by
    simp [sumPairwise, sumPairwiseTable, ho]
  have hiter : ∀ j, (sumPairwise (Op := Op) (Tst := Tst)).table.iter j o = .inr o := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simpa only [Table.iter, Table.comp, ht] using ih
  simp only [pairwise, Profile.over, Profile.iter_table]
  have hl : level1Table (Op := Op) (Tst := Tst) o = .inr o := by
    simp [level1Table, ho]
  simpa only [level1, Table.comp, hl] using hiter k

/-! ### Accounting certificates -/

theorem level1_accounts (wsum : ℕ → ℕ) (I : Interp Op Tst K) :
    (level1Table (Op := Op)).Accounts I (ws wsum) level1Cost (ws wsum) := by
  refine Table.accounts_of_static ?_ ?_ I
  · intro o R hT d offs hd ho
    simp only [level1Table] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT <;> obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
    · obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
      simp [dotSum, prodLoop, staticCost, staticPeak, useCost, level1Cost, ws, h]
    · obtain ⟨a, b, c, e, rfl⟩ := List.length_eq_four.mp ho
      simp [axpyLoop, staticCost, staticPeak, useCost, level1Cost, ws, h]
    · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
      simp [nrm2Sum, prodLoop, staticCost, staticPeak, useCost, level1Cost, ws, h]
    · obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
      simp [scalLoop, staticCost, staticPeak, useCost, level1Cost, ws, h]
    · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
      simp [copyLoop, staticCost, staticPeak, useCost, level1Cost, ws, h]
  · intro o o' hT d
    simp only [level1Table] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT <;> simp [level1Cost, h]

theorem sumSeq_accounts (I : Interp Op Tst K) :
    (sumSeqTable (Op := Op)).Accounts I (ws 0) sumSeqCost (ws 0) := by
  refine Table.accounts_of_static ?_ ?_ I
  · intro o R hT d offs hd ho
    simp only [sumSeqTable] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
    simp [NLAlib.Ops.sumSeq, Stmt.ifPos, staticCost, staticPeak, useCost, sumSeqCost, ws, h]
  · intro o o' hT d
    simp only [sumSeqTable] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT <;> simp [sumSeqCost, h]

omit [Has ScalarOp Op] [Apart Blas1Op ScalarOp Op] in
theorem pairWs_step {n : ℕ} (hn : 2 ≤ n) :
    2 + max (pairWs (n / 2)) (pairWs (n - n / 2)) ≤ pairWs n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
    rw [Nat.clog_of_two_le (by norm_num) hn, show (n + 2 - 1) / 2 = n - n / 2 by omega]
  have h2 : Nat.clog 2 (n / 2) ≤ Nat.clog 2 (n - n / 2) := Nat.clog_mono_right 2 (by omega)
  simp only [pairWs]
  omega

theorem sumPairwise_accounts (I : Interp Op Tst K) :
    (sumPairwiseTable (Op := Op)).Accounts I (ws pairWs) sumPairwiseCost (ws pairWs) := by
  refine Table.accounts_of_static ?_ ?_ I
  · intro o R hT d offs hd ho
    simp only [sumPairwiseTable] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
    refine ⟨by simp [NLAlib.Ops.sumPairwise, Stmt.ifPos, Stmt.ifZero, staticCost, useCost,
      sumPairwiseCost, h, mul_smul, add_assoc], ?_⟩
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have h0 : n / 2 = 0 := by omega
      simp [NLAlib.Ops.sumPairwise, Stmt.ifPos, Stmt.ifZero, staticPeak, ws, h, h0]
    · have h1 : 1 - (1 - n / 2) = 1 := by omega
      have h2 : 1 - n = 0 := by omega
      have h3 : 1 - (n - 1) = 0 := by omega
      have := pairWs_step hn
      simp [NLAlib.Ops.sumPairwise, Stmt.ifPos, Stmt.ifZero, staticPeak, ws, h, h1, h2, h3]
      omega
  · intro o o' hT d
    simp only [sumPairwiseTable] at hT
    rcases h : Has.proj (G := Blas1Op) o with _ | (_ | _ | _ | _ | _ | _) <;>
      simp only [h] at hT <;> cases hT <;> simp [sumPairwiseCost, h]

end NLAlib.Ops.Blas
