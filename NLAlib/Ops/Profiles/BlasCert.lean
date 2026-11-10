/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Blas

/-!
# Certificates and costs of the two level-1 profiles

## Main results

* Constants: `NLAlib.Ops.Blas.seq.err u`, `NLAlib.Ops.Blas.pairwise.err u`, with the `dot` errors
  `(1 + u) ^ n - 1` and `(1 + u) ^ (⌈log₂ n⌉ + 1) - 1`.
* Certificates: `NLAlib.Ops.Blas.seq_certifies`, `NLAlib.Ops.Blas.pairwise_certifies`, over every
  interpretation of scalar arithmetic that is a machine meeting the standard model at `u`. The
  second is the recursion: one level (`NLAlib.Ops.Blas.sumPairwise_certifies`) iterated by
  `NLAlib.Ops.Profile.Certifies.iter`.
* Costs: `NLAlib.Ops.Blas.seq_cost_dot`, `NLAlib.Ops.Blas.pairwise_cost_dot`: `n`
  multiplications and `n - 1` additions in both; the pairwise count is the `k`-fold push-forward,
  evaluated by induction on the depth (`NLAlib.Ops.Blas.sumPairwise_iter_cost_sum`).
* Witness: `NLAlib.Ops.Blas.exists_isBlas1`.
-/

@[expose] public section

namespace NLAlib.Ops.Blas

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op]

/-! ### Constants -/

/-- The accuracy parameters of `level1` over a `sum` of error `es` and scalar arithmetic at the
unit roundoff `u`. -/
def level1Err (u : ℝ) (es : ℕ → ℝ) : Blas1Err :=
  ⟨es, fun n => (1 + u) * (1 + es n) - 1, (1 + u) ^ 2 - 1, u, u⟩

/-- The error of sequential summation. -/
def seqSumErr (u : ℝ) (n : ℕ) : ℝ := (1 + u) ^ (n - 1) - 1

/-- The error of pairwise summation. -/
def pairSumErr (u : ℝ) (n : ℕ) : ℝ := (1 + u) ^ Nat.clog 2 n - 1

/-- The accuracy parameters of the profile of sequential summation. -/
def seq.err (u : ℝ) : Blas1Err := level1Err u (seqSumErr u)

/-- The accuracy parameters of the profile of pairwise summation. -/
def pairwise.err (u : ℝ) : Blas1Err := level1Err u (pairSumErr u)

theorem seqSumErr_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ seqSumErr u n :=
  sub_nonneg.mpr (one_le_pow₀ (by linarith))

theorem pairSumErr_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ pairSumErr u n :=
  sub_nonneg.mpr (one_le_pow₀ (by linarith))

/-- **The `dot` error of sequential summation**: `(1 + u) ^ n - 1`. -/
theorem seq.err_dot (u : ℝ) {n : ℕ} (hn : 1 ≤ n) : (seq.err u).dot n = (1 + u) ^ n - 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [seq.err, level1Err, seqSumErr, Nat.add_sub_cancel]
  ring

/-- **The `dot` error of pairwise summation**: `(1 + u) ^ (⌈log₂ n⌉ + 1) - 1`. -/
theorem pairwise.err_dot (u : ℝ) (n : ℕ) :
    (pairwise.err u).dot n = (1 + u) ^ (Nat.clog 2 n + 1) - 1 := by
  simp only [pairwise.err, level1Err, pairSumErr]
  ring

omit [Apart Blas1Op ScalarOp Op] in
/-- The linked program of the pairwise profile runs with the workspaces of the profile. -/
theorem pairwise_wsLo (k : ℕ) : (pairwise (Op := Op) (Tst := Tst) k).wsLo = ws pairWs :=
  Profile.iter_wsLo _ k

/-! ### Certificates -/

section Cert

variable [Inhabited K] {M : Machine K} {u : ℝ} {dec : K → ℝ}

/-- **The certificate of `level1`**, over scalar arithmetic and a `sum` of error `es`. -/
theorem level1_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) {es : ℕ → ℝ} (hes : ∀ n, 0 ≤ es n)
    (ok : ℕ → Prop) (wsum : ℕ → ℕ) :
    (level1 (Op := Op) (Tst := Tst) wsum).Certifies (fun I => IsScalar M I ∧ IsSum dec es ok I)
      (fun J => IsScalar M J ∧ IsBlas1 dec (level1Err u es) ok J) :=
  .of_accounts (fun I ⟨hI, hS⟩ =>
    ⟨fun a => Interp.link_meets_kept (by simp [level1, level1Table]) (hI a),
    { sum := Interp.link_meets_kept (by simp [level1, level1Table]) hS
      dot := Interp.link_meets (by simp [level1, level1Table]) (dotSum_spec hI hM hS hes)
      axpy := Interp.link_meets (by simp [level1, level1Table]) (axpyLoop_spec hI hM hu ok)
      nrm2 := Interp.link_meets (by simp [level1, level1Table]) (nrm2Sum_spec hI hM hS hes)
      scal := Interp.link_meets (by simp [level1, level1Table]) (scalLoop_spec hI hM ok)
      copy := Interp.link_meets (by simp [level1, level1Table]) (copyLoop_spec hI ok) }⟩)
    (level1_accounts wsum) fun I _ => Profile.tapeLocal_noDraw rfl rfl I

/-- **The certificate of sequential summation.** -/
theorem sumSeq_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (sumSeq (Op := Op) (Tst := Tst)).Certifies (fun I => IsScalar M I)
      (fun J => IsScalar M J ∧ IsSum dec (seqSumErr u) ok J) :=
  .of_accounts (fun I hI =>
    ⟨fun a => Interp.link_meets_kept (by simp [sumSeq, sumSeqTable]) (hI a),
      Interp.link_meets (by simp [sumSeq, sumSeqTable]) (sumSeq_spec hI hM hu ok)⟩)
    sumSeq_accounts fun I _ => Profile.tapeLocal_noDraw rfl rfl I

/-- **One level of pairwise summation**: from the lengths of depth below `k` to those of depth
below `k + 1`. -/
theorem sumPairwise_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) (k : ℕ) :
    (sumPairwise (Op := Op) (Tst := Tst)).Certifies
      (fun I => IsScalar M I ∧ IsSum dec (pairSumErr u) (fun n => Nat.clog 2 n < k) I)
      (fun J => IsScalar M J ∧ IsSum dec (pairSumErr u) (fun n => Nat.clog 2 n < k + 1) J) :=
  .of_accounts (fun I ⟨hI, hS⟩ =>
    ⟨fun a => Interp.link_meets_kept (by simp [sumPairwise, sumPairwiseTable]) (hI a),
      Interp.link_meets (by simp [sumPairwise, sumPairwiseTable])
        (sumPairwise_spec hI hM hu hS)⟩)
    sumPairwise_accounts fun I _ => Profile.tapeLocal_noDraw rfl rfl I

/-- **Pairwise summation of depth `k`**, by iterating one level: over any scalar arithmetic,
whatever `sum` means below. -/
theorem sumPairwise_iter_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) (k : ℕ) :
    ((sumPairwise (Op := Op) (Tst := Tst)).iter k).Certifies (fun I => IsScalar M I)
      (fun J => IsScalar M J ∧ IsSum dec (pairSumErr u) (fun n => Nat.clog 2 n < k) J) :=
  (Profile.Certifies.iter (C := fun k J => IsScalar M J ∧
    IsSum dec (pairSumErr u) (fun n => Nat.clog 2 n < k) J)
    (sumPairwise_certifies hM hu) rfl rfl k).mono
    (fun _ hI => ⟨hI, fun _ _ _ _ _ ⟨_, hadm, _⟩ => absurd hadm.1 (Nat.not_lt_zero _)⟩)
    fun _ h => h

/-- **The certificate of the profile of sequential summation.** -/
theorem seq_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (seq (Op := Op) (Tst := Tst)).Certifies (fun I => IsScalar M I)
      (fun J => IsScalar M J ∧ IsBlas1 dec (seq.err u) ok J) :=
  (level1_certifies hM hu (seqSumErr_nonneg hu) ok 0).over (sumSeq_certifies hM hu ok) rfl rfl

/-- **The certificate of the profile of pairwise summation** of depth `k`, for the lengths `n`
with `⌈log₂ n⌉ < k`. -/
theorem pairwise_certifies (hM : StdModel u dec M) (hu : 0 ≤ u) (k : ℕ) :
    (pairwise (Op := Op) (Tst := Tst) k).Certifies (fun I => IsScalar M I)
      (fun J => IsScalar M J ∧ IsBlas1 dec (pairwise.err u) (fun n => Nat.clog 2 n < k) J) :=
  (level1_certifies hM hu (pairSumErr_nonneg hu) _ pairWs).over
    (sumPairwise_iter_certifies hM hu k) (by simp [level1, sumPairwise])
    (by simp [level1, sumPairwise])

end Cert

/-! ### Costs -/

/-- The scalar operations of pairwise summation of `n` words: a literal if `n = 0`, `n` copies
and `n - 1` additions. -/
noncomputable def pairCount (n : ℕ) : Count Op Tst :=
  (1 - n) • sc (.lit 0) + (n • sc .copy + (n - 1) • sc .add)

omit [Apart Blas1Op ScalarOp Op] in
/-- The iterate of pairwise summation keeps the cost of the operations it keeps. -/
theorem sumPairwise_iter_cost_kept (k : ℕ) {o : Op}
    (h : Has.proj (G := Blas1Op) o ≠ some .sum) (d : List ℕ) :
    ((sumPairwise (Op := Op) (Tst := Tst)).iter k).cost o d = Count.one o d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Profile.iter_cost_succ]
    have : (sumPairwise (Op := Op) (Tst := Tst)).cost o d = Count.one o d := by
      simp only [sumPairwise, sumPairwiseCost]
      split
      · exact absurd (by assumption) h
      · rfl
    rw [this, Count.push_one, ih]

/-- **The cost of pairwise summation of depth `k`**, by evaluating the `k`-fold push-forward:
for `⌈log₂ n⌉ < k`, the count `pairCount n`. No call of `sum` is left. -/
theorem sumPairwise_iter_cost_sum (k n : ℕ) (h : Nat.clog 2 n < k) :
    ((sumPairwise (Op := Op) (Tst := Tst)).iter k).cost (Has.inj Blas1Op.sum) [n] =
      pairCount n := by
  induction k generalizing n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    have hk : ∀ a : ScalarOp, ((sumPairwise (Op := Op) (Tst := Tst)).iter k).cost (Has.inj a)
        [] = sc a := fun a => sumPairwise_iter_cost_kept k (by simp) []
    have hc0 : (sumPairwise (Op := Op) (Tst := Tst)).cost = sumPairwiseCost := rfl
    rw [Profile.iter_cost_succ, hc0]
    simp only [sumPairwiseCost, Has.proj_inj, map_add, map_nsmul, Count.push_one]
    rw [hk, hk, hk]
    obtain rfl | rfl | h2 : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
    · simp [pairCount]
    · simp [pairCount]
    · have hc : Nat.clog 2 (n - n / 2) < k := by
        rw [Nat.clog_of_two_le (by norm_num) h2, show (n + 2 - 1) / 2 = n - n / 2 by omega] at h
        omega
      have hc' : Nat.clog 2 (n / 2) < k := lt_of_le_of_lt (Nat.clog_mono_right 2 (by omega)) hc
      have h1 : 1 - n = 0 := by omega
      have h2 : 1 - (n - 1) = 0 := by omega
      have h3 : 1 - (1 - n / 2) = 1 := by omega
      rw [h1, h2, h3, ih _ hc', ih _ hc, zero_mul, zero_smul, zero_smul, zero_add, zero_add,
        one_smul]
      obtain ⟨a, ha⟩ : ∃ a, n / 2 = a + 1 := ⟨n / 2 - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, n - n / 2 = b + 1 := ⟨n - n / 2 - 1, by omega⟩
      rw [hb, ha]
      obtain rfl : n = a + b + 2 := by omega
      simp only [pairCount, show 1 - (a + 1) = 0 by omega, show 1 - (b + 1) = 0 by omega,
        show 1 - (a + b + 2) = 0 by omega, zero_smul, zero_add, Nat.add_sub_cancel,
        show a + b + 2 - 1 = a + b + 1 by omega]
      module

/-- **The cost of `dot` in the profile of sequential summation**: `n` multiplications, a literal,
a copy if `n ≥ 1`, and `n - 1` additions. -/
@[countNF] theorem seq_cost_dot (n : ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj Blas1Op.dot) [n] =
      n • sc .mul + (sc (.lit 0) + ((1 - (1 - n)) • sc .copy + (n - 1) • sc .add)) := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

/-- **The cost of `dot` in the profile of pairwise summation** of depth `k`, for
`⌈log₂ n⌉ < k`: `n` multiplications, `n` copies and `n - 1` additions. -/
@[countNF] theorem pairwise_cost_dot (k n : ℕ) (h : Nat.clog 2 n < k) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj Blas1Op.dot) [n] =
      n • sc .mul + pairCount n := by
  simp only [pairwise, Profile.over, level1, level1Cost, Has.proj_inj, map_add, map_nsmul,
    Count.push_one]
  rw [sumPairwise_iter_cost_kept k (by simp), sumPairwise_iter_cost_sum k n h]

/-- The costs of the other operations in the profile of pairwise summation of depth `k`, for
`⌈log₂ n⌉ < k`. -/
@[countNF] theorem pairwise_cost_nrm2 (k n : ℕ) (h : Nat.clog 2 n < k) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj Blas1Op.nrm2) [n] =
      n • sc .mul + (pairCount n + sc .sqrt) := by
  simp [pairwise, Profile.over, level1, level1Cost, sumPairwise_iter_cost_kept,
    sumPairwise_iter_cost_sum k n h]

@[countNF] theorem pairwise_cost_axpy (k n : ℕ) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj Blas1Op.axpy) [n] =
      n • (sc .mul + sc .add) := by
  simp [pairwise, Profile.over, level1, level1Cost, sumPairwise_iter_cost_kept]

@[countNF] theorem pairwise_cost_scal (k n : ℕ) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj Blas1Op.scal) [n] = n • sc .div := by
  simp [pairwise, Profile.over, level1, level1Cost, sumPairwise_iter_cost_kept]

@[countNF] theorem pairwise_cost_copy (k n : ℕ) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj Blas1Op.copy) [n] = n • sc .copy := by
  simp [pairwise, Profile.over, level1, level1Cost, sumPairwise_iter_cost_kept]

@[countNF] theorem pairwise_cost_scalar (k : ℕ) (a : ScalarOp) (d : List ℕ) :
    (pairwise (Op := Op) (Tst := Tst) k).cost (Has.inj a) d = Count.one (Has.inj a) d := by
  simp [pairwise, Profile.over, level1, level1Cost, sumPairwise_iter_cost_kept]

/-- The costs of the other operations in the profile of sequential summation. -/
@[countNF] theorem seq_cost_nrm2 (n : ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj Blas1Op.nrm2) [n] =
      n • sc .mul + (sc (.lit 0) + ((1 - (1 - n)) • sc .copy + (n - 1) • sc .add) + sc .sqrt) := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

@[countNF] theorem seq_cost_axpy (n : ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj Blas1Op.axpy) [n] =
      n • (sc .mul + sc .add) := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

@[countNF] theorem seq_cost_scal (n : ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj Blas1Op.scal) [n] = n • sc .div := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

@[countNF] theorem seq_cost_copy (n : ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj Blas1Op.copy) [n] = n • sc .copy := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

@[countNF] theorem seq_cost_scalar (a : ScalarOp) (d : List ℕ) :
    (seq (Op := Op) (Tst := Tst)).cost (Has.inj a) d = Count.one (Has.inj a) d := by
  simp [seq, Profile.over, level1, level1Cost, sumSeq, sumSeqCost]

/-! ### Witness -/

/-- **Witness**: the contracts of scalar arithmetic and of the level-1 operations can be met
together, for every `u ≥ 0`, at the constants of the profile of sequential summation and for
every length. -/
theorem exists_isBlas1 {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (_ : Inhabited K) (dec : K → ℝ) (M : Machine K)
      (J : Interp (ScalarOp ⊕ Blas1Op) Empty K),
      StdModel u dec M ∧ IsScalar M J ∧ IsBlas1 dec (seq.err u) (fun _ => True) J := by
  let F : ScalarOp ⊕ Blas1Op → BlockFn ℝ := fun o => o.elim exactMachine.fn fun _ => .const 0
  have hI : IsScalar exactMachine (Interp.ofFns F : Interp (ScalarOp ⊕ Blas1Op) Empty ℝ) :=
    isScalar_ofFns _ _ fun _ => rfl
  exact ⟨ℝ, ⟨0⟩, id, exactMachine, _, stdModel_exact hu,
    (seq_certifies (stdModel_exact hu) hu _).meets _ hI⟩

/-- **Witness for the contract of `sum` alone**, jointly with scalar arithmetic: for every
`u ≥ 0`, every error function that is nonnegative on the admitted lengths and every set of
admitted lengths, by exact summation. This is the contract set of the implementations over
`sum` (`dotSum_spec`, `nrm2Sum_spec`, `sumPairwise_spec`). -/
theorem exists_isSum {u : ℝ} (hu : 0 ≤ u) (e : ℕ → ℝ) (ok : ℕ → Prop)
    (he : ∀ n, ok n → 0 ≤ e n) :
    ∃ (K : Type) (_ : Inhabited K) (dec : K → ℝ) (M : Machine K)
      (J : Interp (ScalarOp ⊕ Blas1Op) Empty K),
      StdModel u dec M ∧ IsScalar M J ∧ IsSum dec e ok J := by
  let F : ScalarOp ⊕ Blas1Op → BlockFn ℝ := fun o => o.elim exactMachine.fn fun _ =>
    .of1 1 (fun d => d.headD 0) (fun _ => 1) fun d x =>
      some [∑ k ∈ Finset.range (d.headD 0), x.getD k 0]
  have hI : IsScalar exactMachine (Interp.ofFns F : Interp (ScalarOp ⊕ Blas1Op) Empty ℝ) :=
    isScalar_ofFns _ _ fun _ => rfl
  refine ⟨ℝ, ⟨0⟩, id, exactMachine, _, stdModel_exact hu, hI, ?_⟩
  refine (Interp.ofFns_isFn F .total (.inr .sum) AnyOperands).meets_rel (fun _ _ _ _ => trivial)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w xs m ins outs hnd _ hadm hr _
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  refine ⟨[[∑ j ∈ Finset.range k, xs.getD j 0]], by simp [F, BlockFn.of1], rfl, ?_⟩
  simp only [sumRel, IsSumErr, vec, id, List.headD_cons, sub_self, abs_zero]
  exact mul_nonneg (he k hadm.1) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

end NLAlib.Ops.Blas
