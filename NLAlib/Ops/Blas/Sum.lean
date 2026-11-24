/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Logic.Step
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Summation: sequential and pairwise

Two implementations of `sum` over scalar arithmetic.

* `NLAlib.Ops.sumSeqRoutine`: `z := x_0; z := z + x_i`. `n - 1` additions; error
  `(1 + u) ^ (n - 1) - 1`.
* `NLAlib.Ops.sumPairwise`: **recursive**. For `n ≥ 2` it calls `sum` on the two halves and adds
  the results; for `n ≤ 1` it copies. Its tree calls `sum`, the operation it implements; a
  program is obtained by linking it `k` times (`NLAlib.Ops.Table.iter`), which serves the lengths
  `n` with `⌈log₂ n⌉ < k`. `n - 1` additions; error `(1 + u) ^ ⌈log₂ n⌉ - 1`.

Each has its mathematics (the error bound of the function computed, on decoded values) and its
program part (the run of the tree writes that function of the input block).

## Main results

* `NLAlib.Ops.StdModel.abs_add_sub_le`: one rounded addition of two approximate sums.
* `NLAlib.Ops.isSumErr_sumSeqF`, `NLAlib.Ops.isSumErr_sumPairF`: the two error bounds.
* `NLAlib.Ops.sumSeqRoutine_meets_exact`: sequential summation writes `sumSeqF`, for any machine.
* `NLAlib.Ops.sumSeqRoutine_meets`, `NLAlib.Ops.sumPairwiseRoutine_meets`: the judgments under
  the standard model; `NLAlib.Ops.sumSeq_satisfies`, the contract of the operation `sum`,
  follows by `NLAlib.Ops.Routine.Meets.satisfies_ofRel`.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-! ### Mathematics -/

/-- **One rounded addition of two approximate sums**: if `a`, `b` approximate `S₁`, `S₂` up to
`e` relative to `T₁`, `T₂`, their rounded sum approximates `S₁ + S₂` up to
`(1 + u) (1 + e) - 1` relative to `T₁ + T₂`. -/
theorem StdModel.abs_add_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) {a b : K} {S₁ S₂ T₁ T₂ e : ℝ} (h1 : |dec a - S₁| ≤ e * T₁)
    (h2 : |dec b - S₂| ≤ e * T₂) (hS₁ : |S₁| ≤ T₁) (hS₂ : |S₂| ≤ T₂) :
    |dec (M.add a b) - (S₁ + S₂)| ≤ ((1 + u) * (1 + e) - 1) * (T₁ + T₂) := by
  have h := hM.add a b
  generalize dec (M.add a b) = r at h
  generalize dec a = s₁ at h h1
  generalize dec b = s₂ at h h2
  have ha : |s₁| ≤ (1 + e) * T₁ := by
    have := abs_add_le S₁ (s₁ - S₁)
    rw [add_sub_cancel] at this
    linarith
  have hb : |s₂| ≤ (1 + e) * T₂ := by
    have := abs_add_le S₂ (s₂ - S₂)
    rw [add_sub_cancel] at this
    linarith
  have hab : |s₁ + s₂| ≤ (1 + e) * (T₁ + T₂) := (abs_add_le s₁ s₂).trans (by linarith)
  have h3 : |r - (S₁ + S₂)| ≤ |r - (s₁ + s₂)| + |s₁ - S₁| + |s₂ - S₂| := by
    have := abs_add_three (r - (s₁ + s₂)) (s₁ - S₁) (s₂ - S₂)
    rwa [show r - (s₁ + s₂) + (s₁ - S₁) + (s₂ - S₂) = r - (S₁ + S₂) by ring] at this
  have h4 : u * |s₁ + s₂| ≤ u * ((1 + e) * (T₁ + T₂)) := mul_le_mul_of_nonneg_left hab hu
  nlinarith

/-- The words `x_0 + x_1 + … + x_j`, added from the left. -/
def seqF (M : Machine K) (x : ℕ → K) : ℕ → K
  | 0 => x 0
  | j + 1 => M.add (seqF M x j) (x (j + 1))

/-- The function of sequential summation. -/
def sumSeqF (M : Machine K) (x : ℕ → K) (n : ℕ) : K := if n = 0 then M.lit 0 else seqF M x (n - 1)

theorem abs_dec_seqF_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (x : ℕ → K) (j : ℕ) :
    |dec (seqF M x j) - ∑ k ∈ Finset.range (j + 1), dec (x k)| ≤
      ((1 + u) ^ j - 1) * ∑ k ∈ Finset.range (j + 1), |dec (x k)| := by
  induction j with
  | zero => simp [seqF]
  | succ j ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (j + 1), seqF]
    have he : 0 ≤ (1 + u) ^ j - 1 := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + u by linarith) (n := j)
      linarith
    have := hM.abs_add_sub_le hu ih (b := x (j + 1)) (S₂ := dec (x (j + 1)))
      (T₂ := |dec (x (j + 1))|) (by simpa using mul_nonneg he (abs_nonneg _))
      (Finset.abs_sum_le_sum_abs _ _) le_rfl
    rwa [show (1 + u) * (1 + ((1 + u) ^ j - 1)) - 1 = (1 + u) ^ (j + 1) - 1 by ring] at this

/-- **The error of sequential summation**: `(1 + u) ^ (n - 1) - 1`. -/
theorem isSumErr_sumSeqF {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (x : ℕ → K) (n : ℕ) :
    IsSumErr dec ((1 + u) ^ (n - 1) - 1) n x (sumSeqF M x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [IsSumErr, sumSeqF, hM.zero]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simpa [IsSumErr, sumSeqF] using abs_dec_seqF_sub_le hM hu x j

/-! ### Sequential summation: the tree and its run -/

section

variable [Has ScalarOp Op]

/-- **Sequential summation**: the cell `z` receives the rounded sum of the block `x`, added
from the left. -/
def sumSeqRoutine : Routine Op Tst := routine% [n] (x : n) → (z : 1) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (z);
  ifPos n { call (Has.inj ScalarOp.copy) [] (x) → (z) };
  for i < n - 1 { call (Has.inj ScalarOp.add) [] (z, x[(1 + i)]) → (z) }
}

variable [Inhabited K]

/-- What sequential summation writes, for any machine: `sumSeqF` of the block. -/
def sumSeqExactSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (xs) → ([v]) ensures v = sumSeqF M (vec xs) n

/-- Sequential summation, for any machine: the cell `z` receives `sumSeqF` of the block. -/
theorem sumSeqRoutine_meets_exact {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (sumSeqRoutine (Op := Op) (Tst := Tst)).Meets I (sumSeqExactSpec M) := by
  routine_intro [n] (x, z) reads (xs)
  have hz : z.2 < m.store.len z.1 := by omega
  refine (Writes.of_wp_upd_cell (P := fun v => v = sumSeqF M (vec xs) n) hz ?_).mono le_rfl
    fun m' _ ⟨hpos, v, hv, he⟩ => ⟨hpos, [[v]], hv, he⟩
  have hg : ∀ j < n, m.store.get x.1 (x.2 + j) = some (vec xs j) :=
    fun j hj => Store.get_of_readBlock hxs hj default
  refine wp_seq (wp_call_const (hI (.lit 0)) rfl rfl rfl trivial hz ?_)
  refine wp_seq (wp_ifPos rfl ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_neg (lt_irrefl 0)]
    exact wp_loop (k := 0) rfl (fun _ m' => m' = m.upd z (M.lit 0)) rfl
      (fun i hi => absurd hi (by omega))
      fun m' h => ⟨_, rfl, h⟩
  rw [if_pos hn]
  refine wp_call_un (hI .copy) rfl rfl rfl trivial (a := vec xs 0) ?_ rfl ?_ ?_
  · store_simp [show m.store.get x.1 x.2 = _ from hg 0 hn]
  · store_simp
  refine wp_loop (k := n - 1) rfl (fun i m' => m' = m.upd z (seqF M (vec xs) i)) (by simp [seqF]) ?_
    fun m' h => ⟨_, by simp [sumSeqF, hn.ne'], h⟩
  rintro i hi m' rfl
  refine wp_call_bin (hI .add) rfl rfl rfl trivial (a := seqF M (vec xs) i)
    (b := vec xs (1 + i)) ?_ ?_ rfl ?_ ?_
  · store_simp
  · store_simp [hg (1 + i) (by omega)]
  · store_simp
  · simp [seqF, Nat.add_comm]

/-- The written cell is the sum of the entries read, with relative error
$(1 + u)^{n - 1} - 1$ in the sum of their absolute values. -/
def sumSeqSpec (dec : K → ℝ) (u : ℝ) : Routine.Spec K :=
  .ofRel (sumRel dec fun n => (1 + u) ^ (n - 1) - 1) fun _ => True

/-- Sequential summation meets its specification under the standard model of arithmetic: the
bound of the standard model read off the word it writes. -/
theorem sumSeqRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) :
    (sumSeqRoutine (Op := Op) (Tst := Tst)).Meets I (sumSeqSpec dec u) := by
  routine_intro [n] (x, z)
  refine ((sumSeqRoutine_meets_exact hI) [n] [x, z] τ m X rfl rfl hlive hsep hr trivial
    hrooms).mono le_rfl fun m' _ ⟨hpos, zs, hzs, hpost⟩ => ⟨hpos, zs, hzs, ?_⟩
  split_reads hr as (xs)
  rcases zs with _ | ⟨_ | ⟨v, _ | ⟨_, _⟩⟩, _ | ⟨_, _⟩⟩ <;> try exact hpost.elim
  obtain rfl : v = sumSeqF M (vec xs) n := hpost
  exact isSumErr_sumSeqF hM hu _ n

/-- The routine of sequential summation implements the contract of the operation `sum`, the
operands of the routine being the input followed by the output. -/
theorem sumSeqRoutine_implements (dec : K → ℝ) (e : ℕ → ℝ) (ok : ℕ → Prop) :
    (sumSeqRoutine (Op := Op) (Tst := Tst)).Implements (sumRel dec e) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

/-- Sequential summation satisfies the contract of `sum` with the error
`(1 + u) ^ (n - 1) - 1`, for every length: a consequence of the judgment of its routine. -/
theorem sumSeq_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (sumSeqRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((sumRel dec fun n => (1 + u) ^ (n - 1) - 1).spec (OutApart ok)) :=
  (sumSeqRoutine_meets hI hM hu).satisfies_ofRel (sumSeqRoutine_implements dec _ ok)
    fun _ _ _ _ => trivial

end

/-! ### Pairwise summation -/

section Math

variable [Inhabited K]

omit [Inhabited K] in
/-- The error bound of pairwise summation, as a function of the length. -/
theorem pairErr_step {u : ℝ} (n : ℕ) (hn : 2 ≤ n) :
    (1 + u) * (1 + ((1 + u) ^ (Nat.clog 2 (n - n / 2)) - 1)) - 1 = (1 + u) ^ Nat.clog 2 n - 1 := by
  rw [Nat.clog_of_two_le (by norm_num) hn, show (n + 2 - 1) / 2 = n - n / 2 by omega]
  ring

/-- **One step of pairwise summation**: the rounded sum of the sums of the two halves. -/
theorem IsSumErr.pairwise {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) {n : ℕ} (hn : 2 ≤ n) {xs : List K} {v₁ v₂ : K}
    (h1 : IsSumErr dec ((1 + u) ^ Nat.clog 2 (n / 2) - 1) (n / 2) (vec (xs.take (n / 2))) v₁)
    (h2 : IsSumErr dec ((1 + u) ^ Nat.clog 2 (n - n / 2) - 1) (n - n / 2)
      (vec (xs.drop (n / 2))) v₂) :
    IsSumErr dec ((1 + u) ^ Nat.clog 2 n - 1) n (vec xs) (M.add v₁ v₂) := by
  have e1 : ∀ i < n / 2, vec (xs.take (n / 2)) i = vec xs i := fun i hi => by
    simp [vec, List.getD_eq_getElem?_getD, hi]
  have e2 : ∀ i, vec (xs.drop (n / 2)) i = vec xs (n / 2 + i) := fun i => by
    simp [vec, List.getD_eq_getElem?_getD, List.getElem?_drop]
  unfold IsSumErr at h1 h2 ⊢
  have c1 : ∑ k ∈ Finset.range (n / 2), dec (vec (xs.take (n / 2)) k) =
      ∑ k ∈ Finset.range (n / 2), dec (vec xs k) :=
    Finset.sum_congr rfl fun i hi => by rw [e1 i (Finset.mem_range.mp hi)]
  have c2 : ∑ k ∈ Finset.range (n / 2), |dec (vec (xs.take (n / 2)) k)| =
      ∑ k ∈ Finset.range (n / 2), |dec (vec xs k)| :=
    Finset.sum_congr rfl fun i hi => by rw [e1 i (Finset.mem_range.mp hi)]
  rw [c1, c2] at h1
  simp only [e2] at h2
  have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.range n, f k =
      ∑ k ∈ Finset.range (n / 2), f k + ∑ k ∈ Finset.range (n - n / 2), f (n / 2 + k) :=
    fun f => by rw [← Finset.sum_range_add, show n / 2 + (n - n / 2) = n by omega]
  rw [hsplit, hsplit fun k => |dec (vec xs k)|, ← pairErr_step n hn]
  have hmono : (1 + u) ^ Nat.clog 2 (n / 2) - 1 ≤ (1 + u) ^ Nat.clog 2 (n - n / 2) - 1 :=
    sub_le_sub_right (pow_le_pow_right₀ (by linarith)
      (Nat.clog_mono_right 2 (by omega))) 1
  exact hM.abs_add_sub_le hu (h1.trans (mul_le_mul_of_nonneg_right hmono
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))) h2 (Finset.abs_sum_le_sum_abs _ _)
    (Finset.abs_sum_le_sum_abs _ _)

end Math

section

variable [Has ScalarOp Op] [Has Blas1Op Op]

/-- **Pairwise summation**, recursive: the tree calls `sum`. Index variables: `n`, the offsets of
`x`, `z`, then the variables of the branches; buffer variables: `x`, `z`, then two scratch
cells. -/
def sumPairwise : Stmt Op Tst :=
  .seq (.ifZero (.var 0) (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨1, .var 2⟩]))
    (.seq (.ifZero (.var 0 - .const 1)
        (.ifPos (.var 0) (.call (Has.inj ScalarOp.copy) [] [⟨0, .var 1⟩] [⟨1, .var 2⟩])))
      (.ifPos (.var 0 / .const 2) (.alloc (.const 2)
        (.seq (.call (Has.inj Blas1Op.sum) [.var 0 / .const 2] [⟨0, .var 1⟩] [⟨2, .const 0⟩])
          (.seq (.call (Has.inj Blas1Op.sum) [.var 0 - .var 0 / .const 2]
              [⟨0, .var 1 + .var 0 / .const 2⟩] [⟨2, .const 1⟩])
            (.call (Has.inj ScalarOp.add) [] [⟨2, .const 0⟩, ⟨2, .const 1⟩] [⟨1, .var 2⟩]))))))

variable [Inhabited K]

/-- Pairwise summation as a routine: `[n] (x : read n) → (z : write 1)`. -/
def sumPairwiseRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (z : 1) := sumPairwise

/-- The halves of a block of length `n ≥ 2` have `⌈log₂⌉` one less than the block. -/
theorem clog_halves_lt {n k : ℕ} (h2 : 2 ≤ n) (hk : Nat.clog 2 n < k + 1) :
    Nat.clog 2 (n / 2) < k ∧ Nat.clog 2 (n - n / 2) < k := by
  have h1 : Nat.clog 2 (n - n / 2) < k := by
    rw [Nat.clog_of_two_le (by norm_num) h2, show (n + 2 - 1) / 2 = n - n / 2 by omega] at hk
    omega
  exact ⟨lt_of_le_of_lt (Nat.clog_mono_right 2 (by omega)) h1, h1⟩

/-- Pairwise summation meets the specification read off the relation of `sum` for the
lengths `n` with `⌈log₂ n⌉ < k + 1`, over an interpretation whose `sum` meets it for
`⌈log₂ n⌉ < k`: one level of the recursion. The two halves are summed into scratch cells by the
operation `sum`, and the two partial sums are added. -/
theorem sumPairwiseRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) {k : ℕ}
    (hS : IsSum dec (fun n => (1 + u) ^ Nat.clog 2 n - 1) (fun n => Nat.clog 2 n < k) I) :
    (sumPairwiseRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (sumRel dec fun n => (1 + u) ^ Nat.clog 2 n - 1)
        fun d => Nat.clog 2 (d.headD 0) < k + 1) := by
  routine_intro [n] (x, z) reads (xs)
  obtain ⟨hlx, hlz⟩ := hl
  have hz : z.2 < m.store.len z.1 := by omega
  have hk : Nat.clog 2 n < k + 1 := hpre.1
  refine (Writes.of_wp_upd_cell hz ?_).mono le_rfl
    fun m' _ ⟨hpos, v, hv, he⟩ => ⟨hpos, [[v]], hv, he⟩
  obtain rfl | rfl | h2 : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
  · refine wp_seq (wp_ifZero (n := 0) rfl ?_)
    rw [if_pos rfl]
    refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial hz ?_
    refine wp_seq (wp_ifZero (n := 0) rfl ?_)
    rw [if_pos rfl]
    refine wp_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    refine wp_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    exact ⟨M.lit 0, by simp [Routine.Spec.ofRel, sumRel, IsSumErr, hM.zero], rfl⟩
  · have hg : m.store.get x.1 x.2 = some (vec xs 0) := by
      simpa using Store.get_of_readBlock hxs Nat.zero_lt_one default
    refine wp_seq (wp_ifZero (n := 1) rfl ?_)
    rw [if_neg one_ne_zero]
    refine wp_seq (wp_ifZero (n := 0) rfl ?_)
    rw [if_pos rfl]
    refine wp_ifPos (n := 1) rfl ?_
    rw [if_pos Nat.one_pos]
    refine wp_call_un (hI .copy) rfl rfl rfl trivial hg rfl hz ?_
    refine wp_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    exact ⟨vec xs 0, by simp [Routine.Spec.ofRel, sumRel, IsSumErr], rfl⟩
  have hx1 : m.store.readBlock x.1 x.2 (n / 2) = some (xs.take (n / 2)) := by
    simpa using Store.readBlock_sub hxs (o := 0) (n := n / 2) (by omega)
  have hx2 : m.store.readBlock x.1 (x.2 + n / 2) (n - n / 2) = some (xs.drop (n / 2)) := by
    have := Store.readBlock_sub hxs (o := n / 2) (n := n - n / 2) (by omega)
    rwa [List.take_of_length_le (by simp [Store.length_of_readBlock hxs])] at this
  refine wp_seq (wp_ifZero (n := n) rfl ?_)
  rw [if_neg (by omega)]
  refine wp_seq (wp_ifZero (n := n - 1) rfl ?_)
  rw [if_neg (by omega)]
  refine wp_ifPos (n := n / 2) rfl ?_
  rw [if_pos (by omega)]
  obtain ⟨hk₁, hk₂⟩ := clog_halves_lt h2 hk
  refine wp_alloc rfl ?_
  wp_call hS with v₁ h₁
  wp_call hS with v₂ h₂
  wp_call (hI .add)
  refine ⟨M.add v₁ v₂, IsSumErr.pairwise hM hu h2 h₁ h₂, ?_⟩
  store_simp
  rfl


/-- The routine of pairwise summation implements the contract of the operation `sum`, the
operands of the routine being the input followed by the output. -/
theorem sumPairwiseRoutine_implements (dec : K → ℝ) (e : ℕ → ℝ) (ok : ℕ → Prop) :
    (sumPairwiseRoutine (Op := Op) (Tst := Tst)).Implements (sumRel dec e) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

/-- Pairwise summation satisfies the contract of `sum` for the lengths `n` with
`⌈log₂ n⌉ < k + 1`, over an interpretation whose `sum` meets it for `⌈log₂ n⌉ < k`: one level of
the recursion, a consequence of the judgment of its routine. -/
theorem sumPairwise_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) {k : ℕ}
    (hS : IsSum dec (fun n => (1 + u) ^ Nat.clog 2 n - 1) (fun n => Nat.clog 2 n < k) I) :
    (sumPairwiseRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((sumRel dec fun n => (1 + u) ^ Nat.clog 2 n - 1).spec
        (OutApart fun n => Nat.clog 2 n < k + 1)) :=
  (sumPairwiseRoutine_meets hI hM hu hS).satisfies_ofRel (sumPairwiseRoutine_implements dec _ _)
    fun _ _ _ h => h.2.1.1

end

end NLAlib.Ops
