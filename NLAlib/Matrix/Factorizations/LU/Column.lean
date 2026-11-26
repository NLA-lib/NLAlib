/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.GetD
public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Blas.StridedCopy
public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Ops.Logic.EntryRow
public import NLAlib.Ops.Logic.ColumnSuffix

/-!
# Column normalization for LU

The lower multipliers of Gaussian elimination are obtained by dividing the active column by
the pivot. A zero pivot writes literal zeros without performing a division. The routine uses
the existing scalar copy, fill and division loops; its word-level judgment is independent of
any arithmetic error model.

## Main results

* `NLAlib.LU.normalizeColumn_meets`: the actual column words for any scalar machine with exact
  decoded comparisons.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Lower-factor words after materializing column `k`. Entries above the diagonal and all
other columns retain their original words. The Boolean records the actual zero-pivot test. -/
def columnLowerValues (M : Machine K) (zeroPivot : Bool)
    (R L : ℕ → ℕ → K) (k : ℕ) : ℕ → ℕ → K := fun i j =>
  if j = k ∧ k ≤ i then
    if i = k then M.lit 1 else if zeroPivot then M.lit 0 else M.div (R i k) (R k k)
  else L i j

/-- Upper-factor words after copying the pivot-row tail. The earlier columns and all other
rows retain their original words. -/
def columnUpperValues (R U : ℕ → ℕ → K) (k : ℕ) : ℕ → ℕ → K := fun i j =>
  if i = k ∧ k ≤ j then R i j else U i j

/-- Normalize the active column by a pivot. A zero decoded pivot initializes the output with
literal zeros and executes no division. -/
def normalizeColumn : Routine Op Tst := routine% [n] (d : 1, x : n) → (l : n) {
  if (Has.inj CmpTst.isZero) [] (d) {
    run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n] (l)
  } else {
    run copyLoopRoutine [n] (x, l);
    run scalLoopRoutine [n] (d, l)
  }
}

variable [Inhabited K]

/-- The column contains zero literals at a zero decoded pivot, and machine quotients otherwise.
No relation between word division and real division is assumed. -/
def normalizeColumnSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] ([d], xs) → (ls) ensures
    (dec d = 0 → ls = List.replicate n (M.lit 0)) ∧
      (dec d ≠ 0 → ls = scalF M d (vec xs) n)

/-- The guarded column normalization meets its word specification under scalar operations and
exact decoded comparisons, including when the active column has length zero. -/
theorem normalizeColumn_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) :
    (normalizeColumn (Op := Op) (Tst := Tst)).Meets I (normalizeColumnSpec M dec) := by
  routine_intro [n] (d, x, l) reads (ds, xs)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  refine writes_ite rfl rfl (hcmp.test_isZero ha) ?_
  by_cases hz : dec a = 0
  · simp only [hz, decide_true, ite_true]
    call (fillRoutine_meets (hI (.lit 0))) [n] (l) as m₁ hfr₁ hpos₁ (ls) hpost
    routine_exit
    exact ⟨fun _ => hpost, fun h => (h hz).elim⟩
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    call (copyLoopRoutine_meets hI (fun _ => True)) [n] (x, l)
      as m₁ hfr₁ hpos₁ (ys) hcopy
    have heq : ys = xs := (List.cons.inj hcopy).1
    call (scalLoopRoutine_meets_exact hI) [n] (d, l)
      as m₂ hfr₂ hpos₂ (ls) hpost
    routine_exit
    constructor
    · exact fun h => (hz h).elim
    · intro _
      have hs : ls = scalF M a (vec ys) n := hpost
      simpa only [heq] using hs

/-- Under exact arithmetic the guarded word specification gives the ordinary total quotient.
This includes a zero pivot: the branch writes decoded zero, which equals division by zero in
the mathematical field. -/
theorem normalizeColumnSpec_decode {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {n : ℕ} {d : K} {xs ls : List K} {τ : Tape K}
    (hpost : (normalizeColumnSpec M dec).post [n] τ [[d], xs] [ls])
    {i : ℕ} (hi : i < n) : dec (vec ls i) = dec (vec xs i) / dec d := by
  have hp : (dec d = 0 → ls = List.replicate n (M.lit 0)) ∧
      (dec d ≠ 0 → ls = scalF M d (vec xs) n) := hpost
  by_cases hd : dec d = 0
  · rw [hp.1 hd]
    simp [vec, hi, hM.lit, hd]
  · rw [hp.2 hd]
    have hv : vec (scalF M d (vec xs) n) i = M.div (vec xs i) d := by
      simp [vec, scalF, hi]
    rw [hv, hM.div _ _ hd]

/-- Read one actual word of a normalized tail, using the recorded Boolean of its decoded
zero-pivot decision. This is the functional input to column materialization. -/
theorem normalizeColumnSpec_word {M : Machine K} {dec : K → ℝ}
    {n : ℕ} {d : K} {xs ls : List K} {τ : Tape K} (zeroPivot : Bool)
    (hz : zeroPivot = true ↔ dec d = 0)
    (hpost : (normalizeColumnSpec M dec).post [n] τ [[d], xs] [ls])
    {i : ℕ} (hi : i < n) :
    vec ls i = if zeroPivot then M.lit 0 else M.div (vec xs i) d := by
  have hp : (dec d = 0 → ls = List.replicate n (M.lit 0)) ∧
      (dec d ≠ 0 → ls = scalF M d (vec xs) n) := hpost
  cases zeroPivot with
  | false =>
    have hn : dec d ≠ 0 := fun h => Bool.false_ne_true (hz.mpr h)
    rw [hp.2 hn]
    simp [scalF, vec, hi]
  | true =>
    rw [hp.1 (hz.mp rfl)]
    change (List.replicate n (M.lit 0)).getD i default = M.lit 0
    exact List.getD_replicate (α := K) (x := M.lit 0) (h := hi)

private theorem lower_suffix_value (M : Machine K) (dec : K → ℝ)
    (R L : ℕ → ℕ → K) (N k i j : ℕ) (zeroPivot : Bool) (xs ts : List K)
    (τ : Tape K) (hz : zeroPivot = true ↔ dec (R k k) = 0)
    (hpost : (normalizeColumnSpec M dec).post [N - (k + 1)] τ [[R k k], xs] [ts])
    (hx : ∀ q < N - (k + 1), vec xs q = R (k + 1 + q) k) (hi : i < N) :
    (if j = k ∧ k ≤ i then vec (M.lit 1 :: ts) (i - k) else L i j) =
      columnLowerValues M zeroPivot R L k i j := by
  by_cases hc : j = k ∧ k ≤ i
  · simp only [columnLowerValues, if_pos hc]
    by_cases hik : i = k
    · subst i
      simp [vec]
    · simp only [if_neg hik]
      have ht : i - (k + 1) < N - (k + 1) := by omega
      have he : i - k = i - (k + 1) + 1 := by omega
      rw [he]
      change vec ts (i - (k + 1)) = _
      have hword := normalizeColumnSpec_word zeroPivot hz hpost ht
      rw [hx _ ht] at hword
      simpa only [show k + 1 + (i - (k + 1)) = i by omega] using hword
  · simp only [columnLowerValues, if_neg hc]

private theorem lower_after_normalize (M : Machine K) (dec : K → ℝ)
    {N k : ℕ} (hk : k < N) {s s₁ s₂ : Store K} (L : ℕ × ℕ)
    (R W : ℕ → ℕ → K) (zeroPivot : Bool) (xs ts : List K) (τ : Tape K)
    (hW : s.HoldsMat ⟨L.1, L.2, N, N, N⟩ W)
    (hdfr : s.EqOff (Store.inBlock L.1 (L.2 + k * N + k) 1) s₁)
    (hd : s₁.get L.1 (L.2 + k * N + k) = some (M.lit 1))
    (htfr : s₁.EqOff
      (Store.inBlock L.1 (L.2 + k * N + k + 1) (N - (k + 1))) s₂)
    (ht : s₂.readBlock L.1 (L.2 + k * N + k + 1) (N - (k + 1)) = some ts)
    (hz : zeroPivot = true ↔ dec (R k k) = 0)
    (hp : (normalizeColumnSpec M dec).post [N - (k + 1)] τ [[R k k], xs] [ts])
    (hx : ∀ q < N - (k + 1), vec xs q = R (k + 1 + q) k) :
    s₂.HoldsMat ⟨L.1, L.2, N, N, N⟩ (columnLowerValues M zeroPivot R W k) := by
  have hn : N - k = (N - (k + 1)) + 1 := by omega
  have hd' : s₂.get L.1 (L.2 + k * N + k) = some (M.lit 1) := by
    apply (htfr.get_eq ?_).trans hd
    rintro ⟨_, hlo, _⟩
    omega
  have hread : s₂.readBlock L.1 (L.2 + k * N + k) (N - k) =
      some (M.lit 1 :: ts) := by
    rw [hn, Store.readBlock_succ, hd', ht]
    rfl
  have hfr : s.EqOff (Store.inBlock L.1 (L.2 + k * N + k) (N - k)) s₂ := by
    apply (hdfr.trans' htfr).mono
    intro b o ho
    rcases ho with ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ <;>
      exact ⟨rfl, by omega, by omega⟩
  have hnew := hW.update_column_suffix_of_frame le_rfl k k (Nat.le_of_lt hk) hfr hread
  intro i hi j hj
  have hget := hnew i hi j hj
  dsimp only at hget
  rw [lower_suffix_value M dec R W N k i j zeroPivot xs ts τ hz hp hx hi] at hget
  exact hget

private theorem upper_suffix_value (R U : ℕ → ℕ → K) (N k i j : ℕ) (hj : j < N) :
    (if i = k ∧ k ≤ j then
      vec ((List.range (N - k)).map fun q => R k (k + q)) (j - k) else U i j) =
      columnUpperValues R U k i j := by
  by_cases hc : i = k ∧ k ≤ j
  · obtain ⟨hik, hkj⟩ := hc
    subst i
    have hq : j - k < N - k := by omega
    have he : k + (j - k) = j := by omega
    simp [columnUpperValues, hkj, vec, hq, he]
  · simp only [columnUpperValues, if_neg hc]

private theorem upper_after_copy {N k : ℕ} (hk : k < N) {s s' : Store K}
    (U : ℕ × ℕ) (R W : ℕ → ℕ → K)
    (hW : s.HoldsMat ⟨U.1, U.2, N, N, N⟩ W)
    (hfr : s.EqOff
      (Fp.inView U.1 (U.2 + k * N + k) ⟨1, some (N - k, N)⟩) s')
    (hy : s'.readView U.1 (U.2 + k * N + k) ⟨1, some (N - k, N)⟩ =
      some ((List.range (N - k)).map fun q => R k (k + q))) :
    s'.HoldsMat ⟨U.1, U.2, N, N, N⟩ (columnUpperValues R W k) := by
  have hnew := hW.update_row_suffix_of_frame le_rfl hk k hfr hy
  intro i hi j hj
  have hget := hnew i hi j hj
  dsimp only at hget
  rw [upper_suffix_value R W N k i j hj] at hget
  exact hget

omit [Inhabited K] in
private theorem read_lower_tail {N k : ℕ} (hk : k < N) {s : Store K}
    (R : ℕ × ℕ) (A : ℕ → ℕ → K)
    (h : s.HoldsMat ⟨R.1, R.2, N, N, N⟩ A) :
    s.readBlock R.1 (R.2 + k * N + k + 1) (N - (k + 1)) =
      some ((List.range (N - (k + 1))).map fun q => A (k + 1 + q) k) := by
  apply Store.readBlock_eq_some_iff.mpr
  refine ⟨by simp, fun q hq => ?_⟩
  have hqi : k + 1 + q < N := by omega
  have hg := h (k + 1 + q) hqi k hk
  simpa [MatLayout.cell, hq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg

/-- Copy the right suffix of the pivot row into an initialized upper-factor block. Other
entries of the factor are retained. This routine uses the scalar strided-copy kernel. -/
def materializeUpper : Routine Op Tst :=
  routine% [n, k] (R : n * n, U : n * n) → (U) {
    run copyStridedRoutine [n - k, n, n] (R[k * n + k], U[k * n + k])
  }

/-- The upper output differs from its input only in the copied right pivot-row suffix. -/
def materializeUpperSpec : Routine.Spec K :=
  spec% [n, k] (rs, us) → (us') requires k < n ensures
    us' = (EntryCodec.scalar K).packMatrix n n
      (columnUpperValues (fun i j => vec rs (j * n + i))
        (fun i j => vec us (j * n + i)) k)

omit [Has CmpTst Tst] in
/-- Pivot-row materialization meets its exact word specification on every scalar machine.
Its full-matrix frame is derived from the actual strided destination view. -/
theorem materializeUpper_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (materializeUpper (Op := Op) (Tst := Tst)).Meets I materializeUpperSpec := by
  routine_intro [n, k] (R, U) reads (rs, us)
  have hk : k < n := hpre
  let r := fun i j => vec rs (j * n + i)
  let u := fun i j => vec us (j * n + i)
  have hR : m.store.HoldsMat ⟨R.1, R.2, n, n, n⟩ r :=
    Store.holdsMat_of_readBlock rfl hrs
  have hU : m.store.HoldsMat ⟨U.1, U.2, n, n, n⟩ u :=
    Store.holdsMat_of_readBlock rfl hus
  have hrow : m.store.readView R.1 (R.2 + k * n + k) ⟨1, some (n - k, n)⟩ =
      some ((List.range (n - k)).map fun q => r k (k + q)) := hR.readView_row_suffix hk k
  have huro : m.store.readView U.1 (U.2 + k * n + k) ⟨1, some (n - k, n)⟩ =
      some ((List.range (n - k)).map fun q => u k (k + q)) := hU.readView_row_suffix hk k
  have huroom := Store.fits_of_readView huro (by simp; omega)
  call (copyStridedRoutine_meets hI) [n - k, n, n]
    ((R.1, R.2 + k * n + k), (U.1, U.2 + k * n + k))
    as m₁ hfr₁ hpos₁ (ys) hcopy
  case' hcall => exact [(List.range (n - k)).map fun q => r k (k + q)]
  case' hr => exact Mem.readViews_of_cons hrow rfl
  case' hpre => exact fun _ => Nat.zero_lt_of_lt hk
  case' hle =>
    change Fp.views [(U.1, U.2 + k * n + k)] [⟨1, some (n - k, n)⟩] ≤
      Fp.blocks [U] [n * n]
    simp only [Fp.views, Fp.blocks, sup_bot_eq]
    intro b o ho
    obtain ⟨rfl, q, hq, he⟩ := Fp.inView_apply.mp ho
    have hqn : q < n - k := by simpa using hq
    have hcol : k + q < n := by omega
    have hidx : (k + q) * n + k < n * n := Idx.add_lt_mul hcol hk
    have he' : o = U.2 + (k + q) * n + k := by
      simp only [Nat.add_mul]
      simp only [View.offset_runs_one, Nat.mul_comm n q] at he
      omega
    exact ⟨rfl, by omega, by omega⟩
  have hnew : m₁.store.HoldsMat ⟨U.1, U.2, n, n, n⟩ (columnUpperValues r u k) := by
    apply upper_after_copy hk U r u hU
      (by simpa only [Fp.views, sup_bot_eq] using hfr₁)
    have he : ys = (List.range (n - k)).map fun q => r k (k + q) := hcopy
    simpa only [he] using hys
  have hread := (Store.holdsMat_iff_holdsEntries_scalar.mp hnew).readBlock rfl
  simp only [EntryCodec.scalar, Nat.mul_one] at hread
  routine_exit
  rfl

/-- Materialize the lower diagonal and tail, and the upper pivot-row tail. Every earlier
factor entry is retained. The caller supplies the existing factor blocks. -/
def materializeColumn : Routine Op Tst :=
  routine% [n, k] (R : n * n, L : n * n, U : n * n) → (L, U) {
    call (Has.inj (ScalarOp.lit 1)) [] () → (L[k * n + k]);
    run normalizeColumn [n - (k + 1)]
      (R[k * n + k], R[k * n + k + 1], L[k * n + k + 1]);
    run materializeUpper [n, k] (R, U)
  }

/-- Both factor blocks hold the actual word updates. The Boolean in the postcondition is
the decoded zero-pivot decision used by the lower normalization routine. -/
def materializeColumnSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, k] (rs, ls, us) → (ls', us') requires k < n ensures
    ∃ zeroPivot : Bool, (zeroPivot = true ↔ dec (vec rs (k * n + k)) = 0) ∧
      ls' = (EntryCodec.scalar K).packMatrix n n
        (columnLowerValues M zeroPivot (fun i j => vec rs (j * n + i))
          (fun i j => vec ls (j * n + i)) k) ∧
      us' = (EntryCodec.scalar K).packMatrix n n
        (columnUpperValues (fun i j => vec rs (j * n + i))
          (fun i j => vec us (j * n + i)) k)

/-- The materialization routine writes exactly its guarded machine-word updates. The residual
is read only, and all previously stored factor entries outside the two tails are retained. -/
theorem materializeColumn_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) :
    (materializeColumn (Op := Op) (Tst := Tst)).Meets I (materializeColumnSpec M dec) := by
  classical
  routine_intro [n, k] (R, L, U) reads (rs, ls, us)
  have hk : k < n := hpre
  let r := fun i j => vec rs (j * n + i)
  let l := fun i j => vec ls (j * n + i)
  let u := fun i j => vec us (j * n + i)
  have hR : m.store.HoldsMat ⟨R.1, R.2, n, n, n⟩ r :=
    Store.holdsMat_of_readBlock rfl hrs
  have hL : m.store.HoldsMat ⟨L.1, L.2, n, n, n⟩ l :=
    Store.holdsMat_of_readBlock rfl hls
  have hU : m.store.HoldsMat ⟨U.1, U.2, n, n, n⟩ u :=
    Store.holdsMat_of_readBlock rfl hus
  have hidx : k * n + k < n * n := Idx.add_lt_mul hk hk
  have hend : k * n + n ≤ n * n := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hk)
  have htail := read_lower_tail hk R r hR
  have hdp₀ : m.store.get R.1 (R.2 + k * n + k) = some (r k k) := hR k hk k hk
  step (hI (.lit 1)) as m₁ hfr₁ ⟨hpos₁, v, hd, rfl⟩
  have hdp : m₁.store.get R.1 (R.2 + k * n + k) = some (r k k) := by
    keep
  have htail₁ : m₁.store.readBlock R.1 (R.2 + k * n + k + 1) (n - (k + 1)) =
      some ((List.range (n - (k + 1))).map fun q => r (k + 1 + q) k) := by keep
  call (normalizeColumn_meets hI hcmp) [n - (k + 1)]
    ((R.1, R.2 + k * n + k), (R.1, R.2 + k * n + k + 1),
      (L.1, L.2 + k * n + k + 1)) as m₂ hfr₂ hpos₂ (ts) hnorm
  let z : Bool := decide (dec (r k k) = 0)
  have hz : z = true ↔ dec (r k k) = 0 := by simp [z]
  have hL₂ : m₂.store.HoldsMat ⟨L.1, L.2, n, n, n⟩ (columnLowerValues M z r l k) := by
    apply lower_after_normalize M dec hk L r l z _ ts τ hL hfr₁ hd
      (by simpa only [Fp.blocks, sup_bot_eq] using hfr₂) hts hz hnorm
    intro q hq
    simp [vec, hq]
  have hcl₂ := (Store.holdsMat_iff_holdsEntries_scalar.mp hL₂).readBlock rfl
  simp only [EntryCodec.scalar, Nat.mul_one] at hcl₂
  have hrs₂ : m₂.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  have hus₂ : m₂.store.readBlock U.1 U.2 (n * n) = some us := by keep
  call (materializeUpper_meets hI) [n, k] (R, U) (pre := hk)
    as m₃ hfr₃ hpos₃ (ys) hupper
  have hcl : m₃.store.readBlock L.1 L.2 (n * n) =
      some ((EntryCodec.scalar K).packMatrix n n (columnLowerValues M z r l k)) := by keep
  routine_exit
  exact ⟨z, hz, rfl, hupper⟩

omit [Inhabited K] in
/-- Exact decoding of the materialized lower column. At a zero pivot the literal-zero
branch equals the field's total quotient, without executing a machine division by zero. -/
theorem columnLowerValues_dec {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    (zeroPivot : Bool) (R L : ℕ → ℕ → K) (k i j : ℕ)
    (hz : zeroPivot = true ↔ dec (R k k) = 0) :
    dec (columnLowerValues M zeroPivot R L k i j) =
      if j = k ∧ k ≤ i then if i = k then 1 else dec (R i k) / dec (R k k)
      else dec (L i j) := by
  by_cases hc : j = k ∧ k ≤ i
  · rw [columnLowerValues, if_pos hc, if_pos hc]
    by_cases hi : i = k
    · simp only [if_pos hi, hM.lit, Rat.cast_one]
    · simp only [if_neg hi]
      cases zeroPivot with
      | false =>
        have hp : dec (R k k) ≠ 0 := fun h => Bool.false_ne_true (hz.mpr h)
        simp only [Bool.false_eq_true, if_false, hM.div _ _ hp]
      | true =>
        have hp : dec (R k k) = 0 := hz.mp rfl
        simp only [if_true, hM.lit, Rat.cast_zero, hp, div_zero]
  · simp only [columnLowerValues, if_neg hc]

end NLAlib.LU
