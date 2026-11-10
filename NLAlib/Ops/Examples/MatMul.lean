/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot

/-!
# Example: a functional contract, the matrix product by a triple loop

The contract of `mm` is functional: the result is `f` of the two input blocks, for some `f`
(`NLAlib.Ops.Examples.mmFn`, `NLAlib.Ops.Examples.IsMM`). Properties of `f` are mathematics.

## Main results

* Abstract theorem (`NLAlib.Ops.Examples.runs_sq2`): squaring a matrix twice, for every `f`:
  two calls at `[n, n, n]`, and the memory is given by `f`. Each call is one equation.
* Exact certificate (`NLAlib.Ops.Examples.mm_cert`): the run of the triple loop
  `NLAlib.Ops.Examples.mmImpl` is the block function of `NLAlib.Ops.Examples.mmF`, the triple
  loop written as a function on lists through a machine. It reuses the accumulation loop of the
  dot product (`NLAlib.Ops.Examples.wp_dotLoop`) for each entry.
* Mathematics (`NLAlib.Ops.Examples.abs_dec_mmF_sub_le`): each entry of `mmF` is a rounded dot
  product.
* Corollary (`NLAlib.Ops.Examples.runs_sq2_link`): the linked program computes `mmF`, within
  `2 n² (lit + n (mul + add))` scalar operations and one scratch cell.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type} [Inhabited K]

/-- The signature with one operation, the matrix product
`mm [a, b, c] [A, B] [C]` of an `a × b` by a `b × c` block, row by row. -/
inductive MOp where
  /-- The matrix product. -/
  | mm
  deriving DecidableEq

/-- The block function of `mm` given the function `f` on the two blocks. -/
def mmFn (f : ℕ → ℕ → ℕ → List K → List K → List K) : BlockFn K where
  inLens d := match d with
    | [a, b, c] => [a * b, b * c]
    | _ => []
  fn d _ xs := match d, xs with
    | [a, b, c], [As, Bs] => some (f a b c As Bs)
    | _, _ => none

omit [Inhabited K] in
/-- What a successful call of the block function of `mm` is. -/
theorem mmFn_apply {f : ℕ → ℕ → ℕ → List K → List K → List K} {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : Tape K} {m m' : Mem K}
    (h : (mmFn f).apply d ins z τ m = some m') :
    ∃ a b c A B As Bs, d = [a, b, c] ∧ ins = [A, B] ∧
      m.store.readBlock A.1 A.2 (a * b) = some As ∧ m.store.readBlock B.1 B.2 (b * c) = some Bs ∧
      z.2 + (f a b c As Bs).length ≤ m.store.len z.1 ∧ m' = m.updBlock z (f a b c As Bs) := by
  obtain ⟨hlive, X, v, hread, hfn, hlen, rfl⟩ := BlockFn.apply_eq_some_iff.mp h
  rcases d with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, d⟩⟩⟩⟩
  · simp [mmFn] at hfn
  · simp [mmFn] at hfn
  · simp [mmFn] at hfn
  · obtain ⟨A, B, As, Bs, rfl, hA, hB, rfl⟩ := Mem.readBlocks_two hread
    simp only [mmFn, Option.some.injEq] at hfn
    subst hfn
    exact ⟨a, b, c, A, B, As, Bs, rfl, rfl, hA, hB, hlen, rfl⟩
  · simp [mmFn] at hfn

/-- **The functional contract of `mm`**: on input blocks in other buffers than the output, the
result is `f` of the inputs, an `a × c` block. -/
structure IsMM (f : ℕ → ℕ → ℕ → List K → List K → List K) (I : Interp MOp Empty K) : Prop where
  /-- The operation is the block function of `f`. -/
  isFn : I.IsFn .total .mm (mmFn f) DisjointBufs
  /-- The result has `a c` entries. -/
  length : ∀ a b c As Bs, (f a b c As Bs).length = a * c

/-! ### The abstract theorem: squaring twice -/

/-- `P := A A; S := P P` on `n × n` blocks. Index variables: `n`, the offsets of `A`, `P`, `S`. -/
def sq2 : Stmt MOp Empty :=
  .seq (.call .mm [.var 0, .var 0, .var 0] [⟨0, .var 1⟩, ⟨0, .var 1⟩] [⟨1, .var 2⟩])
    (.call .mm [.var 0, .var 0, .var 0] [⟨1, .var 2⟩, ⟨1, .var 2⟩] [⟨2, .var 3⟩])

omit [Inhabited K] in
/-- **The abstract theorem of `sq2`**, for every `f` and every interpretation meeting the
functional contract: two calls of `mm` at `[n, n, n]`, the workspace of one, and the memory is
given by `f`. -/
theorem runs_sq2 {f : ℕ → ℕ → ℕ → List K → List K → List K} {I : Interp MOp Empty K}
    (hI : IsMM f I) (W : MOp → List ℕ → ℕ) {τ : Tape K} {n : ℕ} {A P S : ℕ × ℕ} {m : Mem K}
    {As : List K} (hAP : A.1 ≠ P.1) (hPS : P.1 ≠ S.1)
    (hA : m.store.readBlock A.1 A.2 (n * n) = some As) (hP : P.2 + n * n ≤ m.store.len P.1)
    (hS : S.2 + n * n ≤ m.store.len S.1) (hl : m.Live [A, P, S]) :
    Runs I W τ sq2 ⟨[n, A.2, P.2, S.2], [A.1, P.1, S.1]⟩ m (2 • Count.one .mm [n, n, n])
      (W .mm [n, n, n])
      (· = (m.updBlock P (f n n n As As)).updBlock S
        (f n n n (f n n n As As) (f n n n As As))) := by
  obtain ⟨lA, lP, lS⟩ : A.1 < m.store.length ∧ P.1 < m.store.length ∧ S.1 < m.store.length := by
    simpa using hl
  have h1 : (mmFn f).apply [n, n, n] [A, A] P τ m = some (m.updBlock P (f n n n As As)) :=
    BlockFn.apply_eq_some_iff.mpr ⟨by store_simp, [As, As], _, by simp
    [Mem.readBlocks, hA, mmFn], rfl,
      by rw [hI.length]; exact hP, rfl⟩
  have hPr : (m.store.updBlock P.1 P.2 (f n n n As As)).readBlock P.1 P.2 (n * n) =
      some (f n n n As As) := by
    have := Store.readBlock_updBlock_self (s := m.store) (b := P.1) (off := P.2)
      (xs := f n n n As As) (by rw [hI.length]; exact hP)
    rwa [hI.length] at this
  have h2 : (mmFn f).apply [n, n, n] [P, P] S τ (m.updBlock P (f n n n As As)) =
      some ((m.updBlock P (f n n n As As)).updBlock S
        (f n n n (f n n n As As) (f n n n As As))) :=
    BlockFn.apply_eq_some_iff.mpr ⟨by store_simp, [_, _], _,
      by simp [Mem.readBlocks, hPr, mmFn], rfl, by rw [hI.length]; simpa using hS, rfl⟩
  have hw : Wp .total I τ sq2 ⟨[n, A.2, P.2, S.2], [A.1, P.1, S.1]⟩
      (· = (m.updBlock P (f n n n As As)).updBlock S (f n n n (f n n n As As) (f n n n As As)))
      m :=
    wp_seq (wp_call_fn hI.isFn (z := P) rfl rfl rfl (by simp [DisjointBufs, hAP]) h1
      (wp_call_fn hI.isFn (z := S) rfl rfl rfl (by simp [DisjointBufs, hPS]) h2 rfl))
  obtain ⟨m', hrun, hpost⟩ := hw
  exact (Runs.of_run hrun hpost W).mono (by simp [sq2, staticCost, useCost, two_nsmul])
    (by simp [sq2, staticPeak]) fun _ h => h

/-! ### The implementation: a triple loop, as a function and as a tree -/

/-- Entry `e = i c + j` of the product: the rounded dot product of row `i` of `A` and column `j`
of `B`. -/
def mmEntry (M : Machine K) (b c : ℕ) (As Bs : List K) (e : ℕ) : K :=
  dotF M (fun k => vec As (e / c * b + k)) (fun k => vec Bs (k * c + e % c)) b

/-- The first `N` entries of the product. -/
def mmPrefix (M : Machine K) (b c : ℕ) (As Bs : List K) (N : ℕ) : List K :=
  (List.range N).map (mmEntry M b c As Bs)

/-- **The triple loop as a function on lists**, through a machine. -/
def mmF (M : Machine K) (a b c : ℕ) (As Bs : List K) : List K := mmPrefix M b c As Bs (a * c)

theorem mmPrefix_succ (M : Machine K) (b c : ℕ) (As Bs : List K) (N : ℕ) :
    mmPrefix M b c As Bs (N + 1) = mmPrefix M b c As Bs N ++ [mmEntry M b c As Bs N] := by
  simp [mmPrefix, List.range_succ]

theorem length_mmPrefix (M : Machine K) (b c : ℕ) (As Bs : List K) (N : ℕ) :
    (mmPrefix M b c As Bs N).length = N := by simp [mmPrefix]

/-- **The implementation of `mm`**: a scratch cell, and for each entry the accumulation loop.
Index variables: `a`, `b`, `c`, the offsets of `A`, `B`, `C`, then `i`, `j`, `k`. -/
def mmImpl : Impl ScalarOp Empty where
  nd := 3
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.loop (.var 0) (.loop (.var 2)
    (dotLoop (.var 1) ⟨0, .var 3 + .var 6 * .var 1 + .var 8⟩ ⟨1, .var 4 + .var 8 * .var 2 + .var 7⟩
      ⟨2, .var 5 + .var 6 * .var 2 + .var 7⟩ ⟨3, .const 0⟩)))

/-- One entry: the accumulation loop appends entry `i c + j` to the block written so far. -/
theorem wp_mm_entry {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) {md : Mode}
    {τ : Tape K}
    {a b c i j : ℕ} (hi : i < a) (hj : j < c) {A B C : ℕ × ℕ} {s : Store K} {p : ℕ}
    {As Bs : List K} {tb : Buf K} (hAC : A.1 ≠ C.1) (hBC : B.1 ≠ C.1)
    (hA : s.readBlock A.1 A.2 (a * b) = some As) (hB : s.readBlock B.1 B.2 (b * c) = some Bs)
    (hC : C.2 + a * c ≤ s.len C.1) (htb : tb.length = 1) {Q : Mem K → Prop}
    (hQ : ∀ tb' : Buf K, tb'.length = 1 →
      Q ⟨s.updBlock C.1 C.2 (mmPrefix M b c As Bs (i * c + j + 1)) ++ [tb'], p⟩) :
    Wp md I τ (dotLoop (.var 1) ⟨0, .var 3 + .var 6 * .var 1 + .var 8⟩
        ⟨1, .var 4 + .var 8 * .var 2 + .var 7⟩ ⟨2, .var 5 + .var 6 * .var 2 + .var 7⟩
        ⟨3, .const 0⟩)
      ⟨[a, b, c, A.2, B.2, C.2, i, j], [A.1, B.1, C.1, s.length]⟩ Q
      ⟨s.updBlock C.1 C.2 (mmPrefix M b c As Bs (i * c + j)) ++ [tb], p⟩ := by
  have hic : i * c + c ≤ a * c := by
    have := Nat.mul_le_mul_right c hi
    rwa [Nat.succ_mul] at this
  have hdiv : (i * c + j) / c = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * c + j) % c = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  refine wp_dotLoop hI (s := s.updBlock C.1 C.2 (mmPrefix M b c As Bs (i * c + j)))
    (bz := C.1) (oz := C.2 + i * c + j) (fx := fun k => A.2 + i * b + k)
    (fy := fun k => B.2 + k * c + j) (a := fun k => vec As (i * b + k))
    (b := fun k => vec Bs (k * c + j)) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => by simp [Operand.eval]) htb hAC hBC (by rw [Store.len_updBlock]; omega) ?_ ?_ ?_
  · intro k hk
    have hlt : i * b + k < a * b := by
      have := Nat.mul_le_mul_right b hi
      rw [Nat.succ_mul] at this
      omega
    rw [Store.get_updBlock_of_buf_ne hAC, add_assoc]
    exact Store.get_of_readBlock hA hlt default
  · intro k hk
    have hlt : k * c + j < b * c := by
      have := Nat.mul_le_mul_right c hk
      rw [Nat.succ_mul] at this
      omega
    rw [Store.get_updBlock_of_buf_ne hBC, add_assoc]
    exact Store.get_of_readBlock hB hlt default
  · intro tb' htb'
    have := hQ tb' htb'
    rwa [mmPrefix_succ, Store.updBlock_concat, length_mmPrefix, mmEntry, hdiv, hmod,
      ← add_assoc] at this

/-- **The exact certificate of the triple loop**: where the block function of `mmF` succeeds on
inputs in other buffers than the output, the run of `mmImpl` is that block function. -/
theorem mm_cert {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : Tape K} {m m' : Mem K} (hadm : DisjointBufs d ins z)
    (h : (mmFn (mmF M)).apply d ins z τ m = some m') :
    mmImpl.Fits d.length ins.length 1 ∧
      run I τ mmImpl.body (Env.frame d (ins ++ [z])) m = some m' := by
  obtain ⟨a, b, c, A, B, As, Bs, rfl, rfl, hA, hB, hlen, rfl⟩ := mmFn_apply h
  obtain ⟨s, p⟩ := m
  have hC : z.2 + a * c ≤ s.len z.1 := by simpa [mmF, length_mmPrefix] using hlen
  refine ⟨⟨rfl, rfl, rfl⟩, run_of_wp (wp_alloc rfl (wp_loop (k := a) rfl
    (fun i m' => ∃ tb : Buf K, tb.length = 1 ∧
      m' = ⟨s.updBlock z.1 z.2 (mmPrefix M b c As Bs (i * c)) ++ [tb], p⟩)
    ⟨List.replicate 1 none, rfl, by simp [mmPrefix, Store.push]⟩ ?_ ?_))⟩
  · rintro i hi m' ⟨tb, htb, rfl⟩
    refine wp_loop (k := c) rfl (fun j m' => ∃ tb : Buf K, tb.length = 1 ∧
      m' = ⟨s.updBlock z.1 z.2 (mmPrefix M b c As Bs (i * c + j)) ++ [tb], p⟩) ⟨tb, htb, rfl⟩ ?_
      (fun m' ⟨tb', h1, h2⟩ => ⟨tb', h1, by rw [h2, Nat.succ_mul]⟩)
    rintro j hj m' ⟨tb, htb, rfl⟩
    exact wp_mm_entry hI hi hj (hadm A (by simp)) (hadm B (by simp)) hA hB hC htb
      fun tb' h => ⟨tb', h, rfl⟩
  · rintro m' ⟨tb, _, rfl⟩
    simp [Mem.updBlock, mmF]

/-! ### Mathematics: each entry is a rounded dot product -/

/-- **The entrywise error of the rounded matrix product.** -/
theorem abs_dec_mmF_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (a b c : ℕ) (As Bs : List K) {i j : ℕ} (hi : i < a) (hj : j < c) :
    |dec (vec (mmF M a b c As Bs) (i * c + j)) -
        ∑ k ∈ Finset.range b, dec (vec As (i * b + k)) * dec (vec Bs (k * c + j))| ≤
      ((1 + u) ^ (2 * b) - 1) *
        ∑ k ∈ Finset.range b, |dec (vec As (i * b + k)) * dec (vec Bs (k * c + j))| := by
  have hlt : i * c + j < a * c := by
    have := Nat.mul_le_mul_right c hi
    rw [Nat.succ_mul] at this
    omega
  have hdiv : (i * c + j) / c = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * c + j) % c = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have : vec (mmF M a b c As Bs) (i * c + j) =
      dotF M (fun k => vec As (i * b + k)) (fun k => vec Bs (k * c + j)) b := by
    simp [vec, mmF, mmPrefix, List.getD_eq_getElem?_getD, hlt, mmEntry, hdiv, hmod]
  rw [this]
  exact abs_dec_dotF_sub_le hM hu _ _ b

/-! ### The corollary by linking -/

/-- The table: `mm` by the triple loop. -/
def mmTable : Table MOp ScalarOp Empty
  | .mm => .inl mmImpl

/-- The cost of one `mm` at `[a, b, c]` in scalar operations. -/
noncomputable def mmCost : MOp → List ℕ → Count ScalarOp Empty
  | .mm, [a, b, c] =>
      (a * c) • (Count.one (.lit 0) [] + b • (Count.one .mul [] + Count.one .add []))
  | .mm, _ => 0

omit [Inhabited K] in
/-- The accounting certificate of the triple loop, by evaluating its static cost. -/
theorem mm_accounts (I : Interp ScalarOp Empty K) :
    mmTable.Accounts I (fun _ _ => 0) mmCost (fun _ _ => 1) := by
  refine Table.accounts_of_static ?_ (fun o o' hT => by cases o; cases hT) I
  intro o R hT d offs hd ho
  cases o
  cases hT
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hd
  obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.mp ho
  simp [mmImpl, dotLoop, staticCost, staticPeak, useCost, mmCost, mul_smul]

/-- The induced interpretation meets the functional contract of `mm` with `f = mmF M`. -/
theorem isMM_link {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) :
    IsMM (mmF M) (I.link mmTable) where
  isFn := Interp.link_isFn rfl fun _ _ _ _ _ _ hadm h => mm_cert hI hadm h
  length a b c As Bs := length_mmPrefix M b c As Bs (a * c)

/-- **The concrete corollary**: `sq2` linked with the triple loop computes the rounded products
`mmF`, within the pushed-forward counts and one scratch cell. One application of the linking
theorem. -/
theorem runs_sq2_link {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) {τ : Tape K}
    {n : ℕ}
    {A P S : ℕ × ℕ} {m : Mem K} {As : List K} (hAP : A.1 ≠ P.1) (hPS : P.1 ≠ S.1)
    (hA : m.store.readBlock A.1 A.2 (n * n) = some As) (hP : P.2 + n * n ≤ m.store.len P.1)
    (hS : S.2 + n * n ≤ m.store.len S.1) (hl : m.Live [A, P, S]) :
    Runs I (fun _ _ => 0) τ (sq2.link mmTable) ⟨[n, A.2, P.2, S.2], [A.1, P.1, S.1]⟩ m
      (Count.push mmCost (2 • Count.one .mm [n, n, n])) 1
      (· = (m.updBlock P (mmF M n n n As As)).updBlock S
        (mmF M n n n (mmF M n n n As As) (mmF M n n n As As))) :=
  (runs_sq2 (isMM_link hI) (fun _ _ => 1) hAP hPS hA hP hS hl).link (mm_accounts I)

omit [Inhabited K] in
/-- The scalar counts of the linked `sq2`: `2 n²` literals and `2 n³` multiplications and
additions. -/
theorem push_mmCost_mm (n : ℕ) : Count.push mmCost (2 • Count.one .mm [n, n, n]) =
    (2 * (n * n)) • Count.one (.lit 0) [] +
      (2 * (n * n * n)) • (Count.one .mul [] + Count.one .add []) := by
  simp only [map_nsmul, Count.push_one, mmCost]
  module

/-- **Witness**: the functional contract of `mm` can be met, with an `f` meeting the entrywise
error bound, for every `u ≥ 0`. -/
theorem exists_isMM {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (_ : Inhabited K) (dec : K → ℝ) (M : Machine K) (I : Interp MOp Empty K),
      StdModel u dec M ∧ IsMM (mmF M) I :=
  ⟨ℝ, ⟨0⟩, id, exactMachine, (Interp.ofFns exactMachine.fn).link mmTable, stdModel_exact hu,
    isMM_link fun o => Interp.ofFns_isFn _ _ o _⟩

end NLAlib.Ops.Examples
