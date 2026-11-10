/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot

/-!
# Example: a level of vector operations over scalar arithmetic

The signature `NLAlib.Ops.Examples.BOp` has `dot`, `axpy` and the scalar operations. The
contracts of `dot` and `axpy` are relational (`NLAlib.Ops.Examples.dotSpec`,
`NLAlib.Ops.Examples.axpySpec`): the outputs satisfy an error bound with parameters `εd n` and
`εa`; the scalar operations keep their functional contract. `NLAlib.Ops.Examples.IsBlas` bundles
them.

The table `NLAlib.Ops.Examples.blasTable` implements `dot` and `axpy` by loops over scalar
arithmetic. `NLAlib.Ops.Examples.isBlas_link`: the induced interpretation meets the contracts
with `εd n = (1 + u) ^ (2 n) - 1` and `εa = 2 u + u ^ 2`, the accuracy parameters being fixed by
instantiation. `NLAlib.Ops.Examples.blas_accounts`: the accounting certificate, by evaluating
the static cost of the two trees. `NLAlib.Ops.Examples.exists_isBlas`: the contracts can be met
for every `u ≥ 0`.
## Main results

* `NLAlib.Ops.Examples.isBlas_link`: the induced interpretation meets the contracts of the
  vector level.
* `NLAlib.Ops.Examples.blas_accounts`: the accounting certificate of the table.
* `NLAlib.Ops.Examples.abs_dec_add_mul_sub_le`: one rounded `y + α x`.
* `NLAlib.Ops.Examples.exists_isBlas`: the contracts can be met.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type}

/-- Vector operations and scalar arithmetic. -/
inductive BOp where
  /-- `dot [n] [x, y] [z]`: the dot product of two blocks of length `n`, in the cell `z`. -/
  | dot
  /-- `axpy [n] [α, x, y] [y]`: `y := y + α x` on blocks of length `n`, in place. -/
  | axpy
  /-- A scalar operation. -/
  | ar (a : AOp)
  deriving DecidableEq

/-! ### Mathematics: the error predicates and the rounded `axpy` -/

/-- `v` is the dot product of `a` and `b` up to the relative error `e`. -/
def DotErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (a b : ℕ → K) (v : K) : Prop :=
  |dec v - ∑ k ∈ Finset.range n, dec (a k) * dec (b k)| ≤
    e * ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)|

/-- `z` is `y + α x` up to the componentwise relative error `e`. -/
def AxpyErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (al : K) (x y z : ℕ → K) : Prop :=
  ∀ i < n, |dec (z i) - (dec (y i) + dec al * dec (x i))| ≤
    e * (|dec (y i)| + |dec al * dec (x i)|)

/-- One rounded `y + α x`. -/
theorem abs_dec_add_mul_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (al x y : K) : |dec (M.add y (M.mul al x)) - (dec y + dec al * dec x)| ≤
      (2 * u + u ^ 2) * (|dec y| + |dec al * dec x|) := by
  have h1 := hM.mul al x
  have h2 := hM.add y (M.mul al x)
  generalize dec (M.add y (M.mul al x)) = r at h2
  generalize dec (M.mul al x) = p at h1 h2
  generalize dec al * dec x = q at h1
  generalize dec y = Y at h2
  have hp : |p| ≤ |q| + u * |q| := by
    have := abs_add_le q (p - q)
    rw [add_sub_cancel] at this
    linarith
  have hA : |r - (Y + p)| ≤ u * (|Y| + (|q| + u * |q|)) :=
    h2.trans (mul_le_mul_of_nonneg_left ((abs_add_le Y p).trans (by linarith)) hu)
  have h3 : |r - (Y + q)| ≤ |r - (Y + p)| + |p - q| := by
    have := abs_add_le (r - (Y + p)) (p - q)
    rwa [show r - (Y + p) + (p - q) = r - (Y + q) by ring] at this
  nlinarith [abs_nonneg Y, abs_nonneg q, mul_nonneg hu (abs_nonneg Y),
    mul_nonneg (mul_nonneg hu hu) (abs_nonneg Y), mul_nonneg hu (abs_nonneg q)]

theorem DotErr.congr {dec : K → ℝ} {e : ℝ} {n : ℕ} {a b a' b' : ℕ → K} {v : K}
    (h : DotErr dec e n a b v) (ha : ∀ i < n, a i = a' i) (hb : ∀ i < n, b i = b' i) :
    DotErr dec e n a' b' v := by
  have h1 : ∀ i ∈ Finset.range n, dec (a i) * dec (b i) = dec (a' i) * dec (b' i) :=
    fun i hi => by rw [ha i (Finset.mem_range.mp hi), hb i (Finset.mem_range.mp hi)]
  have h2 : ∀ i ∈ Finset.range n, |dec (a i) * dec (b i)| = |dec (a' i) * dec (b' i)| :=
    fun i hi => by rw [h1 i hi]
  unfold DotErr at h ⊢
  rwa [← Finset.sum_congr rfl h1, ← Finset.sum_congr rfl h2]

theorem AxpyErr.congr {dec : K → ℝ} {e : ℝ} {n : ℕ} {al : K} {x y z x' y' z' : ℕ → K}
    (h : AxpyErr dec e n al x y z) (hx : ∀ i < n, x i = x' i) (hy : ∀ i < n, y i = y' i)
    (hz : ∀ i < n, z i = z' i) : AxpyErr dec e n al x' y' z' := by
  intro i hi
  rw [← hx i hi, ← hy i hi, ← hz i hi]
  exact h i hi

/-! ### Contracts -/

variable [Inhabited K]

/-- **The relational contract of `dot`**: on blocks in other buffers than the output cell, the
cell receives a dot product up to the relative error `ε n`. Readability of the operands is needed
only for success. -/
def dotSpec (dec : K → ℝ) (ε : ℕ → ℝ) : Contract K := fun md d ins outs _ =>
  { pre := fun m => ∃ n x y z, d = [n] ∧ ins = [x, y] ∧ outs = [z] ∧ x.1 ≠ z.1 ∧ y.1 ≠ z.1 ∧
      md.Needs ((m.store.readBlock x.1 x.2 n).isSome ∧ (m.store.readBlock y.1 y.2 n).isSome ∧
        z.2 < m.store.len z.1)
    post := fun m m' => ∃ n x y z xs ys v, d = [n] ∧ ins = [x, y] ∧ outs = [z] ∧
      m.store.readBlock x.1 x.2 n = some xs ∧ m.store.readBlock y.1 y.2 n = some ys ∧
      DotErr dec (ε n) n (vec xs) (vec ys) v ∧ m' = m.upd z v }

/-- **The relational contract of `axpy`**, in place: with `α` and `x` in other buffers than `y`,
the block `y` receives `y + α x` up to the componentwise relative error `ε`. -/
def axpySpec (dec : K → ℝ) (ε : ℝ) : Contract K := fun md d ins outs _ =>
  { pre := fun m => ∃ n al x y, d = [n] ∧ ins = [al, x, y] ∧ outs = [y] ∧ al.1 ≠ y.1 ∧
      x.1 ≠ y.1 ∧ md.Needs ((m.store.get al.1 al.2).isSome ∧
        (m.store.readBlock x.1 x.2 n).isSome ∧ (m.store.readBlock y.1 y.2 n).isSome)
    post := fun m m' => ∃ n al x y a xs ys zs, d = [n] ∧ ins = [al, x, y] ∧ outs = [y] ∧
      m.store.get al.1 al.2 = some a ∧ m.store.readBlock x.1 x.2 n = some xs ∧
      m.store.readBlock y.1 y.2 n = some ys ∧ zs.length = n ∧
      AxpyErr dec ε n a (vec xs) (vec ys) (vec zs) ∧ m' = m.updBlock y zs }

/-- **The contracts of the vector level**, at the accuracy parameters `εd`, `εa`: relational for
`dot` and `axpy`, functional (the machine `M`) for the scalar operations. -/
structure IsBlas (M : Machine K) (dec : K → ℝ) (εd : ℕ → ℝ) (εa : ℝ) (J : Interp BOp K) :
    Prop where
  /-- `dot`. -/
  dot : J.Meets .total .dot (dotSpec dec εd)
  /-- `axpy`. -/
  axpy : J.Meets .total .axpy (axpySpec dec εa)
  /-- Scalar operations. -/
  ar : ∀ a, J.IsFn .total (.ar a) (M.fn a) AnyOperands

/-- A functional `dot` meeting the error bound meets the relational contract. -/
theorem dotSpec_of_isFn {M : Machine K} {dec : K → ℝ} {ε : ℕ → ℝ} {J : Interp BOp K}
    (hJ : J.IsFn .total .dot (dotFn M) DisjointBufs)
    (hε : ∀ n a b, DotErr dec (ε n) n a b (dotF M a b n)) :
    J.Meets .total .dot (dotSpec dec ε) := by
  rintro d ins outs τ m ⟨n, x, y, z, rfl, rfl, rfl, hxz, hyz, hn⟩
  obtain ⟨hx, hy, hz⟩ := hn rfl
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp hy
  have happ : (dotFn M).apply [n] [x, y] z τ m = some (m.upd z (dotF M (vec xs) (vec ys) n)) :=
    BlockFn.apply_eq_some_iff.mpr ⟨[xs, ys], [_], by simp [Mem.readBlocks, hxs, hys, dotFn], rfl,
      by simpa using hz, rfl⟩
  exact ⟨_, hJ.callS_eq (by simp [DisjointBufs, hxz, hyz]) happ, n, x, y, z, xs, ys, _, rfl, rfl,
    rfl, hxs, hys, hε n _ _, rfl⟩

/-! ### The implementation of `axpy` -/

/-- **The implementation of `axpy`**: a scratch cell and a loop of `t := α x_i; z_i := y_i + t`.
Index variables: `n`, the offsets of `α`, `x`, `y`, `z`, then the loop variable. -/
def axpyImpl : Impl AOp where
  nd := 1
  nin := 3
  nout := 1
  body := .alloc (.const 1) (.loop (.var 0) (.seq
    (.call .mul [] [⟨0, .var 1⟩, ⟨1, .var 2 + .var 5⟩] [⟨4, .const 0⟩])
    (.call .add [] [⟨2, .var 3 + .var 5⟩, ⟨4, .const 0⟩] [⟨3, .var 4 + .var 5⟩])))

/-- The values written by the `axpy` loop. -/
def axpyF (M : Machine K) (a : K) (x y : ℕ → K) (n : ℕ) : List K :=
  (List.range n).map fun i => M.add (y i) (M.mul a (x i))

omit [Inhabited K] in
theorem axpyF_succ (M : Machine K) (a : K) (x y : ℕ → K) (n : ℕ) :
    axpyF M a x y (n + 1) = axpyF M a x y n ++ [M.add (y n) (M.mul a (x n))] := by
  simp [axpyF, List.range_succ]

/-- **The `axpy` loop writes `axpyF`** in place of `y`. -/
theorem wp_axpyImpl {M : Machine K} {I : Interp AOp K} (hI : IsArith M I) {md : Mode} {τ : ℕ → K}
    {n : ℕ} {al x y : ℕ × ℕ} {m : Mem K} {a : K} {xs ys : List K} (hal : al.1 ≠ y.1)
    (hxy : x.1 ≠ y.1) (ha : m.store.get al.1 al.2 = some a)
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hy : m.store.readBlock y.1 y.2 n = some ys)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock y (axpyF M a (vec xs) (vec ys) n))) :
    Wp md I τ axpyImpl.body (Env.frame [n] [al, x, y, y]) Q m := by
  obtain ⟨s, p⟩ := m
  have hbal := Store.lt_length_of_get ha
  refine wp_alloc rfl (wp_loop rfl (fun i m' => ∃ tb : Buf K, tb.length = 1 ∧
    m' = ⟨s.updBlock y.1 y.2 (axpyF M a (vec xs) (vec ys) i) ++ [tb], p⟩)
    ⟨List.replicate 1 none, rfl, rfl⟩ ?_ fun m' ⟨tb, _, h⟩ => by simpa [h, Mem.updBlock] using hQ)
  rintro i hi m' ⟨tb, htb, rfl⟩
  have hgx := Store.get_of_readBlock hx hi default
  have hgy := Store.get_of_readBlock hy hi default
  have hlen : (s.updBlock y.1 y.2 (axpyF M a (vec xs) (vec ys) i)).length = s.length :=
    Store.length_updBlock _ _ _ _
  have hby := hlen ▸ Store.lt_length_of_get hgy
  have hFl : (axpyF M a (vec xs) (vec ys) i).length = i := by simp [axpyF]
  refine wp_seq (wp_call_bin (hI .mul) (x := al) (y := (x.1, x.2 + i)) (z := (s.length, 0)) rfl
    rfl rfl trivial (a := a) (b := vec xs i) ?_ ?_ rfl ?_ ?_)
  · change (s.updBlock y.1 y.2 _ ++ [tb]).get al.1 al.2 = some a
    rw [Store.get_append_of_lt (hlen ▸ hbal), Store.get_updBlock_of_buf_ne hal, ha]
  · change (s.updBlock y.1 y.2 _ ++ [tb]).get x.1 (x.2 + i) = some _
    rw [Store.get_append_of_lt (hlen ▸ Store.lt_length_of_get hgx),
      Store.get_updBlock_of_buf_ne hxy, hgx]
  · change 0 < (s.updBlock y.1 y.2 _ ++ [tb]).len s.length
    rw [Store.len_top hlen.symm, htb]
    exact Nat.one_pos
  have e1 : Mem.upd ⟨s.updBlock y.1 y.2 (axpyF M a (vec xs) (vec ys) i) ++ [tb], p⟩
      (s.length, 0) (M.mul a (vec xs i)) =
      ⟨s.updBlock y.1 y.2 (axpyF M a (vec xs) (vec ys) i) ++
        [tb.set 0 (some (M.mul a (vec xs i)))], p⟩ := by
    simp only [Mem.upd]
    rw [Store.upd_top hlen.symm]
  rw [e1]
  refine wp_call_bin (hI .add) (x := (y.1, y.2 + i)) (y := (s.length, 0)) (z := (y.1, y.2 + i))
    rfl rfl rfl trivial (a := vec ys i) (b := M.mul a (vec xs i)) ?_ ?_ rfl ?_ ?_
  · change (s.updBlock y.1 y.2 _ ++ [_]).get y.1 (y.2 + i) = some _
    rw [Store.get_append_of_lt hby, Store.get_updBlock_of_ge (by rw [hFl]), hgy]
  · change (s.updBlock y.1 y.2 _ ++ [_]).get s.length 0 = some _
    rw [Store.get_top hlen.symm]
    simp [htb]
  · change y.2 + i < (s.updBlock y.1 y.2 _ ++ [_]).len y.1
    rw [Store.len_append_of_lt hby, Store.len_updBlock]
    exact Store.lt_len_of_get hgy
  · refine ⟨tb.set 0 (some (M.mul a (vec xs i))), by simpa using htb, ?_⟩
    simp only [Mem.upd]
    rw [Store.upd_append_of_lt hby, axpyF_succ, Store.updBlock_concat, hFl]

/-- The `axpy` loop meets the relational contract when the machine meets the standard model. -/
theorem axpyImpl_spec {M : Machine K} {I : Interp AOp K} (hI : IsArith M I) {u : ℝ} {dec : K → ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : ℕ → K)
    (m : Mem K) (hpre : (axpySpec dec (2 * u + u ^ 2) .total d ins outs τ).pre m) :
    axpyImpl.Fits d.length ins.length outs.length ∧
      Wp .total I τ axpyImpl.body (Env.frame d (ins ++ outs))
        ((axpySpec dec (2 * u + u ^ 2) .total d ins outs τ).post m) m := by
  obtain ⟨n, al, x, y, rfl, rfl, rfl, hal, hxy, hn⟩ := hpre
  obtain ⟨ha, hx, hy⟩ := hn rfl
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp hy
  refine ⟨⟨rfl, rfl, rfl⟩, wp_axpyImpl hI hal hxy ha hxs hys ?_⟩
  refine ⟨n, al, x, y, a, xs, ys, _, rfl, rfl, rfl, ha, hxs, hys, by simp [axpyF], ?_, rfl⟩
  intro i hi
  have : vec (axpyF M a (vec xs) (vec ys) n) i = M.add (vec ys i) (M.mul a (vec xs i)) := by
    simp [vec, axpyF, List.getD_eq_getElem?_getD, hi]
  rw [this]
  exact abs_dec_add_mul_sub_le hM hu _ _ _

/-! ### The table, its certificate, and the contracts of the induced interpretation -/

/-- **The implementation of the vector level over scalar arithmetic.** -/
def blasTable : Table BOp AOp
  | .dot => .inl dotImpl
  | .axpy => .inl axpyImpl
  | .ar a => .inr a

/-- The cost of one call of each vector operation, in scalar operations. -/
noncomputable def blasCost : BOp → List ℕ → Count AOp
  | .dot, [n] => Count.one (.lit 0) [] + n • (Count.one .mul [] + Count.one .add [])
  | .axpy, [n] => n • (Count.one .mul [] + Count.one .add [])
  | .ar a, d => Count.one a d
  | _, _ => 0

/-- The workspace of each vector operation: one scratch cell for `dot` and `axpy`. -/
def blasWs : BOp → List ℕ → ℕ
  | .dot, _ => 1
  | .axpy, _ => 1
  | .ar _, _ => 0

omit [Inhabited K] in
/-- **The accounting certificate of the table**, by evaluating the static cost and workspace of
the two trees; for every interpretation of the scalar operations. -/
theorem blas_accounts (I : Interp AOp K) :
    blasTable.Accounts I (fun _ _ => 0) blasCost blasWs := by
  refine Table.accounts_of_static ?_ ?_ I
  · intro o R hT d offs hd ho
    cases o with
    | dot =>
      cases hT
      obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
      obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
      simp [dotImpl, dotLoop, staticCost, staticPeak, useCost, blasCost, blasWs]
    | axpy =>
      cases hT
      obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
      obtain ⟨a, b, c, e, rfl⟩ := List.length_eq_four.mp ho
      simp [axpyImpl, staticCost, staticPeak, useCost, blasCost, blasWs]
    | ar a => cases hT
  · intro o o' hT d
    cases o with
    | dot => cases hT
    | axpy => cases hT
    | ar a => cases hT; exact ⟨le_rfl, le_rfl⟩

/-- **The induced interpretation meets the contracts of the vector level**, with the accuracy
parameters of the two implementations at the unit roundoff `u`. -/
theorem isBlas_link {M : Machine K} {I : Interp AOp K} (hI : IsArith M I) {u : ℝ} {dec : K → ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) :
    IsBlas M dec (fun n => (1 + u) ^ (2 * n) - 1) (2 * u + u ^ 2) (I.link blasTable) where
  dot := dotSpec_of_isFn (Interp.link_isFn rfl fun _ _ _ _ _ _ hadm h => dot_cert hI hadm h)
    fun n a b => abs_dec_dotF_sub_le hM hu a b n
  axpy := Interp.link_meets rfl (axpyImpl_spec hI hM hu)
  ar a := Interp.link_meets_kept rfl (hI a)

/-- **Witness**: the contracts of the vector level can be met, for every `u ≥ 0`, with the
accuracy parameters of the implementations. -/
theorem exists_isBlas {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (_ : Inhabited K) (dec : K → ℝ) (M : Machine K) (J : Interp BOp K),
      StdModel u dec M ∧ IsBlas M dec (fun n => (1 + u) ^ (2 * n) - 1) (2 * u + u ^ 2) J :=
  ⟨ℝ, ⟨0⟩, id, exactMachine, (Interp.ofFns exactMachine.fn).link blasTable, stdModel_exact hu,
    isBlas_link (fun o => Interp.ofFns_isFn _ _ o _) (stdModel_exact hu) hu⟩

end NLAlib.Ops.Examples
