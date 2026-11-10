/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot

/-!
# Example: going down the hierarchy, word addition over bit operations

The words are bits. `wadd [w] [x, y] [z]` adds two little-endian blocks of `w` bits modulo `2 ^ w`.
Its contract is functional (`NLAlib.Ops.Examples.IsWAdd`): the result is `f` of the inputs, for
some `f` that is addition modulo `2 ^ w` on values (`NLAlib.Ops.Examples.AddMod`).

## Main results

* Abstract theorem (`NLAlib.Ops.Examples.runs_add3`): two additions compute the sum of three
  numbers modulo `2 ^ w`, with two calls at `[w]`.
* The implementation (`NLAlib.Ops.Examples.rippleImpl`): a ripple-carry adder over the bit
  operations `xor3` and `maj`, with a carry cell. Its exact certificate
  (`NLAlib.Ops.Examples.ripple_cert`): the run is the block function of
  `NLAlib.Ops.Examples.rippleF`.
* Mathematics (`NLAlib.Ops.Examples.addMod_ripple`): `rippleF` is addition modulo `2 ^ w`.
* Corollary (`NLAlib.Ops.Examples.runs_add3_link`): the linked program, with its counts of bit
  operations, by the same linking step as every other level.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

/-- The bit operations. -/
inductive BitOp where
  /-- The bit `false`. -/
  | zero
  /-- The sum bit of a full adder. -/
  | xor3
  /-- The carry bit of a full adder. -/
  | maj
  deriving DecidableEq

/-- The word level: one operation, addition of `w`-bit numbers. -/
inductive WOp where
  /-- `wadd [w] [x, y] [z]`. -/
  | wadd
  deriving DecidableEq

/-- The sum bit of a full adder. -/
def xor3 (x y c : Bool) : Bool := (x ^^ y) ^^ c

/-- The carry bit of a full adder. -/
def maj (x y c : Bool) : Bool := (x && y) || (x && c) || (y && c)

/-- The block functions of the bit operations: the model primitives of the bit level. -/
def bitFns : BitOp → BlockFn Bool
  | .zero => .const false
  | .xor3 => .tern fun x y c => some (xor3 x y c)
  | .maj => .tern fun x y c => some (maj x y c)

/-- **The contract of the bit level**: each operation is its Boolean function. -/
def IsBits (I : Interp BitOp Empty Bool) : Prop := ∀ o, I.IsFn .total o (bitFns o) AnyOperands

/-! ### Mathematics: the ripple-carry adder on values -/

/-- The carry into position `k`. -/
def carry (a b : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => maj (a k) (b k) (carry a b k)

/-- The sum bit at position `k`. -/
def sumBit (a b : ℕ → Bool) (k : ℕ) : Bool := xor3 (a k) (b k) (carry a b k)

/-- The value of the `w` low bits. -/
def bitsVal (a : ℕ → Bool) (w : ℕ) : ℕ := ∑ k ∈ Finset.range w, (a k).toNat * 2 ^ k

theorem bitsVal_lt (a : ℕ → Bool) (w : ℕ) : bitsVal a w < 2 ^ w := by
  induction w with
  | zero => simp [bitsVal]
  | succ w ih =>
    rw [bitsVal, Finset.sum_range_succ, ← bitsVal, pow_succ]
    have : (a w).toNat ≤ 1 := Bool.toNat_le _
    nlinarith

/-- The sum bits and the last carry are the sum of the two values. -/
theorem bitsVal_sumBit_add (a b : ℕ → Bool) (w : ℕ) :
    bitsVal (sumBit a b) w + (carry a b w).toNat * 2 ^ w = bitsVal a w + bitsVal b w := by
  induction w with
  | zero => simp [bitsVal, carry]
  | succ w ih =>
    simp only [bitsVal, Finset.sum_range_succ] at ih ⊢
    simp only [sumBit, carry, pow_succ] at ih ⊢
    generalize carry a b w = c at ih ⊢
    generalize a w = x
    generalize b w = y
    cases x <;> cases y <;> cases c <;> simp [xor3, maj] at ih ⊢ <;> omega

/-- The ripple-carry adder as a function on lists of bits. -/
def rippleF (w : ℕ) (xs ys : List Bool) : List Bool :=
  (List.range w).map (sumBit (vec xs) (vec ys))

/-- A function on bit blocks is **addition modulo `2 ^ w`** on values. -/
def AddMod (f : ℕ → List Bool → List Bool → List Bool) : Prop :=
  ∀ w xs ys, (f w xs ys).length = w ∧
    bitsVal (vec (f w xs ys)) w = (bitsVal (vec xs) w + bitsVal (vec ys) w) % 2 ^ w

/-- **The ripple-carry adder is addition modulo `2 ^ w`.** -/
theorem addMod_ripple : AddMod rippleF := by
  intro w xs ys
  refine ⟨by simp [rippleF], ?_⟩
  have hv : bitsVal (vec (rippleF w xs ys)) w = bitsVal (sumBit (vec xs) (vec ys)) w :=
    Finset.sum_congr rfl fun k hk => by
      have hk' := Finset.mem_range.mp hk
      simp [vec, rippleF, List.getD_eq_getElem?_getD, hk']
  rw [hv, ← bitsVal_sumBit_add (vec xs) (vec ys) w, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (bitsVal_lt _ _)]

/-! ### The functional contract of the word level and an abstract theorem -/

/-- The block function of `wadd` given the function `f` on the two blocks. -/
def waddFn (f : ℕ → List Bool → List Bool → List Bool) : BlockFn Bool where
  inLens d := match d with
    | [w] => [w, w]
    | _ => []
  fn d _ xs := match d, xs with
    | [w], [xs, ys] => some (f w xs ys)
    | _, _ => none

/-- What a successful call of the block function of `wadd` is. -/
theorem waddFn_apply {f : ℕ → List Bool → List Bool → List Bool} {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → Bool} {m m' : Mem Bool}
    (h : (waddFn f).apply d ins z τ m = some m') :
    ∃ w x y xs ys, d = [w] ∧ ins = [x, y] ∧ m.store.readBlock x.1 x.2 w = some xs ∧
      m.store.readBlock y.1 y.2 w = some ys ∧ z.2 + (f w xs ys).length ≤ m.store.len z.1 ∧
      m' = m.updBlock z (f w xs ys) := by
  obtain ⟨hlive, X, v, hread, hfn, hlen, rfl⟩ := BlockFn.apply_eq_some_iff.mp h
  rcases d with _ | ⟨w, _ | ⟨w', d⟩⟩
  · simp [waddFn] at hfn
  · obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
    simp only [waddFn, Option.some.injEq] at hfn
    subst hfn
    exact ⟨w, x, y, xs, ys, rfl, rfl, hx, hy, hlen, rfl⟩
  · simp [waddFn] at hfn

/-- A call of the block function of `wadd`, on readable blocks. -/
theorem waddFn_apply_of {f : ℕ → List Bool → List Bool → List Bool} {w : ℕ} {x y z : ℕ × ℕ}
    {τ : ℕ → Bool} {m : Mem Bool} {xs ys : List Bool}
    (hx : m.store.readBlock x.1 x.2 w = some xs) (hy : m.store.readBlock y.1 y.2 w = some ys)
    (hz : z.2 + (f w xs ys).length ≤ m.store.len z.1) (hl : m.Live [x, y, z]) :
    (waddFn f).apply [w] [x, y] z τ m = some (m.updBlock z (f w xs ys)) :=
  BlockFn.apply_eq_some_iff.mpr ⟨hl, [xs, ys], _, by simp [Mem.readBlocks, hx, hy, waddFn], rfl, hz,
    rfl⟩

/-- **The functional contract of `wadd`**: on input blocks in other buffers than the output, the
result is `f` of the inputs. -/
def IsWAdd (f : ℕ → List Bool → List Bool → List Bool) (I : Interp WOp Empty Bool) : Prop :=
  I.IsFn .total .wadd (waddFn f) DisjointBufs

/-- `s := x + y; r := s + z` on `w`-bit numbers. Index variables: `w`, the offsets of `x`, `y`,
`z`, `s`, `r`. -/
def add3 : Stmt WOp Empty :=
  .seq (.call .wadd [.var 0] [⟨0, .var 1⟩, ⟨1, .var 2⟩] [⟨3, .var 4⟩])
    (.call .wadd [.var 0] [⟨3, .var 4⟩, ⟨2, .var 3⟩] [⟨4, .var 5⟩])

/-- **The abstract theorem of `add3`**, for every `f` that is addition modulo `2 ^ w` and every
interpretation meeting the functional contract: two calls of `wadd` at `[w]`, and `r` holds the
sum of the three numbers modulo `2 ^ w`. -/
theorem runs_add3 {f : ℕ → List Bool → List Bool → List Bool} (hf : AddMod f)
    {I : Interp WOp Empty Bool} (hI : IsWAdd f I) (W : WOp → List ℕ → ℕ) {τ : ℕ → Bool} {w : ℕ}
    {x y z s r : ℕ × ℕ} {m : Mem Bool} {xs ys zs : List Bool} (hxs : x.1 ≠ s.1)
    (hys : y.1 ≠ s.1) (hzs : z.1 ≠ s.1) (hsr : s.1 ≠ r.1) (hzr : z.1 ≠ r.1)
    (hx : m.store.readBlock x.1 x.2 w = some xs) (hy : m.store.readBlock y.1 y.2 w = some ys)
    (hz : m.store.readBlock z.1 z.2 w = some zs) (hs : s.2 + w ≤ m.store.len s.1)
    (hr : r.2 + w ≤ m.store.len r.1) (hl : m.Live [x, y, z, s, r]) :
    Runs I W τ add3 ⟨[w, x.2, y.2, z.2, s.2, r.2], [x.1, y.1, z.1, s.1, r.1]⟩ m
      (2 • Count.one .wadd [w]) (W .wadd [w])
      fun m' => ∃ ss rs, m' = (m.updBlock s ss).updBlock r rs ∧
        bitsVal (vec rs) w =
          (bitsVal (vec xs) w + bitsVal (vec ys) w + bitsVal (vec zs) w) % 2 ^ w := by
  have h1 := waddFn_apply_of (f := f) (z := s) (τ := τ) hx hy (by rw [(hf w xs ys).1]; exact hs)
    (by simp_all)
  have hs' : (m.updBlock s (f w xs ys)).store.readBlock s.1 s.2 w = some (f w xs ys) := by
    have := Store.readBlock_updBlock_self (s := m.store) (b := s.1) (off := s.2)
      (xs := f w xs ys) (by rw [(hf w xs ys).1]; exact hs)
    rwa [(hf w xs ys).1] at this
  have hz' : (m.updBlock s (f w xs ys)).store.readBlock z.1 z.2 w = some zs := by
    rw [← hz]
    exact Store.readBlock_congr fun i _ => Store.get_updBlock_of_buf_ne hzs _ _ _
  have h2 := waddFn_apply_of (f := f) (z := r) (τ := τ) hs' hz'
    (by rw [(hf w _ zs).1]; simpa using hr) (by simp_all)
  have hw : Wp .total I τ add3 ⟨[w, x.2, y.2, z.2, s.2, r.2], [x.1, y.1, z.1, s.1, r.1]⟩
      (· = (m.updBlock s (f w xs ys)).updBlock r (f w (f w xs ys) zs)) m :=
    wp_seq (wp_call_fn hI (z := s) rfl rfl rfl (by simp [DisjointBufs, hxs, hys]) h1
      (wp_call_fn hI (z := r) rfl rfl rfl (by simp [DisjointBufs, hsr, hzr]) h2 rfl))
  obtain ⟨m', hrun, hpost⟩ := hw
  refine (Runs.of_run hrun hpost W).mono (by simp [add3, staticCost, useCost, two_nsmul])
    (by simp [add3, staticPeak]) fun m' h => ⟨_, _, h, ?_⟩
  rw [(hf w _ zs).2, (hf w xs ys).2, Nat.mod_add_mod]

/-! ### The implementation over bit operations and its exact certificate -/

/-- **The ripple-carry adder**: a carry cell, cleared, then for each position the sum bit and the
next carry. Index variables: `w`, the offsets of `x`, `y`, `z`, then the loop variable. -/
def rippleImpl : Impl BitOp Empty where
  nd := 1
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.seq (.call .zero [] [] [⟨3, .const 0⟩]) (.loop (.var 0) (.seq
    (.call .xor3 [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2 + .var 4⟩, ⟨3, .const 0⟩]
      [⟨2, .var 3 + .var 4⟩])
    (.call .maj [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2 + .var 4⟩, ⟨3, .const 0⟩]
      [⟨3, .const 0⟩]))))

/-- The first `i` sum bits. -/
def ripplePrefix (a b : ℕ → Bool) (i : ℕ) : List Bool := (List.range i).map (sumBit a b)

theorem ripplePrefix_succ (a b : ℕ → Bool) (i : ℕ) :
    ripplePrefix a b (i + 1) = ripplePrefix a b i ++ [sumBit a b i] := by
  simp [ripplePrefix, List.range_succ]

/-- One position of the adder: the sum bit is appended to the block, the carry cell is updated. -/
theorem wp_ripple_step {I : Interp BitOp Empty Bool} (hI : IsBits I) {md : Mode} {τ : ℕ → Bool}
    {w i : ℕ} (hi : i < w) {x y z : ℕ × ℕ} {s : Store Bool} {p : ℕ} {xs ys : List Bool}
    (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1) (hx : s.readBlock x.1 x.2 w = some xs)
    (hy : s.readBlock y.1 y.2 w = some ys) (hz : z.2 + w ≤ s.len z.1) {Q : Mem Bool → Prop}
    (hQ : Q ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) (i + 1)) ++
      [[some (carry (vec xs) (vec ys) (i + 1))]], p⟩) :
    Wp md I τ (.seq
        (.call .xor3 [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2 + .var 4⟩, ⟨3, .const 0⟩]
          [⟨2, .var 3 + .var 4⟩])
        (.call .maj [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2 + .var 4⟩, ⟨3, .const 0⟩]
          [⟨3, .const 0⟩]))
      ⟨[w, x.2, y.2, z.2, i], [x.1, y.1, z.1, s.length]⟩ Q
      ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) i) ++
        [[some (carry (vec xs) (vec ys) i)]], p⟩ := by
  have hbz : z.1 < s.length := Store.lt_length_of_lt_len (i := z.2) (by omega)
  have hL : ∀ L : List Bool, (s.updBlock z.1 z.2 L).length = s.length :=
    fun L => Store.length_updBlock _ _ _ _
  have hgx : ∀ (L : List Bool) (tb : Buf Bool),
      (s.updBlock z.1 z.2 L ++ [tb]).get x.1 (x.2 + i) = some (vec xs i) := fun L tb => by
    have h := Store.get_of_readBlock hx hi default
    rw [Store.get_append_of_lt (by rw [hL]; exact Store.lt_length_of_get h),
      Store.get_updBlock_of_buf_ne hxz, h]
  have hgy : ∀ (L : List Bool) (tb : Buf Bool),
      (s.updBlock z.1 z.2 L ++ [tb]).get y.1 (y.2 + i) = some (vec ys i) := fun L tb => by
    have h := Store.get_of_readBlock hy hi default
    rw [Store.get_append_of_lt (by rw [hL]; exact Store.lt_length_of_get h),
      Store.get_updBlock_of_buf_ne hyz, h]
  have hgc : ∀ (L : List Bool) (c : Bool),
      (s.updBlock z.1 z.2 L ++ [[some c]]).get s.length 0 = some c := fun L c => by
    rw [Store.get_top (hL L).symm]
    rfl
  have hPl : (ripplePrefix (vec xs) (vec ys) i).length = i := by simp [ripplePrefix]
  refine wp_seq (wp_call_tern (hI .xor3) (x := (x.1, x.2 + i)) (y := (y.1, y.2 + i))
    (w := (s.length, 0)) (z := (z.1, z.2 + i)) rfl rfl rfl trivial (hgx _ _) (hgy _ _) (hgc _ _)
    rfl ?_ ?_)
  · change z.2 + i < (s.updBlock z.1 z.2 _ ++ [_]).len z.1
    rw [Store.len_append_of_lt (by rw [hL]; exact hbz), Store.len_updBlock]
    omega
  have e1 : Mem.upd ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) i) ++
        [[some (carry (vec xs) (vec ys) i)]], p⟩ (z.1, z.2 + i)
        (xor3 (vec xs i) (vec ys i) (carry (vec xs) (vec ys) i)) =
      ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) (i + 1)) ++
        [[some (carry (vec xs) (vec ys) i)]], p⟩ := by
    simp only [Mem.upd]
    rw [Store.upd_append_of_lt (by rw [hL]; exact hbz), ripplePrefix_succ,
      Store.updBlock_concat, hPl]
    rfl
  rw [e1]
  refine wp_call_tern (hI .maj) (x := (x.1, x.2 + i)) (y := (y.1, y.2 + i))
    (w := (s.length, 0)) (z := (s.length, 0)) rfl rfl rfl trivial (hgx _ _) (hgy _ _) (hgc _ _)
    rfl ?_ ?_
  · change 0 < (s.updBlock z.1 z.2 _ ++ [_]).len s.length
    rw [Store.len_top (hL _).symm]
    exact Nat.one_pos
  · simp only [Mem.upd]
    rw [Store.upd_top (hL _).symm]
    exact hQ

/-- **The exact certificate of the ripple-carry adder**: where the block function of `rippleF`
succeeds on inputs in other buffers than the output, the run of the adder is that block
function. -/
theorem ripple_cert {I : Interp BitOp Empty Bool} (hI : IsBits I) {d : List ℕ} {ins : List (ℕ × ℕ)}
    {z : ℕ × ℕ} {τ : ℕ → Bool} {m m' : Mem Bool} (hadm : DisjointBufs d ins z)
    (h : (waddFn rippleF).apply d ins z τ m = some m') :
    rippleImpl.Fits d.length ins.length 1 ∧
      run I τ rippleImpl.body (Env.frame d (ins ++ [z])) m = some m' := by
  obtain ⟨w, x, y, xs, ys, rfl, rfl, hx, hy, hlen, rfl⟩ := waddFn_apply h
  obtain ⟨s, p⟩ := m
  have hz : z.2 + w ≤ s.len z.1 := by simpa [rippleF] using hlen
  refine ⟨⟨rfl, rfl, rfl⟩, run_of_wp (wp_alloc rfl (wp_seq (wp_call_const (hI .zero)
    (z := (s.length, 0)) rfl rfl rfl trivial ?_ ?_)))⟩
  · change 0 < (s ++ [List.replicate 1 none]).len s.length
    simp
  have e0 : (⟨s.push 1, p⟩ : Mem Bool).upd (s.length, 0) false =
      ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) 0) ++
        [[some (carry (vec xs) (vec ys) 0)]], p⟩ := by
    simp only [Mem.upd, Store.push]
    rw [Store.upd_append_top]
    rfl
  rw [e0]
  refine wp_loop (k := w) rfl (fun i m' => m' =
    ⟨s.updBlock z.1 z.2 (ripplePrefix (vec xs) (vec ys) i) ++
      [[some (carry (vec xs) (vec ys) i)]], p⟩) rfl ?_ ?_
  · rintro i hi m' rfl
    exact wp_ripple_step hI hi (hadm x (by simp)) (hadm y (by simp)) hx hy hz rfl
  · rintro m' rfl
    simp [Mem.updBlock, rippleF, ripplePrefix]

/-! ### The corollary by linking -/

/-- The table: `wadd` by the ripple-carry adder. -/
def wordTable : Table WOp BitOp Empty
  | .wadd => .inl rippleImpl

/-- The cost of one `wadd` at `[w]` in bit operations. -/
noncomputable def wordCost : WOp → List ℕ → Count BitOp Empty
  | .wadd, [w] => Count.one .zero [] + w • (Count.one .xor3 [] + Count.one .maj [])
  | .wadd, _ => 0

/-- The accounting certificate of the adder, by evaluating its static cost. -/
theorem word_accounts (I : Interp BitOp Empty Bool) :
    wordTable.Accounts I (fun _ _ => 0) wordCost fun _ _ => 1 := by
  refine Table.accounts_of_static ?_ (fun o o' hT => by cases o; cases hT) I
  intro o R hT d offs hd ho
  cases o
  cases hT
  obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
  simp [rippleImpl, staticCost, staticPeak, useCost, wordCost]

/-- The induced interpretation meets the functional contract of `wadd` with `f = rippleF`. -/
theorem isWAdd_link {I : Interp BitOp Empty Bool} (hI : IsBits I) :
    IsWAdd rippleF (I.link wordTable) :=
  Interp.link_isFn rfl fun _ _ _ _ _ _ hadm h => ripple_cert hI hadm h

/-- **The concrete corollary**: `add3` linked down to bit operations computes the sum of three
`w`-bit numbers modulo `2 ^ w`, within the pushed-forward counts and one scratch cell. -/
theorem runs_add3_link {I : Interp BitOp Empty Bool} (hI : IsBits I) {τ : ℕ → Bool} {w : ℕ}
    {x y z s r : ℕ × ℕ} {m : Mem Bool} {xs ys zs : List Bool} (hxs : x.1 ≠ s.1)
    (hys : y.1 ≠ s.1) (hzs : z.1 ≠ s.1) (hsr : s.1 ≠ r.1) (hzr : z.1 ≠ r.1)
    (hx : m.store.readBlock x.1 x.2 w = some xs) (hy : m.store.readBlock y.1 y.2 w = some ys)
    (hz : m.store.readBlock z.1 z.2 w = some zs) (hs : s.2 + w ≤ m.store.len s.1)
    (hr : r.2 + w ≤ m.store.len r.1) (hl : m.Live [x, y, z, s, r]) :
    Runs I (fun _ _ => 0) τ (add3.link wordTable)
      ⟨[w, x.2, y.2, z.2, s.2, r.2], [x.1, y.1, z.1, s.1, r.1]⟩ m
      (Count.push wordCost (2 • Count.one .wadd [w])) 1
      fun m' => ∃ ss rs, m' = (m.updBlock s ss).updBlock r rs ∧
        bitsVal (vec rs) w =
          (bitsVal (vec xs) w + bitsVal (vec ys) w + bitsVal (vec zs) w) % 2 ^ w :=
  (runs_add3 addMod_ripple (isWAdd_link hI) (fun _ _ => 1) hxs hys hzs hsr hzr hx hy hz hs
    hr hl).link (word_accounts I)

/-- The bit-operation counts of the linked `add3`. -/
theorem push_wordCost_wadd (w : ℕ) : Count.push wordCost (2 • Count.one .wadd [w]) =
    2 • Count.one .zero [] + (2 * w) • (Count.one .xor3 [] + Count.one .maj []) := by
  simp only [map_nsmul, Count.push_one, wordCost]
  module

/-- **Witness**: the bit operations exist, and with them the functional contract of `wadd` is
met by a function that is addition modulo `2 ^ w`. -/
theorem exists_isWAdd :
    ∃ (I : Interp BitOp Empty Bool) (f : ℕ → List Bool → List Bool → List Bool),
      IsBits I ∧ AddMod f ∧ IsWAdd f (I.link wordTable) :=
  ⟨Interp.ofFns bitFns, rippleF, fun o => Interp.ofFns_isFn _ _ o _, addMod_ripple,
    isWAdd_link fun o => Interp.ofFns_isFn _ _ o _⟩

/-- A run of the linked adder on words: `5 + 6 = 3` modulo `8`, on three-bit blocks. -/
example : run (Interp.ofFns bitFns) (fun _ => false) rippleImpl.body
    (Env.frame [3] [(0, 0), (1, 0), (2, 0)])
    ⟨[[some true, some false, some true], [some false, some true, some true],
      [none, none, none]], 0⟩ =
    some ⟨[[some true, some false, some true], [some false, some true, some true],
      [some true, some true, some false]], 0⟩ := by
  rfl

end NLAlib.Ops.Examples
