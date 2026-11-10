/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot

/-!
# Example: a partial-correctness corollary through the induced interpretation

`div` is implemented by `t := recip y; z := x * t`, and `recip` fails on a word that decodes to
zero. The contract of `div` (`NLAlib.Ops.Examples.divSpec`) is mode-generic: readability of the
operands and a nonzero divisor are needed only for success (`Mode.Needs`), and are *conclusions*
of a successful call.

## Main results

* Liberal abstract theorem (`NLAlib.Ops.Examples.runsL_scale`): dividing a block by a cell;
  **if the run succeeds**, every entry is a rounded quotient and, if the block is not empty, the
  divisor is not zero. Nothing is assumed of the divisor.
* Grounding in liberal mode (`NLAlib.Ops.Examples.div_link_liberal`): the induced interpretation
  meets the liberal contract of `div`.
* Corollary (`NLAlib.Ops.Examples.runsL_scale_link`): the same statement for the linked
  program, by `RunsL.link`: liberal theorems transfer through the induced interpretation, with no
  certificate.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type}

/-- The lower signature: a reciprocal that may fail, and a multiplication. -/
inductive ROp where
  /-- `recip [] [y] [t]`. -/
  | recip
  /-- `mul [] [x, y] [z]`. -/
  | mul
  deriving DecidableEq

/-- The upper signature: a division. -/
inductive DOp where
  /-- `div [] [x, y] [z]`. -/
  | div
  deriving DecidableEq

/-! ### Mathematics -/

/-- A reciprocal and a multiplication with relative error `u`; the reciprocal is defined only
away from zero. -/
structure RecipModel (u : ℝ) (dec : K → ℝ) (recipF : K → Option K) (mulF : K → K → K) :
    Prop where
  /-- A reciprocal that is defined is that of a nonzero number, up to `u`. -/
  recip : ∀ b t, recipF b = some t → dec b ≠ 0 ∧ |dec t - 1 / dec b| ≤ u * |1 / dec b|
  /-- Rounded multiplication. -/
  mul : ∀ a b, |dec (mulF a b) - dec a * dec b| ≤ u * |dec a * dec b|

/-- A quotient computed as a rounded product with a rounded reciprocal. -/
theorem abs_sub_div_le {u A B t v : ℝ} (hu : 0 ≤ u) (ht : |t - 1 / B| ≤ u * |1 / B|)
    (hv : |v - A * t| ≤ u * |A * t|) : |v - A / B| ≤ (2 * u + u ^ 2) * |A / B| := by
  rw [div_eq_mul_one_div A B, abs_mul A (1 / B)]
  rw [abs_mul] at hv
  generalize 1 / B = r at ht
  have h1 : |t| ≤ |r| + u * |r| := by
    have := abs_add_le r (t - r)
    rw [add_sub_cancel] at this
    linarith
  have h2 : |v - A * r| ≤ |v - A * t| + |A| * |t - r| := by
    have := abs_add_le (v - A * t) (A * (t - r))
    rw [abs_mul] at this
    rwa [show v - A * t + A * (t - r) = v - A * r by ring] at this
  have hA := abs_nonneg A
  have h3 : |A| * |t - r| ≤ |A| * (u * |r|) := mul_le_mul_of_nonneg_left ht hA
  have h4 : u * (|A| * |t|) ≤ u * (|A| * (|r| + u * |r|)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hA) hu
  nlinarith

/-! ### Contracts -/

/-- **The mode-generic contract of `div`**: the quotient up to the
relative error `ε`. Readability and a nonzero divisor are needed only for success, and hold after
a successful call. -/
def divSpec (dec : K → ℝ) (ε : ℝ) : Contract K where
  spec md d ins outs _ :=
    { pre := fun m => ∃ x y z, d = [] ∧ ins = [x, y] ∧ outs = [z] ∧
        md.Needs (∃ a b, m.store.get x.1 x.2 = some a ∧ m.store.get y.1 y.2 = some b ∧
          dec b ≠ 0 ∧ z.2 < m.store.len z.1)
      post := fun m m' => ∃ x y z a b v, ins = [x, y] ∧ outs = [z] ∧
        m.store.get x.1 x.2 = some a ∧ m.store.get y.1 y.2 = some b ∧ dec b ≠ 0 ∧
        |dec v - dec a / dec b| ≤ ε * |dec a / dec b| ∧ m' = m.upd z v }

theorem divSpec_pre {dec : K → ℝ} {ε : ℝ} {md : Mode} {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {τ : Tape K} {m : Mem K} : ((divSpec dec ε).on md d ins outs τ m).pre m ↔
      ∃ x y z, d = [] ∧ ins = [x, y] ∧ outs = [z] ∧
        md.Needs (∃ a b, m.store.get x.1 x.2 = some a ∧ m.store.get y.1 y.2 = some b ∧
          dec b ≠ 0 ∧ z.2 < m.store.len z.1) := Iff.rfl

theorem divSpec_post {dec : K → ℝ} {ε : ℝ} {md : Mode} {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {τ : Tape K} {m m' : Mem K} : ((divSpec dec ε).on md d ins outs τ m).post m m' ↔
      ∃ x y z a b v, ins = [x, y] ∧ outs = [z] ∧
        m.store.get x.1 x.2 = some a ∧ m.store.get y.1 y.2 = some b ∧ dec b ≠ 0 ∧
        |dec v - dec a / dec b| ≤ ε * |dec a / dec b| ∧ m' = m.upd z v := Iff.rfl

/-- **The liberal contracts of the lower level**: a successful call of `recip` or `mul` is the
function. -/
structure IsRecipMul (recipF : K → Option K) (mulF : K → K → K)
    (I : Interp ROp Empty K) : Prop where
  /-- `recip`. -/
  recip : I.IsFn .liberal .recip (.un recipF) AnyOperands
  /-- `mul`. -/
  mul : I.IsFn .liberal .mul (.bin fun a b => some (mulF a b)) AnyOperands

/-! ### The implementation and its grounding in liberal mode -/

/-- **The implementation of `div`**: `t := recip y; z := x * t`. Index variables: the offsets of
`x`, `y`, `z`. -/
def divImpl : Impl ROp Empty where
  nd := 0
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.seq (.call .recip [] [⟨1, .var 1⟩] [⟨3, .const 0⟩])
    (.call .mul [] [⟨0, .var 0⟩, ⟨3, .const 0⟩] [⟨2, .var 2⟩]))

/-- The table: `div` by reciprocal and multiplication. -/
def divTable : Table DOp ROp Empty
  | .div => .inl divImpl

/-- **The induced interpretation meets the liberal contract of `div`**: if the implementation
succeeds, the operands were readable, the divisor nonzero, and the result is the quotient up to
`2 u + u ^ 2`. -/
theorem div_link_liberal {recipF : K → Option K} {mulF : K → K → K} {I : Interp ROp Empty K}
    (hI : IsRecipMul recipF mulF I) {u : ℝ} {dec : K → ℝ}
    (hM : RecipModel u dec recipF mulF) (hu : 0 ≤ u) :
    (I.link divTable).Meets .liberal .div (divSpec dec (2 * u + u ^ 2)) := by
  refine Interp.link_meets (R := divImpl) rfl ?_
  intro d ins outs τ m hpre
  obtain ⟨s, p⟩ := m
  obtain ⟨x, y, z, rfl, rfl, rfl, -⟩ := divSpec_pre.mp hpre
  refine ⟨by simp, fun hl => ?_⟩
  obtain ⟨hbx, hby, hbz⟩ : x.1 < s.length ∧ y.1 < s.length ∧ z.1 < s.length := by simpa using hl
  refine ⟨⟨rfl, rfl, rfl⟩, wp_alloc rfl (wp_seq (wp_call_fn_liberal hI.recip
    (b := [(s.length, 0)]) rfl rfl rfl rfl trivial fun m₁ h₁ => ?_))⟩
  obtain ⟨b, t, hy, hg, -, rfl⟩ := BlockFn.apply_un_eq_some_iff.mp h₁
  have hy' : s.get y.1 y.2 = some b := by
    rw [← Store.get_append_of_lt hby [List.replicate 1 none]]
    exact hy
  have e1 : (⟨s.push 1, p⟩ : Mem K).upd (s.length, 0) t = ⟨s ++ [[some t]], p⟩ := by
    simp only [Mem.upd, Store.push]
    rw [Store.upd_append_top]
    rfl
  rw [e1]
  refine wp_call_fn_liberal hI.mul (b := [z]) rfl rfl rfl rfl trivial fun m₂ h₂ => ?_
  obtain ⟨a, t', v, hx, ht, hgm, -, rfl⟩ := BlockFn.apply_bin_eq_some_iff.mp h₂
  have hx' : s.get x.1 x.2 = some a := by
    rw [← Store.get_append_of_lt hbx [[some t]]]
    exact hx
  have ht' : (s ++ [[some t]]).get s.length 0 = some t' := ht
  rw [Store.get_append_top] at ht'
  obtain rfl : t = t' := by simpa using ht'
  obtain rfl := Option.some.inj hgm
  obtain ⟨hb0, hrec⟩ := hM.recip b t hg
  refine divSpec_post.mpr ⟨x, y, z, a, b, mulF a t, rfl, rfl, hx', hy', hb0,
    abs_sub_div_le hu hrec (hM.mul a t), ?_⟩
  simp only [Mem.upd]
  rw [Store.upd_append_of_lt hbz, Store.pop_append_top]

/-! ### A liberal abstract theorem and its corollary -/

variable [Inhabited K]

/-- `v_i := v_i / s` for `i < n`. Index variables: `n`, the offsets of `v`, `s`, then the loop
variable. -/
def scale : Stmt DOp Empty :=
  .loop (.var 0) (.call .div [] [⟨0, .var 1 + .var 3⟩, ⟨1, .var 2⟩] [⟨0, .var 1 + .var 3⟩])

/-- The conclusion of a successful run of `scale` from `m`: the block holds rounded quotients of
its former entries by the divisor, and the divisor was not zero if the block is not empty. -/
def ScalePost (dec : K → ℝ) (ε : ℝ) (n : ℕ) (v s : ℕ × ℕ) (m m' : Mem K) : Prop :=
  ∃ zs : List K, zs.length = n ∧ m' = m.updBlock v zs ∧
    ∀ j < n, ∃ a b, m.store.get v.1 (v.2 + j) = some a ∧ m.store.get s.1 s.2 = some b ∧
      dec b ≠ 0 ∧ |dec (vec zs j) - dec a / dec b| ≤ ε * |dec a / dec b|

/-- **A liberal abstract theorem**: for every interpretation meeting the liberal contract of
`div`, if the run of `scale` succeeds then its conclusion holds. No hypothesis on the divisor, on
the readability of the block or on the handles: the evaluator rejects a handle outside the store. -/
theorem runsL_scale {dec : K → ℝ} {ε : ℝ} {J : Interp DOp Empty K}
    (hJ : J.Meets .liberal .div (divSpec dec ε)) {τ : Tape K} {n : ℕ} {v s : ℕ × ℕ} {m : Mem K}
    (hvs : v.1 ≠ s.1) :
    RunsL J τ scale ⟨[n, v.2, s.2], [v.1, s.1]⟩ m (ScalePost dec ε n v s m) := by
  refine wp_liberal_iff.mp (wp_loop (k := n) rfl (fun i m' => ScalePost dec ε i v s m m')
    ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩ ?_ fun _ h => h)
  rintro i hi m' ⟨zs, hzl, rfl, hzs⟩
  refine wp_call hJ (d := []) (a := [(v.1, v.2 + i), s]) (b := [(v.1, v.2 + i)]) rfl rfl rfl
    (divSpec_pre.mpr ⟨_, _, _, rfl, rfl, rfl, by simp⟩) ?_
  intro m₂ hpost
  obtain ⟨x', y', z', a, b, w, hi', ho', hx, hy, hb0, herr, rfl⟩ := divSpec_post.mp hpost
  cases hi'
  cases ho'
  have hx' : m.store.get v.1 (v.2 + i) = some a := by
    rw [← hx]
    exact (Store.get_updBlock_of_ge (by rw [hzl])).symm
  have hy' : m.store.get s.1 s.2 = some b := by
    rw [← hy]
    exact (Store.get_updBlock_of_buf_ne hvs.symm _ _ _).symm
  refine ⟨zs ++ [w], by simp [hzl], ?_, fun j hj => ?_⟩
  · simp only [Mem.upd, Mem.updBlock]
    rw [Store.updBlock_concat, hzl]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · obtain ⟨a', b', h1, h2, h3, h4⟩ := hzs j hlt
      refine ⟨a', b', h1, h2, h3, ?_⟩
      rwa [show vec (zs ++ [w]) j = vec zs j by
        simp [vec, List.getD_eq_getElem?_getD, List.getElem?_append_left (hzl ▸ hlt)]]
    · refine ⟨a, b, hx', hy', hb0, ?_⟩
      rwa [show vec (zs ++ [w]) j = w by simp [vec, List.getD_eq_getElem?_getD, ← hzl]]

/-- **The liberal corollary, through the induced interpretation**: if the linked program
(reciprocals and multiplications) succeeds, the conclusion holds with `ε = 2 u + u ^ 2`. One
application of `link_liberal`; no certificate and no proof about the loop. -/
theorem runsL_scale_link {recipF : K → Option K} {mulF : K → K → K} {I : Interp ROp Empty K}
    (hI : IsRecipMul recipF mulF I) {u : ℝ} {dec : K → ℝ} (hM : RecipModel u dec recipF mulF)
    (hu : 0 ≤ u) {τ : Tape K} {n : ℕ} {v s : ℕ × ℕ} {m : Mem K} (hvs : v.1 ≠ s.1) :
    RunsL I τ (scale.link divTable) ⟨[n, v.2, s.2], [v.1, s.1]⟩ m
      (ScalePost dec (2 * u + u ^ 2) n v s m) :=
  link_liberal (Ck := fun J => J.Meets .liberal .div (divSpec dec (2 * u + u ^ 2)))
    (fun _ hJ => runsL_scale hJ hvs) (div_link_liberal hI hM hu)

/-! ### A liberal statement can be vacuous -/

/-- The table whose implementation of `div` fails. -/
def abortTable : Table DOp ROp Empty
  | .div => .inl ⟨0, 2, 1, .abort⟩

/-- **The liberal corollary holds for the table that fails, with the error `0`**: the linked
program never succeeds, so "if it succeeds the quotients are exact" is true and says nothing.
A liberal theorem is therefore never a result by itself: it is registered only together with a
statement of success (here `NLAlib.Ops.Examples.exists_isRecipMul` and a range on which the
reciprocal is defined). -/
theorem runsL_scale_link_abort (I : Interp ROp Empty K) (dec : K → ℝ) {τ : Tape K} {n : ℕ}
    {v s : ℕ × ℕ} {m : Mem K} (hvs : v.1 ≠ s.1) :
    RunsL I τ (scale.link abortTable) ⟨[n, v.2, s.2], [v.1, s.1]⟩ m
      (ScalePost dec 0 n v s m) :=
  link_liberal (Ck := fun J => J.Meets .liberal .div (divSpec dec 0))
    (fun _ hJ => runsL_scale hJ hvs)
    (Interp.link_meets_liberal_of_abort (R := ⟨0, 2, 1, .abort⟩) rfl rfl _)

/-! ### Witness -/

/-- The exact reciprocal of a real number, undefined at zero. -/
noncomputable def recipExact (b : ℝ) : Option ℝ := if b = 0 then none else some (1 / b)

theorem recipModel_exact {u : ℝ} (hu : 0 ≤ u) :
    RecipModel u id recipExact (fun a b => a * b) where
  recip b t h := by
    unfold recipExact at h
    split_ifs at h with hb
    cases h
    refine ⟨hb, ?_⟩
    simp only [id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  mul a b := by
    simp only [id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)

/-- **Witness**: the liberal contracts of the lower level and of `div` can be met, for every
`u ≥ 0`. -/
theorem exists_isRecipMul {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (dec : K → ℝ) (recipF : K → Option K) (mulF : K → K → K) (I : Interp ROp Empty K),
      RecipModel u dec recipF mulF ∧ IsRecipMul recipF mulF I ∧
        (I.link divTable).Meets .liberal .div (divSpec dec (2 * u + u ^ 2)) := by
  let F : ROp → BlockFn ℝ := fun o => match o with
    | .recip => .un recipExact
    | .mul => .bin fun a b => some (a * b)
  have hI : IsRecipMul recipExact (fun a b => a * b) (Interp.ofFns F) :=
    ⟨Interp.ofFns_isFn F _ .recip _, Interp.ofFns_isFn F _ .mul _⟩
  exact ⟨ℝ, id, recipExact, fun a b => a * b, Interp.ofFns F, recipModel_exact hu, hI,
    div_link_liberal hI (recipModel_exact hu) hu⟩

end NLAlib.Ops.Examples
