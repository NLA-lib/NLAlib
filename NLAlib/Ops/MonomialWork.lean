/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Ring
public import NLAlib.Ops.Confined
public import NLAlib.Ops.Logic.KernelRfl
public meta import Lean.Elab.Tactic.Basic

/-!
# Monomial bounds on the number of instructions of a program

A syntactic bound on `NLAlib.Ops.Count.size` of the static count `NLAlib.Ops.stmtCost`, as a
monomial $c\,\prod_i b_i^{e_i}$ in a list of bases, computed from the tree alone
(`NLAlib.Ops.stmtWorkMono`): every index slot carries a monomial bound on its value, a loop or a
`whileFuel` multiplies by the bound of its count, and a sum takes the larger exponents. The guard
`ifPos (e + 1 - j)` of a comparison $j \le e$ narrows the bound of the slot $j$ in its body to
that of $e$ (`NLAlib.Ops.loopSlots`). A call
site contributes one instruction for each list of dimensions its bounds allow, counted once: the
static count takes a pointwise supremum over the branches of an `ite`, the values of a `bindIdx`
and the exits of a `whileFuel`, so the bound needs one count that dominates them all, and one
exists that depends only on the bounds of the slots. The bound of a fixed program is evaluated
by `kernel_rfl` (`NLAlib/Ops/Logic/KernelRfl.lean`), an equation by reflexivity left to the
kernel (which evaluates it with sharing, where the elaborator's `rfl` does not). It keeps each
base with its own exponent, unlike the one-base estimate
`NLAlib.Ops.stmtWeightedCost_le_coefficient_mul_pow`. The bases are a list, one per size of the
program; a monomial lists its exponents, missing ones being $0$.

## Main definitions

* `NLAlib.Ops.WorkMono`: a monomial in a list of bases.
* `NLAlib.Ops.stmtWorkMono`: the monomial bound of a tree at monomial bounds of its slots.

## Main results

* `NLAlib.Ops.size_stmtCost_le_stmtWorkMono`: the number of instructions of the static count is
  at most the monomial bound.
* `NLAlib.Ops.stmtWorkMono_instrument`: the bound of an instrumented tree is computed on the tree
  (`NLAlib.Ops.instrWorkMono`), without building the instrumented tree.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The exponents of a sum: the larger exponent at each base, a missing exponent being $0$. -/
def maxExps : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => max x y :: maxExps xs ys

/-- The exponents of a product: the sum of the exponents at each base, a missing exponent being
$0$. -/
def addExps : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addExps xs ys

/-- The product $\prod_i b_i^{e_i}$ of the bases `bs` at the exponents `es`, over the shorter of
the two lists. -/
def powProd : List ℕ → List ℕ → ℕ
  | b :: bs, e :: es => b ^ e * powProd bs es
  | _, _ => 1

@[simp] theorem powProd_nil_left (es : List ℕ) : powProd [] es = 1 := by cases es <;> rfl

@[simp] theorem powProd_nil_right (bs : List ℕ) : powProd bs [] = 1 := by cases bs <;> rfl

@[simp] theorem powProd_cons_cons (b e : ℕ) (bs es : List ℕ) :
    powProd (b :: bs) (e :: es) = b ^ e * powProd bs es := rfl

theorem powProd_addExps : ∀ (bs xs ys : List ℕ),
    powProd bs (addExps xs ys) = powProd bs xs * powProd bs ys
  | [], _, _ => by simp
  | _ :: _, [], ys => by simp [addExps]
  | _ :: _, _ :: _, [] => by simp [addExps]
  | b :: bs, x :: xs, y :: ys => by
    simp only [addExps, powProd_cons_cons, powProd_addExps bs xs ys, pow_add]; ring

theorem maxExps_comm : ∀ xs ys : List ℕ, maxExps xs ys = maxExps ys xs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp only [maxExps, max_comm x y, maxExps_comm xs ys]

/-- At bases at least $1$, raising the exponents to those of a sum raises the product. -/
theorem powProd_le_powProd_maxExps {bs : List ℕ} (hb : ∀ b ∈ bs, 1 ≤ b) (xs ys : List ℕ) :
    powProd bs xs ≤ powProd bs (maxExps xs ys) := by
  induction bs generalizing xs ys with
  | nil => simp
  | cons b bs ih =>
    have hb0 : 1 ≤ b := hb b (by simp)
    have hbs : ∀ c ∈ bs, 1 ≤ c := fun c hc => hb c (by simp [hc])
    rcases xs with _ | ⟨x, xs⟩
    · simp only [powProd_nil_right]
      exact Nat.one_le_iff_ne_zero.mpr (by
        rcases ys with _ | ⟨y, ys⟩
        · simp [maxExps]
        · simp only [maxExps, powProd_cons_cons]
          exact Nat.mul_ne_zero (pow_ne_zero _ (by omega))
            (Nat.one_le_iff_ne_zero.mp ((ih hbs [] ys).trans' (by simp))))
    · rcases ys with _ | ⟨y, ys⟩
      · simp [maxExps]
      · simp only [maxExps, powProd_cons_cons]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right hb0 (le_max_left x y)) (ih hbs xs ys)

/-- At bases at least $1$, raising each exponent raises the product. -/
theorem powProd_le_powProd_of_forall₂ {bs : List ℕ} (hb : ∀ b ∈ bs, 1 ≤ b) {es fs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) es fs) : powProd bs es ≤ powProd bs fs := by
  induction h generalizing bs with
  | nil => simp
  | cons hab _ ih =>
    rcases bs with _ | ⟨b, bs⟩
    · simp
    · simp only [powProd_cons_cons]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (hb b (by simp)) hab)
        (ih fun c hc => hb c (by simp [hc]))

/-- **A monomial in a list of bases**: $c\prod_i b_i^{e_i}$, with the exponents `e`. -/
structure WorkMono where
  /-- The coefficient. -/
  c : ℕ
  /-- The exponents of the bases, in order; a missing exponent is $0$. -/
  e : List ℕ
  deriving DecidableEq, Repr

namespace WorkMono

/-- The constant monomial $n$. -/
def const (n : ℕ) : WorkMono := ⟨n, []⟩

/-- A monomial bounding a sum: the coefficients add, the exponents take the larger value. -/
def add (x y : WorkMono) : WorkMono := ⟨x.c + y.c, maxExps x.e y.e⟩

/-- The product of two monomials. -/
def mul (x y : WorkMono) : WorkMono := ⟨x.c * y.c, addExps x.e y.e⟩

/-- The value of a monomial at the bases `bs`. -/
def eval (x : WorkMono) (bs : List ℕ) : ℕ := x.c * powProd bs x.e

variable {bs : List ℕ}

@[simp] theorem eval_const (n : ℕ) : (const n).eval bs = n := by simp [const, eval]

theorem eval_mul (x y : WorkMono) : (x.mul y).eval bs = x.eval bs * y.eval bs := by
  simp only [mul, eval, powProd_addExps]; ring

theorem add_eval_le_eval_add (hb : ∀ b ∈ bs, 1 ≤ b) (x y : WorkMono) :
    x.eval bs + y.eval bs ≤ (x.add y).eval bs := by
  have hx := powProd_le_powProd_maxExps hb x.e y.e
  have hy := powProd_le_powProd_maxExps hb y.e x.e
  rw [maxExps_comm] at hy
  simp only [eval, add, Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hx) (Nat.mul_le_mul_left _ hy)

/-- At bases at least $1$, raising the exponents raises the value. -/
theorem eval_le_of_le (hb : ∀ b ∈ bs, 1 ≤ b) {c : ℕ} {es fs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) es fs) : eval ⟨c, es⟩ bs ≤ eval ⟨c, fs⟩ bs :=
  Nat.mul_le_mul_left _ (powProd_le_powProd_of_forall₂ hb h)

end WorkMono

/-- The monomial bound of an index expression at monomial bounds `σ` of the slots: a difference
or a quotient is bounded by its first argument. -/
def IExp.workMono (σ : List WorkMono) : IExp → WorkMono
  | .var i => σ.getD i (WorkMono.const 0)
  | .const n => WorkMono.const n
  | .add a b => (a.workMono σ).add (b.workMono σ)
  | .mul a b => (a.workMono σ).mul (b.workMono σ)
  | .sub a _ => a.workMono σ
  | .div a _ => a.workMono σ

/-- The comparison a loop count guards: `some (e, j)` for the count
$1 - (1 - (e + 1 - j))$ of `NLAlib.Ops.Stmt.ifPos` $(e + 1 - j)$, whose body runs only when the
slot $j$ is at most $e$; `none` for any other count. -/
def IExp.guardLe : IExp → Option (IExp × ℕ)
  | .sub (.const 1) (.sub (.const 1) (.sub (.add e (.const 1)) (.var j))) => some (e, j)
  | _ => none

/-- The slot bounds in the body of a loop of count `n`: the bound of `n` for the counter; and in
the body of the guard of $j \le e$ (`NLAlib.Ops.IExp.guardLe`), the bound of $e$ for the slot $j$.
-/
def loopSlots (σ : List WorkMono) (n : IExp) : List WorkMono :=
  match n.guardLe with
  | some (e, j) => σ.set j (e.workMono σ) ++ [n.workMono σ]
  | none => σ ++ [n.workMono σ]

/-- The monomial bound of the number of lists of dimensions a call site allows:
$\prod_i (\hat d_i + 1)$. -/
def boxWorkMono (σ : List WorkMono) : List IExp → WorkMono
  | [] => WorkMono.const 1
  | e :: es => ((e.workMono σ).add (WorkMono.const 1)).mul (boxWorkMono σ es)

variable {Op Tst : Type}

/-- **The monomial bound of a tree** at monomial bounds `σ` of its slots: a call or a test counts
the lists of dimensions it allows, a branch both sides, a loop and a `whileFuel` multiply by the
bound of their count (the guard of a comparison narrows a slot in its body,
`NLAlib.Ops.loopSlots`), a `bindIdx` binds its slot to the bound of its value, and a frame
evaluates its dimensions and offsets. -/
def stmtWorkMono : Stmt Op Tst → List WorkMono → WorkMono
  | .skip, _ => WorkMono.const 0
  | .abort, _ => WorkMono.const 0
  | .seq s t, σ => (stmtWorkMono s σ).add (stmtWorkMono t σ)
  | .call _ ds _ _, σ => boxWorkMono σ ds
  | .ite _ ds _ t e, σ => (boxWorkMono σ ds).add ((stmtWorkMono t σ).add (stmtWorkMono e σ))
  | .whileFuel fuel _ ds _ body k, σ =>
      ((fuel.workMono σ).mul ((boxWorkMono (σ ++ [fuel.workMono σ]) ds).add
        (stmtWorkMono body (σ ++ [fuel.workMono σ])))).add
        (stmtWorkMono k (σ ++ [fuel.workMono σ]))
  | .bindIdx _ _ bound body, σ =>
      (WorkMono.const 1).add (stmtWorkMono body (σ ++ [bound.workMono σ]))
  | .allocAs _ _ body, σ => stmtWorkMono body σ
  | .loop n body, σ => (n.workMono σ).mul (stmtWorkMono body (loopSlots σ n))
  | .frame ds args body, σ =>
      stmtWorkMono body (ds.map (IExp.workMono σ) ++ (args.map Operand.off).map (IExp.workMono σ))
  | .note _ s, σ => stmtWorkMono s σ

/-! ### The bound of an instrumented tree, without the instrumented tree -/

/-- The monomial bound of a list of structural instructions (`NLAlib.Ops.tally`): one per
instruction, at any slot bounds. -/
def tallyWorkMono : List Bookkeeping → WorkMono
  | [] => WorkMono.const 0
  | _ :: ks => (WorkMono.const 1).add (tallyWorkMono ks)

/-- **The monomial bound of the instrumented tree**, computed on the tree itself: the recursion of
`NLAlib.Ops.stmtWorkMono` on `NLAlib.Ops.Stmt.instrument` of `s`, with the structural instructions
of each node added as `NLAlib.Ops.tallyWorkMono`. It equals the bound of the instrumented tree
(`NLAlib.Ops.stmtWorkMono_instrument`) and is cheaper to evaluate, since the instrumented tree is
never built. -/
def instrWorkMono : Stmt Op Tst → List WorkMono → WorkMono
  | .skip, _ => tallyWorkMono [.skip]
  | .abort, _ => WorkMono.const 0
  | .seq s t, σ => (tallyWorkMono [.sequence]).add ((instrWorkMono s σ).add (instrWorkMono t σ))
  | .call _ ds ins outs, σ =>
      (tallyWorkMono (indexBookkeeping ds ++ operandBookkeeping (ins ++ outs))).add
        (boxWorkMono σ ds)
  | .ite _ ds ins t e, σ =>
      (tallyWorkMono (indexBookkeeping ds ++ operandBookkeeping ins ++ [.branch])).add
        ((boxWorkMono σ ds).add ((instrWorkMono t σ).add (instrWorkMono e σ)))
  | .whileFuel fuel _ ds ins body k, σ =>
      (tallyWorkMono (fuel.bookkeeping ++ [.loop])).add
        (((fuel.workMono σ).mul ((boxWorkMono (σ ++ [fuel.workMono σ]) ds).add
          ((tallyWorkMono (indexBookkeeping ds ++ operandBookkeeping ins ++ [.round])).add
            (instrWorkMono body (σ ++ [fuel.workMono σ]))))).add
          ((tallyWorkMono (indexBookkeeping ds ++ operandBookkeeping ins ++ [.exit])).add
            (instrWorkMono k (σ ++ [fuel.workMono σ]))))
  | .bindIdx _ ins bound body, σ =>
      (tallyWorkMono (operandBookkeeping ins ++ bound.bookkeeping ++ [.bindIdx])).add
        ((WorkMono.const 1).add (instrWorkMono body (σ ++ [bound.workMono σ])))
  | .allocAs fmt len body, σ =>
      (tallyWorkMono len.bookkeeping).add ((boxWorkMono σ [.const fmt.bytes, len]).add
        ((instrWorkMono body σ).add (boxWorkMono σ [.const fmt.bytes, len])))
  | .loop n body, σ =>
      (tallyWorkMono (n.bookkeeping ++ [.loop])).add
        ((n.workMono σ).mul ((tallyWorkMono [.round]).add (instrWorkMono body (loopSlots σ n))))
  | .frame ds args body, σ =>
      (tallyWorkMono (indexBookkeeping ds ++ operandBookkeeping args ++ [.frame])).add
        (instrWorkMono body
          (ds.map (IExp.workMono σ) ++ (args.map Operand.off).map (IExp.workMono σ)))
  | .note _ s, σ => instrWorkMono s σ

/-- The monomial bound of `NLAlib.Ops.tally` does not depend on the slot bounds. -/
theorem stmtWorkMono_tally (ks : List Bookkeeping) (σ : List WorkMono) :
    stmtWorkMono (tally (Op := Op) (Tst := Tst) ks) σ = tallyWorkMono ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [tally, stmtWorkMono, boxWorkMono, tallyWorkMono, ih]

/-- **The bound of an instrumented tree is computed on the tree**: `NLAlib.Ops.stmtWorkMono` of
`NLAlib.Ops.Stmt.instrument` of `s` is `NLAlib.Ops.instrWorkMono` of `s`, at every list of slot
bounds. A work bound of a fixed program is evaluated by rewriting with this equation and
`kernel_rfl` on the right side, which needs a fraction of the kernel memory of the left. -/
theorem stmtWorkMono_instrument (s : Stmt Op Tst) (σ : List WorkMono) :
    stmtWorkMono s.instrument σ = instrWorkMono s σ := by
  induction s generalizing σ with
  | skip => exact stmtWorkMono_tally _ _
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally, instrWorkMono,
      ihs, iht]
  | call o ds ins outs => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono]
  | ite q ds ins t e iht ihe => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono, iht, ihe]
  | whileFuel fuel q ds ins body k ihb ihk => simp only [Stmt.instrument, stmtWorkMono,
      stmtWorkMono_tally, instrWorkMono, ihb, ihk]
  | bindIdx q ins bound body ih => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono, ih]
  | allocAs fmt len body ih => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono, ih, boxWorkMono]
  | loop n body ih => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono, ih]
  | frame ds args body ih => simp only [Stmt.instrument, stmtWorkMono, stmtWorkMono_tally,
      instrWorkMono, ih]
  | note n s ih => simp only [Stmt.instrument, instrWorkMono, ih]

/-! ### Soundness -/

section Soundness

variable {bs : List ℕ}

/-- The values `idx` are bounded by the monomials `σ` at the bases. -/
abbrev SlotsLe (bs : List ℕ) (idx : List ℕ) (σ : List WorkMono) : Prop :=
  List.Forall₂ (fun v m => v ≤ WorkMono.eval m bs) idx σ

private theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {i : ℕ} {a : α} (ha : l₁[i]? = some a) :
    ∃ b, l₂[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => simp at ha
  | cons hr _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      exact ⟨_, rfl, ha ▸ hr⟩
    | succ i => simpa using ih (by simpa using ha)

theorem IExp.eval_le_workMono {idx : List ℕ} {σ : List WorkMono}
    (hσ : SlotsLe bs idx σ) (hb : ∀ b ∈ bs, 1 ≤ b) :
    ∀ (e : IExp) {v : ℕ}, e.eval idx = some v → v ≤ (e.workMono σ).eval bs
  | .var i, v, h => by
    obtain ⟨m, hm, hv⟩ := forall₂_getElem? hσ h
    simp only [IExp.workMono, List.getD_eq_getElem?_getD, hm, Option.getD_some]
    exact hv
  | .const n, v, h => by
    simp only [IExp.eval, Option.some.injEq] at h
    simp [IExp.workMono, h]
  | .add a c, v, h => by
    simp only [IExp.eval] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    rename_i x y hx hy
    rw [← h]
    exact (Nat.add_le_add (IExp.eval_le_workMono hσ hb a hx)
      (IExp.eval_le_workMono hσ hb c hy)).trans
      (WorkMono.add_eval_le_eval_add hb _ _)
  | .mul a c, v, h => by
    simp only [IExp.eval] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    rename_i x y hx hy
    rw [← h, IExp.workMono, WorkMono.eval_mul]
    exact Nat.mul_le_mul (IExp.eval_le_workMono hσ hb a hx) (IExp.eval_le_workMono hσ hb c hy)
  | .sub a c, v, h => by
    simp only [IExp.eval] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    rename_i x y hx hy
    rw [← h]
    exact (Nat.sub_le x y).trans (IExp.eval_le_workMono hσ hb a hx)
  | .div a c, v, h => by
    simp only [IExp.eval] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    rename_i x y hx hy
    rw [← h]
    exact (Nat.div_le_self x y).trans (IExp.eval_le_workMono hσ hb a hx)

theorem IExp.evalList_le_workMono {idx : List ℕ} {σ : List WorkMono}
    (hσ : SlotsLe bs idx σ) (hb : ∀ b ∈ bs, 1 ≤ b) :
    ∀ (ds : List IExp) {d : List ℕ}, IExp.evalList idx ds = some d →
      SlotsLe bs d (ds.map (IExp.workMono σ))
  | [], d, h => by simp only [IExp.evalList, Option.some.injEq] at h; subst h; exact .nil
  | e :: es, d, h => by
    simp only [IExp.evalList] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    rename_i x xs hx hxs
    subst h
    exact .cons (IExp.eval_le_workMono hσ hb e hx) (IExp.evalList_le_workMono hσ hb es hxs)

/-- The lists of naturals bounded entrywise by `bs`. -/
def boxLists : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | b :: bs => ((Finset.range (b + 1)) ×ˢ boxLists bs).image fun p => p.1 :: p.2

theorem mem_boxLists : ∀ {d bs : List ℕ}, List.Forall₂ (· ≤ ·) d bs → d ∈ boxLists bs
  | _, _, .nil => by simp [boxLists]
  | _, _, .cons (a := x) (b := b) hx h => by
    simp only [boxLists, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    exact ⟨x, _, ⟨by omega, mem_boxLists h⟩, rfl⟩

theorem card_boxLists_le_eval (hb : ∀ b ∈ bs, 1 ≤ b) (σ : List WorkMono) :
    ∀ ds : List IExp, (boxLists (ds.map fun e => (e.workMono σ).eval bs)).card ≤
      (boxWorkMono σ ds).eval bs
  | [] => by simp [boxLists, boxWorkMono]
  | e :: es => by
    simp only [List.map_cons, boxLists, boxWorkMono, WorkMono.eval_mul]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range]
    refine Nat.mul_le_mul ?_ (card_boxLists_le_eval hb σ es)
    simpa using WorkMono.add_eval_le_eval_add hb (e.workMono σ)
      (WorkMono.const 1)

/-- The count with one use of `k` at each list of dimensions of `boxLists bs`. -/
noncomputable def boxCount (k : Op ⊕ Tst) (bs : List ℕ) : Count Op Tst :=
  ∑ d ∈ boxLists bs, Finsupp.single (k, d) 1

theorem size_single (k : (Op ⊕ Tst) × List ℕ) : Count.size (Finsupp.single k 1) = 1 := by
  simp [Count.size, Count.lift_single]

theorem size_boxCount (k : Op ⊕ Tst) (bs : List ℕ) :
    Count.size (boxCount k bs) = (boxLists bs).card := by
  simp [boxCount, map_sum, size_single]

theorem size_mono {c G : Count Op Tst} (h : c ≤ G) : Count.size c ≤ Count.size G := by
  obtain ⟨r, rfl⟩ := exists_add_of_le h
  rw [map_add]; exact Nat.le_add_right _ _

/-- A call site's count at bounded dimensions is dominated by its box count. -/
theorem evalList_map_le_boxCount {k : Op ⊕ Tst} {idx : List ℕ} {σ : List WorkMono}
    (hσ : SlotsLe bs idx σ) (hb : ∀ b ∈ bs, 1 ≤ b) (ds : List IExp) :
    ((IExp.evalList idx ds).map fun d => Finsupp.single (k, d) 1).getD 0 ≤
      boxCount k (ds.map fun e => (e.workMono σ).eval bs) := by
  cases hd : IExp.evalList idx ds with
  | none => exact zero_le
  | some d =>
    have hm : d ∈ boxLists (ds.map fun e => (e.workMono σ).eval bs) := by
      refine mem_boxLists ?_
      have := IExp.evalList_le_workMono hσ hb ds hd
      unfold SlotsLe at this
      rw [List.forall₂_map_right_iff] at this ⊢
      exact this
    exact Finset.single_le_sum (f := fun d => Finsupp.single (k, d) 1)
      (fun _ _ => zero_le) hm

/-- A count of the slot values below `n` dominated by one count `G` is at most `n̂ • G`. -/
theorem sum_range_le_nsmul {N M : ℕ} {f : ℕ → Count Op Tst} {G : Count Op Tst} (hN : N ≤ M)
    (hf : ∀ i < N, f i ≤ G) : ∑ i ∈ Finset.range N, f i ≤ M • G := by
  refine (Finset.sum_le_card_nsmul _ _ G fun i hi => hf i (Finset.mem_range.mp hi)).trans ?_
  rw [Finset.card_range]
  exact nsmul_le_nsmul_left zero_le hN

theorem getD_eval_le_workMono {idx : List ℕ} {σ : List WorkMono}
    (hσ : SlotsLe bs idx σ) (hb : ∀ b ∈ bs, 1 ≤ b) (e : IExp) :
    (e.eval idx).getD 0 ≤ (e.workMono σ).eval bs := by
  cases h : e.eval idx with
  | none => exact Nat.zero_le _
  | some v => exact IExp.eval_le_workMono hσ hb e h

theorem slotsLe_append {idx : List ℕ} {σ : List WorkMono} (hσ : SlotsLe bs idx σ)
    {v : ℕ} {m : WorkMono} (hv : v ≤ m.eval bs) :
    SlotsLe bs (idx ++ [v]) (σ ++ [m]) :=
  List.rel_append hσ (.cons hv .nil)

theorem slotsLe_set {idx : List ℕ} {σ : List WorkMono} (hσ : SlotsLe bs idx σ) {j : ℕ}
    {m : WorkMono} (hv : ∀ v, idx[j]? = some v → v ≤ m.eval bs) :
    SlotsLe bs idx (σ.set j m) := by
  induction hσ generalizing j with
  | nil => exact .nil
  | cons hr _ ih =>
    cases j with
    | zero => exact .cons (hv _ rfl) (by simpa using ‹List.Forall₂ _ _ _›)
    | succ j => exact .cons hr (ih fun v h => hv v (by simpa using h))

/-- The guard of a comparison holds in its body: a count $1 - (1 - (e + 1 - j))$ with a positive
value has $j \le e$. -/
theorem IExp.le_of_guardLe {n e : IExp} {j : ℕ} (hg : n.guardLe = some (e, j)) {idx : List ℕ}
    {i : ℕ} (hi : i < (n.eval idx).getD 0) :
    ∃ a, e.eval idx = some a ∧ ∀ v, idx[j]? = some v → v ≤ a := by
  unfold IExp.guardLe at hg
  split at hg <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hg
  obtain ⟨h1, h2⟩ := hg
  subst e j
  rename_i e j
  cases he : e.eval idx with
  | none => simp [IExp.eval, he] at hi
  | some a =>
    refine ⟨a, rfl, fun v hv => ?_⟩
    simp only [IExp.eval, he, hv, Option.getD_some] at hi
    omega

/-- The slot bounds of a loop body hold at every value of its counter. -/
theorem slotsLe_loopSlots {idx : List ℕ} {σ : List WorkMono} (hσ : SlotsLe bs idx σ)
    (hb : ∀ b ∈ bs, 1 ≤ b) {n : IExp} {i : ℕ} (hi : i < (n.eval idx).getD 0) :
    SlotsLe bs (idx ++ [i]) (loopSlots σ n) := by
  have hn : i ≤ (n.workMono σ).eval bs := by have := getD_eval_le_workMono hσ hb n; omega
  unfold loopSlots
  split
  · rename_i e j hg
    obtain ⟨a, ha, hj⟩ := IExp.le_of_guardLe hg hi
    exact slotsLe_append (slotsLe_set hσ fun v hv =>
      (hj v hv).trans (IExp.eval_le_workMono hσ hb e ha)) hn
  · exact slotsLe_append hσ hn

/-- The bound of a tree: one count, depending only on the bounds of the slots, dominates the
static count at every bounded slot values, and has at most the monomial bound of instructions. -/
abbrev WorkMonoDominates (bs : List ℕ) (s : Stmt Op Tst) (σ : List WorkMono) : Prop :=
  ∃ G : Count Op Tst, Count.size G ≤ (stmtWorkMono s σ).eval bs ∧
    ∀ idx, SlotsLe bs idx σ → stmtCost s idx ≤ G

theorem workMonoDominates_whileFuel (hb : ∀ b ∈ bs, 1 ≤ b) {fuel : IExp}
    {q : Tst} {ds : List IExp} {ins : List Operand} {body k : Stmt Op Tst} {σ : List WorkMono}
    (hB : WorkMonoDominates bs body (σ ++ [fuel.workMono σ]))
    (hK : WorkMonoDominates bs k (σ ++ [fuel.workMono σ])) :
    WorkMonoDominates bs (.whileFuel fuel q ds ins body k) σ := by
  obtain ⟨Gb, hGb, hb'⟩ := hB
  obtain ⟨Gk, hGk, hk'⟩ := hK
  have hadd := WorkMono.add_eval_le_eval_add hb
  refine ⟨(fuel.workMono σ).eval bs • (boxCount (.inr q)
    (ds.map fun e => (e.workMono (σ ++ [fuel.workMono σ])).eval bs) + Gb) + Gk, ?_,
    fun idx hσ => ?_⟩
  · rw [map_add, map_nsmul, map_add, size_boxCount, smul_eq_mul]
    simp only [stmtWorkMono]
    refine le_trans ?_ (hadd _ _)
    rw [WorkMono.eval_mul]
    exact Nat.add_le_add (Nat.mul_le_mul le_rfl
      ((Nat.add_le_add (card_boxLists_le_eval hb _ ds) hGb).trans (hadd _ _))) hGk
  have hF := getD_eval_le_workMono hσ hb fuel
  simp only [stmtCost]
  refine add_le_add (sum_range_le_nsmul hF fun i hi => add_le_add ?_ ?_) ?_
  · exact evalList_map_le_boxCount (slotsLe_append hσ (by omega)) hb ds
  · exact hb' _ (slotsLe_append hσ (by omega))
  · exact Finset.sup_le fun j hj => hk' _ (slotsLe_append hσ (by
      have := Finset.mem_range.mp hj; omega))

/-- The monomial bound dominates the static count: for every tree and monomial bounds of
its slots there is one count, depending only on the bounds, that dominates the static count at
all slot values within the bounds and has at most the monomial bound of instructions. -/
theorem workMonoDominates (hb : ∀ b ∈ bs, 1 ≤ b) :
    ∀ (s : Stmt Op Tst) (σ : List WorkMono), WorkMonoDominates bs s σ
  | .skip, _ => ⟨0, by simp, fun _ _ => le_rfl⟩
  | .abort, _ => ⟨0, by simp, fun _ _ => le_rfl⟩
  | .seq s t, σ => by
    obtain ⟨Gs, hGs, hs⟩ := workMonoDominates hb s σ
    obtain ⟨Gt, hGt, ht⟩ := workMonoDominates hb t σ
    refine ⟨Gs + Gt, ?_, fun idx h => add_le_add (hs idx h) (ht idx h)⟩
    rw [map_add]
    exact (Nat.add_le_add hGs hGt).trans
      (WorkMono.add_eval_le_eval_add hb _ _)
  | .call o ds _ _, σ =>
    ⟨boxCount (.inl o) (ds.map fun e => (e.workMono σ).eval bs),
      by rw [size_boxCount]; exact card_boxLists_le_eval hb σ ds,
      fun _ h => evalList_map_le_boxCount h hb ds⟩
  | .ite q ds _ t e, σ => by
    obtain ⟨Gt, hGt, ht⟩ := workMonoDominates hb t σ
    obtain ⟨Ge, hGe, he⟩ := workMonoDominates hb e σ
    refine ⟨boxCount (.inr q) (ds.map fun e => (e.workMono σ).eval bs) + (Gt + Ge), ?_,
      fun idx h => add_le_add (evalList_map_le_boxCount h hb ds)
        (sup_le (le_add_right (ht idx h)) (le_add_left (he idx h)))⟩
    rw [map_add, map_add, size_boxCount]
    have hadd := WorkMono.add_eval_le_eval_add hb
    exact (Nat.add_le_add (card_boxLists_le_eval hb σ ds)
      ((Nat.add_le_add hGt hGe).trans (hadd _ _))).trans (hadd _ _)
  | .whileFuel fuel q ds ins body k, σ =>
    workMonoDominates_whileFuel hb (workMonoDominates hb body _) (workMonoDominates hb k _)
  | .bindIdx q _ bound body, σ => by
    obtain ⟨Gb, hGb, hb'⟩ := workMonoDominates hb body (σ ++ [bound.workMono σ])
    refine ⟨Count.test q [] + Gb, ?_, fun idx h => add_le_add le_rfl
      (Finset.sup_le fun v hv => hb' _ (slotsLe_append h (by
        have := Finset.mem_range.mp hv
        have := getD_eval_le_workMono h hb bound
        omega)))⟩
    rw [map_add, Count.test, size_single]
    simp only [stmtWorkMono]
    have h1 := WorkMono.add_eval_le_eval_add hb (WorkMono.const 1)
      (stmtWorkMono body (σ ++ [bound.workMono σ]))
    rw [WorkMono.eval_const] at h1
    exact (Nat.add_le_add_left hGb 1).trans h1
  | .allocAs _ _ body, σ => workMonoDominates hb body σ
  | .loop n body, σ => by
    obtain ⟨Gb, hGb, hb'⟩ := workMonoDominates hb body (loopSlots σ n)
    refine ⟨(n.workMono σ).eval bs • Gb, ?_, fun idx h =>
      sum_range_le_nsmul (getD_eval_le_workMono h hb n) fun i hi =>
        hb' _ (slotsLe_loopSlots h hb hi)⟩
    rw [map_nsmul, smul_eq_mul]
    simp only [stmtWorkMono]
    rw [WorkMono.eval_mul]
    exact Nat.mul_le_mul le_rfl hGb
  | .frame ds args body, σ => by
    obtain ⟨G, hG, hg⟩ := workMonoDominates hb body
      (ds.map (IExp.workMono σ) ++ (args.map Operand.off).map (IExp.workMono σ))
    refine ⟨G, hG, fun idx h => ?_⟩
    simp only [stmtCost]
    split
    · rename_i d o hd ho
      exact hg _ (List.rel_append (IExp.evalList_le_workMono h hb ds hd)
        (IExp.evalList_le_workMono h hb _ ho))
    · exact zero_le
  | .note _ s, σ => workMonoDominates hb s σ

/-- The number of instructions of the static count is at most the monomial bound: at bases
at least $1$ and slot values bounded by the monomials `σ`,
`Count.size (stmtCost s idx) ≤ (stmtWorkMono s σ).eval b₀ b₁ b₂ b₃`. No printed source. -/
theorem size_stmtCost_le_stmtWorkMono (hb : ∀ b ∈ bs, 1 ≤ b)
    (s : Stmt Op Tst) {σ : List WorkMono} {idx : List ℕ} (hσ : SlotsLe bs idx σ) :
    Count.size (stmtCost s idx) ≤ (stmtWorkMono s σ).eval bs := by
  obtain ⟨G, hG, hg⟩ := workMonoDominates hb s σ
  exact (size_mono (hg idx hσ)).trans hG

end Soundness


/-- The instructions of a supremum of counts and of their infimum add up to those of the two
counts. -/
theorem size_sup_add_size_inf {Op Tst : Type} (x y : Count Op Tst) :
    Count.size (x ⊔ y) + Count.size (x ⊓ y) = Count.size x + Count.size y := by
  rw [← map_add, ← map_add]
  congr 1
  ext a
  simp [Finsupp.sup_apply, Finsupp.inf_apply, max_add_min]

end NLAlib.Ops
