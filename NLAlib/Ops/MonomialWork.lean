/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Ring
public import NLAlib.Ops.Confined
public meta import Lean.Elab.Tactic.Basic

/-!
# Monomial bounds on the number of instructions of a program

A syntactic bound on `NLAlib.Ops.Count.size` of the static count `NLAlib.Ops.stmtCost`, as a
monomial $c\,b_0^{e_0}b_1^{e_1}b_2^{e_2}b_3^{e_3}$ in four bases, computed from the tree alone
(`NLAlib.Ops.stmtWorkMono`): every index slot carries a monomial bound on its value, a loop or a
`whileFuel` multiplies by the bound of its count, and a sum takes the larger exponents. A call
site contributes one instruction for each list of dimensions its bounds allow, counted once: the
static count takes a pointwise supremum over the branches of an `ite`, the values of a `bindIdx`
and the exits of a `whileFuel`, so the bound needs one count that dominates them all, and one
exists that depends only on the bounds of the slots. The bound of a fixed program is evaluated
by `kernel_rfl`, an equation by reflexivity left to the kernel (which evaluates it with sharing,
where the elaborator's `rfl` does not). It keeps each base with its own exponent, unlike the
one-base estimate `NLAlib.Ops.stmtWeightedCost_le_coefficient_mul_pow`. The number of bases is
fixed at four; a version over a list of bases would serve programs with other numbers of sizes.

## Main definitions

* `NLAlib.Ops.WorkMono`: a monomial in four bases.
* `NLAlib.Ops.stmtWorkMono`: the monomial bound of a tree at monomial bounds of its slots.

## Main results

* `NLAlib.Ops.size_stmtCost_le_stmtWorkMono`: the number of instructions of the static count is
  at most the monomial bound.
* `kernel_rfl`: an equation closed by reflexivity, checked by the kernel only.
-/

@[expose] public section

namespace NLAlib.Ops

/-- **A monomial in four bases**: $c\,b_0^{e_0}b_1^{e_1}b_2^{e_2}b_3^{e_3}$. -/
structure WorkMono where
  /-- The coefficient. -/
  c : ℕ
  /-- The exponent of the first base. -/
  e0 : ℕ
  /-- The exponent of the second base. -/
  e1 : ℕ
  /-- The exponent of the third base. -/
  e2 : ℕ
  /-- The exponent of the fourth base. -/
  e3 : ℕ
  deriving DecidableEq, Repr

namespace WorkMono

/-- The constant monomial $n$. -/
def const (n : ℕ) : WorkMono := ⟨n, 0, 0, 0, 0⟩

/-- A monomial bounding a sum: the coefficients add, the exponents take the larger value. -/
def add (x y : WorkMono) : WorkMono :=
  ⟨x.c + y.c, max x.e0 y.e0, max x.e1 y.e1, max x.e2 y.e2, max x.e3 y.e3⟩

/-- The product of two monomials. -/
def mul (x y : WorkMono) : WorkMono :=
  ⟨x.c * y.c, x.e0 + y.e0, x.e1 + y.e1, x.e2 + y.e2, x.e3 + y.e3⟩

/-- The value of a monomial at the bases $b_0, b_1, b_2, b_3$. -/
def eval (x : WorkMono) (b0 b1 b2 b3 : ℕ) : ℕ :=
  x.c * b0 ^ x.e0 * b1 ^ x.e1 * b2 ^ x.e2 * b3 ^ x.e3

variable {b0 b1 b2 b3 : ℕ}

@[simp] theorem eval_const (n : ℕ) : (const n).eval b0 b1 b2 b3 = n := by simp [const, eval]

theorem eval_mul (x y : WorkMono) :
    (x.mul y).eval b0 b1 b2 b3 = x.eval b0 b1 b2 b3 * y.eval b0 b1 b2 b3 := by
  simp only [mul, eval, pow_add]; ring

/-- At bases at least $1$, raising the exponents raises the value. -/
theorem eval_le_of_le (h0 : 1 ≤ b0) (h1 : 1 ≤ b1) (h2 : 1 ≤ b2) (h3 : 1 ≤ b3) {c : ℕ}
    {e0 e1 e2 e3 f0 f1 f2 f3 : ℕ} (g0 : e0 ≤ f0) (g1 : e1 ≤ f1) (g2 : e2 ≤ f2) (g3 : e3 ≤ f3) :
    eval ⟨c, e0, e1, e2, e3⟩ b0 b1 b2 b3 ≤ eval ⟨c, f0, f1, f2, f3⟩ b0 b1 b2 b3 := by
  simp only [eval]
  gcongr

theorem add_eval_le_eval_add (h0 : 1 ≤ b0) (h1 : 1 ≤ b1) (h2 : 1 ≤ b2) (h3 : 1 ≤ b3)
    (x y : WorkMono) :
    x.eval b0 b1 b2 b3 + y.eval b0 b1 b2 b3 ≤ (x.add y).eval b0 b1 b2 b3 := by
  have hx := eval_le_of_le h0 h1 h2 h3 (c := x.c) (le_max_left x.e0 y.e0)
    (le_max_left x.e1 y.e1) (le_max_left x.e2 y.e2) (le_max_left x.e3 y.e3)
  have hy := eval_le_of_le h0 h1 h2 h3 (c := y.c) (le_max_right x.e0 y.e0)
    (le_max_right x.e1 y.e1) (le_max_right x.e2 y.e2) (le_max_right x.e3 y.e3)
  calc x.eval b0 b1 b2 b3 + y.eval b0 b1 b2 b3 ≤ _ + _ := Nat.add_le_add hx hy
    _ = (x.add y).eval b0 b1 b2 b3 := by simp only [add, eval]; ring

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

/-- The monomial bound of the number of lists of dimensions a call site allows:
$\prod_i (\hat d_i + 1)$. -/
def boxWorkMono (σ : List WorkMono) : List IExp → WorkMono
  | [] => WorkMono.const 1
  | e :: es => ((e.workMono σ).add (WorkMono.const 1)).mul (boxWorkMono σ es)

variable {Op Tst : Type}

/-- **The monomial bound of a tree** at monomial bounds `σ` of its slots: a call or a test counts
the lists of dimensions it allows, a branch both sides, a loop and a `whileFuel` multiply by the
bound of their count, a `bindIdx` binds its slot to the bound of its value, and a frame evaluates
its dimensions and offsets. -/
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
  | .loop n body, σ => (n.workMono σ).mul (stmtWorkMono body (σ ++ [n.workMono σ]))
  | .frame ds args body, σ =>
      stmtWorkMono body (ds.map (IExp.workMono σ) ++ (args.map Operand.off).map (IExp.workMono σ))

/-! ### Soundness -/

section Soundness

variable {b0 b1 b2 b3 : ℕ}

/-- The values `idx` are bounded by the monomials `σ` at the bases. -/
abbrev SlotsLe (b0 b1 b2 b3 : ℕ) (idx : List ℕ) (σ : List WorkMono) : Prop :=
  List.Forall₂ (fun v m => v ≤ WorkMono.eval m b0 b1 b2 b3) idx σ

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
    (hσ : SlotsLe b0 b1 b2 b3 idx σ) (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) :
    ∀ (e : IExp) {v : ℕ}, e.eval idx = some v → v ≤ (e.workMono σ).eval b0 b1 b2 b3
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
      (WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 _ _)
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
    (hσ : SlotsLe b0 b1 b2 b3 idx σ) (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) :
    ∀ (ds : List IExp) {d : List ℕ}, IExp.evalList idx ds = some d →
      SlotsLe b0 b1 b2 b3 d (ds.map (IExp.workMono σ))
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

theorem card_boxLists_le_eval (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) (σ : List WorkMono) :
    ∀ ds : List IExp, (boxLists (ds.map fun e => (e.workMono σ).eval b0 b1 b2 b3)).card ≤
      (boxWorkMono σ ds).eval b0 b1 b2 b3
  | [] => by simp [boxLists, boxWorkMono]
  | e :: es => by
    simp only [List.map_cons, boxLists, boxWorkMono, WorkMono.eval_mul]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range]
    refine Nat.mul_le_mul ?_ (card_boxLists_le_eval hb σ es)
    simpa using WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (e.workMono σ)
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
    (hσ : SlotsLe b0 b1 b2 b3 idx σ) (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) (ds : List IExp) :
    ((IExp.evalList idx ds).map fun d => Finsupp.single (k, d) 1).getD 0 ≤
      boxCount k (ds.map fun e => (e.workMono σ).eval b0 b1 b2 b3) := by
  cases hd : IExp.evalList idx ds with
  | none => exact zero_le
  | some d =>
    have hm : d ∈ boxLists (ds.map fun e => (e.workMono σ).eval b0 b1 b2 b3) := by
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
    (hσ : SlotsLe b0 b1 b2 b3 idx σ) (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) (e : IExp) :
    (e.eval idx).getD 0 ≤ (e.workMono σ).eval b0 b1 b2 b3 := by
  cases h : e.eval idx with
  | none => exact Nat.zero_le _
  | some v => exact IExp.eval_le_workMono hσ hb e h

theorem slotsLe_append {idx : List ℕ} {σ : List WorkMono} (hσ : SlotsLe b0 b1 b2 b3 idx σ)
    {v : ℕ} {m : WorkMono} (hv : v ≤ m.eval b0 b1 b2 b3) :
    SlotsLe b0 b1 b2 b3 (idx ++ [v]) (σ ++ [m]) :=
  List.rel_append hσ (.cons hv .nil)

/-- The bound of a tree: one count, depending only on the bounds of the slots, dominates the
static count at every bounded slot values, and has at most the monomial bound of instructions. -/
abbrev WorkMonoDominates (b0 b1 b2 b3 : ℕ) (s : Stmt Op Tst) (σ : List WorkMono) : Prop :=
  ∃ G : Count Op Tst, Count.size G ≤ (stmtWorkMono s σ).eval b0 b1 b2 b3 ∧
    ∀ idx, SlotsLe b0 b1 b2 b3 idx σ → stmtCost s idx ≤ G

theorem workMonoDominates_whileFuel (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) {fuel : IExp}
    {q : Tst} {ds : List IExp} {ins : List Operand} {body k : Stmt Op Tst} {σ : List WorkMono}
    (hB : WorkMonoDominates b0 b1 b2 b3 body (σ ++ [fuel.workMono σ]))
    (hK : WorkMonoDominates b0 b1 b2 b3 k (σ ++ [fuel.workMono σ])) :
    WorkMonoDominates b0 b1 b2 b3 (.whileFuel fuel q ds ins body k) σ := by
  obtain ⟨Gb, hGb, hb'⟩ := hB
  obtain ⟨Gk, hGk, hk'⟩ := hK
  have hadd := WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  refine ⟨(fuel.workMono σ).eval b0 b1 b2 b3 • (boxCount (.inr q)
    (ds.map fun e => (e.workMono (σ ++ [fuel.workMono σ])).eval b0 b1 b2 b3) + Gb) + Gk, ?_,
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
theorem workMonoDominates (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3) :
    ∀ (s : Stmt Op Tst) (σ : List WorkMono), WorkMonoDominates b0 b1 b2 b3 s σ
  | .skip, _ => ⟨0, by simp, fun _ _ => le_rfl⟩
  | .abort, _ => ⟨0, by simp, fun _ _ => le_rfl⟩
  | .seq s t, σ => by
    obtain ⟨Gs, hGs, hs⟩ := workMonoDominates hb s σ
    obtain ⟨Gt, hGt, ht⟩ := workMonoDominates hb t σ
    refine ⟨Gs + Gt, ?_, fun idx h => add_le_add (hs idx h) (ht idx h)⟩
    rw [map_add]
    exact (Nat.add_le_add hGs hGt).trans
      (WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 _ _)
  | .call o ds _ _, σ =>
    ⟨boxCount (.inl o) (ds.map fun e => (e.workMono σ).eval b0 b1 b2 b3),
      by rw [size_boxCount]; exact card_boxLists_le_eval hb σ ds,
      fun _ h => evalList_map_le_boxCount h hb ds⟩
  | .ite q ds _ t e, σ => by
    obtain ⟨Gt, hGt, ht⟩ := workMonoDominates hb t σ
    obtain ⟨Ge, hGe, he⟩ := workMonoDominates hb e σ
    refine ⟨boxCount (.inr q) (ds.map fun e => (e.workMono σ).eval b0 b1 b2 b3) + (Gt + Ge), ?_,
      fun idx h => add_le_add (evalList_map_le_boxCount h hb ds)
        (sup_le (le_add_right (ht idx h)) (le_add_left (he idx h)))⟩
    rw [map_add, map_add, size_boxCount]
    have hadd := WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
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
    have h1 := (Nat.add_le_add_left hGb 1).trans
      (WorkMono.add_eval_le_eval_add hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (WorkMono.const 1) _)
    simpa using h1
  | .allocAs _ _ body, σ => workMonoDominates hb body σ
  | .loop n body, σ => by
    obtain ⟨Gb, hGb, hb'⟩ := workMonoDominates hb body (σ ++ [n.workMono σ])
    refine ⟨(n.workMono σ).eval b0 b1 b2 b3 • Gb, ?_, fun idx h =>
      sum_range_le_nsmul (getD_eval_le_workMono h hb n) fun i hi =>
        hb' _ (slotsLe_append h (by have := getD_eval_le_workMono h hb n; omega))⟩
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

/-- The number of instructions of the static count is at most the monomial bound: at bases
at least $1$ and slot values bounded by the monomials `σ`,
`Count.size (stmtCost s idx) ≤ (stmtWorkMono s σ).eval b₀ b₁ b₂ b₃`. No printed source. -/
theorem size_stmtCost_le_stmtWorkMono (hb : 1 ≤ b0 ∧ 1 ≤ b1 ∧ 1 ≤ b2 ∧ 1 ≤ b3)
    (s : Stmt Op Tst) {σ : List WorkMono} {idx : List ℕ} (hσ : SlotsLe b0 b1 b2 b3 idx σ) :
    Count.size (stmtCost s idx) ≤ (stmtWorkMono s σ).eval b0 b1 b2 b3 := by
  obtain ⟨G, hG, hg⟩ := workMonoDominates hb s σ
  exact (size_mono (hg idx hσ)).trans hG

end Soundness

open Lean Elab Tactic Meta in
/-- **`kernel_rfl`**: close an equation `a = b` by `Eq.refl a` without the elaborator's
definitional check; the kernel checks it when the declaration is added (and fails it there if
`a` and `b` are not definitionally equal). For closed computations, such as the monomial bound
of a fixed program, that the kernel evaluates with sharing. -/
elab (name := kernelRfl) "kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "kernel_rfl: not an equation"
  g.assign (← mkEqRefl a)
  replaceMainGoal []

end NLAlib.Ops
