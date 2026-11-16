/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import NLAlib.Ops.WeightedCost
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring

/-!
# An explicit polynomial for the number of instructions of a program

The static count of a program (`NLAlib.Ops.staticCost`) is a sum over the loops of its tree. This
file computes from the tree a polynomial in the sizes, one variable per size, that bounds the
number of instructions of every run: primitives, queries and structural instructions alike.
Under a model whose weights are all at most one, that number bounds the work.

A polynomial is a list of terms, a coefficient and the list of its variables with multiplicity
(`NLAlib.Ops.CountPoly`). The polynomial of a tree is computed by a structural recursion with no
proof inside, so the kernel evaluates it on a fixed program and the result is an explicit list.
A loop multiplies the polynomial of its body by an upper bound of its number of rounds; a branch
adds its two sides; a truncated difference and a quotient are bounded by their first argument.

## Main results

* `NLAlib.Ops.stmtWeightedCost_le_countPoly`: the weighted static cost of a tree is at most its
  polynomial, when every weight is at most one.
* `NLAlib.Ops.Program.exec_work_le_countPoly`: the work of a canonical run is at most the
  polynomial of the instrumented program at its sizes.
* `NLAlib.Ops.Program.exec_weight_le_countPoly`: the same for any weights at most one, which
  need not be those of the run.
* `NLAlib.Ops.Algorithm.withCountPoly`: a certificate restated with that explicit work.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A polynomial with natural coefficients in the variables `x₀, x₁, …`: a list of terms, each a
coefficient and the list of the indices of its variables, with multiplicity. -/
abbrev CountPoly := List (ℕ × List ℕ)

namespace CountPoly

/-- The value of a monomial at the point `x`; a variable beyond `x` is zero. -/
def monoEval (x : List ℕ) (m : List ℕ) : ℕ := (m.map fun i => x.getD i 0).prod

/-- The value of a polynomial at the point `x`. -/
def eval (x : List ℕ) (p : CountPoly) : ℕ := (p.map fun t => t.1 * monoEval x t.2).sum

/-- The constant polynomial. -/
def const (c : ℕ) : CountPoly := [(c, [])]

/-- The variable `xᵢ`. -/
def var (i : ℕ) : CountPoly := [(1, [i])]

/-- The sum of two polynomials. -/
def add (p q : CountPoly) : CountPoly := p ++ q

/-- The product of two polynomials. -/
def mul (p q : CountPoly) : CountPoly :=
  p.flatMap fun s => q.map fun t => (s.1 * t.1, s.2 ++ t.2)

/-- Add a term to a polynomial, merging it with a term of the same monomial. -/
def insert (t : ℕ × List ℕ) : CountPoly → CountPoly
  | [] => [t]
  | s :: p => if s.2 = t.2 then (s.1 + t.1, s.2) :: p else s :: insert t p

/-- Insert a variable into a sorted monomial. -/
def sortedInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: m => if a ≤ b then a :: b :: m else b :: sortedInsert a m

/-- Sort the variables of a monomial. The kernel unfolds this definition on a fixed program. -/
def sortMono (m : List ℕ) : List ℕ := m.foldr sortedInsert []

/-- The normal form: the variables of each monomial sorted, equal monomials merged. -/
def normalize (p : CountPoly) : CountPoly :=
  (p.map fun t => (t.1, sortMono t.2)).foldr insert []

@[simp] theorem eval_nil (x : List ℕ) : eval x [] = 0 := rfl

@[simp] theorem eval_cons (x : List ℕ) (t : ℕ × List ℕ) (p : CountPoly) :
    eval x (t :: p) = t.1 * monoEval x t.2 + eval x p := rfl

@[simp] theorem eval_const (x : List ℕ) (c : ℕ) : eval x (const c) = c := by
  simp [const, monoEval]

@[simp] theorem eval_var (x : List ℕ) (i : ℕ) : eval x (var i) = x.getD i 0 := by
  simp [var, monoEval]

@[simp] theorem eval_add (x : List ℕ) (p q : CountPoly) :
    eval x (add p q) = eval x p + eval x q := by
  simp [eval, add]

theorem monoEval_append (x : List ℕ) (m m' : List ℕ) :
    monoEval x (m ++ m') = monoEval x m * monoEval x m' := by
  simp [monoEval]

theorem eval_map_mul (x : List ℕ) (s : ℕ × List ℕ) (q : CountPoly) :
    eval x (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) = s.1 * monoEval x s.2 * eval x q := by
  induction q with
  | nil => simp
  | cons t q ih =>
    rw [List.map_cons, eval_cons, eval_cons, ih, monoEval_append]
    ring

@[simp] theorem eval_mul (x : List ℕ) (p q : CountPoly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul]
  | cons s p ih =>
    have hmul : mul (s :: p) q = add (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) (mul p q) := by
      simp [mul, add]
    rw [hmul, eval_add, eval_map_mul, ih, eval_cons]
    ring

theorem eval_insert (x : List ℕ) (t : ℕ × List ℕ) (p : CountPoly) :
    eval x (insert t p) = t.1 * monoEval x t.2 + eval x p := by
  induction p with
  | nil => simp [insert]
  | cons s p ih =>
    by_cases h : s.2 = t.2
    · rw [insert, if_pos h, eval_cons, eval_cons, h]
      ring
    · rw [insert, if_neg h, eval_cons, ih, eval_cons]
      ring

theorem monoEval_sortedInsert (x : List ℕ) (a : ℕ) (m : List ℕ) :
    monoEval x (sortedInsert a m) = x.getD a 0 * monoEval x m := by
  induction m with
  | nil => rfl
  | cons b m ih =>
    by_cases h : a ≤ b
    · simp [sortedInsert, h, monoEval]
    · have hb : monoEval x (b :: sortedInsert a m) =
          x.getD b 0 * monoEval x (sortedInsert a m) := by
        simp [monoEval]
      have hc : monoEval x (b :: m) = x.getD b 0 * monoEval x m := by simp [monoEval]
      rw [sortedInsert, if_neg h, hb, ih, hc]
      ring

theorem monoEval_sortMono (x : List ℕ) (m : List ℕ) : monoEval x (sortMono m) = monoEval x m := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    have h : sortMono (a :: m) = sortedInsert a (sortMono m) := rfl
    rw [h, monoEval_sortedInsert, ih]
    simp [monoEval]

@[simp] theorem eval_normalize (x : List ℕ) (p : CountPoly) : eval x (normalize p) = eval x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    have h : normalize (t :: p) = insert (t.1, sortMono t.2) (normalize p) := rfl
    rw [h, eval_insert, ih, monoEval_sortMono, eval_cons]

end CountPoly

/-- An upper bound of an index expression, as a polynomial in the sizes: each index variable is
replaced by its bound in `env`, a truncated difference and a quotient by their first argument. -/
def IExp.upper (env : List CountPoly) : IExp → CountPoly
  | .var i => env.getD i []
  | .const n => CountPoly.const n
  | .add a b => (a.upper env).add (b.upper env)
  | .mul a b => (a.upper env).mul (b.upper env)
  | .sub a _ => a.upper env
  | .div a _ => a.upper env

/-- The values `idx` of the index variables are at most their bounds `env` at the sizes `x`. -/
abbrev BoundedBy (x : List ℕ) (idx : List ℕ) (env : List CountPoly) : Prop :=
  List.Forall₂ (fun v p => v ≤ CountPoly.eval x p) idx env

theorem BoundedBy.getElem? {x idx : List ℕ} {env : List CountPoly} (h : BoundedBy x idx env)
    {i v : ℕ} (hv : idx[i]? = some v) : v ≤ CountPoly.eval x (env.getD i []) := by
  induction h generalizing i with
  | nil => simp at hv
  | @cons a p idx env hap _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      simpa using hap
    | succ i => simpa using ih (by simpa using hv)

/-- The value of an index expression is at most its upper bound. -/
theorem IExp.eval_le_upper {x idx : List ℕ} {env : List CountPoly} (h : BoundedBy x idx env)
    {e : IExp} {v : ℕ} (he : e.eval idx = some v) : v ≤ CountPoly.eval x (e.upper env) := by
  induction e generalizing v with
  | var i => exact h.getElem? he
  | const n =>
    cases he
    simp [IExp.upper]
  | add a b iha ihb =>
    rw [show (IExp.add a b) = a + b from rfl, IExp.eval_add] at he
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp he
    simpa [IExp.upper] using Nat.add_le_add (iha hu) (ihb hw)
  | mul a b iha ihb =>
    rw [show (IExp.mul a b) = a * b from rfl, IExp.eval_mul] at he
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp he
    simpa [IExp.upper] using Nat.mul_le_mul (iha hu) (ihb hw)
  | sub a b iha _ =>
    rw [show (IExp.sub a b) = a - b from rfl, IExp.eval_sub] at he
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp he
    exact (Nat.sub_le u w).trans (iha hu)
  | div a b iha _ =>
    rw [show (IExp.div a b) = a / b from rfl, IExp.eval_div] at he
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp he
    exact (Nat.div_le_self u w).trans (iha hu)

/-- The values of a list of index expressions are at most their upper bounds. -/
theorem IExp.evalList_le_upper {x idx : List ℕ} {env : List CountPoly} (h : BoundedBy x idx env)
    {es : List IExp} {vs : List ℕ} (he : IExp.evalList idx es = some vs) :
    BoundedBy x vs (es.map (IExp.upper env)) := by
  induction es generalizing vs with
  | nil =>
    cases he
    exact .nil
  | cons e es ih =>
    rw [IExp.evalList_cons] at he
    obtain ⟨v, hv, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp he
    exact .cons (IExp.eval_le_upper h hv) (ih hws)

variable {Op Tst : Type}

/-- **The instruction polynomial of a tree**, given bounds `env` of its index variables as
polynomials in the sizes. A call and a query count one; a loop multiplies its body by the bound
of its number of rounds; a branch adds its two sides. -/
def Stmt.countPoly : Stmt Op Tst → List CountPoly → CountPoly
  | .skip, _ | .abort, _ => []
  | .call _ _ _ _, _ => CountPoly.const 1
  | .seq s t, env => ((s.countPoly env).add (t.countPoly env)).normalize
  | .ite _ _ _ s t, env =>
      ((CountPoly.const 1).add ((s.countPoly env).add (t.countPoly env))).normalize
  | .whileFuel fuel _ _ _ s k, env =>
      let rounds := (fuel.upper env).normalize
      ((rounds.mul ((CountPoly.const 1).add (s.countPoly (env ++ [rounds])))).add
        (k.countPoly (env ++ [rounds]))).normalize
  | .bindIdx _ _ bound s, env =>
      ((CountPoly.const 1).add (s.countPoly (env ++ [(bound.upper env).normalize]))).normalize
  | .allocAs _ _ s, env => s.countPoly env
  | .loop n s, env =>
      let rounds := (n.upper env).normalize
      (rounds.mul (s.countPoly (env ++ [rounds]))).normalize
  | .frame ds args s, env =>
      s.countPoly (ds.map (fun e => (e.upper env).normalize) ++
        args.map (fun a => (a.off.upper env).normalize))

private theorem boundedBy_push {x idx : List ℕ} {env : List CountPoly} (h : BoundedBy x idx env)
    {v : ℕ} {p : CountPoly} (hv : v ≤ CountPoly.eval x p) :
    BoundedBy x (idx ++ [v]) (env ++ [p]) :=
  List.rel_append h (.cons hv .nil)

private theorem getD_le_one {α : Type} {f : α → List ℕ → ℕ} (hf : ∀ a d, f a d ≤ 1) (a : α)
    (o : Option (List ℕ)) : (o.map (f a)).getD 0 ≤ 1 := by
  cases o with
  | none => exact Nat.zero_le _
  | some d => exact hf a d

private theorem boundedBy_normalize {x vs : List ℕ} {ps : List CountPoly}
    (h : BoundedBy x vs ps) : BoundedBy x vs (ps.map CountPoly.normalize) := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (by simpa using hv) ih

/-- The weighted static cost of a tree is at most its instruction polynomial, when every
primitive and query weight is at most one and the index variables are within their bounds. -/
theorem stmtWeightedCost_le_countPoly {op : Op → List ℕ → ℕ} {query : Tst → List ℕ → ℕ}
    (hop : ∀ o d, op o d ≤ 1) (hq : ∀ q d, query q d ≤ 1) (s : Stmt Op Tst) {x idx : List ℕ}
    {env : List CountPoly} (h : BoundedBy x idx env) :
    stmtWeightedCost op query s idx ≤ CountPoly.eval x (s.countPoly env) := by
  induction s generalizing idx env with
  | skip => exact Nat.zero_le _
  | abort => exact Nat.zero_le _
  | call o ds ins outs => simpa [Stmt.countPoly, stmtWeightedCost] using getD_le_one hop o _
  | seq s t ihs iht =>
    simpa [Stmt.countPoly, stmtWeightedCost] using Nat.add_le_add (ihs h) (iht h)
  | ite q ds ins s t ihs iht =>
    have h1 := getD_le_one hq q (IExp.evalList idx ds)
    have h2 := ihs h
    have h3 := iht h
    simp only [Stmt.countPoly, stmtWeightedCost, CountPoly.eval_normalize, CountPoly.eval_add,
      CountPoly.eval_const]
    omega
  | whileFuel fuel q ds ins s k ihs ihk =>
    have hfuel : (fuel.eval idx).getD 0 ≤ CountPoly.eval x (fuel.upper env).normalize := by
      cases hn : fuel.eval idx with
      | none => exact Nat.zero_le _
      | some v => simpa using IExp.eval_le_upper h hn
    have hpush : ∀ i ≤ (fuel.eval idx).getD 0,
        BoundedBy x (idx ++ [i]) (env ++ [(fuel.upper env).normalize]) :=
      fun i hi => boundedBy_push h (hi.trans hfuel)
    have hsum : (∑ i ∈ Finset.range ((fuel.eval idx).getD 0),
        (((IExp.evalList (idx ++ [i]) ds).map (query q)).getD 0 +
          stmtWeightedCost op query s (idx ++ [i]))) ≤ (fuel.eval idx).getD 0 *
          (1 + CountPoly.eval x (s.countPoly (env ++ [(fuel.upper env).normalize]))) := by
      refine (Finset.sum_le_sum fun i hi => ?_).trans_eq
        (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul])
      exact Nat.add_le_add (getD_le_one hq q _)
        (ihs (hpush i (Nat.le_of_lt (Finset.mem_range.mp hi))))
    have hsup : ((Finset.range ((fuel.eval idx).getD 0 + 1)).sup fun j =>
        stmtWeightedCost op query k (idx ++ [j])) ≤
        CountPoly.eval x (k.countPoly (env ++ [(fuel.upper env).normalize])) :=
      Finset.sup_le fun j hj => ihk (hpush j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    simp only [Stmt.countPoly, stmtWeightedCost, CountPoly.eval_normalize, CountPoly.eval_add,
      CountPoly.eval_mul, CountPoly.eval_const]
    exact Nat.add_le_add (hsum.trans (Nat.mul_le_mul_right _ (by simpa using hfuel))) hsup
  | bindIdx q ins bound s ih =>
    have hbound : (bound.eval idx).getD 0 ≤ CountPoly.eval x (bound.upper env).normalize := by
      cases hn : bound.eval idx with
      | none => exact Nat.zero_le _
      | some v => simpa using IExp.eval_le_upper h hn
    have hsup : ((Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v =>
        stmtWeightedCost op query s (idx ++ [v])) ≤
        CountPoly.eval x (s.countPoly (env ++ [(bound.upper env).normalize])) :=
      Finset.sup_le fun v hv => ih (boundedBy_push h
        ((Nat.le_of_lt_succ (Finset.mem_range.mp hv)).trans hbound))
    simp only [Stmt.countPoly, stmtWeightedCost, CountPoly.eval_normalize, CountPoly.eval_add,
      CountPoly.eval_const]
    exact Nat.add_le_add (hq q []) hsup
  | allocAs fmt len s ih => exact ih h
  | loop n s ih =>
    have hn : (n.eval idx).getD 0 ≤ CountPoly.eval x (n.upper env).normalize := by
      cases hv : n.eval idx with
      | none => exact Nat.zero_le _
      | some v => simpa using IExp.eval_le_upper h hv
    have hsum : (∑ i ∈ Finset.range ((n.eval idx).getD 0),
        stmtWeightedCost op query s (idx ++ [i])) ≤ (n.eval idx).getD 0 *
          CountPoly.eval x (s.countPoly (env ++ [(n.upper env).normalize])) := by
      refine (Finset.sum_le_sum fun i hi => ?_).trans_eq
        (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul])
      exact ih (boundedBy_push h ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hn))
    simp only [Stmt.countPoly, stmtWeightedCost, CountPoly.eval_normalize, CountPoly.eval_mul]
    exact hsum.trans (Nat.mul_le_mul_right _ (by simpa using hn))
  | frame ds args s ih =>
    simp only [stmtWeightedCost, Stmt.countPoly]
    cases hd : IExp.evalList idx ds <;> cases ho : IExp.evalList idx (args.map Operand.off)
    all_goals try exact Nat.zero_le _
    refine ih ?_
    have h1 := boundedBy_normalize (IExp.evalList_le_upper h hd)
    have h2 := boundedBy_normalize (IExp.evalList_le_upper h ho)
    simpa only [List.map_map, Function.comp_def] using List.rel_append h1 h2

/-- The bounds of the index variables of a program at its start: each size is a variable, each
initial offset is zero. -/
def Program.sizeBounds (r b : ℕ) : List CountPoly :=
  (List.range r).map CountPoly.var ++ List.replicate b []

/-- The sizes of a program are within their own bounds. -/
theorem Program.boundedBy_sizeBounds {r b : ℕ} (d : Fin r → ℕ) :
    BoundedBy (List.ofFn d) (Program.environment (b := b) d).idx (Program.sizeBounds r b) := by
  refine List.rel_append ?_ ?_
  · refine List.forall₂_iff_get.mpr ⟨by simp, fun i h1 h2 => ?_⟩
    have hi : i < r := by simpa using h1
    simp [List.getD_eq_getElem?_getD, hi]
  · refine List.forall₂_iff_get.mpr ⟨by simp, fun i h1 h2 => ?_⟩
    simp

/-- **The instruction polynomial of a program**: the polynomial of its instrumented tree, in
the sizes. Every primitive, query and structural instruction of a canonical run is counted. -/
def Program.countPoly {r b : ℕ} (p : Program Op Tst r b) : CountPoly :=
  p.body.instrument.countPoly (Program.sizeBounds r b)

/-- The weight of a canonical run under any weights that are at most one is at most the
instruction polynomial of the program at its sizes. The weights `R'` need not be those `R` of the
run: a count is weighed after the fact, for instance with the weight of some primitives set to
zero. -/
theorem Program.exec_weight_le_countPoly {K : Type} {r b : ℕ} (p : Program Op Tst r b)
    (R R' : ResourceModel Op Tst) (hop : ∀ o d, R'.operationWork o d ≤ 1)
    (hcore : ∀ k d, R'.coreWork k d ≤ 1) (hq : ∀ q d, R'.queryWork q d ≤ 1)
    {I : Interp Op Tst K} {τ : Tape K} {formats : Fin b → StorageFormat} {d : Fin r → ℕ}
    {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (hr : exec p I R formats τ d m = some st) :
    R'.work st.cost ≤ CountPoly.eval (List.ofFn d) p.countPoly := by
  unfold exec at hr
  split_ifs at hr with ht
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hcost := evalCounted_weight_le (Sum.elim R'.operationWork R'.coreWork) R'.queryWork hraw
  have hpoly := stmtWeightedCost_le_countPoly (op := Sum.elim R'.operationWork R'.coreWork)
    (query := R'.queryWork) (fun o d => by cases o <;> simp [hop, hcore]) hq p.body.instrument
    (Program.boundedBy_sizeBounds (b := b) d)
  simp only [St.init, map_zero, Nat.zero_add] at hcost
  have hwork := hcost.trans hpoly
  simpa only [St.reserveQueries, ResourceModel.work, Program.countPoly] using hwork

/-- The work of a canonical run is at most the instruction polynomial of the program at its
sizes, when every primitive, query and structural weight is at most one. -/
theorem Program.exec_work_le_countPoly {K : Type} {r b : ℕ} (p : Program Op Tst r b)
    (R : ResourceModel Op Tst) (hop : ∀ o d, R.operationWork o d ≤ 1)
    (hcore : ∀ k d, R.coreWork k d ≤ 1) (hq : ∀ q d, R.queryWork q d ≤ 1)
    {I : Interp Op Tst K} {τ : Tape K} {formats : Fin b → StorageFormat} {d : Fin r → ℕ}
    {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (hr : exec p I R formats τ d m = some st) :
    R.work st.cost ≤ CountPoly.eval (List.ofFn d) p.countPoly :=
  p.exec_weight_le_countPoly R R hop hcore hq hr

/-- **A certificate with explicit work.** The work and span of a certificate are restated by a
bound `W` of the instruction polynomial of its program, when every weight of the model is at
most one. The program, the model, the count budget and the postcondition are unchanged. -/
def Algorithm.withCountPoly {K : Type} {r b : ℕ} {P : Problem K r b}
    {M : AccessModel Op Tst P} {S : Specification Op Tst P} (A : Algorithm M S)
    (hop : ∀ o d, M.resources.operationWork o d ≤ 1)
    (hcore : ∀ k d, M.resources.coreWork k d ≤ 1) (hq : ∀ q d, M.resources.queryWork q d ≤ 1)
    (W : (Fin r → ℕ) → ℕ)
    (hW : ∀ d, P.valid d → CountPoly.eval (List.ofFn d) A.program.countPoly ≤ W d) :
    Algorithm M { S with work := W, span := W } where
  program := A.program
  correct := by
    intro d hd x I hI τ
    obtain ⟨st, hr, hp, hc, -, -, hm, hg⟩ := A.correct d hd x I hI τ
    have hw := (A.program.exec_work_le_countPoly M.resources hop hcore hq hr).trans (hW d hd)
    exact ⟨st, hr, hp, hc, hw, (M.resources.span_le_work st.cost).trans hw, hm, hg⟩

end NLAlib.Ops
