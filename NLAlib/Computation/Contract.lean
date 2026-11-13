/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact
public import NLAlib.Computation.Rounding
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Error contracts on a value semantics

An error analysis of a program is done once, against a contract on the value semantics, and
holds for every semantics meeting it. `NLAlib.Computation.IsRelErrSem u dec safe sem` is Higham's
standard model as such a contract: at decoding `dec` (the real value of a stored word at a tag),
unit roundoff `u` and range condition `safe`, each operation family has an error clause and a
success clause. The success clauses matter: a theorem that asserts success (as
`NLAlib.Computation.RunsWithin` does) cannot be proved from error clauses alone, which the
semantics that always fails meets. Exact real arithmetic meets the full contract with $u = 0$ and
every value in range (`NLAlib.Computation.isRelErrSem_exactSem`); the always-failing semantics
does not (`NLAlib.Computation.not_isRelErrSem_failSem`). Design: `docs/design/Computation.md`
(D19, §7).

The kernel analyses use only the arithmetic part of a contract,
`NLAlib.Computation.IsArithErrSem err dec safe sem`, with the error of each arithmetic operation
given by a relation `err p b a z` between the exact result $a$ on the decoded operands and the
decoded result $z$: the standard model is the relation `NLAlib.Computation.RelErr` of relative
error, and a model with underflow adds an absolute term. `NLAlib.Computation.AddsZeroExactly`
says that adding a decoded zero is exact, as in IEEE, fixed-point and exact arithmetic; with it
the kernels, which accumulate from a zero, keep the constants of [Higham2002].

## Main definitions

* `NLAlib.Computation.IsRelErrSem`: the relative-error contract with success clauses.
* `NLAlib.Computation.IsFloorRelErrSem`: the same with an absolute floor (gradual underflow).
* `NLAlib.Computation.BinOp.realOp`, `NLAlib.Computation.BinOp.IsArith`,
  `NLAlib.Computation.failSem`.
* `NLAlib.Computation.IsArithErrSem`: arithmetic error and success clauses for an error
  relation.
* `NLAlib.Computation.AddsZeroExactly`: adding a decoded zero is exact.
* `NLAlib.Computation.IsExactIntLit`: integer literals up to a bound are exact.
* `NLAlib.Computation.IsExactToNat`: the conversion to an index is the exact floor.
* `NLAlib.Computation.IsIndexExactSem`: exact integer literals and conversion, at one decoding.
* `NLAlib.Computation.MulShrinks`: multiplication by a value of modulus at most one does not
  increase the modulus.
* `NLAlib.Computation.IsTapeRounding`: the stored draws are a rounding of the ideal tape.
* `NLAlib.Computation.IsMatvecErr`: a normwise accuracy and success contract for an oracle.
* `NLAlib.Computation.MatrixFreeRounded`: the matrix-free model in the standard model of
  floating point.

## Main results

* `NLAlib.Computation.isRelErrSem_exactSem`: exact arithmetic meets the contract.
* `NLAlib.Computation.not_isRelErrSem_failSem`: the always-failing semantics does not.
* `NLAlib.Computation.IsRelErrSem.toFloor`: the standard model meets the floor model at every
  floor.
* `NLAlib.Computation.IsRelErrSem.isArithErrSem`: the standard-model contract gives the
  arithmetic part with the relation `NLAlib.Computation.RelErr`.
* `NLAlib.Computation.IsRelErrSem.nonneg`: the unit roundoff is nonnegative.
* `NLAlib.Computation.addsZeroExactly_exactSem`: exact arithmetic adds zero exactly.
* `NLAlib.Computation.isExactIntLit_exactSem`: exact arithmetic.
* `NLAlib.Computation.IsExactIntLit.mono`: a smaller bound.
* `NLAlib.Computation.isExactToNat_exactSem`, `NLAlib.Computation.isIndexExactSem_exactSem`,
  `NLAlib.Computation.IsIndexExactSem.mono`: index exactness of exact arithmetic.
* `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some`: the round trip of a size.
* `NLAlib.Computation.mulShrinks_exactSem`: exact real multiplication by a factor of modulus at
  most one does not enlarge.
* `NLAlib.Computation.IsExactIntLit.exists_exec_litIdx`: a size written as a literal decodes to
  itself.
* `NLAlib.Computation.isTapeRounding_id`: the exact rounding of the tape.
-/

@[expose] public section

namespace NLAlib.Computation

section Contracts
variable {P K : Type}

/-- Exact real meaning of the four arithmetic operations. -/
noncomputable def BinOp.realOp : BinOp → ℝ → ℝ → ℝ
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·) | _ => fun _ _ => 0

/-- The four arithmetic operations. -/
def BinOp.IsArith : BinOp → Prop
  | .add | .sub | .mul | .div => True
  | _ => False

/-- **The standard model as a contract on a value semantics**, at decoding `dec` (the real
value of a stored word at a tag), unit roundoff `u` and range condition `safe`. Each operation
family has an error clause and a success clause, since an error clause alone is met by the
semantics that always fails:
* arithmetic: the decoded result is the exact result times $1 + \delta$ with
  $\lvert \delta \rvert \le u$, and the operation succeeds when the exact result is in range and
  the divisor nonzero;
* literals: the same, for the rational value;
* `neg`, `conj`, `re`: exact and always defined on real decodings;
* `sqrt`: relative error, defined on nonnegative decodings;
* comparisons: exact on decoded values;
* `convert p q`: relative error at the target tag, defined when in range there.
[Higham2002, §2.2], the model (2.4) there for the arithmetic operations, here with success
clauses and for every operation family. -/
structure IsRelErrSem (u : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop)
    (sem : ScalarSem P K) : Prop where
  /-- Arithmetic has relative error at most the unit roundoff. -/
  bin_err : ∀ (p : P) (b : BinOp) (x y z : K), b.IsArith → sem.bin p b x y = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ)
  /-- Arithmetic succeeds in range, the divisor nonzero. -/
  bin_ok : ∀ (p : P) (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
    safe p (b.realOp (dec p x) (dec p y)) → ∃ z, sem.bin p b x y = some z
  /-- Literals have relative error at most the unit roundoff. -/
  lit_err : ∀ (p : P) (q : ℚ) (z : K), sem.lit p q = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = (q : ℝ) * (1 + δ)
  /-- Literals in range succeed. -/
  lit_ok : ∀ (p : P) (q : ℚ), safe p q → ∃ z, sem.lit p q = some z
  /-- Negation is exact and defined. -/
  neg : ∀ (p : P) (x : K), ∃ z, sem.un p .neg x = some z ∧ dec p z = -dec p x
  /-- Conjugation is the identity on real decodings, and defined. -/
  conj : ∀ (p : P) (x : K), ∃ z, sem.un p .conj x = some z ∧ dec p z = dec p x
  /-- The real part is the identity on real decodings, and defined. -/
  re : ∀ (p : P) (x : K), ∃ z, sem.un p .re x = some z ∧ dec p z = dec p x
  /-- The square root has relative error at most the unit roundoff. -/
  sqrt_err : ∀ (p : P) (x z : K), sem.un p .sqrt x = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = √(dec p x) * (1 + δ)
  /-- The square root of a nonnegative decoding succeeds. -/
  sqrt_ok : ∀ (p : P) (x : K), 0 ≤ dec p x → ∃ z, sem.un p .sqrt x = some z
  /-- Equality tests are exact on decodings. -/
  cmp_eq : ∀ (p : P) (x y : K), sem.cmp p .eq x y = some (decide (dec p x = dec p y))
  /-- Strict comparisons are exact on decodings. -/
  cmp_lt : ∀ (p : P) (x y : K), sem.cmp p .lt x y = some (decide (dec p x < dec p y))
  /-- Comparisons are exact on decodings. -/
  cmp_le : ∀ (p : P) (x y : K), sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))
  /-- Conversions have relative error at most the target's unit roundoff. -/
  convert_err : ∀ (p q : P) (x z : K), sem.convert p q x = some z →
    ∃ δ : ℝ, |δ| ≤ u q ∧ dec q z = dec p x * (1 + δ)
  /-- Conversions in range at the target succeed. -/
  convert_ok : ∀ (p q : P) (x : K), safe q (dec p x) → ∃ z, sem.convert p q x = some z

/-- Increasing a scalar roundoff allowance preserves the relative-error contract and all
its success clauses. This lets a solver choose a common run budget covering scalar
rounding and an independently specified matvec error. -/
theorem IsRelErrSem.mono {u v : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) (hu : ∀ p, u p ≤ v p) :
    IsRelErrSem v dec safe sem where
  bin_err p b x y z hb he := by
    obtain ⟨δ, hδ, hd⟩ := h.bin_err p b x y z hb he
    exact ⟨δ, hδ.trans (hu p), hd⟩
  bin_ok := h.bin_ok
  lit_err p q z he := by
    obtain ⟨δ, hδ, hd⟩ := h.lit_err p q z he
    exact ⟨δ, hδ.trans (hu p), hd⟩
  lit_ok := h.lit_ok
  neg := h.neg
  conj := h.conj
  re := h.re
  sqrt_err p x z he := by
    obtain ⟨δ, hδ, hd⟩ := h.sqrt_err p x z he
    exact ⟨δ, hδ.trans (hu p), hd⟩
  sqrt_ok := h.sqrt_ok
  cmp_eq := h.cmp_eq
  cmp_lt := h.cmp_lt
  cmp_le := h.cmp_le
  convert_err p q x z he := by
    obtain ⟨δ, hδ, hd⟩ := h.convert_err p q x z he
    exact ⟨δ, hδ.trans (hu q), hd⟩
  convert_ok := h.convert_ok

/-- **Exact real arithmetic meets the standard-model contract** with unit roundoff $0$, the identity
decoding and every value in range: `NLAlib.Computation.exactSem` over $\mathbb{R}$ satisfies every
error and success clause. [Higham2002, §2.2], the model (2.4) at $u = 0$.
Result: computation-exact-meets-contract -/
theorem isRelErrSem_exactSem : IsRelErrSem (P := P) (fun _ => 0) (fun _ x => x)
    (fun _ _ => True) (exactSem (𝕜 := ℝ)) where
  bin_err p b x y z hb h := by
    refine ⟨0, by simp, ?_⟩
    cases b <;> simp only [BinOp.IsArith] at hb <;> simp only [exactSem, Option.some.injEq] at h
    · subst h; simp [BinOp.realOp]
    · subst h; simp [BinOp.realOp]
    · subst h; simp [BinOp.realOp]
    · by_cases hy : y = 0
      · simp [hy] at h
      · simp only [hy, ↓reduceIte, Option.some.injEq] at h; subst h; simp [BinOp.realOp]
  bin_ok p b x y hb hdiv _ := by
    cases b <;> simp only [BinOp.IsArith] at hb <;> simp only [exactSem]
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp [hdiv rfl]
  lit_err p q z h := by
    simp only [exactSem, Option.some.injEq] at h
    exact ⟨0, by simp, by simp [← h]⟩
  lit_ok p q _ := ⟨_, rfl⟩
  neg p x := ⟨-x, rfl, rfl⟩
  conj p x := ⟨x, by simp [exactSem], rfl⟩
  re p x := ⟨x, by simp [exactSem], rfl⟩
  sqrt_err p x z h := by
    simp only [exactSem] at h
    split_ifs at h with hx
    simp only [Option.some.injEq] at h
    exact ⟨0, by simp, by simp [← h]⟩
  sqrt_ok p x hx := by simp [exactSem, hx]
  cmp_eq p x y := by simp only [exactSem]
  cmp_lt p x y := by simp only [exactSem, RCLike.im_to_real, and_self, ↓reduceIte]
  cmp_le p x y := by simp only [exactSem, RCLike.im_to_real, and_self, ↓reduceIte]
  convert_err p q x z h := by
    simp only [exactSem, Option.some.injEq] at h
    exact ⟨0, by simp, by simp [h]⟩
  convert_ok p q x _ := ⟨x, rfl⟩

/-- The semantics that always fails. -/
def failSem : ScalarSem P K :=
  ⟨fun _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none,
    fun _ _ => none⟩

/-- **The success clauses matter**: for a nonempty type of tags, the semantics that always fails
does not meet the standard-model contract, for any unit roundoff and decoding with every value in
range. No printed source.
Result: computation-failing-semantics -/
theorem not_isRelErrSem_failSem [Nonempty P] (u : P → ℝ) (dec : P → K → ℝ) :
    ¬ IsRelErrSem u dec (fun _ _ => True) (failSem (P := P) (K := K)) := fun h => by
  obtain ⟨z, hz⟩ := h.lit_ok (Classical.arbitrary P) 0 trivial
  simp [failSem] at hz

/-- **The standard model with an absolute floor as a contract on a value semantics**, at
decoding `dec`, unit roundoff `u`, floor `τ` and range condition `safe`: the model of a bounded
format with gradual underflow, where a result below the floor has an absolute error at most
$u(p)\tau(p)$ instead of a relative one. Each operation family has an error clause and a success
clause, since an error clause alone is met by the semantics that always fails:
* arithmetic: the exact result $a$ on the decoded operands and the decoded result $z$ satisfy
  $\lvert a - z \rvert \le u\max(\lvert a \rvert, \tau)$, and the operation succeeds when $a$ is
  in range and the divisor nonzero;
* literals: the same, for the rational value;
* `neg`, `conj`, `re`: exact and always defined on real decodings;
* `sqrt`: the same error, defined on a nonnegative decoding whose exact root is in range;
* comparisons: exact on decoded values;
* `convert p q`: the same error at the target tag, defined when in range there.
At $\tau = 0$ the error clauses are those of `NLAlib.Computation.IsRelErrSem`, which implies this
contract at every floor (`NLAlib.Computation.IsRelErrSem.toFloor`). [Higham2002, §2.2], the model
(2.4) there, with the underflow term of gradual underflow written as a floor. -/
structure IsFloorRelErrSem (u τ : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop)
    (sem : ScalarSem P K) : Prop where
  /-- Arithmetic errs by at most the unit roundoff times the larger of the result and the
  floor. -/
  bin_err : ∀ (p : P) (b : BinOp) (x y z : K), b.IsArith → sem.bin p b x y = some z →
    |b.realOp (dec p x) (dec p y) - dec p z| ≤ u p * max |b.realOp (dec p x) (dec p y)| (τ p)
  /-- Arithmetic succeeds in range, the divisor nonzero. -/
  bin_ok : ∀ (p : P) (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
    safe p (b.realOp (dec p x) (dec p y)) → ∃ z, sem.bin p b x y = some z
  /-- Literals err by at most the unit roundoff times the larger of the value and the floor. -/
  lit_err : ∀ (p : P) (q : ℚ) (z : K), sem.lit p q = some z →
    |(q : ℝ) - dec p z| ≤ u p * max |(q : ℝ)| (τ p)
  /-- Literals in range succeed. -/
  lit_ok : ∀ (p : P) (q : ℚ), safe p q → ∃ z, sem.lit p q = some z
  /-- Negation is exact and defined. -/
  neg : ∀ (p : P) (x : K), ∃ z, sem.un p .neg x = some z ∧ dec p z = -dec p x
  /-- Conjugation is the identity on real decodings, and defined. -/
  conj : ∀ (p : P) (x : K), ∃ z, sem.un p .conj x = some z ∧ dec p z = dec p x
  /-- The real part is the identity on real decodings, and defined. -/
  re : ∀ (p : P) (x : K), ∃ z, sem.un p .re x = some z ∧ dec p z = dec p x
  /-- The square root errs by at most the unit roundoff times the larger of the root and the
  floor. -/
  sqrt_err : ∀ (p : P) (x z : K), sem.un p .sqrt x = some z →
    |√(dec p x) - dec p z| ≤ u p * max √(dec p x) (τ p)
  /-- The square root of a nonnegative decoding succeeds when the root is in range. -/
  sqrt_ok : ∀ (p : P) (x : K), 0 ≤ dec p x → safe p √(dec p x) → ∃ z, sem.un p .sqrt x = some z
  /-- Equality tests are exact on decodings. -/
  cmp_eq : ∀ (p : P) (x y : K), sem.cmp p .eq x y = some (decide (dec p x = dec p y))
  /-- Strict comparisons are exact on decodings. -/
  cmp_lt : ∀ (p : P) (x y : K), sem.cmp p .lt x y = some (decide (dec p x < dec p y))
  /-- Comparisons are exact on decodings. -/
  cmp_le : ∀ (p : P) (x y : K), sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))
  /-- Conversions err by at most the target's unit roundoff times the larger of the value and
  the target's floor. -/
  convert_err : ∀ (p q : P) (x z : K), sem.convert p q x = some z →
    |dec p x - dec q z| ≤ u q * max |dec p x| (τ q)
  /-- Conversions in range at the target succeed. -/
  convert_ok : ∀ (p q : P) (x : K), safe q (dec p x) → ∃ z, sem.convert p q x = some z

/-- A relative error $\delta$ with $\lvert\delta\rvert \le u$ is an error of at most
$u\max(\lvert a\rvert, \tau)$, at every floor $\tau$. -/
private theorem abs_sub_mul_one_add_le {u τ a δ : ℝ} (hδ : |δ| ≤ u) :
    |a - a * (1 + δ)| ≤ u * max |a| τ := by
  have e : a - a * (1 + δ) = -(a * δ) := by ring
  rw [e, abs_neg, abs_mul, mul_comm]
  exact mul_le_mul hδ (le_max_left _ _) (abs_nonneg a) ((abs_nonneg δ).trans hδ)

/-- **The standard model meets the floor model at every floor**: a semantics meeting
`NLAlib.Computation.IsRelErrSem` at unit roundoff `u`, decoding `dec` and range condition `safe`
meets `NLAlib.Computation.IsFloorRelErrSem` at the same `u`, `dec` and `safe` and every floor
`τ`: a relative error $\delta$ with $\lvert\delta\rvert \le u$ errs by
$\lvert a\delta\rvert \le u\max(\lvert a\rvert, \tau)$, and a square root that succeeds on every
nonnegative decoding succeeds on those whose root is in range. [Higham2002, §2.2], the model
(2.4) there. -/
theorem IsRelErrSem.toFloor {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) (τ : P → ℝ) :
    IsFloorRelErrSem u τ dec safe sem where
  bin_err p b x y z hb he := by
    obtain ⟨δ, hδ, hd⟩ := h.bin_err p b x y z hb he
    rw [hd]
    exact abs_sub_mul_one_add_le hδ
  bin_ok := h.bin_ok
  lit_err p q z he := by
    obtain ⟨δ, hδ, hd⟩ := h.lit_err p q z he
    rw [hd]
    exact abs_sub_mul_one_add_le hδ
  lit_ok := h.lit_ok
  neg := h.neg
  conj := h.conj
  re := h.re
  sqrt_err p x z he := by
    obtain ⟨δ, hδ, hd⟩ := h.sqrt_err p x z he
    rw [hd]
    have h' := abs_sub_mul_one_add_le (a := √(dec p x)) (τ := τ p) hδ
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h'
  sqrt_ok p x hx _ := h.sqrt_ok p x hx
  cmp_eq := h.cmp_eq
  cmp_lt := h.cmp_lt
  cmp_le := h.cmp_le
  convert_err p q x z he := by
    obtain ⟨δ, hδ, hd⟩ := h.convert_err p q x z he
    rw [hd]
    exact abs_sub_mul_one_add_le hδ
  convert_ok := h.convert_ok

end Contracts

/-! ### The arithmetic part of a contract, for the kernel analyses -/

section ArithErr

variable {P K : Type}

/-- **The arithmetic part of an error contract**, at error relation `err` (the decoded result is
related to the exact result on the decoded operands), decoding `dec` and range condition `safe`:
* arithmetic satisfies the error relation, and succeeds in range with a nonzero divisor;
* the literal $0$ succeeds and decodes to $0$;
* negation and conjugation are exact and defined on real decodings.
`NLAlib.Computation.IsRelErrSem` gives it with the relation of relative error
(`NLAlib.Computation.IsRelErrSem.isArithErrSem`). [Higham2002, §2.2], the model (2.4) there,
with the error clause abstracted. -/
structure IsArithErrSem (err : P → BinOp → ℝ → ℝ → Prop) (dec : P → K → ℝ)
    (safe : P → ℝ → Prop) (sem : ScalarSem P K) : Prop where
  /-- Arithmetic satisfies the error relation. -/
  bin_err : ∀ (p : P) (b : BinOp) (x y z : K), b.IsArith → sem.bin p b x y = some z →
    err p b (b.realOp (dec p x) (dec p y)) (dec p z)
  /-- Arithmetic succeeds in range, the divisor nonzero. -/
  bin_ok : ∀ (p : P) (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
    safe p (b.realOp (dec p x) (dec p y)) → ∃ z, sem.bin p b x y = some z
  /-- The literal zero succeeds and decodes to zero. -/
  lit_zero : ∀ p : P, ∃ z, sem.lit p 0 = some z ∧ dec p z = 0
  /-- Negation is exact and defined. -/
  neg : ∀ (p : P) (x : K), ∃ z, sem.un p .neg x = some z ∧ dec p z = -dec p x
  /-- Conjugation is the identity on real decodings, and defined. -/
  conj : ∀ (p : P) (x : K), ∃ z, sem.un p .conj x = some z ∧ dec p z = dec p x

/-- **Adding zero is exact**: whenever an addition at tag `p` succeeds and its first operand
decodes to $0$, the result decodes to the second operand. True of IEEE arithmetic, where
$0 + y = y$ exactly because every word is representable; false under flush-to-zero (a subnormal
$y$ flushes to $0$) and for a semantics that rounds words off the grid
($\mathrm{fl}(0 + y) = \mathrm{fl}(y) \ne y$). `NLAlib.Computation.gridSem` meets it together
with the standard model at $u > 0$. No printed source. -/
def AddsZeroExactly (dec : P → K → ℝ) (sem : ScalarSem P K) : Prop :=
  ∀ (p : P) (x y z : K), sem.bin p .add x y = some z → dec p x = 0 → dec p z = dec p y

/-- **Integer literals up to $B$ are exact**: at every tag `p`, the literal of every natural
number $k \le B$ succeeds and decodes to $k$. True of IEEE arithmetic below $2^t$ ($t$ the
precision) within its finite representable range, of fixed grids containing the integers up to
$B$, and of exact arithmetic for every $B$; not implied by the standard model, under which a
literal may decode to $k(1 + \delta)$. A size at most $B$ written by `litIdx` reads back exactly.
An equality test between such literals decides equality of sizes when comparisons are also exact
on decoded values, as required separately by `NLAlib.Computation.IsRelErrSem`.
No printed source. -/
def IsExactIntLit (dec : P → K → ℝ) (sem : ScalarSem P K) (B : ℕ) : Prop :=
  ∀ (p : P) (k : ℕ), k ≤ B → ∃ z, sem.lit p k = some z ∧ dec p z = k

/-- **The conversion to an index is the exact floor**: at every tag `p`, the conversion of a
stored value with nonnegative decoding succeeds and is the floor of its decoding, and the
conversion of a stored value with negative decoding fails (no clamping at $0$: a negative size is
a failure of the run). True of IEEE truncation of a float to an unsigned integer with an invalid
operation below zero, and of `NLAlib.Computation.exactSem` on real values. With
`NLAlib.Computation.IsExactIntLit`, a size written by `litIdx` and read back by an index binder
is the size. No printed source. -/
def IsExactToNat (dec : P → K → ℝ) (sem : ScalarSem P K) : Prop :=
  ∀ (p : P) (x : K), sem.toNat p x = if 0 ≤ dec p x then some ⌊dec p x⌋₊ else none

/-- **Index exactness of a semantics** at the decoding `dec`: integer literals up to $B$ are exact
(`NLAlib.Computation.IsExactIntLit`) and the conversion to an index is the exact floor, failing
below zero (`NLAlib.Computation.IsExactToNat`), both at the one decoding `dec`. A size written by
`litIdx` up to $B$ and read back by an index binder is the size. Every rounded probabilistic
target assumes it (`NLAlib.Computation.MatrixFreeRoundedProb`), at the decoding of its other
contracts. No printed source. -/
structure IsIndexExactSem (dec : P → K → ℝ) (B : ℕ) (sem : ScalarSem P K) : Prop where
  /-- Integer literals up to `B` are exact. -/
  intLit : IsExactIntLit dec sem B
  /-- The conversion to an index is the exact floor. -/
  toNat : IsExactToNat dec sem

/-- **Multiplication by a value of modulus at most one does not increase the modulus**: whenever
a product at tag `p` succeeds and its second factor decodes into $[-1, 1]$, the result decodes to
at most the modulus of the first factor. True of every monotone rounding that is exact on the
stored values (IEEE rounding to nearest, `NLAlib.Computation.gridSem`), not implied by the standard
model, under which $\mathrm{fl}(s v)$ may exceed $s$. A uniform shift $\mathrm{fl}(s v)$ then stays
in the window $[-s, s]$, the clause $\lvert \bar c \rvert \le \bar s$ of `NLAlib.IsUnifSampler`.
No printed source. -/
def MulShrinks (dec : P → K → ℝ) (sem : ScalarSem P K) : Prop :=
  ∀ (p : P) (x y z : K), sem.bin p .mul x y = some z → |dec p y| ≤ 1 → |dec p z| ≤ |dec p x|

/-- **The tape-rounding contract**: the stored draws are a rounding $\rho$ of the ideal tape.
For every distribution $d$, tape position $i$ and ideal value $x$ with $\lvert x \rvert \le \Omega$,
the stored value $\rho(d, i, x)$ at tag `p` decodes to within $c(d)\,u\max(\lvert x \rvert, \tau)$
of $x$: relative error $c(d)\,u$ above the floor $\tau$ (gradual underflow; $0$ with an unbounded
exponent), in the range $\Omega$ (overflow). A uniform draw of $x \in [-1, 1]$ decodes into
$[-1, 1]$. The rounding may depend on the position, as the state of a hardware sampler does; the
law of the ideal tape is fixed by the model that uses the contract. [Shah2024, Definition 1.3],
[Shah2024, Definition 1.4], the coupling of a computed and an ideal sample realised by the ideal
tape. -/
def IsTapeRounding (dec : P → K → ℝ) (p : P) (u τ Ω : ℝ) (c : Dist → ℝ)
    (ρ : Dist → ℕ → ℝ → K) : Prop :=
  (∀ (d : Dist) (i : ℕ) (x : ℝ), |x| ≤ Ω → |dec p (ρ d i x) - x| ≤ c d * u * max |x| τ) ∧
    ∀ (i : ℕ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 → dec p (ρ .uniform i x) ∈ Set.Icc (-1 : ℝ) 1

/-- **The standard model gives the arithmetic part** of the contract with the relation of
relative error: if `sem` meets `NLAlib.Computation.IsRelErrSem` at unit roundoff `u`, it meets
`NLAlib.Computation.IsArithErrSem` with $\mathrm{err}(p, b, a, z)$ the statement that $z =
a(1 + \delta)$ for some $\lvert \delta \rvert \le u(p)$, and the zero literal is safe whenever
every value is. [Higham2002, §2.2], the model (2.4) there. -/
theorem IsRelErrSem.isArithErrSem {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) (hsafe : ∀ p, safe p 0) :
    IsArithErrSem (fun p _ => RelErr (u p)) dec safe sem := by
  refine ⟨h.bin_err, h.bin_ok, fun p => ?_, h.neg, h.conj⟩
  obtain ⟨z, hz⟩ := h.lit_ok p 0 (by simpa using hsafe p)
  obtain ⟨δ, -, hδ⟩ := h.lit_err p 0 z hz
  exact ⟨z, hz, by simpa using hδ⟩

/-- The unit roundoff of a contract is nonnegative at every tag $p$ where $0$ is in range: an
operation that succeeds has an error $\delta$ with $\lvert \delta \rvert \le u(p)$, and the
literal $0$ succeeds when it is in range. No printed source. -/
theorem IsRelErrSem.nonneg {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) {p : P} (hp : safe p 0) :
    0 ≤ u p := by
  obtain ⟨z, hz⟩ := h.lit_ok p 0 (by simpa using hp)
  obtain ⟨δ, hδ, -⟩ := h.lit_err p 0 z hz
  exact (abs_nonneg δ).trans hδ

/-- Exact arithmetic adds zero exactly: `NLAlib.Computation.exactSem` over $\mathbb{R}$, with
the identity decoding, satisfies `NLAlib.Computation.AddsZeroExactly`. No printed source. -/
theorem addsZeroExactly_exactSem : AddsZeroExactly (P := P) (fun _ x => x)
    (exactSem (𝕜 := ℝ)) := by
  intro p x y z h hx
  simp only [exactSem, Option.some.injEq] at h hx ⊢
  rw [← h, hx, zero_add]

end ArithErr

section Oracle
open scoped Matrix
variable {P ι K C : Type}

/-- **A normwise matvec contract** for oracle `o` of interpretation `I`, at tag `p`, for the
real $N \times N$ matrix $\mathbf{H}$ and bound $c$: the oracle has height $N$, and on every
single column $\mathbf{x}$ of $N$ words it succeeds with $N$ words $\mathbf{y}$ with
$\lVert\mathbf{H}\mathbf{x} - \mathbf{y}\rVert \le c\lVert\mathbf{x}\rVert$, vectors read
through the decoding. The value semantics constrains scalar operations only, so the accuracy of
an oracle is an assumption on the interpretation; a
relative contract $\lVert\mathbf{H}\mathbf{x} - \mathbf{y}\rVert \le
\varepsilon\lVert\mathbf{H}\rVert_2\lVert\mathbf{x}\rVert$ takes
$c = \varepsilon\lVert\mathbf{H}\rVert_2$ (the spectral norm is a Matrix-layer name, which this
layer does not import). -/
def IsMatvecErr (I : Interp P ι K C) (o : ι) (dec : P → K → ℝ) (p : P) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) : Prop :=
  I.height o = N ∧ ∀ X : Array K, (hX : X.size = N) → ∃ Y : Array K, ∃ hY : Y.size = N,
    I.oracle o 1 X = some Y ∧
      ‖WithLp.toLp 2 ((H *ᵥ fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2))) -
          fun i : Fin N => dec p (Y[i.1]'(hY ▸ i.2)))‖ ≤
        c * ‖WithLp.toLp 2 (fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2)))‖

/-- A matvec oracle succeeds with normwise error at most $c\|\mathbf{x}\|+\eta$ on
decoded inputs satisfying `domain`. The domain is an input obligation, independent of whether
the call succeeds. The absolute allowance retains underflow. Unlike `IsMatvecErr`, this
contract does not require success on inputs whose exact products overflow the word format.
No printed source. -/
def IsMatvecErrOn (I : Interp P ι K C) (o : ι) (dec : P → K → ℝ) (p : P) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (domain : (Fin N → ℝ) → Prop) (c η : ℝ) : Prop :=
  I.height o = N ∧ ∀ X : Array K, (hX : X.size = N) →
    domain (fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2))) →
      ∃ Y : Array K, ∃ hY : Y.size = N, I.oracle o 1 X = some Y ∧
        ‖WithLp.toLp 2 ((H *ᵥ fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2))) -
            fun i : Fin N => dec p (Y[i.1]'(hY ▸ i.2)))‖ ≤
          c * ‖WithLp.toLp 2 (fun i : Fin N => dec p (X[i.1]'(hX ▸ i.2)))‖ + η

/-- The global relative oracle contract restricts to any decoded input domain, with zero
absolute allowance. Its success clause supplies the required calls. No printed source. -/
theorem IsMatvecErr.toOn {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ} {p : P}
    {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ}
    (h : IsMatvecErr I o dec p H c) (domain : (Fin N → ℝ) → Prop) :
    IsMatvecErrOn I o dec p H domain c 0 := by
  refine ⟨h.1, fun X hX _ => ?_⟩
  simpa only [add_zero] using h.2 X hX

/-- Restricting the admitted input domain preserves success and the mixed normwise error.
No printed source. -/
theorem IsMatvecErrOn.mono_domain {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ} {p : P}
    {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c η : ℝ}
    {domain domain' : (Fin N → ℝ) → Prop} (h : IsMatvecErrOn I o dec p H domain c η)
    (hd : ∀ x, domain' x → domain x) : IsMatvecErrOn I o dec p H domain' c η :=
  ⟨h.1, fun X hX hx => h.2 X hX (hd _ hx)⟩

/-- A bounded-word carrier attaining a positive maximum $B$ cannot support a globally
successful oracle for $[2]$ with coefficient $c<1$: on input $B$, every output is at least
$B$ away from $2B$. This obstruction is independent of the scalar arithmetic contract and
motivates an input domain for finite-range oracle certificates. No printed source. -/
theorem not_isMatvecErr_of_bounded_decode (I : Interp P ι K C) (o : ι)
    (dec : P → K → ℝ) (p : P) (B c : ℝ) (hB : 0 < B) (hc : c < 1)
    (hbound : ∀ w : K, dec p w ≤ B) (x : K) (hx : dec p x = B) :
    ¬ IsMatvecErr I o dec p (fun (_ _ : Fin 1) => (2 : ℝ)) c := by
  intro h
  obtain ⟨Y, hY, _, herr⟩ := h.2 #[x] rfl
  have hn (v : Fin 1 → ℝ) : ‖WithLp.toLp 2 v‖ = |v 0| := by
    have hv : v = Function.const (Fin 1) (v 0) := by
      ext i
      exact congrArg v (Subsingleton.elim i 0)
    rw [hv, PiLp.norm_toLp_const (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp
  rw [hn, hn] at herr
  have he : |2 * B - dec p (Y[0]'(by omega))| ≤ c * B := by
    simpa [Matrix.mulVec, dotProduct, hx, abs_of_pos hB] using herr
  norm_num at he
  have hb := hbound (Y[0]'(by omega))
  have hmul : c * B < B := by nlinarith
  have hl := le_abs_self (2 * B - dec p (Y[0]'(by omega)))
  norm_num at hl
  nlinarith

/-- Increasing the operator-error allowance preserves oracle accuracy and success. -/
theorem IsMatvecErr.mono {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ} {p : P}
    {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c d : ℝ}
    (h : IsMatvecErr I o dec p H c) (hc : c ≤ d) : IsMatvecErr I o dec p H d := by
  refine ⟨h.1, ?_⟩
  intro X hX
  obtain ⟨Y, hY, hr, he⟩ := h.2 X hX
  exact ⟨Y, hY, hr, he.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))⟩

variable [DecidableEq P] [AddMonoid C] in
/-- **The matrix-free model in the standard model of floating point.** The program family
`prog` (a statement for each size; a compiled program enters as `Prog.toStmt`) runs, for all
sizes $N$, $n$ satisfying `valid`, every declared input $x$ (of type `X N n`) and every real
$N \times N$ matrix $\mathbf{H}$ satisfying the precondition `pre N n x H`, under **every**
interpretation $I$ whose value semantics meets `NLAlib.Computation.IsRelErrSem` (unit roundoff
`u`, decoding `dec`, every value in range) and `NLAlib.Computation.AddsZeroExactly`, and whose
every oracle meets `NLAlib.Computation.IsMatvecErr` for $\mathbf{H}$ with the bound
`mvBound N n H`, from the initial state that holds the declared buffers `inputs N n x` at tag
`p` and nothing else, and ends in a state satisfying `post N n x H`.

As in `NLAlib.Computation.MatrixFree`, the program is bound before the sizes, the matrix and the
inputs, and learns $\mathbf{H}$ only through oracle calls; unlike it, the arithmetic is any
semantics meeting the two contracts on scalars and the oracles any meeting the matvec contract
(two contracts, not one bundled contract on `Interp`). No counts: the charge of `I` is arbitrary. -/
def MatrixFreeRounded {r b : ℕ} (p : P) (prog : ℕ → (Fin r → ℕ) → Stmt P ι ℕ ℕ)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K))
    (u : P → ℝ) (dec : P → K → ℝ)
    (mvBound : (N : ℕ) → (Fin r → ℕ) → Matrix (Fin N) (Fin N) ℝ → ℝ)
    (pre : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ → Prop)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ → St P K C → Prop) :
    Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (H : Matrix (Fin N) (Fin N) ℝ) (I : Interp P ι K C),
    IsRelErrSem u dec (fun _ _ => True) I.sem → AddsZeroExactly dec I.sem →
    (∀ o, IsMatvecErr I o dec p H (mvBound N n H)) → pre N n x H →
    ∃ st', exec I (prog N n) (inputState p (List.ofFn (inputs N n x))) = some st' ∧
      post N n x H st'

end Oracle

/-! ### Exact integer literals and tape roundings -/

section ExactIntLit

variable {P K : Type}

/-- Exact arithmetic has exact integer literals: `NLAlib.Computation.exactSem` over
$\mathbb{R}$, with the identity decoding, meets `NLAlib.Computation.IsExactIntLit` at every bound
$B$. No printed source. -/
theorem isExactIntLit_exactSem (B : ℕ) :
    IsExactIntLit (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) B := by
  intro p k _
  exact ⟨(k : ℝ), by simp [exactSem], rfl⟩

/-- A smaller bound: exact integer literals up to $B$ are exact up to every $B' \le B$.
No printed source. -/
theorem IsExactIntLit.mono {dec : P → K → ℝ} {sem : ScalarSem P K} {B B' : ℕ}
    (h : IsExactIntLit dec sem B) (hB : B' ≤ B) : IsExactIntLit dec sem B' :=
  fun p k hk => h p k (hk.trans hB)

/-- Exact real arithmetic converts exactly: `NLAlib.Computation.exactSem` over $\mathbb{R}$, with
the identity decoding, meets `NLAlib.Computation.IsExactToNat`. No printed source. -/
theorem isExactToNat_exactSem : IsExactToNat (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) := by
  intro p x
  simp [exactSem]

/-- Exact real arithmetic is index exact at every bound: `NLAlib.Computation.exactSem` over
$\mathbb{R}$, with the identity decoding, meets `NLAlib.Computation.IsIndexExactSem` at $B$.
No printed source. -/
theorem isIndexExactSem_exactSem (B : ℕ) :
    IsIndexExactSem (P := P) (fun _ x => x) B (exactSem (𝕜 := ℝ)) :=
  ⟨isExactIntLit_exactSem B, isExactToNat_exactSem⟩

/-- A smaller bound: index exactness up to $B$ holds up to every $B' \le B$. No printed
source. -/
theorem IsIndexExactSem.mono {dec : P → K → ℝ} {sem : ScalarSem P K} {B B' : ℕ}
    (h : IsIndexExactSem dec B sem) (hB : B' ≤ B) : IsIndexExactSem dec B' sem :=
  ⟨h.intLit.mono hB, h.toNat⟩

/-- The round trip of a size: under exact integer literals up to $B$ and the exact floor
conversion, the literal of $k \le B$ converts back to $k$. So a size written by `litIdx` and read by
an index binder is the size. No printed source. -/
theorem IsExactIntLit.toNat_eq_of_lit_eq_some {dec : P → K → ℝ} {sem : ScalarSem P K} {B : ℕ}
    (hlit : IsExactIntLit dec sem B) (htn : IsExactToNat dec sem) {p : P} {k : ℕ} (hk : k ≤ B)
    {z : K} (hz : sem.lit p k = some z) : sem.toNat p z = some k := by
  obtain ⟨z', hz', hdec⟩ := hlit p k hk
  have hzz : z = z' := Option.some_injective _ (hz.symm.trans hz')
  subst hzz
  rw [htn p z, hdec, Nat.floor_natCast]
  simp

/-- Exact real multiplication by a factor of modulus at most one does not enlarge:
`NLAlib.Computation.exactSem` over $\mathbb{R}$, with the identity decoding, meets
`NLAlib.Computation.MulShrinks`. No printed source. -/
theorem mulShrinks_exactSem : MulShrinks (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) := by
  intro p x y z h hy
  have hz : x * y = z := Option.some.inj h
  subst hz
  change |x * y| ≤ |x|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg x) hy

variable [DecidableEq P]

/-- A size written as a literal decodes to itself: under exact integer literals up to $B$,
if the cell $(b, i)$ can be written at tag `p` and the index expression $e$ has value at most $B$,
the instruction `litIdx p (b, i) e` succeeds, and the cell then reads a word that decodes to the
value of $e$. No printed source. -/
theorem IsExactIntLit.exists_exec_litIdx {dec : P → K → ℝ} {sem : ScalarSem P K} {B : ℕ}
    (h : IsExactIntLit dec sem B) (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ)
    (p : P) (b i : ℕ) (e : IExp ℕ) (he : e.eval ≤ B)
    (hw : ∀ v : K, ∃ s', s.write p b i v = some s') :
    ∃ r z, (Instr.litIdx p ⟨b, .const i⟩ e).run sem tape s pos = some r ∧
      r.1.read p b i = some z ∧ dec p z = e.eval ∧ r.2 = pos := by
  obtain ⟨z, hz, hdz⟩ := h p e.eval he
  obtain ⟨s', hs'⟩ := hw z
  refine ⟨(s', pos), z, ?_, Store.read_of_write_eq_some hs', hdz, rfl⟩
  simp only [Instr.run, hz, Option.bind_some, hs', Option.map_some, IExp.eval]

omit [DecidableEq P] in
/-- The exact rounding of the tape: storing each ideal draw as itself in $\mathbb{R}$ meets
`NLAlib.Computation.IsTapeRounding` with the identity decoding, for every unit roundoff $u$,
floor $\tau$, range $\Omega$ and constants $c$ with $c(d)\,u \ge 0$. No printed source. -/
theorem isTapeRounding_id (p : P) (u τ Ω : ℝ) (c : Dist → ℝ) (hc : ∀ d, 0 ≤ c d * u) :
    IsTapeRounding (fun _ x => x) p u τ Ω c (fun _ _ x => x) := by
  refine ⟨fun d i x _ => ?_, fun i x hx => hx⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg (hc d) (le_max_of_le_left (abs_nonneg x))

end ExactIntLit

end NLAlib.Computation
