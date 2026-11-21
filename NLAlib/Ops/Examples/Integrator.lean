/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Operator
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.Ops.Confined

/-!
# Example: an explicit integrator, certified

The example of the page *Programs, models and certificates*: the integrator
$x_{t+1} = x_t + h A x_t$ written over two operations, a product with $A$ and a vector update,
each known only through its contract.

## Main definitions

* `NLAlib.Ops.Examples.Integrator.MyOperation`: the two operations.
* `NLAlib.Ops.Examples.Integrator.myStep`, `NLAlib.Ops.Examples.Integrator.myIntegrate`: the
  routines.
* `NLAlib.Ops.Examples.Integrator.myMatvecRel`, `NLAlib.Ops.Examples.Integrator.myAxpyRel`: the
  contracts.

## Main results

* `NLAlib.Ops.Examples.Integrator.myStep_meets`: one step, with its error.
* `NLAlib.Ops.Examples.Integrator.myIntegrate_meets`: the integrator, with its accuracy bound.
* `NLAlib.Ops.Examples.Integrator.myAlgorithm`: the certificate, with closed-form work, span and
  scratch.
* `NLAlib.Ops.Examples.Integrator.myProgram_calls`, `NLAlib.Ops.Examples.Integrator.myProgram_peak`:
  the calls and the scratch of the tree.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Integrator

open NLAlib.Ops
open scoped Matrix Matrix.Norms.L2Operator

/-! ### The operations and the routines -/

/-- The two operations of the integrator: a product with the matrix, and a vector update. -/
inductive MyOperation where
  /-- `matvec [n, n] (x) → (y)`. -/
  | matvec
  /-- `axpy [n] (α, x, y) → (y)`. -/
  | axpy
  deriving DecidableEq

/-- One step: `X ← X + h · (A X)`. -/
def myStep : Routine MyOperation Empty := noted% routine% [n] (h : 1, X : n) → (X) {
  let Y ← alloc n;
  call MyOperation.matvec [n, n] (X) → (Y);
  call MyOperation.axpy [n] (h, Y, X) → (X)
}

/-- `N` steps. -/
def myIntegrate : Routine MyOperation Empty := noted% routine% [n, N] (h : 1, X : n) → (X) {
  for t < N { run myStep [n] (h, X) }
}

/-! ### The contracts -/

/-- `matvec [n, n] (x) → (y)`: $\lVert A x - y \rVert \le \delta \lVert x \rVert$. -/
@[simps (attr := storeNF)]
def myMatvecRel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : BlockRel ℝ where
  nd := 2
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ Y := match X, Y with
    | [x], [y] => let n := d.headD 0
        ‖WithLp.toLp 2 (A n *ᵥ decv id n x - decv id n y)‖ ≤
          δ * ‖WithLp.toLp 2 (decv id n x)‖
    | _, _ => False

/-- `axpy [n] (α, x, y) → (y)`:
$\lvert z_i - (y_i + \alpha x_i) \rvert \le e (\lvert y_i \rvert + \lvert \alpha x_i \rvert)$. -/
@[simps (attr := storeNF)]
def myAxpyRel (e : ℝ) : BlockRel ℝ where
  nd := 1
  inLens d := [1, d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ Y := match X, Y with
    | [[a], x, y], [z] => ∀ i < d.headD 0,
        |vec z i - (vec y i + a * vec x i)| ≤ e * (|vec y i| + |a * vec x i|)
    | _, _ => False

/-- The update contract is the library's `axpyRel`, for the identity decoding. -/
theorem myAxpyRel_eq (e : ℝ) : myAxpyRel e = axpyRel id e := by
  unfold myAxpyRel axpyRel
  congr 1
  funext d X w Y
  rcases X with _ | ⟨_ | ⟨a, _ | ⟨_, _⟩⟩, _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩⟩ <;>
    rcases Y with _ | ⟨z, _ | ⟨_, _⟩⟩ <;> rfl

/-- The error of one step relative to the norm of the vector:
$\eta = \lvert h \rvert \delta + e (1 + \lvert h \rvert (\lVert A \rVert + \delta))$. -/
noncomputable def myEta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (δ e h : ℝ) : ℝ :=
  |h| * δ + e * (1 + |h| * (‖A‖ + δ))

/-! ### Norms of decoded vectors -/

/-- A vector whose entries are bounded in absolute value by those of another is no longer. -/
theorem norm_toLp_le {n : ℕ} {u v : Fin n → ℝ} (h : ∀ i, |u i| ≤ v i) :
    ‖WithLp.toLp 2 u‖ ≤ ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((h i).trans (le_abs_self _)) 2

/-- Taking absolute values entrywise keeps the Euclidean norm. -/
theorem norm_toLp_abs {n : ℕ} (u : Fin n → ℝ) :
    ‖WithLp.toLp 2 (fun i => |u i|)‖ = ‖WithLp.toLp 2 u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, abs_abs]

/-- The product with a matrix is bounded by its operator norm. -/
theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ := by
  simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)

/-- The Euclidean norm of a sum is at most the sum of the norms. -/
theorem norm_toLp_add_le {n : ℕ} (u v : Fin n → ℝ) :
    ‖WithLp.toLp 2 (u + v)‖ ≤ ‖WithLp.toLp 2 u‖ + ‖WithLp.toLp 2 v‖ := by
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

/-- The Euclidean norm of a multiple. -/
theorem norm_toLp_smul {n : ℕ} (a : ℝ) (u : Fin n → ℝ) :
    ‖WithLp.toLp 2 (a • u)‖ = |a| * ‖WithLp.toLp 2 u‖ := by
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-! ### One step -/

/-- The error of the update is bounded in norm: entrywise errors
$e (\lvert x_i \rvert + \lvert a y_i \rvert)$ have norm at most
$e (\lVert x \rVert + \lvert a \rvert \lVert y \rVert)$. -/
theorem norm_axpy_err_le {n : ℕ} {e a : ℝ} (he : 0 ≤ e) {x y z : Fin n → ℝ}
    (hz : ∀ i, |z i - (x i + a * y i)| ≤ e * (|x i| + |a * y i|)) :
    ‖WithLp.toLp 2 (z - (x + a • y))‖ ≤
      e * (‖WithLp.toLp 2 x‖ + |a| * ‖WithLp.toLp 2 y‖) := by
  have h₁ : ‖WithLp.toLp 2 (z - (x + a • y))‖ ≤
      ‖WithLp.toLp 2 (e • ((fun i => |x i|) + |a| • fun i => |y i|) : Fin n → ℝ)‖ := by
    refine norm_toLp_le fun i => ?_
    have := hz i
    rw [abs_mul] at this
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  refine h₁.trans ?_
  rw [norm_toLp_smul, abs_of_nonneg he]
  refine mul_le_mul_of_nonneg_left ?_ he
  refine (norm_toLp_add_le _ _).trans ?_
  rw [norm_toLp_smul, norm_toLp_abs, norm_toLp_abs, abs_abs]

/-- The step bound: from a product accurate to $\delta$ and an update accurate to $e$, one
step computes $G x$, $G = I + a A$, up to $\eta \lVert x \rVert$. -/
theorem step_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {δ e a : ℝ} (he : 0 ≤ e)
    {x y z : Fin n → ℝ} (hy : ‖WithLp.toLp 2 (A *ᵥ x - y)‖ ≤ δ * ‖WithLp.toLp 2 x‖)
    (hz : ∀ i, |z i - (x i + a * y i)| ≤ e * (|x i| + |a * y i|)) :
    ‖WithLp.toLp 2 (z - (1 + a • A) *ᵥ x)‖ ≤ myEta A δ e a * ‖WithLp.toLp 2 x‖ := by
  have hsplit : z - (1 + a • A) *ᵥ x = (z - (x + a • y)) + a • (y - A *ᵥ x) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hAx := norm_mulVec_le A x
  have hny : ‖WithLp.toLp 2 y‖ ≤ (‖A‖ + δ) * ‖WithLp.toLp 2 x‖ := by
    have hy' : y = A *ᵥ x + -(A *ᵥ x - y) := by abel
    rw [hy']
    refine (norm_toLp_add_le _ _).trans ?_
    rw [WithLp.toLp_neg, norm_neg]
    linarith
  have hyx : ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ≤ δ * ‖WithLp.toLp 2 x‖ := by
    rw [WithLp.toLp_sub, norm_sub_rev, ← WithLp.toLp_sub]
    exact hy
  rw [hsplit]
  refine (norm_toLp_add_le _ _).trans ?_
  rw [norm_toLp_smul]
  have h₁ := norm_axpy_err_le he hz
  have ha := abs_nonneg a
  have hx := norm_nonneg (WithLp.toLp 2 x)
  have h₂ : |a| * ‖WithLp.toLp 2 y‖ ≤ |a| * ((‖A‖ + δ) * ‖WithLp.toLp 2 x‖) :=
    mul_le_mul_of_nonneg_left hny ha
  have h₃ : |a| * ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ≤ |a| * (δ * ‖WithLp.toLp 2 x‖) :=
    mul_le_mul_of_nonneg_left hyx ha
  have h₄ : e * (‖WithLp.toLp 2 x‖ + |a| * ‖WithLp.toLp 2 y‖) ≤
      e * (‖WithLp.toLp 2 x‖ + |a| * ((‖A‖ + δ) * ‖WithLp.toLp 2 x‖)) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl h₂) he
  unfold myEta
  nlinarith

/-- One step computes $G x$, $G = I + h A$, up to $\eta \lVert x \rVert$. -/
noncomputable def myStepSpec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) :
    Routine.Spec ℝ :=
  spec% [n] ([h], x) → (z) ensures
    ‖WithLp.toLp 2 (decv id n z - (1 + h • A n) *ᵥ decv id n x)‖ ≤
      myEta (A n) δ e h * ‖WithLp.toLp 2 (decv id n x)‖

/-- One step meets its specification, from the two contracts. -/
theorem myStep_meets (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (he : 0 ≤ e)
    {I : Interp MyOperation Empty ℝ}
    (hmatvec : I.Satisfies .total .matvec ((myMatvecRel A δ).spec (OutApart fun _ => True)))
    (haxpy : I.Satisfies .total .axpy ((myAxpyRel e).spec (InPlace fun _ => True))) :
    myStep.Meets I (myStepSpec A δ e) := by
  routine_intro [n] (h, X) reads (hs, xs)
  refine writes_alloc rfl fun s₁ hs₁ hY hbelow => ?_
  step hmatvec as m₁ hfr₁ ⟨hpos₁, y, hy, hrel₁⟩
  step haxpy as m₂ hfr₂ ⟨hpos₂, z, hz, hrel₂⟩
  intro s₂ hs₂ hbelow₂
  obtain ⟨a, -, rfl⟩ := Store.readBlock_one_eq_some.mp hhs
  have hz₂ : s₂.readBlock X.1 X.2 n = some z := by keep
  routine_exit
  change ‖WithLp.toLp 2 (decv id n z - (1 + a • A n) *ᵥ decv id n xs)‖ ≤
    myEta (A n) δ e a * ‖WithLp.toLp 2 (decv id n xs)‖
  refine step_bound (A n) he (y := decv id n y) hrel₁ fun i => ?_
  exact hrel₂ i i.isLt


/-! ### N steps -/

/-- The error of one step is nonnegative. -/
theorem myEta_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {δ e : ℝ} (hδ : 0 ≤ δ)
    (he : 0 ≤ e) (h : ℝ) : 0 ≤ myEta A δ e h := by
  unfold myEta
  have := norm_nonneg A
  positivity

/-- One more step of the induction: if $x_i$ is within
$((g + \eta)^i - g^i) \lVert x_0 \rVert$ of $G^i x_0$ and has norm at most
$(g + \eta)^i \lVert x_0 \rVert$, and $z$ is $G x_i$ up to $\eta \lVert x_i \rVert$, then the
same holds for $z$ at $i + 1$. -/
theorem iterate_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) {η : ℝ} (hη : 0 ≤ η)
    {x₀ x z : Fin n → ℝ} {i : ℕ}
    (hx : ‖WithLp.toLp 2 (x - (G ^ i) *ᵥ x₀)‖ ≤
      ((‖G‖ + η) ^ i - ‖G‖ ^ i) * ‖WithLp.toLp 2 x₀‖)
    (hnx : ‖WithLp.toLp 2 x‖ ≤ (‖G‖ + η) ^ i * ‖WithLp.toLp 2 x₀‖)
    (hz : ‖WithLp.toLp 2 (z - G *ᵥ x)‖ ≤ η * ‖WithLp.toLp 2 x‖) :
    ‖WithLp.toLp 2 (z - (G ^ (i + 1)) *ᵥ x₀)‖ ≤
        ((‖G‖ + η) ^ (i + 1) - ‖G‖ ^ (i + 1)) * ‖WithLp.toLp 2 x₀‖ ∧
      ‖WithLp.toLp 2 z‖ ≤ (‖G‖ + η) ^ (i + 1) * ‖WithLp.toLp 2 x₀‖ := by
  have hg := norm_nonneg G
  have hsplit : z - (G ^ (i + 1)) *ᵥ x₀ = (z - G *ᵥ x) + G *ᵥ (x - (G ^ i) *ᵥ x₀) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel
  have hGx := norm_mulVec_le G (x - (G ^ i) *ᵥ x₀)
  have hGx' := norm_mulVec_le G x
  have hz' : z = (z - G *ᵥ x) + G *ᵥ x := by abel
  constructor
  · rw [hsplit]
    refine (norm_toLp_add_le _ _).trans ?_
    have h₁ := mul_le_mul_of_nonneg_left hx hg
    have h₂ := mul_le_mul_of_nonneg_left hnx hη
    calc _ ≤ η * ‖WithLp.toLp 2 x‖ + ‖G‖ * ‖WithLp.toLp 2 (x - (G ^ i) *ᵥ x₀)‖ :=
          add_le_add hz hGx
      _ ≤ η * ((‖G‖ + η) ^ i * ‖WithLp.toLp 2 x₀‖) +
          ‖G‖ * (((‖G‖ + η) ^ i - ‖G‖ ^ i) * ‖WithLp.toLp 2 x₀‖) := add_le_add h₂ h₁
      _ = _ := by ring
  · rw [hz']
    refine (norm_toLp_add_le _ _).trans ?_
    have h₂ := mul_le_mul_of_nonneg_left hnx (add_nonneg hg hη)
    calc _ ≤ η * ‖WithLp.toLp 2 x‖ + ‖G‖ * ‖WithLp.toLp 2 x‖ := add_le_add hz hGx'
      _ = (‖G‖ + η) * ‖WithLp.toLp 2 x‖ := by ring
      _ ≤ (‖G‖ + η) * ((‖G‖ + η) ^ i * ‖WithLp.toLp 2 x₀‖) := h₂
      _ = _ := by ring

/-- After $N$ steps the vector is $G^N x_0$ up to
$((g + \eta)^N - g^N) \lVert x_0 \rVert$, $g = \lVert G \rVert$. -/
noncomputable def myIntegrateSpec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) :
    Routine.Spec ℝ :=
  spec% [n, N] ([h], x₀) → (xT) ensures
    ‖WithLp.toLp 2 (decv id n xT - ((1 + h • A n) ^ N) *ᵥ decv id n x₀)‖ ≤
      ((‖1 + h • A n‖ + myEta (A n) δ e h) ^ N - ‖1 + h • A n‖ ^ N) *
        ‖WithLp.toLp 2 (decv id n x₀)‖

/-- The postcondition of the integrator, unfolded. -/
theorem myIntegrateSpec_post {A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ} {δ e : ℝ} {n N : ℕ}
    {ω : Tape ℝ} {a : ℝ} {x₀ xT : List ℝ} :
    (myIntegrateSpec A δ e).post [n, N] ω [[a], x₀] [xT] ↔
      ‖WithLp.toLp 2 (decv id n xT - ((1 + a • A n) ^ N) *ᵥ decv id n x₀)‖ ≤
        ((‖1 + a • A n‖ + myEta (A n) δ e a) ^ N - ‖1 + a • A n‖ ^ N) *
          ‖WithLp.toLp 2 (decv id n x₀)‖ :=
  Iff.rfl

/-- The integrator meets its specification, from the two contracts. Each round calls the
judgment of the step; the tree of the step is not inspected. The norm of a matrix is the
operator norm for the Euclidean norm (`Matrix.Norms.L2Operator`). -/
theorem myIntegrate_meets (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (hδ : 0 ≤ δ)
    (he : 0 ≤ e) {I : Interp MyOperation Empty ℝ}
    (hmatvec : I.Satisfies .total .matvec ((myMatvecRel A δ).spec (OutApart fun _ => True)))
    (haxpy : I.Satisfies .total .axpy ((myAxpyRel e).spec (InPlace fun _ => True))) :
    myIntegrate.Meets I (myIntegrateSpec A δ e) := by
  routine_intro [n, N] (h, X) reads (hs, xs)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hhs
  have hstep := myStep_meets A δ e he hmatvec haxpy
  set G := 1 + a • A n
  have hη := myEta_nonneg (A n) hδ he a
  loop_inv (fun _ => Fp.blocks [X] [n])
    (fun i m' => m'.pos = m.pos ∧ ∃ x, m'.store.readBlock X.1 X.2 n = some x ∧
      ‖WithLp.toLp 2 (decv id n x - (G ^ i) *ᵥ decv id n xs)‖ ≤
        ((‖G‖ + myEta (A n) δ e a) ^ i - ‖G‖ ^ i) * ‖WithLp.toLp 2 (decv id n xs)‖ ∧
      ‖WithLp.toLp 2 (decv id n x)‖ ≤
        (‖G‖ + myEta (A n) δ e a) ^ i * ‖WithLp.toLp 2 (decv id n xs)‖)
    with i hi m₁ hfr hP
  case round =>
    obtain ⟨hpos₁, x, hx, hbound, hnorm⟩ := hP
    have hh₁ : m₁.store.readBlock h.1 h.2 1 = some [a] := by keep
    call hstep [n] (h, X) as m₂ hfr₂ hpos₂ (zs) hpost
    have hz : ‖WithLp.toLp 2 (decv id n zs - G *ᵥ decv id n x)‖ ≤
        myEta (A n) δ e a * ‖WithLp.toLp 2 (decv id n x)‖ := hpost
    exact ⟨hpos₂.trans hpos₁, zs, hzs, iterate_bound G hη hbound hnorm hz⟩
  case initial =>
    exact ⟨rfl, xs, hxs, by simp, by simp⟩
  case exit =>
    rintro m₁ - ⟨hpos₁, x, hx, hbound, -⟩
    exact ⟨hpos₁, [x], Mem.readBlocks_of_cons hx rfl, hbound⟩


/-! ### The problem, the resources and the model -/

/-- The admitted inputs of the integrator: at every size `n = d 0`, `N = d 1`, every step `h`
(one cell) and every initial vector $x_0$ ($n$ cells), each held by its operand. -/
def myDomain : myIntegrate.Domain ℝ 2 2 where
  valid _ := True
  In d := ℝ × (Fin (d 0) → ℝ)
  accepts _ _ := True
  slot d := ![.stored Codec.scalar Prod.fst, .stored (Codec.vector (d 0)) Prod.snd]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext (Codec.scalar.encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(0, fun _ => 0), trivial⟩

/-- The problem of the integrator: the step and the initial vector, and nothing else. Every
step and every vector is admitted (`NLAlib.Ops.Routine.Domain.covers`). -/
def myProblem : Problem ℝ 2 2 := myDomain.problem

/-- The weight of a call: $2 n^2$ for a product, $2 n$ for an update. -/
def myWork : MyOperation → List ℕ → ℕ
  | .matvec, d => 2 * d.headD 0 ^ 2
  | .axpy, d => 2 * d.headD 0

/-- Calls weighed by `myWork`, structural instructions by one, no workspace. -/
def myResources : ResourceModel MyOperation Empty where
  formats := [.cell]
  operation
    | .matvec => ⟨[.cell], [.cell]⟩
    | .axpy => ⟨[.cell, .cell, .cell], [.cell]⟩
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := 0
  queryWorkspace q := nomatch q
  operationWork := myWork
  operationSpan := myWork
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- The exact product, as a block function. -/
noncomputable def myExactMatvec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) : BlockFn ℝ where
  nd := 2
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  fn d _ X := match X with
    | [x] => some [List.ofFn (A (d.headD 0) *ᵥ decv id (d.headD 0) x)]
    | _ => none

/-- The exact update, as a block function. -/
def myExactAxpy : BlockFn ℝ where
  nd := 1
  inLens d := [1, d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  fn d _ X := match X with
    | [[a], x, y] => some [List.ofFn fun i : Fin (d.headD 0) => vec y i + a * vec x i]
    | _ => none

/-- The exact product and the exact update. -/
noncomputable def myExact (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) :
    MyOperation → BlockFn ℝ
  | .matvec => myExactMatvec A
  | .axpy => myExactAxpy

/-- The entry of a list of a vector's entries. -/
theorem vec_ofFn {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : vec (List.ofFn f) i = f i := by
  simp [vec, List.getD_eq_getElem?_getD]

/-- An interpretation whose operation `o` is the exact product satisfies the contract of
`matvec` at `o`, for every allowance $\delta \ge 0$. -/
theorem myExactMatvec_satisfies {Op Tst : Type} (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (F : Op → BlockFn ℝ) (o : Op) (hF : F o = myExactMatvec A) :
    (Interp.ofFns F : Interp Op Tst ℝ).Satisfies .total o
      ((myMatvecRel A δ).spec (OutApart fun _ => True)) := by
  have h := Interp.ofFns_isFn (Tst := Tst) F .total o (fun _ _ _ => True)
  rw [hF] at h
  refine h.satisfies_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) ?_
  intro d w X m ins outs _ _ _ hX _
  obtain ⟨x', x, -, hx, rfl⟩ := Mem.readBlocks_one hX
  refine ⟨[List.ofFn (A (d.headD 0) *ᵥ decv id (d.headD 0) x)], rfl, by simp, ?_⟩
  change ‖WithLp.toLp 2 (A _ *ᵥ decv id _ x - decv id _ (List.ofFn _))‖ ≤ _
  rw [decv_ofFn, sub_self, WithLp.toLp_zero, norm_zero]
  exact mul_nonneg hδ (norm_nonneg _)

/-- The exact product satisfies the contract of `matvec`, for every allowance $\delta \ge 0$. -/
theorem myExact_matvec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Interp.ofFns (myExact A) : Interp MyOperation Empty ℝ).Satisfies .total .matvec
      ((myMatvecRel A δ).spec (OutApart fun _ => True)) :=
  myExactMatvec_satisfies A hδ (myExact A) .matvec rfl

/-- The exact update satisfies the contract of `axpy`, for every allowance $e \ge 0$. -/
theorem myExact_axpy (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) {e : ℝ} (he : 0 ≤ e) :
    (Interp.ofFns (myExact A) : Interp MyOperation Empty ℝ).Satisfies .total .axpy
      ((myAxpyRel e).spec (InPlace fun _ => True)) := by
  refine (Interp.ofFns_isFn (myExact A) .total .axpy (fun _ _ _ => True)).satisfies_rel
    (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w X m ins outs _ _ _ hX _
  obtain ⟨al, x, y, as, xs, ys, -, ha, -, -, rfl⟩ := Mem.readBlocks_three hX
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  refine ⟨[List.ofFn fun i : Fin (d.headD 0) => vec ys i + a * vec xs i], rfl, by simp,
    fun i hi => ?_⟩
  rw [show vec (List.ofFn fun i : Fin (d.headD 0) => vec ys i + a * vec xs i) i =
      vec ys i + a * vec xs i from vec_ofFn (fun i : Fin (d.headD 0) => vec ys i + a * vec xs i)
        ⟨i, hi⟩, sub_self, abs_zero]
  positivity

/-- The model: the two contracts, the weights of `myResources`, and the witness that the
exact operations satisfy the contracts, so that the contracts are not contradictory. -/
noncomputable def myModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ)
    (hδ : 0 ≤ δ) (he : 0 ≤ e) : AccessModel MyOperation Empty myProblem where
  word := 0
  operation _ _
    | .matvec => (myMatvecRel A δ).spec (OutApart fun _ => True)
    | .axpy => (myAxpyRel e).spec (InPlace fun _ => True)
  query _ _ q := nomatch q
  resources := myResources
  realize _ _ _ := ⟨Interp.ofFns (myExact A), fun o => by
    cases o
    · exact myExact_matvec A hδ
    · exact myExact_axpy A he, fun q => nomatch q⟩

/-- Every contract of the model is in operand form: the model is confined. -/
instance confined_myModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (hδ : 0 ≤ δ)
    (he : 0 ≤ e) : (myModel A δ e hδ he).Confined :=
  ⟨fun _ _ o => by cases o <;> exact BlockRel.confined_spec _ _, fun _ _ q => nomatch q⟩

/-- The contracts depend on the parameters $A$, $\delta$ and $e$ of the model, not on the size
or the input: the model is uniform. -/
instance uniform_myModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (hδ : 0 ≤ δ)
    (he : 0 ≤ e) : (myModel A δ e hδ he).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ q => nomatch q⟩

/-- The model is not charged: an update of length $0$ weighs nothing. -/
theorem not_charged_myModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (hδ : 0 ≤ δ)
    (he : 0 ≤ e) : ¬ (myModel A δ e hδ he).Charged :=
  fun h => lt_irrefl 0 (h.operation .axpy [])

/-! ### The program, its count and its scratch -/

/-- The program: the integrator on the supplied buffers, `n` and `N` as its dimensions. -/
def myProgram : Program MyOperation Empty 2 2 := myIntegrate.close 2 2

/-- The calls of the tree: $N$ products at $[n, n]$ and $N$ updates at $[n]$, and no other
operation. Structural instructions are set aside by `Count.original`. -/
theorem myProgram_calls (d : Fin 2 → ℕ) :
    Count.original (staticCost myProgram d) =
      d 1 • (Count.one MyOperation.matvec [d 0, d 0] + Count.one MyOperation.axpy [d 0]) := by
  rw [staticCost, original_stmtCost_instrument]
  simp [myProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, myIntegrate,
    myStep, Program.environment, List.ofFn_succ, Routine.closeDims, Routine.closeOps,
    List.range_succ, stmtCost, useCost, IExp.evalList, IExp.eval, Finset.sum_const]

/-- The scratch of the tree: at most the $n$ cells of `Y`, reused by every round (none when
$N = 0$, since the loop then never allocates). -/
theorem myProgram_peak (d : Fin 2 → ℕ) : staticPeak myResources myProgram d ≤ d 0 := by
  rw [staticPeak, myResources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
  simp [myProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, myIntegrate,
    myStep, Program.environment, List.ofFn_succ, Routine.closeDims, Routine.closeOps,
    List.range_succ, stmtPeak_tally, Stmt.instrument, indexBookkeeping, operandBookkeeping,
    stmtPeak, myResources, instrumentWorkspace, IExp.evalList, IExp.eval]

/-- The work of the tree: $N$ products weighing $2 n^2$, $N$ updates weighing $2 n$, $28$
structural instructions in each round and $11$ outside the loop. -/
def myProgramWork (d : Fin 2 → ℕ) : ℕ := 2 * d 1 * d 0 ^ 2 + 2 * d 1 * d 0 + 28 * d 1 + 11

/-- The weighted count of the tree is `myProgramWork`. -/
theorem work_myProgram (d : Fin 2 → ℕ) :
    myResources.work (staticCost myProgram d) = myProgramWork d := by
  rw [staticCost]
  simp [myProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, myIntegrate,
    myStep, Program.environment, List.ofFn_succ, Routine.closeDims, Routine.closeOps,
    List.range_succ, stmtCost, useCost, IExp.evalList, IExp.eval, Stmt.instrument,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, ResourceModel.work, myResources, myWork,
    lift_stmtCost_tally, myProgramWork]
  ring

/-- Calls run one after another, so the span of the tree is its work. -/
theorem span_myProgram (d : Fin 2 → ℕ) :
    myResources.span (staticCost myProgram d) = myProgramWork d := by
  rw [staticCost]
  simp [myProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, myIntegrate,
    myStep, Program.environment, List.ofFn_succ, Routine.closeDims, Routine.closeOps,
    List.range_succ, stmtCost, useCost, IExp.evalList, IExp.eval, Stmt.instrument,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, ResourceModel.span, myResources, myWork,
    lift_stmtCost_tally, myProgramWork]
  ring


/-- The accuracy claim: the buffer `X` holds $x_T$ within
$((g + \eta)^N - g^N) \lVert x_0 \rVert$ of $G^N x_0$, $G = I + h A$, $g = \lVert G \rVert$. -/
def myGood (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) (d : Fin 2 → ℕ)
    (x : myProblem.Input d) (μ : Mem ℝ) : Prop :=
  ∃ xT, μ.store.readBlock 1 0 (d 0) = some xT ∧
    let G := 1 + x.val.1.1 • A (d 0)
    ‖WithLp.toLp 2 (decv id (d 0) xT - (G ^ d 1) *ᵥ x.val.1.2)‖ ≤
      ((‖G‖ + myEta (A (d 0)) δ e x.val.1.1) ^ d 1 - ‖G‖ ^ d 1) * ‖WithLp.toLp 2 x.val.1.2‖

/-- The claims: the accuracy of `myGood`; the count of the tree as the budget, and in closed
form its work and span (`myProgramWork`), its scratch ($n$ cells) and its memory (the scratch and
the $1 + n$ input cells). -/
noncomputable def mySpec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ) :
    Specification MyOperation Empty myProblem where
  good d x _ _ μ := myGood A δ e d x μ
  budget := staticCost myProgram
  work := myProgramWork
  span := myProgramWork
  scratch d := d 0
  memory d := 1 + 2 * d 0

/-- The blocks the integrator reads: `h` and $x_0$. -/
def myBlocks (d : Fin 2 → ℕ) (x : myProblem.Input d) : List (List ℝ) :=
  myDomain.blocks d x.val.1

/-- The blocks read are the step and the vector, as lists. -/
theorem myBlocks_eq (d : Fin 2 → ℕ) (x : myProblem.Input d) :
    myBlocks d x = [[x.val.1.1], List.ofFn x.val.1.2] := rfl

/-- The input occupies $1 + n$ cells. -/
theorem initialBytes_myProblem (d : Fin 2 → ℕ) (x : myProblem.Input d) :
    myProblem.initialBytes d x = 1 + d 0 := by
  refine (myDomain.initialBytes_eq x).trans ?_
  simp [myDomain, Slot.len, Codec.vector, Codec.scalar, List.ofFn_succ]

/-- The certificate, from the judgment of the integrator. -/
noncomputable def myAlgorithm (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ)
    (hδ : 0 ≤ δ) (he : 0 ≤ e) :
    Algorithm (myModel A δ e hδ he) (mySpec A δ e) :=
  myDomain.algorithm (fun _ _ => myIntegrateSpec A δ e)
    (fun _ _ _ _ hI => myIntegrate_meets A δ e hδ he (hI.1 .matvec) (hI.1 .axpy))
    (fun _ _ _ _ _ => trivial)
    (fun d _ x τ m' _ _ ys hys hpost c _ => by
      read_outputs hys as (zs)
      refine ⟨zs, hzs, ?_⟩
      have h := (myIntegrateSpec_post (n := d 0) (N := d 1) (a := x.val.1.1)
        (x₀ := List.ofFn x.val.1.2)).mp hpost
      rw [decv_ofFn] at h
      exact h)
    (fun _ _ => le_rfl) (fun d _ => myProgram_peak d) (fun d _ => (work_myProgram d).le)
    (fun d _ => (span_myProgram d).le)
    (fun d _ x => by
      refine (Nat.add_le_add_right (initialBytes_myProblem d x).le _).trans ?_
      change 1 + d 0 + d 0 ≤ 1 + 2 * d 0
      omega)

/-- The certificate of the integrator: for every size, input and implementation that
satisfies the contracts, the program runs to completion, within the count and the scratch of
its tree, with work and span at most `myProgramWork`, scratch at most $n$ cells, and leaves in
`X` a vector within the stated bound of $G^N x_0$. -/
theorem myProgram_certifies (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ)
    (hδ : 0 ≤ δ) (he : 0 ≤ e) :
    myProgram.Certifies (myModel A δ e hδ he) (mySpec A δ e) :=
  (myAlgorithm A δ e hδ he).correct


/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work and the span of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). Every step size and vector is admitted. -/
theorem myIntegrate_checked (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ e : ℝ)
    (hδ : 0 ≤ δ) (he : 0 ≤ e) : myDomain.Checked (myAlgorithm A δ e hδ he) :=
  myDomain.checked_all _

end NLAlib.Ops.Examples.Integrator
