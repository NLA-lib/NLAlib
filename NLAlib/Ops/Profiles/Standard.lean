/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.BlasCert
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Compare

/-!
# Named standard operation models

Exact, sequential rounded BLAS and pairwise rounded BLAS share a closed scalar/BLAS/matvec
signature. Every contract is declared individually. Joint realizability follows from a native
scalar/matvec/comparison witness and the proved BLAS profile, rather than an arbitrary extra
interpreter predicate. Comparison queries cannot be used as index conversions.

Resource weights remain explicit model choices. Unit operations and length-weighted BLAS
configurations are provided; both have sequential span. Pairwise arithmetic alone is not a
parallel scheduler. Supplied resident data belong in the problem's initial buffers.

## Main results

* `NLAlib.Ops.Standard.Scheme`: the three standard numerical choices.
* `NLAlib.Ops.Standard.Model.access`: a jointly realized closed operation model.
* `NLAlib.Ops.Standard.Model.laws`: derive the numerical operation interfaces from contracts.
-/

@[expose] public section

namespace NLAlib.Ops.Standard

/-- The closed operation signature for the standard Krylov models. -/
inductive Operation where
  /-- Scalar arithmetic. -/
  | scalar (op : ScalarOp)
  /-- Level-one vector operations. -/
  | blas (op : Blas1Op)
  /-- Matrix-vector operations. -/
  | matvec
  deriving DecidableEq

/-- The scalar group of the closed signature. -/
instance : Has ScalarOp Operation where
  inj := .scalar
  proj := fun o => match o with | .scalar a => some a | _ => none
  proj_inj _ := rfl
  inj_of_proj o a h := by
    cases o with
    | scalar b => exact congrArg Operation.scalar (Option.some.inj h).symm
    | blas _ => cases h
    | matvec => cases h

/-- The BLAS group of the closed signature. -/
instance : Has Blas1Op Operation where
  inj := .blas
  proj := fun o => match o with | .blas a => some a | _ => none
  proj_inj _ := rfl
  inj_of_proj o a h := by
    cases o with
    | blas b => exact congrArg Operation.blas (Option.some.inj h).symm
    | scalar _ => cases h
    | matvec => cases h

/-- The matvec group of the closed signature. -/
instance : Has OperatorOp Operation where
  inj := fun .matvec => .matvec
  proj := fun o => match o with | .matvec => some .matvec | _ => none
  proj_inj o := by cases o; rfl
  inj_of_proj o a h := by
    cases a
    cases o with
    | matvec => rfl
    | scalar _ => cases h
    | blas _ => cases h

/-- BLAS names cannot be scalar names. -/
instance : Apart Blas1Op ScalarOp Operation := ⟨fun _ => rfl⟩

/-- BLAS names cannot be matvec names. -/
instance : Apart Blas1Op OperatorOp Operation := ⟨fun _ => rfl⟩

/-- Exact arithmetic, sequential rounded summation, or pairwise summation at a fixed depth. -/
inductive Scheme where
  /-- Zero unit roundoff. -/
  | exact
  /-- Standard scalar arithmetic and sequential BLAS reductions. -/
  | sequential
  /-- Standard scalar arithmetic and pairwise reductions within the recursion depth. -/
  | pairwise (depth : ℕ)

/-- The exact model sets the unit roundoff to zero. Other choices retain the supplied value. -/
def Scheme.roundoff (s : Scheme) (u : ℝ) : ℝ := match s with
  | .exact => 0
  | _ => u

/-- The existing proved BLAS profile selected by a standard numerical choice. -/
noncomputable def Scheme.profile (s : Scheme) : Profile Operation Operation CmpTst :=
  match s with
  | .exact | .sequential => Blas.seq
  | .pairwise k => Blas.pairwise k

/-- Numerical BLAS error constants derived from the selected implementation. -/
def Scheme.errors (s : Scheme) (u : ℝ) : Blas1Err := match s with
  | .exact | .sequential => Blas.seq.err (s.roundoff u)
  | .pairwise _ => Blas.pairwise.err (s.roundoff u)

/-- Pairwise reduction is admitted precisely within its fixed recursion depth. -/
def Scheme.admits (s : Scheme) (n : ℕ) : Prop := match s with
  | .exact | .sequential => True
  | .pairwise k => Nat.clog 2 n < k

/-- Every selected profile supplies its own scalar and BLAS contracts. -/
theorem Scheme.certifies {K : Type} [Inhabited K] (s : Scheme) {M : Machine K}
    {dec : K → ℝ} {u : ℝ} (hM : StdModel (s.roundoff u) dec M) (hu : 0 ≤ u) :
    s.profile.Refines (fun I => IsScalar M I)
      (fun J => IsScalar M J ∧ IsBlas1 dec (s.errors u) s.admits J) := by
  cases s with
  | exact => exact Blas.seq_certifies hM le_rfl (fun _ => True)
  | sequential => exact Blas.seq_certifies hM hu (fun _ => True)
  | pairwise k => exact Blas.pairwise_certifies hM hu k

/-- The selected BLAS implementation preserves the supplied matvec primitive. -/
theorem Scheme.table_matvec (s : Scheme) :
    s.profile.table (Has.inj OperatorOp.matvec) = .inr (Has.inj OperatorOp.matvec) := by
  cases s with
  | exact | sequential => exact Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)
  | pairwise k => exact Blas.pairwise_table_kept k (Apart.proj_inj OperatorOp.matvec)

/-- Nonnegative numerical allowances of every standard scheme. -/
theorem Scheme.errors_nonneg (s : Scheme) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ s.roundoff u ∧ 0 ≤ (s.errors u).dot n ∧
      0 ≤ (s.errors u).axpy ∧ 0 ≤ (s.errors u).scal := by
  cases s with
  | exact => simp [Scheme.roundoff, Scheme.errors, Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
  | sequential =>
    have hs := Blas.seqSumErr_nonneg hu n
    dsimp [Scheme.roundoff, Scheme.errors, Blas.seq.err, Blas.level1Err]
    exact ⟨hu, by nlinarith [mul_nonneg hu hs], by nlinarith, hu⟩
  | pairwise k =>
    have hs := Blas.pairSumErr_nonneg hu n
    dsimp [Scheme.roundoff, Scheme.errors, Blas.pairwise.err, Blas.level1Err]
    exact ⟨hu, by nlinarith [mul_nonneg hu hs], by nlinarith, hu⟩

/-- A simple common accuracy envelope sufficient for both CG and Lanczos operation budgets.
The stricter scalar/dot/division margins discharge Lanczos normalization automatically. -/
structure Accuracy (em u E : ℝ) (errors : Blas1Err) (n : ℕ) : Prop where
  /-- Nonnegative common allowance. -/
  nonneg : 0 ≤ E
  /-- Existing finite-precision run interfaces require a small local allowance. -/
  small : E ≤ 1 / 100
  /-- Rounded matvec contribution. -/
  matvec : em ≤ E
  /-- Scalar arithmetic contribution. -/
  scalar : u ≤ E / 16
  /-- Dot-product contribution at the actual vector length. -/
  dot : errors.dot n ≤ E / 16
  /-- Vector update contribution. -/
  axpy : errors.axpy ≤ E
  /-- Division contribution. -/
  scal : errors.scal ≤ E / 16

/-- Standard models may charge one per primitive call or work proportional to vector length. -/
inductive Costing where
  /-- One abstract unit per scalar or BLAS call; matvec work remains explicit. -/
  | unit
  /-- Length-weighted BLAS work; matvec work remains an explicit supplied function. -/
  | lengthWeighted

/-- Declared vector-operation work, distinct from the full program's structural bookkeeping. -/
def Costing.blasWork (c : Costing) (o : Blas1Op) (d : List ℕ) : ℕ :=
  match c with
  | .unit => 1
  | .lengthWeighted =>
    let n := d.headD 0
    match o with
    | .sum => n + 1
    | .dot => 2 * n + 1
    | .axpy => 2 * n
    | .nrm2 => 2 * n + 2
    | .scal | .copy => n

/-- The fixed scalar/BLAS/matvec storage signatures, in abstract cells. -/
def signature : Operation → OperandSignature
  | .scalar (.lit _) => ⟨[], [.cell]⟩
  | .scalar .add | .scalar .sub | .scalar .mul | .scalar .div => ⟨[.cell, .cell], [.cell]⟩
  | .scalar .neg | .scalar .sqrt | .scalar .copy => ⟨[.cell], [.cell]⟩
  | .blas .sum | .blas .nrm2 | .blas .copy | .matvec => ⟨[.cell], [.cell]⟩
  | .blas .dot | .blas .scal => ⟨[.cell, .cell], [.cell]⟩
  | .blas .axpy => ⟨[.cell, .cell, .cell], [.cell]⟩

/-- A named resource configuration with explicit matvec work and scratch reservation. Span is
sequential even for the pairwise scheme. Resident input payload is supplied by Problem. -/
noncomputable def resources (scheme : Scheme) (cost : Costing)
    (matvecWork matvecWorkspace : List ℕ → ℕ) : ResourceModel Operation CmpTst where
  formats := [.cell]
  operation := signature
  testInputs q := q.lens.map (fun _ => .cell)
  indexInputs _ := []
  workspace o d := match o with
    | .matvec => matvecWorkspace d
    | _ => scheme.profile.ws o d
  queryWorkspace _ := 0
  operationWork o d := match o with
    | .scalar _ => 1
    | .blas b => cost.blasWork b d
    | .matvec => matvecWork d
  operationSpan o d := match o with
    | .scalar _ => 1
    | .blas b => cost.blasWork b d
    | .matvec => matvecWork d
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Explicit BLAS contracts selected by operation name. -/
def blasContract {K : Type} [Inhabited K] (dec : K → ℝ) (e : Blas1Err) (ok : ℕ → Prop) :
    Blas1Op → Contract K
  | .sum => (sumRel dec e.sum).spec (OutApart ok)
  | .dot => (dotRel dec e.dot).spec (OutApart ok)
  | .axpy => (axpyRel dec e.axpy).spec (InPlace ok)
  | .nrm2 => (nrm2Rel dec e.dot e.sqrt).spec (OutApart ok)
  | .scal => (scalRel dec e.scal).spec (InPlace ok)
  | .copy => copyRel.spec (OutApart ok)

/-- Standard operation data and its native primitive realization, before BLAS implementation.
Only scalar, matvec and comparison contracts are requested of that native backend. -/
structure Model {K : Type} [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (n : (Fin r → ℕ) → ℕ) where
  /-- Named arithmetic/reduction choice. -/
  scheme : Scheme
  /-- Supplied scalar roundoff. The exact scheme overrides it with zero. -/
  unit : ℝ
  /-- Nonnegative supplied roundoff. -/
  unit_nonneg : 0 ≤ unit
  /-- The fixed scalar machine. -/
  machine : Machine K
  /-- Fixed numerical decoding. -/
  decode : K → ℝ
  /-- Numerical law of the same fixed machine. -/
  scalar : StdModel (scheme.roundoff unit) decode machine
  /-- The operator supplied at each admitted problem instance. -/
  matrix : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ
  /-- Absolute operator-norm error allowance for matvec. -/
  matvecAllowance : (d : Fin r → ℕ) → P.Input d → ℝ
  /-- Nonnegative declared matvec allowance on admitted inputs. -/
  matvec_nonneg : ∀ d, P.valid d → ∀ x : P.Input d, 0 ≤ matvecAllowance d x
  /-- Declared formats, operation weights, workspace and span. -/
  resources : ResourceModel Operation CmpTst
  /-- A joint native witness at every admitted problem input. -/
  native : ∀ d, P.valid d → ∀ x : P.Input d, ∃ I : Interp Operation CmpTst K,
    IsScalar machine I ∧
      IsMatvec decode (matrix d x) (scheme.roundoff (matvecAllowance d x)) I ∧ IsCmp decode I

variable {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b} {n : (Fin r → ℕ) → ℕ}

/-- Build a standard model directly from a fixed scalar machine and word-level matvec kernels.
The backend author proves only the scalar numerical law and the local kernel error bound;
the constructor supplies exact comparisons, memory interfaces and the joint BLAS realization. -/
noncomputable def Model.ofKernels (scheme : Scheme) (u : ℝ) (hu : 0 ≤ u)
    (machine : Machine K) (decode : K → ℝ) (hM : StdModel (scheme.roundoff u) decode machine)
    (matrix : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ)
    (allowance : (d : Fin r → ℕ) → P.Input d → ℝ)
    (ha : ∀ d, P.valid d → ∀ x, 0 ≤ allowance d x)
    (R : ResourceModel Operation CmpTst)
    (kernel : (d : Fin r → ℕ) → P.Input d → (Fin (n d) → K) → Fin (n d) → K)
    (hk : ∀ d, P.valid d → ∀ x (v : Fin (n d) → K),
      ‖WithLp.toLp 2 ((matrix d x).mulVec (fun i => decode (v i)) -
        (fun i => decode (kernel d x v i)))‖ ≤
          scheme.roundoff (allowance d x) * ‖WithLp.toLp 2 (fun i => decode (v i))‖) :
    Model P n where
  scheme := scheme
  unit := u
  unit_nonneg := hu
  machine := machine
  decode := decode
  scalar := hM
  matrix := matrix
  matvecAllowance := allowance
  matvec_nonneg := ha
  resources := R
  native d hd x := by
    let F : Operation → BlockFn K := fun o => match o with
      | .scalar a => machine.fn a
      | .blas _ => BlockFn.const default
      | .matvec => matvecFn (kernel d x)
    let I := { (Interp.ofFns F : Interp Operation CmpTst K) with
      test := fun (q : CmpTst) _ a m => (m.readBlocks a q.lens).map (q.fn decode)
      index := fun _ _ _ => none }
    have hS : IsScalar machine I := isScalar_ofFns (Tst := CmpTst) machine F (fun _ => rfl)
    have hF := Interp.ofFns_isFn (Tst := CmpTst) F .total (.matvec) AnyOperands
    have hA : IsMatvec decode (matrix d x) (scheme.roundoff (allowance d x)) I :=
      hF.meets_matvec_error (hk d hd x)
    refine ⟨I, hS, hA, ?_⟩
    intro q d a m xs hr
    change (m.readBlocks a q.lens).map (q.fn decode) = _
    rw [hr]
    rfl

/-- An explicit idealized reference model with genuinely rounded scalar arithmetic and
matvec: the identity operator returns (1+u) times its input in the rounded schemes.
This witnesses all three model constructors; it is not a native floating-point certificate. -/
noncomputable def referenceModel (P : Problem ℝ r b) (n : (Fin r → ℕ) → ℕ)
    (scheme : Scheme) (u : ℝ) (hu : 0 ≤ u) (cost : Costing)
    (matvecWork matvecWorkspace : List ℕ → ℕ) : Model P n := by
  have ht := (scheme.errors_nonneg hu 0).1
  exact Model.ofKernels scheme u hu (inflMachine (scheme.roundoff u)) id (stdModel_infl ht)
    (fun _ _ => 1) (fun _ _ => u) (fun _ _ _ => hu)
    (resources scheme cost matvecWork matvecWorkspace)
    (fun _ _ v => (1 + scheme.roundoff u) • v) (by
      intro d hd x v
      change ‖WithLp.toLp 2 ((1 : Matrix (Fin (n d)) (Fin (n d)) ℝ).mulVec v -
        (1 + scheme.roundoff u) • v)‖ ≤ scheme.roundoff u * ‖WithLp.toLp 2 v‖
      have hv : v - (1 + scheme.roundoff u) • v = (-scheme.roundoff u) • v := by
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [Matrix.one_mulVec, hv, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg ht])

/-- All permitted operation contracts; there is no escape operation outside this signature. -/
def Model.operation (m : Model P n) (d : Fin r → ℕ) (x : P.Input d) : Operation → Contract K
  | .scalar a => (m.machine.fn a).rel.spec AnyOperands
  | .blas a => blasContract m.decode (m.scheme.errors m.unit) m.scheme.admits a
  | .matvec =>
    (matvecErrorRel m.decode (m.matrix d x) (m.scheme.roundoff (m.matvecAllowance d x))).spec
      (MatvecOperands (n d) (n d))

/-- Exact comparison contracts; comparison names do not supply integer conversions. -/
noncomputable def comparisonContract (dec : K → ℝ) (q : CmpTst) : QueryContract K where
  test _d a m result := ∀ xs, m.readBlocks a q.lens = some xs → result = some (q.fn dec xs)
  index _ _ result := result = none

/-- Every primitive operation and query has a jointly realized declared contract. -/
noncomputable def Model.access (m : Model P n) : AccessModel Operation CmpTst P where
  word := default
  operation := m.operation
  query _ _ := comparisonContract m.decode
  resources := m.resources
  realize d hd x := by
    obtain ⟨I, hS, hA, hC⟩ := m.native d hd x
    obtain ⟨hS', hB⟩ := (m.scheme.certifies m.scalar m.unit_nonneg).meets I hS
    have hA' := Interp.link_meets_kept m.scheme.table_matvec hA
    let J := { I.link m.scheme.profile.table with index := fun _ _ _ => none }
    refine ⟨J, ?_, ?_⟩
    · intro o
      cases o with
      | scalar a => exact hS' a
      | blas a => cases a with
          | sum => exact hB.sum
          | dot => exact hB.dot
          | axpy => exact hB.axpy
          | nrm2 => exact hB.nrm2
          | scal => exact hB.scal
          | copy => exact hB.copy
      | matvec => exact hA'
    · intro q
      exact ⟨fun d a s xs hr => hC q d a s xs hr, fun _ _ => rfl⟩

/-- Solver authors obtain exactly the fixed numerical laws by satisfying the declared model.
No whole-program predicate or extra interpreter-wide assumption is added. -/
theorem Model.laws (m : Model P n) {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation CmpTst K} (h : m.access.contracts d x I) :
    IsScalar m.machine I ∧ IsBlas1 m.decode (m.scheme.errors m.unit) m.scheme.admits I ∧
      IsMatvec m.decode (m.matrix d x) (m.scheme.roundoff (m.matvecAllowance d x)) I ∧
        IsCmp m.decode I := by
  refine ⟨fun a => h.1 (.scalar a), ?_, h.1 (.matvec), ?_⟩
  · exact ⟨h.1 (.blas .sum), h.1 (.blas .dot), h.1 (.blas .axpy),
      h.1 (.blas .nrm2), h.1 (.blas .scal), h.1 (.blas .copy)⟩
  · intro q d a s xs hr
    exact (h.2 q).1 d a s xs hr

/-- A comparison identifier cannot secretly supply an index conversion in a standard model. -/
theorem Model.index_eq_none (m : Model P n) {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation CmpTst K} (h : m.access.contracts d x I)
    (q : CmpTst) (a : List (ℕ × ℕ)) (s : Mem K) : I.index q a s = none :=
  (h.2 q).2 a s

end NLAlib.Ops.Standard
