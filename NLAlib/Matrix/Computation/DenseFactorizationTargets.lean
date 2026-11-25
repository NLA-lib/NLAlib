/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ClosedCountBudget
public import NLAlib.Computation.Model
public import NLAlib.Matrix.Computation.DenseFactorizationResources
public import NLAlib.Matrix.Computation.DenseFactorizationSpace
public import NLAlib.Matrix.Computation.DenseFactorizationResourceTags

/-!
# Stored-entry targets for dense factorizations

These closed real-word programs receive their source entries in declared buffers, with
uninitialized caller output storage and no ROM. Every operation kind has the independent
cubic budget `closedCountBudget`; memory includes caller capacity and scoped workspace.
The pivoted domains include singular matrices, and their postconditions decode the actual
swap logs in the current-position-to-original-position convention.

## Main results

* `StoredEntriesDenseLU`, `StoredEntriesDensePLU`, `StoredEntriesDensePLUQ` and
  `StoredEntriesDenseScaledPLU`: exact LU targets with their respective pivot policies.
* `StoredEntriesDenseCholesky`, `StoredEntriesDenseSemidefiniteCholesky` and
  `StoredEntriesDenseLDL`: exact Cholesky and scalar-pivot LDL targets.
* Each target has a separate `NonVacuous` companion for every lower order bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

namespace DenseFactorizationTarget

/-- A real square input matrix. -/
abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

/-- The concrete real-word state, with no oracle names. -/
abbrev State := St Unit ℝ (OpCount Unit Empty)

/-- All additional size variables are zero offsets; the matrix order is unrestricted. -/
def Valid {r : ℕ} (_N : ℕ) (n : Fin r → ℕ) : Prop := ∀ j, n j = 0

/-- Input-only nonbreakdown domain for unpivoted LU. -/
def LUInput (N : ℕ) (_n : Fin 3 → ℕ) :=
  {A : Mat N // ∀ k : Fin N, gaussState A k k k ≠ 0}

/-- Arbitrary matrices for the row-pivoted and fixed-scale drivers. -/
def PLUInput (N : ℕ) (_n : Fin 4 → ℕ) := Mat N

/-- Arbitrary matrices for the independently row/column-pivoted driver. -/
def PLUQInput (N : ℕ) (_n : Fin 5 → ℕ) := Mat N

/-- Input-only positive-definite domain. -/
def SPDInput (N : ℕ) (_n : Fin 2 → ℕ) := {A : Mat N // A.PosDef}

/-- Input-only positive-semidefinite domain, including singular matrices. -/
def PSDInput (N : ℕ) (_n : Fin 2 → ℕ) := {A : Mat N // A.PosSemidef}

/-- Input-only Hermitian nonbreakdown domain for scalar LDL. -/
def LDLInput (N : ℕ) (_n : Fin 3 → ℕ) :=
  {A : Mat N // A.IsHermitian ∧ ∀ k : Fin N, gaussState A k k k ≠ 0}

/-- Caller arrays for unpivoted LU: source, lower factor, upper factor. -/
noncomputable def luInputs (N : ℕ) (n : Fin 3 → ℕ) (x : LUInput N n) : Fin 3 → Array (Option ℝ) :=
  ![(flatten x.val).map some, Array.replicate (N * N) none, Array.replicate (N * N) none]

/-- Caller arrays for partial or fixed-scale pivoting: source, factors and actual row log. -/
noncomputable def pluInputs (N : ℕ) (n : Fin 4 → ℕ) (A : PLUInput N n) : Fin 4 → Array (Option ℝ) :=
  ![(flatten A).map some, Array.replicate (N * N) none,
    Array.replicate (N * N) none, Array.replicate N none]

/-- Caller arrays for complete pivoting: source, factors and two independent logs. -/
noncomputable def pluqInputs (N : ℕ) (n : Fin 5 → ℕ) (A : PLUQInput N n) :
    Fin 5 → Array (Option ℝ) :=
  ![(flatten A).map some, Array.replicate (N * N) none,
    Array.replicate (N * N) none, Array.replicate N none, Array.replicate N none]

/-- Caller arrays for SPD Cholesky. -/
noncomputable def spdInputs (N : ℕ) (n : Fin 2 → ℕ) (x : SPDInput N n) : Fin 2 → Array (Option ℝ) :=
  ![(flatten x.val).map some, Array.replicate (N * N) none]

/-- Caller arrays for PSD Cholesky. -/
noncomputable def psdInputs (N : ℕ) (n : Fin 2 → ℕ) (x : PSDInput N n) : Fin 2 → Array (Option ℝ) :=
  ![(flatten x.val).map some, Array.replicate (N * N) none]

/-- Caller arrays for LDL: source, lower factor and scalar diagonal. -/
noncomputable def ldlInputs (N : ℕ) (n : Fin 3 → ℕ) (x : LDLInput N n) : Fin 3 → Array (Option ℝ) :=
  ![(flatten x.val).map some, Array.replicate (N * N) none, Array.replicate N none]

/-- No read-only ROM data is supplied. -/
def romLength {r : ℕ} (_N : ℕ) (_n : Fin r → ℕ) : ℕ := 0

/-- All storage is at the sole unit tag, including caller arrays and additional live words. -/
def memory (caller scratch : ℕ → ℕ) (N : ℕ) (_q : Unit) : ℕ := caller N + scratch N

/-- The original source entries and all initial buffer extents are retained. -/
def Retains {N b : ℕ} (A : Mat N) (ao : ℕ) (bufs : Fin b → Array (Option ℝ))
    (out : State) : Prop :=
  Holds out.store () 0 ao A ∧
    out.store.shape = (inputState (C := OpCount Unit Empty) () (List.ofFn bufs)).store.shape

/-- Actual unpivoted canonical factor reads, exact factorization, retained input and shape. -/
def LUPost (N : ℕ) (n : Fin 3 → ℕ) (x : LUInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  Holds out.store () 1 (n 1) (luLower x.val) ∧
  Holds out.store () 2 (n 2) (luUpper x.val) ∧
  IsLU x.val (luLower x.val) (luUpper x.val) ∧
  Retains x.val (n 0) (luInputs N n x) out

/-- Actual row log determines the permuted input and both canonical factor reads. -/
def PLUPost (N : ℕ) (n : Fin 4 → ℕ) (A : PLUInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  ∃ p : Fin N → Fin N,
    (∀ j : Fin N, out.store.read () 3 (n 3 + j) = some ((p j).val : ℝ)) ∧
    (∀ j, j ≤ p j) ∧
    Holds out.store () 1 (n 1) (luLower (A.submatrix (luPivotPermutation p N) id)) ∧
    Holds out.store () 2 (n 2) (luUpper (A.submatrix (luPivotPermutation p N) id)) ∧
    IsLU (A.submatrix (luPivotPermutation p N) id)
      (luLower (A.submatrix (luPivotPermutation p N) id))
      (luUpper (A.submatrix (luPivotPermutation p N) id)) ∧
    Retains A (n 0) (pluInputs N n A) out

/-- Both actual logs independently determine the canonical factors of the permuted input. -/
def PLUQPost (N : ℕ) (n : Fin 5 → ℕ) (A : PLUQInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  ∃ p q : Fin N → Fin N,
    (∀ j : Fin N, out.store.read () 3 (n 3 + j) = some ((p j).val : ℝ)) ∧
    (∀ j : Fin N, out.store.read () 4 (n 4 + j) = some ((q j).val : ℝ)) ∧
    (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
    Holds out.store () 1 (n 1)
      (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
    Holds out.store () 2 (n 2)
      (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
    IsLU (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))
      (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)))
      (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
    Retains A (n 0) (pluqInputs N n A) out

/-- SPD output has the actual canonical factor and the existing positive-diagonal predicate. -/
def SPDPost (N : ℕ) (n : Fin 2 → ℕ) (x : SPDInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  Holds out.store () 1 (n 1) (choleskyLower x.val) ∧
  IsCholesky x.val (choleskyLower x.val) ∧ Retains x.val (n 0) (spdInputs N n x) out

/-- PSD output permits zero diagonal: actual lower factor, nonnegative diagonal and Gram. -/
def PSDPost (N : ℕ) (n : Fin 2 → ℕ) (x : PSDInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  Holds out.store () 1 (n 1) (choleskyLower x.val) ∧
  (choleskyLower x.val).IsLowerTriangular ∧
  (∀ i, 0 ≤ choleskyLower x.val i i) ∧
  x.val = choleskyLower x.val * (choleskyLower x.val)ᴴ ∧
  Retains x.val (n 0) (psdInputs N n x) out

/-- Actual canonical LDL factor and pivot-diagonal reads, factorization, source and shape. -/
def LDLPost (N : ℕ) (n : Fin 3 → ℕ) (x : LDLInput N n)
    (_vals : ℕ → ℝ) (_tape : Dist → ℕ → ℝ) (out : State) : Prop :=
  Holds out.store () 1 (n 1) (luLower x.val) ∧
  (∀ i : Fin N, out.store.read () 2 (n 2 + i) = some (gaussState x.val i i i)) ∧
  IsLDL x.val (luLower x.val) (fun i => gaussState x.val i i i) ∧
  Retains x.val (n 0) (ldlInputs N n x) out

end DenseFactorizationTarget

open DenseFactorizationTarget

/-- Exact real-word unpivoted LU for every square matrix with nonzero canonical elimination pivots.
The actual output buffers hold the canonical lower and upper factors and certify their product;
the source and all buffer extents are retained. The order includes zero. The sole tag is `Unit`,
oracle names are `Empty`, all offsets and ROM length are zero, and word width is zero.
Each standard operation-kind count is at most $1024(N+1)^3$; total live cells, including caller
capacity, are at most $4N^2+2N+3$. -/
def StoredEntriesDenseLU : Prop :=
  StoredEntries () (luResourceTree ()) Valid LUInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k) (fun k => k * k + 2 * k + 3) N) LUPost

/-- Exact real-word partial-pivoted LU for all square matrices, including singular matrices and
order zero. The actual row-swap log decodes current positions to original rows; the output
buffers hold canonical factors of that row-permuted source and certify their product. Source
entries and all buffer extents are retained. The sole tag is `Unit`, oracle names are `Empty`,
all offsets and ROM length are zero, and word width is zero. Each standard operation-kind
count is at most $1024(N+1)^3$; total live cells including caller capacity are at most
$4N^2+3N+7$. -/
def StoredEntriesDensePLU : Prop :=
  StoredEntries () (pluResourceTree ()) Valid PLUInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + k) (fun k => k * k + 2 * k + 7) N) PLUPost

/-- Exact real-word complete-pivoted LU for all square matrices, including singular matrices and
order zero. Both actual swap logs decode current positions to original rows and columns;
output buffers hold canonical factors of the jointly permuted source and certify their
product. Source entries and buffer extents are retained. The sole tag is `Unit`, oracle names
are `Empty`, all offsets and ROM length are zero, and word width is zero. Each standard
operation-kind count is at most $1024(N+1)^3$; total live cells including caller capacity are
at most $4N^2+4N+7$. -/
def StoredEntriesDensePLUQ : Prop :=
  StoredEntries () (pluqResourceTree ()) Valid PLUQInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + 2 * k) (fun k => k * k + 2 * k + 7) N) PLUQPost

/-- Exact real-word fixed-original-row-scale pivoted LU for all square matrices, including
singular matrices and order zero. The actual row-swap log decodes current positions to
original rows; output buffers hold canonical factors of the row-permuted source and certify
their product, without an unweighted multiplier bound. Source entries and buffer extents are
retained. The sole tag is `Unit`, oracle names are `Empty`, all offsets and ROM length are zero,
and word width is zero. Each standard operation-kind count is at most $1024(N+1)^3$; total live
cells including caller capacity are at most $4N^2+4N+7$. -/
def StoredEntriesDenseScaledPLU : Prop :=
  StoredEntries () (scaledPluResourceTree ()) Valid PLUInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + k) (fun k => k * k + 3 * k + 7) N) PLUPost

/-- Exact real-word Cholesky for positive-definite square inputs, including order zero. The actual
factor buffer holds the canonical lower factor with strictly positive diagonal and its exact
Gram identity. Source entries and buffer extents are retained. The sole tag is `Unit`, oracle
names are `Empty`, all offsets and ROM length are zero, and word width is zero. Each standard
operation-kind count is at most $1024(N+1)^3$; total live cells including caller capacity are
at most $3N^2+2N+3$. -/
def StoredEntriesDenseCholesky : Prop :=
  StoredEntries () (choleskyResourceTree ()) Valid SPDInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k) (fun k => k * k + 2 * k + 3) N) SPDPost

/-- Exact real-word Cholesky for positive-semidefinite square inputs, including singular matrices
and order zero. The actual buffer holds the canonical lower factor, with nonnegative diagonal
and exact Gram identity. Source entries and buffer extents are retained. The sole tag is
`Unit`, oracle names are `Empty`, all offsets and ROM length are zero, and word width is zero.
Each standard operation-kind count is at most $1024(N+1)^3$; total live cells including caller
capacity are at most $3N^2+2N+4$. -/
def StoredEntriesDenseSemidefiniteCholesky : Prop :=
  StoredEntries () (semidefiniteCholeskyResourceTree ()) Valid PSDInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k) (fun k => k * k + 2 * k + 4) N) PSDPost

/-- Exact real-word scalar-pivot LDL for Hermitian square inputs with nonzero canonical elimination
pivots, including order zero. The actual buffers hold the canonical unit lower factor and
pivot diagonal and certify their diagonal Gram factorization. Source entries and buffer
extents are retained. The sole tag is `Unit`, oracle names are `Empty`, all offsets and ROM
length are zero, and word width is zero. Each standard operation-kind count is at most
$1024(N+1)^3$; total live cells including caller capacity are at most $4N^2+3N+3$. -/
def StoredEntriesDenseLDL : Prop :=
  StoredEntries () (ldlResourceTree ()) Valid LDLInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k + k) (fun k => 2 * k * k + 2 * k + 3) N) LDLPost

/-- Nonvacuity obligation for LU; intended witnesses are identity matrices. -/
abbrev StoredEntriesDenseLUNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (luResourceTree ()) Valid LUInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k) (fun k => k * k + 2 * k + 3) N) LUPost N₀

/-- Nonvacuity obligation for PLU; intended witnesses are identity matrices. -/
abbrev StoredEntriesDensePLUNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (pluResourceTree ()) Valid PLUInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + k) (fun k => k * k + 2 * k + 7) N) PLUPost N₀

/-- Nonvacuity obligation for PLUQ; intended witnesses are identity matrices. -/
abbrev StoredEntriesDensePLUQNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (pluqResourceTree ()) Valid PLUQInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + 2 * k) (fun k => k * k + 2 * k + 7) N) PLUQPost N₀

/-- Nonvacuity obligation for ScaledPLU;
intended witnesses are identity matrices. -/
abbrev StoredEntriesDenseScaledPLUNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (scaledPluResourceTree ()) Valid PLUInput (fun N _ x =>
      ![(flatten x).map some, Array.replicate (N * N) none,
        Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 3 * k * k + k) (fun k => k * k + 3 * k + 7) N) PLUPost N₀

/-- Nonvacuity obligation for Cholesky;
intended witnesses are identity matrices. -/
abbrev StoredEntriesDenseCholeskyNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (choleskyResourceTree ()) Valid SPDInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k) (fun k => k * k + 2 * k + 3) N) SPDPost N₀

/-- Nonvacuity obligation for SemidefiniteCholesky;
intended witnesses are identity matrices. -/
abbrev StoredEntriesDenseSemidefiniteCholeskyNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (semidefiniteCholeskyResourceTree ())
    Valid PSDInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k) (fun k => k * k + 2 * k + 4) N) PSDPost N₀

/-- Nonvacuity obligation for LDL; intended witnesses are identity matrices. -/
abbrev StoredEntriesDenseLDLNonVacuous : Prop :=
  ∀ N₀, StoredEntries.NonVacuous () (ldlResourceTree ()) Valid LDLInput (fun N _ x =>
      ![(flatten x.val).map some, Array.replicate (N * N) none, Array.replicate N none]) romLength
    (fun N _ => closedCountBudget N)
    (fun N _ => memory (fun k => 2 * k * k + k) (fun k => 2 * k * k + 2 * k + 3) N) LDLPost N₀

end NLAlib.Computation
