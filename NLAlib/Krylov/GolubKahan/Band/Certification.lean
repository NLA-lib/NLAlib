/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import NLAlib.Krylov.GolubKahan.Band.Run
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Catalog.Functional
public import NLAlib.Ops.Certification
public import NLAlib.Ops.Profiles.Confined
public import NLAlib.Ops.Workspace

/-!
# Canonical exact certificate of the block Golub–Kahan program

The program `NLAlib.Krylov.GolubKahan.Band.program` is certified against a closed operation model
whose operations are the two products with a matrix $\mathbf{A}$, the extension of a stored basis
by a block and scalar draws. The matrix is the semantic datum of the problem and is reached only
through the two products (the matrix-free form of the Lanczos certificates); the five supplied
buffers are the uninitialized output blocks. The contract of the basis extension is the exact
relation `NLAlib.Ops.exactExtendRel`, not a function: the certificate holds for every
interpretation that meets it, hence for every exact orthogonalization scheme after linking
(`NLAlib/Krylov/GolubKahan/Band/Linked.lean`).

**Realization.** An operation model carries a joint realization of its contracts
(`NLAlib.Ops.AccessModel.realize`), so the model can only be defined with one exact scheme at
hand. Here it is the block function `NLAlib.Krylov.GolubKahan.Band.Certification.exactExtendFn`,
which returns an extension chosen by `NLAlib.exists_isBasisExtension`; it is a witness of
consistency and appears in no contract. Every dimension $(m, n, b, q)$ is admitted.

**Declared oracle.** The pair of products `NLAlib.Ops.OperatorPairOp` is the declared oracle of
the certificate: its contracts name the matrix of the input. The model is therefore confined
(`NLAlib.Krylov.GolubKahan.Band.Certification.confined_model`: every contract is in operand form)
and not uniform. It is not charged: the work of the primitives is a parameter.

**Resources.** The budget is the static count of the fixed tree, a manifest. Its primitive part is
`NLAlib.Krylov.GolubKahan.Band.solveCount`: $nb$ draws, $qb$ products with $\mathbf{A}$, $qb$
products with $\mathbf{A}^{\mathsf{H}}$ and $2q + 1$ basis extensions. The scratch is closed:
`NLAlib.Krylov.GolubKahan.Band.solvePeak`, the block of $\max(m, n)\,b$ words of the products
plus the largest workspace of a primitive call of the run, plus the reservation of the queries.
Design: `docs/design/LowRank-BlockLanczos.md` §4.1.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.solveCount`: the primitive counts of a run.
* `NLAlib.Krylov.GolubKahan.Band.primitivePeak`, `NLAlib.Krylov.GolubKahan.Band.solvePeak`: the
  scratch of a run in closed form.
* `NLAlib.Krylov.GolubKahan.Band.Certification.Operation`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.contract`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.resources`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.model`: the operation model.
* `NLAlib.Krylov.GolubKahan.Band.Certification.exactExtension`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.stackCoef`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.exactExtendFn`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.functions`: the realization.
* `NLAlib.Krylov.GolubKahan.Band.Certification.slots`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.problem`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.matrix`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.outputs`: the supplied buffers.
* `NLAlib.Krylov.GolubKahan.Band.Certification.storedProduct`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.Good`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.staticBudget`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.specification`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.algorithm`: the specification and the certificate.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.stmtCost_applyColumns`,
  `NLAlib.Krylov.GolubKahan.Band.stmtCost_step`,
  `NLAlib.Krylov.GolubKahan.Band.stmtCost_solve`,
  `NLAlib.Krylov.GolubKahan.Band.stmtPeak_solve_le`,
  `NLAlib.Krylov.GolubKahan.Band.stmtPeak_solve_le_solvePeak`: the static count and scratch of the
  program.
* `NLAlib.Krylov.GolubKahan.Band.Certification.coefTop_stackCoef`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.coefBot_stackCoef`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.decodeMatrix_packFinMatrix`: the packed round trip.
* `NLAlib.Krylov.GolubKahan.Band.Certification.isBasisExtension_exactExtension`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.meets_exactExtendFn`: the chosen extension realizes
  the exact contract.
* `NLAlib.Krylov.GolubKahan.Band.Certification.confined_contract`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.confined_model`: the model is confined.
* `NLAlib.Krylov.GolubKahan.Band.Certification.laws`: the contracts of an interpretation of the
  model.
* `NLAlib.Krylov.GolubKahan.Band.Certification.initial_len`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.initial_room`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.initialBytes_problem`: the initial memory.
* `NLAlib.Krylov.GolubKahan.Band.Certification.wellTyped_program`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.original_staticBudget`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.staticPeak_program_le`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.staticPeak_program_le_solvePeak`: formats, counts,
  scratch.
* `NLAlib.Krylov.GolubKahan.Band.Certification.Good.storedProduct_eq_rsvd`: the stored factors.
* `NLAlib.Krylov.GolubKahan.Band.Certification.wp_program`,
  `NLAlib.Krylov.GolubKahan.Band.Certification.certifies`: total execution and certification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

/-! ### The primitive counts -/

section Count

variable {Op Tst : Type} [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op]

/-- The primitive counts of a run at the dimensions $(m, n, b, q)$: $nb$ draws from the stream,
$qb$ products with $\mathbf{A}$ at the dimensions `[m, n]`, $qb$ products with
$\mathbf{A}^{\mathsf{H}}$ at the dimensions `[n, m]`, and $2q + 1$ basis extensions: the start
block at `[n, 0, b]` and, for every $j < q$, one at `[m, j * b, b]` and one at
`[n, (j + 1) * b, b]`. -/
noncomputable def solveCount (stream m n b q : ℕ) : Count Op Tst :=
  (n * b) • Count.one (Has.inj (SampleOp.draw stream)) [] +
    (q * b) • Count.one (Has.inj OperatorPairOp.matvec) [m, n] +
    (q * b) • Count.one (Has.inj OperatorPairOp.rmatvec) [n, m] +
    Count.one (Has.inj OrthOp.extend) [n, 0, b] +
    ∑ j ∈ Finset.range q, (Count.one (Has.inj OrthOp.extend) [m, j * b, b] +
      Count.one (Has.inj OrthOp.extend) [n, (j + 1) * b, b])

omit [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op] in
/-- The static count of a block of products: `b` calls of the operation `o` at the dimensions
`[m, n]`, for all offsets `x`, `y` of the two operands. -/
theorem stmtCost_applyColumns (o : Op) (m n b x y : ℕ) :
    stmtCost (applyColumns (Tst := Tst) o).body [m, n, b, x, y] = b • Count.one o [m, n] := by
  simp [applyColumns, stmtCost, useCost]

omit [Has SampleOp Op] in
/-- The static count of block step `j` at the dimensions $(m, n, b)$: `b` products with
$\mathbf{A}$, one basis extension at `[m, j * b, b]`, `b` products with
$\mathbf{A}^{\mathsf{H}}$ and one basis extension at `[n, (j + 1) * b, b]`, for all offsets
of the five operands. -/
theorem stmtCost_step (m n b j u v r s w : ℕ) :
    stmtCost (step (Op := Op) (Tst := Tst)).body [m, n, b, j, u, v, r, s, w] =
      b • Count.one (Has.inj OperatorPairOp.matvec) [m, n] +
        Count.one (Has.inj OrthOp.extend) [m, j * b, b] +
        b • Count.one (Has.inj OperatorPairOp.rmatvec) [n, m] +
        Count.one (Has.inj OrthOp.extend) [n, (j + 1) * b, b] := by
  simp [step, stmtCost, useCost, stmtCost_applyColumns]
  module

/-- The static count of the program is `NLAlib.Krylov.GolubKahan.Band.solveCount`, for all
dimensions $(m, n, b, q)$ and all offsets `u`, `v`, `g`, `r`, `s` of the five output operands:
the counts depend on the dimensions only. -/
theorem stmtCost_solve (stream m n b q u v g r s : ℕ) :
    stmtCost (solve (Op := Op) (Tst := Tst) stream).body [m, n, b, q, u, v, g, r, s] =
      solveCount stream m n b q := by
  simp [solve, stmtCost, useCost, stmtCost_sampleVector, stmtCost_step, solveCount,
    Finset.sum_add_distrib, ← mul_nsmul']
  module

/-- The scratch of the program at the dimensions $(m, n, b, q)$ is at most the block of
$(m + (n - m))\,b = \max(m, n)\,b$ cells that holds the drawn block and the products, plus a
common bound `w` of the workspace of every primitive, for all offsets `u`, `v`, `g`, `r`, `s` of
the five output operands. -/
theorem stmtPeak_solve_le (W : Op → List ℕ → ℕ) (w : ℕ) (hW : ∀ o ds, W o ds ≤ w)
    (stream m n b q u v g r s : ℕ) :
    stmtPeak W (solve (Op := Op) (Tst := Tst) stream).body [m, n, b, q, u, v, g, r, s] ≤
      (m + (n - m)) * b + w := by
  refine (stmtPeak_le_zero_add W w hW _ _).trans (Nat.add_le_add_right ?_ w)
  have hSample (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (sampleVector (Op := Op) (Tst := Tst) stream).body) (idx := idx) (by rfl)
  have hStep (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (step (Op := Op) (Tst := Tst)).body) (idx := idx) (by rfl)
  have hz (t : Finset ℕ) : (t.sup fun _ => (0 : ℕ)) = 0 := Finset.sup_bot t
  simp [solve, stmtPeak, Stmt.alloc, hSample, hStep, hz]

/-- The largest workspace of a primitive call of a run at the dimensions $(m, n, b, q)$, for the
workspace `W` of every call: the maximum over a draw, a product with $\mathbf{A}$ at `[m, n]`, a
product with $\mathbf{A}^{\mathsf{H}}$ at `[n, m]` and the $2q + 1$ basis extensions of
`NLAlib.Krylov.GolubKahan.Band.solveCount`. -/
def primitivePeak (W : Op → List ℕ → ℕ) (stream m n b q : ℕ) : ℕ :=
  max (max (W (Has.inj (SampleOp.draw stream)) []) (W (Has.inj OperatorPairOp.matvec) [m, n]))
    (max (max (W (Has.inj OperatorPairOp.rmatvec) [n, m]) (W (Has.inj OrthOp.extend) [n, 0, b]))
      ((Finset.range q).sup fun j => max (W (Has.inj OrthOp.extend) [m, j * b, b])
        (W (Has.inj OrthOp.extend) [n, (j + 1) * b, b])))

/-- The scratch of a run at the dimensions $(m, n, b, q)$ in closed form: the block of
$(m + (n - m))\,b = \max(m, n)\,b$ cells that holds the drawn block and the products, plus the
largest workspace `NLAlib.Krylov.GolubKahan.Band.primitivePeak` of a primitive call. -/
def solvePeak (W : Op → List ℕ → ℕ) (stream m n b q : ℕ) : ℕ :=
  (m + (n - m)) * b + primitivePeak W stream m n b q

/-- The static workspace of the program at the dimensions $(m, n, b, q)$ is at most
`NLAlib.Krylov.GolubKahan.Band.solvePeak`, for every workspace `W` of the primitives and all
offsets `u`, `v`, `g`, `r`, `s` of the five output operands. No common bound of `W` is assumed:
only the calls of the run contribute. -/
theorem stmtPeak_solve_le_solvePeak (W : Op → List ℕ → ℕ) (stream m n b q u v g r s : ℕ) :
    stmtPeak W (solve (Op := Op) (Tst := Tst) stream).body [m, n, b, q, u, v, g, r, s] ≤
      solvePeak W stream m n b q := by
  have hsmul (k : ℕ) (o : Op) (ds : List ℕ) (h : W o ds ≤ primitivePeak W stream m n b q) :
      (k • (Count.one o ds : Count Op Tst)).BoundsWorkspace W
        (primitivePeak W stream m n b q) := by
    have hk : k • (Count.one o ds : Count Op Tst) = ∑ _i ∈ Finset.range k, Count.one o ds := by
      simp
    have hsum : (∑ _i ∈ Finset.range k, (Count.one o ds : Count Op Tst)).CallsSatisfy
        fun o ds => W o ds ≤ primitivePeak W stream m n b q :=
      (Count.callsSatisfy_sum _ _ _).mpr fun _ _ => (Count.callsSatisfy_one _ _ _).mpr h
    exact hsum.mono hk.le
  have hext (j : ℕ) (hj : j ∈ Finset.range q) :
      max (W (Has.inj OrthOp.extend) [m, j * b, b]) (W (Has.inj OrthOp.extend) [n, (j + 1) * b, b])
        ≤ primitivePeak W stream m n b q :=
    (Finset.le_sup (f := fun j => max (W (Has.inj OrthOp.extend) [m, j * b, b])
      (W (Has.inj OrthOp.extend) [n, (j + 1) * b, b])) hj).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  refine (stmtPeak_le_zero_add_on_support W (primitivePeak W stream m n b q) _ _ ?_).trans
    (Nat.add_le_add_right ?_ _)
  · rw [stmtCost_solve, solveCount]
    simp only [Count.BoundsWorkspace, Count.callsSatisfy_add, Count.callsSatisfy_sum,
      Count.callsSatisfy_one]
    exact ⟨⟨⟨⟨hsmul _ _ _ ((le_max_left _ _).trans (le_max_left _ _)),
      hsmul _ _ _ ((le_max_right _ _).trans (le_max_left _ _))⟩,
      hsmul _ _ _ ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))⟩,
      (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))⟩,
      fun j hj => ⟨(le_max_left _ _).trans (hext j hj), (le_max_right _ _).trans (hext j hj)⟩⟩
  · exact stmtPeak_solve_le (fun _ _ => 0) 0 (fun _ _ => le_rfl) stream m n b q u v g r s

end Count

namespace Certification

/-! ### The operations and their contracts -/

/-- The operations of the abstract driver: the basis extension, the two products and the scalar
draws. -/
abbrev Operation := OrthOp ⊕ (OperatorPairOp ⊕ SampleOp)

instance : Has OperatorPairOp Operation := Has.sumRight _ OrthOp _ inferInstance

instance : Has SampleOp Operation := Has.sumRight _ OrthOp _ inferInstance

/-- The contract of every operation for the matrix $\mathbf{A}$ over real words: the basis
extension meets the exact relation at all dimensions, the two products are the exact products
with $\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$, and a draw stores the next word of its
stream. -/
noncomputable def contract {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Operation → Contract ℝ
  | .inl .extend => (exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands
  | .inr (.inl .matvec) => (matvecRel id A).spec (MatvecOperands m n)
  | .inr (.inl .rmatvec) => (matvecRel id Aᴴ).spec (MatvecOperands n m)
  | .inr (.inr (.draw stream)) => (BlockFn.draw stream).rel.spec AnyOperands

/-- The storage shapes of the operations: every operand is a block of scalar cells. -/
def signature : Operation → OperandSignature
  | .inl .extend => ⟨[.cell, .cell], [.cell, .cell, .cell]⟩
  | .inr (.inl _) => ⟨[.cell], [.cell]⟩
  | .inr (.inr _) => ⟨[], [.cell]⟩

/-- Sequential resources over scalar cells with explicit work and workspace of every primitive;
structural instructions cost one unit. -/
def resources (work workspace : Operation → List ℕ → ℕ) : ResourceModel Operation CmpTst :=
  Functional.cellResources signature work workspace

/-! ### The realization -/

/-- An exact extension of the basis $\mathbf{Q}$ by the block $\mathbf{W}$, chosen once for every
pair: the triple $(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ of the new block and the coefficients
against the old and the new columns. -/
noncomputable def exactExtension {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (W : Matrix (Fin n) (Fin b) ℝ) :
    Matrix (Fin n) (Fin b) ℝ × Matrix (Fin k) (Fin b) ℝ × Matrix (Fin b) (Fin b) ℝ :=
  ⟨(exists_isBasisExtension Q W).choose, (exists_isBasisExtension Q W).choose_spec.choose,
    (exists_isBasisExtension Q W).choose_spec.choose_spec.choose⟩

/-- The chosen triple is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$, for every basis
$\mathbf{Q}$ and every block $\mathbf{W}$ with the same number of rows. -/
theorem isBasisExtension_exactExtension {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (W : Matrix (Fin n) (Fin b) ℝ) :
    IsBasisExtension Q W (exactExtension Q W).1 (exactExtension Q W).2.1
      (exactExtension Q W).2.2 :=
  (exists_isBasisExtension Q W).choose_spec.choose_spec.choose_spec

/-- The coefficient block of $k + b$ rows with $\mathbf{H}$ in its first $k$ rows and
$\mathbf{R}$ in its last $b$ rows. -/
def stackCoef {k b : ℕ} (H : Matrix (Fin k) (Fin b) ℝ) (R : Matrix (Fin b) (Fin b) ℝ) :
    Matrix (Fin (k + b)) (Fin b) ℝ :=
  Matrix.of fun i c => Fin.append (fun i => H i c) (fun i => R i c) i

/-- The first $k$ rows of the stacked coefficient block are $\mathbf{H}$. -/
theorem coefTop_stackCoef {k b : ℕ} (H : Matrix (Fin k) (Fin b) ℝ)
    (R : Matrix (Fin b) (Fin b) ℝ) : coefTop (stackCoef H R) = H := by
  ext i c
  simp [coefTop, stackCoef]

/-- The last $b$ rows of the stacked coefficient block are $\mathbf{R}$. -/
theorem coefBot_stackCoef {k b : ℕ} (H : Matrix (Fin k) (Fin b) ℝ)
    (R : Matrix (Fin b) (Fin b) ℝ) : coefBot (stackCoef H R) = R := by
  ext i c
  simp [coefBot, stackCoef]

/-- The packed words of a real matrix, one word per entry, decode to the matrix. -/
theorem decodeMatrix_packFinMatrix {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) :
    decodeMatrix id n k ((EntryCodec.scalar ℝ).packFinMatrix A) = A := by
  simp [decodeMatrix]

/-- A block function of the basis extension over real words: at the dimensions `[n, k, b]` it
decodes the basis and the block, and returns the packed new block of the chosen exact extension,
the input block unchanged, and the packed coefficients. It realizes the exact contract; no
program calls it. -/
noncomputable def exactExtendFn : BlockFn ℝ where
  nd := 3
  inLens d := [d.getD 1 0 * d.headD 0, d.getD 2 0 * d.headD 0]
  outLens d := [d.getD 2 0 * d.headD 0, d.getD 2 0 * d.headD 0,
    (d.getD 1 0 + d.getD 2 0) * d.getD 2 0]
  fn d _ xs := match xs with
    | [qs, ws] =>
        let E := exactExtension (decodeMatrix id (d.headD 0) (d.getD 1 0) qs)
          (decodeMatrix id (d.headD 0) (d.getD 2 0) ws)
        some [(EntryCodec.scalar ℝ).packFinMatrix E.1, ws,
          (EntryCodec.scalar ℝ).packFinMatrix (stackCoef E.2.1 E.2.2)]
    | _ => none

/-- An operation interpreted as the block function of the chosen exact extension meets the exact
contract of a basis extension over real words, at all dimensions and on all admitted operands. -/
theorem meets_exactExtendFn {Op Tst : Type} {I : Interp Op Tst ℝ} {o : Op}
    (h : I.IsFn .total o exactExtendFn AnyOperands) :
    I.Meets .total o ((exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands) := by
  refine h.meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) ?_
  intro d w X μ ins outs hnd hw hadm hr hdom
  obtain ⟨x, y, qs, ws, -, hq, hws, rfl⟩ := Mem.readBlocks_two hr
  have hlen : ws.length = d.getD 2 0 * d.headD 0 := Store.length_of_readBlock hws
  refine ⟨[(EntryCodec.scalar ℝ).packFinMatrix (exactExtension
      (decodeMatrix id (d.headD 0) (d.getD 1 0) qs)
      (decodeMatrix id (d.headD 0) (d.getD 2 0) ws)).1, ws,
    (EntryCodec.scalar ℝ).packFinMatrix (stackCoef (exactExtension
      (decodeMatrix id (d.headD 0) (d.getD 1 0) qs)
      (decodeMatrix id (d.headD 0) (d.getD 2 0) ws)).2.1 (exactExtension
      (decodeMatrix id (d.headD 0) (d.getD 1 0) qs)
      (decodeMatrix id (d.headD 0) (d.getD 2 0) ws)).2.2)], rfl, ?_, ?_⟩
  · simp [exactExtendRel, hlen, mul_comm]
  · change IsBasisExtension _ _ (decodeMatrix id _ _ _) (coefTop (decodeMatrix id _ _ _))
      (coefBot (decodeMatrix id _ _ _))
    rw [decodeMatrix_packFinMatrix, decodeMatrix_packFinMatrix, coefTop_stackCoef,
      coefBot_stackCoef]
    exact isBasisExtension_exactExtension _ _

/-- The block functions of the realization for the matrix $\mathbf{A}$: the chosen exact
extension, the exact real products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, and the
draws. -/
noncomputable def functions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Operation → BlockFn ℝ
  | .inl .extend => exactExtendFn
  | .inr (.inl o) => exactMatvecPairFn A o
  | .inr (.inr (.draw stream)) => .draw stream

/-! ### The problem -/

/-- The five supplied buffers at the dimensions $(m, n, b, q)$: uninitialized blocks of the output
lengths of `U`, `V`, `G`, `R`, `S`. -/
def slots (d : Fin 4 → ℕ) : Fin 5 → Buf ℝ :=
  fun i => List.replicate ((outLens (d 0) (d 1) (d 2) (d 3)).getD i.val 0) none

/-- The problem of the abstract driver. The sizes are $(m, n, b, q)$ and all of them are
admitted; the datum is a real $m \times n$ matrix, reached through the two products only; the
supplied buffers are the five uninitialized output blocks. -/
def problem : Problem ℝ 4 5 where
  formats _ := .cell
  valid _ := True
  Data d := Matrix (Fin (d 0)) (Fin (d 1)) ℝ
  admissible d _ buffers := buffers = slots d
  admitted := ⟨fun _ => 0, trivial⟩
  supply d _ := ⟨0, slots d, rfl⟩

/-- The matrix $\mathbf{A}$ of an input of the problem, with its type as a real $m \times n$
matrix. -/
abbrev matrix {d : Fin 4 → ℕ} (x : problem.Input d) : Matrix (Fin (d 0)) (Fin (d 1)) ℝ :=
  x.val.1

/-- The operands of the five output blocks `U`, `V`, `G`, `R`, `S` in the initial memory. -/
def outputs : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]

/-- Every supplied buffer has the length of its output block. -/
theorem initial_len (d : Fin 4 → ℕ) (x : problem.Input d) (i : Fin 5) :
    (problem.initial d x).store.len i.val =
      (outLens (d 0) (d 1) (d 2) (d 3)).getD i.val 0 := by
  have h : x.val.2 = slots d := x.property
  rw [Problem.initial_len, h, slots, List.length_replicate]

/-- The supplied buffers have room for the five output blocks. -/
theorem initial_room (d : Fin 4 → ℕ) (x : problem.Input d) :
    (problem.initial d x).Room outputs (outLens (d 0) (d 1) (d 2) (d 3)) := by
  have h := initial_len d x
  simp only [outputs, outLens, Mem.room_cons, Mem.room_nil, Nat.zero_add, and_true]
  exact ⟨(h 0).ge, (h 1).ge, (h 2).ge, (h 3).ge, (h 4).ge⟩

/-- The resident payload of the supplied buffers is the total length of the five output
blocks. -/
theorem initialBytes_problem (d : Fin 4 → ℕ) (x : problem.Input d) :
    problem.initialBytes d x = (outLens (d 0) (d 1) (d 2) (d 3)).sum := by
  have h : x.val.2 = slots d := x.property
  rw [Problem.initialBytes_of_lengths d x
    (fun i => (outLens (d 0) (d 1) (d 2) (d 3)).getD i.val 0)
    (fun i => by rw [h, slots, List.length_replicate])]
  simp [problem, outLens, List.ofFn_succ]

/-! ### The model -/

/-- The closed operation model of the abstract driver for the supplied matrix: the contracts
`NLAlib.Krylov.GolubKahan.Band.Certification.contract` at the datum of the input, exact
comparisons, and explicit primitive work and workspace. The joint realization interprets the
basis extension as the chosen exact extension; the contract of that operation stays the relation,
so the interpretations of the model are all exact schemes. The pair of products
`NLAlib.Ops.OperatorPairOp` is the declared oracle of the model: its contracts name the matrix of
the input, so the model is confined
(`NLAlib.Krylov.GolubKahan.Band.Certification.confined_model`) and not uniform. -/
noncomputable def model (work workspace : Operation → List ℕ → ℕ) :
    AccessModel Operation CmpTst problem where
  word := 0
  operation _ x := contract x.val.1
  query _ _ := Functional.query id
  resources := resources work workspace
  realize _ _ x := by
    refine ⟨Functional.interp id (functions x.val.1), ?_, fun c =>
      ⟨(Functional.interp_contracts id (functions x.val.1)).2 c, fun _ _ => rfl⟩⟩
    have hF (o : Operation) : (Functional.interp id (functions x.val.1)).IsFn .total o
        (functions x.val.1 o) AnyOperands :=
      Interp.ofFns_isFn (Tst := CmpTst) (functions x.val.1) .total o AnyOperands
    rintro (o | o | o)
    · cases o
      exact meets_exactExtendFn (hF (.inl .extend))
    · cases o
      · exact (hF (.inr (.inl .matvec))).meets_matvec
      · exact (hF (.inr (.inl .rmatvec))).meets_matvec
    · cases o with
      | draw stream => exact hF (.inr (.inr (.draw stream)))

/-- Every contract of the driver is confined: each is in operand form
(`NLAlib.Ops.BlockRel.spec`), for every matrix $\mathbf{A}$. The basis extension, the two
products and the draws read their operand blocks and the tape window and write their output
blocks only. -/
theorem confined_contract {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (o : Operation) :
    (contract A o).Confined := by
  rcases o with ⟨⟩ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨stream⟩ <;> exact BlockRel.confined_spec _ _

/-- **The model of the abstract driver is confined**: every primitive and every comparison reads
and writes its operand blocks only. The model is not uniform: the contracts of the two products
name the matrix of the input, the declared oracle of the certificate. -/
instance confined_model (work workspace : Operation → List ℕ → ℕ) :
    (model work workspace).Confined :=
  ⟨fun _ x o => confined_contract x.val.1 o, fun _ _ c => Functional.confined_query id c⟩

/-- Every interpretation of the model has the exact pair of products with the supplied matrix,
an exact basis extension, and draws that return the words of the tape. -/
theorem laws {work workspace : Operation → List ℕ → ℕ} {d : Fin 4 → ℕ} {x : problem.Input d}
    {I : Interp Operation CmpTst ℝ} (h : (model work workspace).contracts d x I) :
    IsExactMatvecPair id x.val.1 I ∧
      I.Meets .total (Has.inj OrthOp.extend) ((exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands) ∧
      IsSample I :=
  ⟨⟨h.1 (.inr (.inl .matvec)), h.1 (.inr (.inl .rmatvec))⟩, h.1 (.inl .extend),
    fun stream => h.1 (.inr (.inr (.draw stream)))⟩

/-! ### The specification -/

/-- The product $\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ of the factors stored
in a memory at the dimensions $(m, n, b, q)$: $\mathbf{U}$ and $\mathbf{V}$ are decoded from the
buffers `0` and `1` and $\mathbf{S}$ is assembled from the packed block columns in the buffer
`4`. A block that cannot be read counts as the empty list. -/
noncomputable def storedProduct (m n b q : ℕ) (μ : Mem ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  decodeMatrix id m (q * b) ((μ.store.readBlock 0 0 (q * b * m)).getD []) *
      (assembleRight b q fun j => decodeMatrix id ((j + 1) * b + b) b
        (((μ.store.readBlock 4 0 (coefOffsetS b q)).getD []).drop (coefOffsetS b j)))ᴴ *
    (decodeMatrix id n ((q + 1) * b) ((μ.store.readBlock 1 0 ((q + 1) * b * n)).getD []))ᴴ

/-- The postcondition of a run at the sizes `d` $= (m, n, b, q)$ for the matrix $\mathbf{A}$ on
the tape `τ`: exactly $nb$ words of the tape are consumed, the store has its five buffers and no
scratch, and the five output blocks decode to an exact run for $\mathbf{A}$ from the start block
decoded from the window of $nb$ words of the stream at the position zero. -/
def Good (stream : ℕ) (d : Fin 4 → ℕ) (A : Matrix (Fin (d 0)) (Fin (d 1)) ℝ) (τ : Tape ℝ)
    (μ : Mem ℝ) : Prop :=
  μ.pos = d 1 * d 2 ∧ μ.store.length = 5 ∧ ∃ us vs gs rs ss,
    μ.readBlocks outputs (outLens (d 0) (d 1) (d 2) (d 3)) = some [us, vs, gs, rs, ss] ∧
    StoredOut id (d 0) (d 1) (d 2) (d 3) (IsExactStoredRun A (d 2) (d 3))
      (τ.window stream 0 (d 1 * d 2)) us vs gs rs ss

/-- The stored factors of a good final memory are the randomized SVD approximation at the block
Krylov matrix: if the memory satisfies the postcondition of a run for $\mathbf{A}$ at the sizes
$(m, n, b, q)$ on the tape `τ`, and $\mathbf{\Omega}$ is the $n \times b$ block decoded from the
window of the tape, then the stored product is
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} = \mathsf{rsvd}(\mathbf{A},
[\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}])\,.$$ -/
theorem Good.storedProduct_eq_rsvd {stream : ℕ} {d : Fin 4 → ℕ}
    {A : Matrix (Fin (d 0)) (Fin (d 1)) ℝ} {τ : Tape ℝ} {μ : Mem ℝ} (h : Good stream d A τ μ) :
    storedProduct (d 0) (d 1) (d 2) (d 3) μ =
      rsvd A (blockKrylovMatrix (Aᴴ * A)
        (decodeMatrix id (d 1) (d 2) (τ.window stream 0 (d 1 * d 2))) (d 3)) := by
  obtain ⟨-, -, us, vs, gs, rs, ss, hr, hS⟩ := h
  simp only [outputs, outLens] at hr
  obtain ⟨x, xs, hu, hr, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
  cases he
  obtain ⟨x, xs, hv, hr, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
  cases he
  obtain ⟨x, xs, -, hr, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
  cases he
  obtain ⟨x, xs, -, hr, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
  cases he
  obtain ⟨x, xs, hs, -, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
  cases he
  have hu' : μ.store.readBlock 0 0 (d 3 * d 2 * d 0) = some us := hu
  have hv' : μ.store.readBlock 1 0 ((d 3 + 1) * d 2 * d 1) = some vs := hv
  have hs' : μ.store.readBlock 4 0 (coefOffsetS (d 2) (d 3)) = some ss := hs
  rw [storedProduct, hu', hv', hs']
  exact hS.mul_conjTranspose_mul_conjTranspose_eq_rsvd

/-- The full static count of the fixed program, with index expressions, addressing, allocation
and control. -/
noncomputable def staticBudget (stream : ℕ) (d : Fin 4 → ℕ) :
    Count (Operation ⊕ Bookkeeping) CmpTst := staticCost (program stream) d

/-- The fixed program is well typed for the scalar-cell resources of the model. -/
theorem wellTyped_program (work workspace : Operation → List ℕ → ℕ) (stream : ℕ) :
    (program (Op := Operation) (Tst := CmpTst) stream).wellTyped (resources work workspace)
      (fun _ => .cell) = true := by
  rfl

/-- The primitive part of the static budget at the sizes $(m, n, b, q)$ is
`NLAlib.Krylov.GolubKahan.Band.solveCount`: $nb$ draws, $qb$ products with $\mathbf{A}$, $qb$
products with $\mathbf{A}^{\mathsf{H}}$ and $2q + 1$ basis extensions. The full budget also counts
the structural instructions. -/
theorem original_staticBudget (stream : ℕ) (d : Fin 4 → ℕ) :
    Count.original (staticBudget stream d) =
      solveCount (Op := Operation) (Tst := CmpTst) stream (d 0) (d 1) (d 2) (d 3) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  change stmtCost (solve stream).body [d 0, d 1, d 2, d 3, 0, 0, 0, 0, 0] = _
  exact stmtCost_solve ..

/-- The scratch of the fixed program at the sizes $(m, n, b, q)$ is at most the block of
$\max(m, n)\,b$ words that holds the drawn block and the products, plus a common bound `w` of the
workspace of every primitive and the reservation of the queries. -/
theorem staticPeak_program_le (R : ResourceModel Operation CmpTst) (w : ℕ)
    (hW : ∀ o ds, R.workspace o ds ≤ w) (stream : ℕ) (d : Fin 4 → ℕ) :
    staticPeak R (program stream) d ≤
      (d 0 + (d 1 - d 0)) * d 2 + w + R.queryReserve (staticBudget stream d) := by
  rw [staticPeak_eq]
  change stmtPeak R.workspace (solve stream).body [d 0, d 1, d 2, d 3, 0, 0, 0, 0, 0] + _ ≤ _
  exact Nat.add_le_add_right
    (stmtPeak_solve_le R.workspace w hW stream (d 0) (d 1) (d 2) (d 3) 0 0 0 0 0) _

/-- The scratch of the fixed program at the sizes $(m, n, b, q)$ is at most the closed form
`NLAlib.Krylov.GolubKahan.Band.solvePeak` at the workspace of the resource model `R`, plus the
reservation of the queries; no common bound of the workspace of the primitives is assumed. -/
theorem staticPeak_program_le_solvePeak (R : ResourceModel Operation CmpTst) (stream : ℕ)
    (d : Fin 4 → ℕ) :
    staticPeak R (program stream) d ≤
      solvePeak R.workspace stream (d 0) (d 1) (d 2) (d 3) +
        R.queryReserve (staticBudget stream d) := by
  rw [staticPeak_eq]
  change stmtPeak R.workspace (solve stream).body [d 0, d 1, d 2, d 3, 0, 0, 0, 0, 0] + _ ≤ _
  exact Nat.add_le_add_right
    (stmtPeak_solve_le_solvePeak R.workspace stream (d 0) (d 1) (d 2) (d 3) 0 0 0 0 0) _

/-- The specification of the exact certificate: the full static count as budget; as scratch the
closed form `NLAlib.Krylov.GolubKahan.Band.solvePeak` (the block of $\max(m, n)\,b$ words of the
products plus the largest workspace of a primitive call of the run) plus the reservation of the
queries; work and span of the budget; resident memory of the five output blocks plus the scratch;
and the postcondition `NLAlib.Krylov.GolubKahan.Band.Certification.Good` at the supplied
matrix. -/
noncomputable def specification (work workspace : Operation → List ℕ → ℕ) (stream : ℕ) :
    Specification Operation CmpTst problem where
  budget := staticBudget stream
  scratch d := solvePeak (resources work workspace).workspace stream (d 0) (d 1) (d 2) (d 3) +
    (resources work workspace).queryReserve (staticBudget stream d)
  work d := (resources work workspace).work (staticBudget stream d)
  span d := (resources work workspace).span (staticBudget stream d)
  memory d := (outLens (d 0) (d 1) (d 2) (d 3)).sum +
    (solvePeak (resources work workspace).workspace stream (d 0) (d 1) (d 2) (d 3) +
      (resources work workspace).queryReserve (staticBudget stream d))
  good d x τ _ μ := Good stream d x.val.1 τ μ

/-! ### The certificate -/

/-- Total execution of the fixed program from the initial memory, for any signature that contains
the operations of the driver. If the two products are the exact products with the supplied matrix
$\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$, the basis extension meets the exact contract
and the draws return the words of the tape, then at all sizes $(m, n, b, q)$ and on every tape
the program terminates in a memory that satisfies the postcondition
`NLAlib.Krylov.GolubKahan.Band.Certification.Good`. The interpretation may be one induced by
linking an orthogonalization scheme. -/
theorem wp_program {Op Tst : Type} [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op]
    {d : Fin 4 → ℕ} {x : problem.Input d} {I : Interp Op Tst ℝ}
    (hA : IsExactMatvecPair id x.val.1 I)
    (hO : I.Meets .total (Has.inj OrthOp.extend)
      ((exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (τ : Tape ℝ) :
    Wp .total I τ (program stream).body (Program.environment (b := 5) d)
      (Good stream d x.val.1 τ) (problem.initial d x) := by
  have hl : (problem.initial d x).Live outputs := by
    simp [outputs, Mem.Live, Problem.initial]
  have hRun := solve_writes hA hO hSample stream (τ := τ) (μ := problem.initial d x)
    (U := (0, 0)) (V := (1, 0)) (G := (2, 0)) (R := (3, 0)) (S := (4, 0)) (b := d 2)
    (q := d 3) (by simp) hl (initial_room d x)
  change Wp .total I τ (.frame _ _ _) _ _ (problem.initial d x)
  apply wp_frame rfl rfl hl
  exact hRun.wp fun μ' hfr hp =>
    ⟨by simpa [Problem.initial] using hp.1, by simpa [Problem.initial] using hfr.length_eq,
      hp.2⟩

/-- The fixed program is certified in total mode. For all sizes $(m, n, b, q)$, every real
$m \times n$ matrix $\mathbf{A}$, every interpretation whose products are the exact products with
$\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ and whose basis extension is exact, and every tape, the
counted run succeeds within the static budget, the closed scratch, work, span and memory; it
consumes $nb$
words of the tape, releases its scratch and leaves five output blocks that decode to an exact
run for $\mathbf{A}$ from the start block decoded from the tape. There is no rank, nonbreakdown
or success hypothesis. -/
theorem certifies (work workspace : Operation → List ℕ → ℕ) (stream : ℕ) :
    (program stream).Certifies (model work workspace) (specification work workspace stream) := by
  refine (Algorithm.ofWp (M := model work workspace)
    (S := specification work workspace stream) (program stream)
    (wellTyped_program work workspace stream) ?_ (fun _ _ => le_rfl)
    (fun d _ => staticPeak_program_le_solvePeak _ stream d)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_).correct
  · intro d _ x I hI τ
    obtain ⟨hA, hO, hSample⟩ := laws hI
    exact (wp_program hA hO hSample stream τ).mono fun _ h _ _ => h
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- The canonical exact certificate of the abstract driver: the fixed program with its total
certification against the model and the specification. The model is confined and, because the
pair of products with the supplied matrix is a declared oracle, not uniform; the budget is the
static count of the program (a manifest) and the scratch is the closed form
`NLAlib.Krylov.GolubKahan.Band.solvePeak` plus the reservation of the queries. -/
noncomputable def algorithm (work workspace : Operation → List ℕ → ℕ) (stream : ℕ) :
    Algorithm (model work workspace) (specification work workspace stream) where
  program := program stream
  correct := certifies work workspace stream

end Certification

end NLAlib.Krylov.GolubKahan.Band
