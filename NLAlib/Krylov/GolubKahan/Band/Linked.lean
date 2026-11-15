/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.GolubKahan.Band.Certification
public import NLAlib.Ops.Transfer

/-!
# The block Golub–Kahan program linked with an orthogonalization scheme

An orthogonalization scheme is an implementation `E` of the basis extension over a lower
signature `Lo` that contains the two products and the draws (and whatever `E` calls: vector
operations, scalar arithmetic). The table `NLAlib.Krylov.GolubKahan.Band.linkTable` maps the
basis extension to `E` and keeps the products and the draws. Everything here is generic in `E`:
the only hypothesis on the scheme is its certificate `NLAlib.Ops.Impl.Triple` against the exact
contract `NLAlib.Ops.exactExtendRel`, resp. the rounded contract `NLAlib.Ops.extendRel`, over
the lower interpretation. Tests are not mapped by a table, so the driver and the scheme share
the test signature.

**Costs.** One call of the basis extension at the dimensions `[n, k, b]` becomes the tree of
`E`, which costs at most `κ [n, k, b]`; the linked run costs the draws and products of the driver
and the sum of `κ` over the $2q + 1$ extensions of the run
(`NLAlib.Krylov.GolubKahan.Band.linkedSolveCount`). The scratch is that of the driver plus a
common bound of the scratch of `E` and of the lower primitives. The stored-run conclusions feed
`NLAlib/Krylov/GolubKahan/Band/Run.lean`: the factored identity for an exact run, orthogonality
and the forward bound for a rounded run. Design: `docs/design/LowRank-BlockLanczos.md` §5, E5.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.linkTable`, `NLAlib.Krylov.GolubKahan.Band.linkedSolve`,
  `NLAlib.Krylov.GolubKahan.Band.linkedProgram`: the table and the linked trees.
* `NLAlib.Krylov.GolubKahan.Band.linkCost`, `NLAlib.Krylov.GolubKahan.Band.linkedSolveCount`:
  the counts after linking.
* `NLAlib.Krylov.GolubKahan.Band.Rounded.StoredBounds`: orthogonality and forward bound of the
  stored factors.
* `NLAlib.Krylov.GolubKahan.Band.linkedSpecification`,
  `NLAlib.Krylov.GolubKahan.Band.linkedAlgorithm`: the canonical exact certificate after linking.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.isExactMatvecPair_link`,
  `NLAlib.Krylov.GolubKahan.Band.isMatvecPair_link`,
  `NLAlib.Krylov.GolubKahan.Band.isSample_link`,
  `NLAlib.Krylov.GolubKahan.Band.meets_extend_link`: the contracts of the induced interpretation.
* `NLAlib.Krylov.GolubKahan.Band.linkedSolve_spec`,
  `NLAlib.Krylov.GolubKahan.Band.Rounded.linkedSolve_spec`: the linked program meets the exact,
  resp. rounded, contract of the driver.
* `NLAlib.Krylov.GolubKahan.Band.accounts_linkTable`,
  `NLAlib.Krylov.GolubKahan.Band.push_solveCount`: accounting of the table.
* `NLAlib.Krylov.GolubKahan.Band.runs_linkedSolve`,
  `NLAlib.Krylov.GolubKahan.Band.runs_linkedSolve_rsvd`,
  `NLAlib.Krylov.GolubKahan.Band.Rounded.runs_linkedSolve`: total counted execution.
* `NLAlib.Krylov.GolubKahan.Band.Rounded.storedBounds_of_storedOut`: the bounds of a rounded run.
* `NLAlib.Krylov.GolubKahan.Band.linked_certifies`: total certification of the linked program.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops Certification

variable {K Lo Tst : Type} [Has OperatorPairOp Lo] [Has SampleOp Lo]

/-! ### The table -/

/-- The table of an orthogonalization scheme `E`: the basis extension is implemented by `E`, the
two products and the draws are kept. -/
def linkTable (E : Impl Lo Tst) : Table Operation Lo Tst
  | .inl .extend => .inl E
  | .inr (.inl o) => .inr (Has.inj o)
  | .inr (.inr o) => .inr (Has.inj o)

/-- The driver linked with the scheme `E`: every call of the basis extension is the frame of the
tree of `E`. It has the dimensions `[m, n, b, q]` and the five output operands of the driver. -/
def linkedSolve (E : Impl Lo Tst) (stream : ℕ) : Impl Lo Tst :=
  ⟨(solve (Op := Operation) (Tst := Tst) stream).nd,
    (solve (Op := Operation) (Tst := Tst) stream).nin,
    (solve (Op := Operation) (Tst := Tst) stream).nout,
    (solve (Op := Operation) (Tst := Tst) stream).body.link (linkTable E)⟩

/-- The fixed program linked with the scheme `E`. -/
def linkedProgram (E : Impl Lo Tst) (stream : ℕ) : Program Lo Tst 4 5 :=
  (program (Op := Operation) (Tst := Tst) stream).link (linkTable E)

/-! ### The induced interpretation -/

section Induced

variable [Inhabited K] {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
  {I : Interp Lo Tst K} {E : Impl Lo Tst}

/-- Exact products below are exact products of the induced interpretation. -/
theorem isExactMatvecPair_link (hA : IsExactMatvecPair dec A I) :
    IsExactMatvecPair dec A (I.link (linkTable E)) :=
  ⟨Interp.link_meets_kept (T := linkTable E) (o := Has.inj OperatorPairOp.matvec) rfl hA.1,
    Interp.link_meets_kept (T := linkTable E) (o := Has.inj OperatorPairOp.rmatvec) rfl hA.2⟩

/-- Products within the allowances $\delta$, $\delta'$ below are products within the same
allowances of the induced interpretation. -/
theorem isMatvecPair_link {δ δ' : ℝ} (hA : IsMatvecPair dec A δ δ' I) :
    IsMatvecPair dec A δ δ' (I.link (linkTable E)) :=
  ⟨Interp.link_meets_kept (T := linkTable E) (o := Has.inj OperatorPairOp.matvec) rfl hA.1,
    Interp.link_meets_kept (T := linkTable E) (o := Has.inj OperatorPairOp.rmatvec) rfl hA.2⟩

omit [Inhabited K] in
/-- Draws below are draws of the induced interpretation. -/
theorem isSample_link (hSample : IsSample I) : IsSample (I.link (linkTable E)) :=
  fun stream => Interp.link_meets_kept (T := linkTable E)
    (o := Has.inj (SampleOp.draw stream)) rfl (hSample stream)

omit [Inhabited K] in
/-- The basis extension of the induced interpretation meets every contract that the scheme `E`
is certified against. -/
theorem meets_extend_link {C : Contract K} (hE : E.Triple I .total C) :
    (I.link (linkTable E)).Meets .total (Has.inj OrthOp.extend) C :=
  Interp.link_meets (T := linkTable E) (o := Has.inj OrthOp.extend) rfl hE

/-! ### The contracts of the linked program -/

/-- The linked program meets the exact contract of the driver. If the lower interpretation has
the exact products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ and draws that return the
words of the tape, and the scheme `E` is certified in total mode against the exact contract of a
basis extension, then on five output blocks in distinct buffers the linked program terminates
and writes blocks that decode to an exact run for $\mathbf{A}$ from the drawn start block. -/
theorem linkedSolve_spec (hA : IsExactMatvecPair dec A I) (hSample : IsSample I)
    (hE : E.Triple I .total ((exactExtendRel dec).spec ExtendOperands)) (stream : ℕ) :
    (linkedSolve E stream).Triple I .total ((solveRel stream dec A).spec (SolveOperands m n)) := by
  have h := solve_spec (Op := Operation) (isExactMatvecPair_link (E := E) hA)
    (meets_extend_link hE) (isSample_link hSample) stream
  intro d ins outs τ μ hpre
  obtain ⟨hl, hw⟩ := h d ins outs τ μ hpre
  refine ⟨hl, fun hlive => ⟨(hw hlive).1, ?_⟩⟩
  have hwp := (hw hlive).2
  rw [Wp, ← run_link] at hwp
  exact hwp

/-- The linked program meets the rounded contract of the driver. If the lower interpretation has
products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ within the allowances $\delta$,
$\delta'$ and draws that return the words of the tape, and the scheme `E` is certified in total
mode against the rounded contract of a basis extension with parameters
$(\eta_0, \mu, \varepsilon)$ at the dimensions admitted by `ok`, which include every extension
with $m$ or $n$ rows, then on five output blocks in distinct buffers the linked program
terminates and writes blocks that decode to a rounded run for $\mathbf{A}$, the executed
history. There is no orthogonality, rank or nonbreakdown hypothesis. -/
theorem Rounded.linkedSolve_spec {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop}
    (hA : IsMatvecPair dec A δ δ' I) (hSample : IsSample I)
    (hE : E.Triple I .total ((extendRel dec η₀ μ ε ok).spec ExtendOperands)) (stream : ℕ)
    (hok : ∀ k b, ok m k b ∧ ok n k b) :
    (linkedSolve E stream).Triple I .total
      ((Rounded.solveRel stream dec A δ δ' η₀ μ ε).spec (SolveOperands m n)) := by
  have h := Rounded.solve_spec (Op := Operation) (isMatvecPair_link (E := E) hA)
    (meets_extend_link hE) (isSample_link hSample) stream hok
  intro d ins outs τ ν hpre
  obtain ⟨hl, hw⟩ := h d ins outs τ ν hpre
  refine ⟨hl, fun hlive => ⟨(hw hlive).1, ?_⟩⟩
  have hwp := (hw hlive).2
  rw [Wp, ← run_link] at hwp
  exact hwp

end Induced

/-! ### Accounting -/

/-- The cost of one call of the driver after linking: a basis extension at the dimensions `d`
costs `κ d`, the cost of the scheme; a product or a draw costs itself. -/
noncomputable def linkCost (κ : List ℕ → Count Lo Tst) : Operation → List ℕ → Count Lo Tst
  | .inl .extend, d => κ d
  | .inr (.inl o), d => Count.one (Has.inj o) d
  | .inr (.inr o), d => Count.one (Has.inj o) d

/-- The counts of a linked run at the dimensions $(m, n, b, q)$, for a scheme that costs `κ`:
$nb$ draws, $qb$ products with $\mathbf{A}$, $qb$ products with $\mathbf{A}^{\mathsf{H}}$, and
the cost of the scheme at the start block `[n, 0, b]` and, for every $j < q$, at
`[m, j * b, b]` and at `[n, (j + 1) * b, b]`. -/
noncomputable def linkedSolveCount (κ : List ℕ → Count Lo Tst) (stream m n b q : ℕ) :
    Count Lo Tst :=
  (n * b) • Count.one (Has.inj (SampleOp.draw stream)) [] +
    (q * b) • Count.one (Has.inj OperatorPairOp.matvec) [m, n] +
    (q * b) • Count.one (Has.inj OperatorPairOp.rmatvec) [n, m] +
    κ [n, 0, b] + ∑ j ∈ Finset.range q, (κ [m, j * b, b] + κ [n, (j + 1) * b, b])

/-- The counts of the driver pushed through the table are the counts of the linked run. -/
theorem push_solveCount (κ : List ℕ → Count Lo Tst) (stream m n b q : ℕ) :
    Count.push (linkCost κ) (solveCount (Op := Operation) (Tst := Tst) stream m n b q) =
      linkedSolveCount κ stream m n b q := by
  have h1 (d : List ℕ) : linkCost κ (Has.inj OrthOp.extend) d = κ d := rfl
  have h2 (o : OperatorPairOp) (d : List ℕ) :
      linkCost κ (Has.inj o) d = Count.one (Has.inj o) d := rfl
  have h3 (o : SampleOp) (d : List ℕ) :
      linkCost κ (Has.inj o) d = Count.one (Has.inj o) d := rfl
  simp only [solveCount, linkedSolveCount, map_add, map_nsmul, map_sum, Count.push_one, h1, h2,
    h3]

/-- The accounting certificate of the table of a scheme `E`: if every run of the tree of `E` at
the dimensions `d` costs at most `κ d` and uses at most `w` scratch, statically, and every lower
primitive has workspace at most `w`, then one call of the driver costs at most
`NLAlib.Krylov.GolubKahan.Band.linkCost` and uses at most `w` scratch, for every lower
interpretation. -/
theorem accounts_linkTable (E : Impl Lo Tst) (κ : List ℕ → Count Lo Tst)
    (W : Lo → List ℕ → ℕ) (w : ℕ)
    (hE : ∀ d offs : List ℕ, d.length = E.nd → offs.length = E.nin + E.nout →
      stmtCost E.body (d ++ offs) ≤ κ d ∧ stmtPeak W E.body (d ++ offs) ≤ w)
    (hW : ∀ o ds, W o ds ≤ w) (I : Interp Lo Tst K) :
    (linkTable E).Accounts I W (linkCost κ) (fun _ _ => w) := by
  refine Table.accounts_of_static (fun o R hT d offs hd ho => ?_) (fun o o' hT d => ?_) I
  · rcases o with ⟨⟩ | o | o
    · obtain rfl : E = R := Sum.inl.inj hT
      exact hE d offs hd ho
    · exact absurd hT (by simp [linkTable])
    · exact absurd hT (by simp [linkTable])
  · rcases o with ⟨⟩ | o | o
    · exact absurd hT (by simp [linkTable])
    · obtain rfl : Has.inj o = o' := Sum.inr.inj hT
      exact ⟨le_rfl, hW _ _⟩
    · obtain rfl : Has.inj o = o' := Sum.inr.inj hT
      exact ⟨le_rfl, hW _ _⟩

/-! ### Total counted execution -/

section Runs

variable [Inhabited K] {dec : K → ℝ} {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
  {I : Interp Lo Tst K} {E : Impl Lo Tst}

/-- Total counted execution of the linked program under exact contracts. Let the lower
interpretation have the exact products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ and draws
that return the words of the tape, let the scheme `E` be certified against the exact contract of
a basis extension, cost at most `κ d` at the dimensions `d` and use at most `w` scratch, and let
every lower primitive have workspace at most `w`. Then for all dimensions $(m, n, b, q)$, on five
live output blocks in distinct buffers with room for the output lengths, the linked program
terminates within the counts `NLAlib.Krylov.GolubKahan.Band.linkedSolveCount` and the scratch
$\max(m, n)\,b + w$, consumes $nb$ samples, and the stored blocks decode to an exact run for
$\mathbf{A}$ from the start block decoded from the window of the tape. -/
theorem runs_linkedSolve (hA : IsExactMatvecPair dec A I) (hSample : IsSample I)
    (hE : E.Triple I .total ((exactExtendRel dec).spec ExtendOperands))
    (κ : List ℕ → Count Lo Tst) (W : Lo → List ℕ → ℕ) (w : ℕ)
    (hcost : ∀ d offs : List ℕ, d.length = E.nd → offs.length = E.nin + E.nout →
      stmtCost E.body (d ++ offs) ≤ κ d ∧ stmtPeak W E.body (d ++ offs) ≤ w)
    (hW : ∀ o ds, W o ds ≤ w) (stream : ℕ) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    ConditionalRuns I W τ (linkedSolve E stream).body (Env.frame [m, n, b, q] [U, V, G, R, S]) μ
      (linkedSolveCount κ stream m n b q) ((m + (n - m)) * b + w)
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsExactStoredRun A b q) (τ.window stream μ.pos (n * b))
          us vs gs rs ss) := by
  obtain ⟨μ', hrun, -, hp⟩ := solve_writes (Op := Operation)
    (isExactMatvecPair_link (E := E) hA) (meets_extend_link hE) (isSample_link hSample) stream
    (τ := τ) (b := b) (q := q) hbuf hl hz
  have h := (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
      μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
      StoredOut dec m n b q (IsExactStoredRun A b q) (τ.window stream μ.pos (n * b))
        us vs gs rs ss) hrun hp (fun _ _ => w)).link
    (accounts_linkTable E κ W w hcost hW I)
  refine h.mono (le_of_eq ?_) ?_ fun _ hq => hq
  · rw [← push_solveCount]
    exact congrArg _ (stmtCost_solve stream m n b q U.2 V.2 G.2 R.2 S.2)
  · exact stmtPeak_solve_le (fun _ _ => w) w (fun _ _ => le_rfl) stream m n b q U.2 V.2 G.2 R.2 S.2

/-- Total counted execution of the linked program under exact contracts, with the factored
identity. Let the lower interpretation have the exact products with $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ and draws that return the words of the tape, let the scheme `E` be
certified against the exact contract of a basis extension, cost at most `κ d` at the dimensions
`d` and use at most `w` scratch, and let every lower primitive have workspace at most `w`. Then
for all dimensions $(m, n, b, q)$, on five live output blocks in distinct buffers with room for
the output lengths, the linked program terminates within the counts
`NLAlib.Krylov.GolubKahan.Band.linkedSolveCount` and the scratch $\max(m, n)\,b + w$, and the
decoded stored blocks $\mathbf{U}$, $\mathbf{V}$ and the matrix $\mathbf{S}$ assembled from the
packed block columns satisfy
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} = \mathsf{rsvd}(\mathbf{A},
[\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}])\,,$$
with $\mathbf{\Omega}$ the start block decoded from the window of the tape. -/
theorem runs_linkedSolve_rsvd (hA : IsExactMatvecPair dec A I) (hSample : IsSample I)
    (hE : E.Triple I .total ((exactExtendRel dec).spec ExtendOperands))
    (κ : List ℕ → Count Lo Tst) (W : Lo → List ℕ → ℕ) (w : ℕ)
    (hcost : ∀ d offs : List ℕ, d.length = E.nd → offs.length = E.nin + E.nout →
      stmtCost E.body (d ++ offs) ≤ κ d ∧ stmtPeak W E.body (d ++ offs) ≤ w)
    (hW : ∀ o ds, W o ds ≤ w) (stream : ℕ) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    ConditionalRuns I W τ (linkedSolve E stream).body (Env.frame [m, n, b, q] [U, V, G, R, S]) μ
      (linkedSolveCount κ stream m n b q) ((m + (n - m)) * b + w)
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        decodeMatrix dec m (q * b) us *
            (assembleRight b q fun j =>
              decodeMatrix dec ((j + 1) * b + b) b (ss.drop (coefOffsetS b j)))ᴴ *
            (decodeMatrix dec n ((q + 1) * b) vs)ᴴ =
          rsvd A (blockKrylovMatrix (Aᴴ * A)
            (decodeMatrix dec n b (τ.window stream μ.pos (n * b))) q)) :=
  (runs_linkedSolve hA hSample hE κ W w hcost hW stream hbuf hl hz).mono le_rfl le_rfl
    fun _ ⟨hpos, us, vs, gs, rs, ss, hr, hs⟩ =>
      ⟨hpos, us, vs, gs, rs, ss, hr, hs.mul_conjTranspose_mul_conjTranspose_eq_rsvd⟩

/-- Total counted execution of the linked program under rounded contracts, with the executed
history. Let the lower interpretation have products with $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ within the allowances $\delta$, $\delta'$ and draws that return the
words of the tape, let the scheme `E` be certified against the rounded contract of a basis
extension with parameters $(\eta_0, \mu, \varepsilon)$ at the dimensions admitted by `ok`, cost
at most `κ d` at the dimensions `d` and use at most `w` scratch, and let every lower primitive
have workspace at most `w`. If `ok` admits every extension of the run, then on five live output
blocks in distinct buffers with room for the output lengths the linked program terminates within
the counts `NLAlib.Krylov.GolubKahan.Band.linkedSolveCount` and the scratch
$\max(m, n)\,b + w$, consumes $nb$ samples, and the stored blocks decode to a rounded run for
$\mathbf{A}$. There is no orthogonality, rank or nonbreakdown hypothesis. -/
theorem Rounded.runs_linkedSolve {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop}
    (hA : IsMatvecPair dec A δ δ' I) (hSample : IsSample I)
    (hE : E.Triple I .total ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (κ : List ℕ → Count Lo Tst) (W : Lo → List ℕ → ℕ) (w : ℕ)
    (hcost : ∀ d offs : List ℕ, d.length = E.nd → offs.length = E.nin + E.nout →
      stmtCost E.body (d ++ offs) ≤ κ d ∧ stmtPeak W E.body (d ++ offs) ≤ w)
    (hW : ∀ o ds, W o ds ≤ w) (stream : ℕ) (hok₀ : ok n 0 b)
    (hokU : ∀ j < q, ok m (j * b) b) (hokV : ∀ j < q, ok n ((j + 1) * b) b)
    {τ : Tape K} {ν : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : ν.Live [U, V, G, R, S])
    (hz : ν.Room [U, V, G, R, S] (outLens m n b q)) :
    ConditionalRuns I W τ (linkedSolve E stream).body (Env.frame [m, n, b, q] [U, V, G, R, S]) ν
      (linkedSolveCount κ stream m n b q) ((m + (n - m)) * b + w)
      (fun ν' => ν'.pos = ν.pos + n * b ∧ ∃ us vs gs rs ss,
        ν'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsRoundedStoredRun A δ δ' η₀ μ ε b q)
          (τ.window stream ν.pos (n * b)) us vs gs rs ss) := by
  obtain ⟨ν', hrun, -, hp⟩ := Rounded.solve_writes (Op := Operation)
    (isMatvecPair_link (E := E) hA) (meets_extend_link hE) (isSample_link hSample) stream
    hok₀ hokU hokV (τ := τ) hbuf hl hz
  have h := (ConditionalRuns.of_run (Q := fun ν' => ν'.pos = ν.pos + n * b ∧ ∃ us vs gs rs ss,
      ν'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
      StoredOut dec m n b q (IsRoundedStoredRun A δ δ' η₀ μ ε b q) (τ.window stream ν.pos (n * b))
        us vs gs rs ss) hrun hp (fun _ _ => w)).link
    (accounts_linkTable E κ W w hcost hW I)
  refine h.mono (le_of_eq ?_) ?_ fun _ hq => hq
  · rw [← push_solveCount]
    exact congrArg _ (stmtCost_solve stream m n b q U.2 V.2 G.2 R.2 S.2)
  · exact stmtPeak_solve_le (fun _ _ => w) w (fun _ _ => le_rfl) stream m n b q U.2 V.2 G.2 R.2 S.2

/-- Orthogonality and the forward bound of stored factors at the dimensions $(m, n, b, q)$, for
the matrix $\mathbf{A}$, extension parameters $(\eta_0, \mu, \varepsilon)$ and a product
parameter $\varepsilon_{\mathrm{mv}}$: $\mathbf{U}$, $\mathbf{V}$ are decoded from the words
`us`, `vs` and $\mathbf{S}$ is assembled from the packed block columns in `ss`. -/
structure Rounded.StoredBounds (dec : K → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (η₀ μ ε εmv : ℝ)
    (b q : ℕ) (us vs ss : List K) : Prop where
  /-- The Gram defect of the left basis on its nonzero columns is at most
  $\sqrt{3qb}\,\mu$ in the Frobenius norm. -/
  left : frobNorm (gramDefect (decodeMatrix dec m (q * b) us)) ≤ Real.sqrt (3 * q * b) * μ
  /-- The Gram defect of the right basis on its nonzero columns is at most
  $\sqrt{3(q+1)b}\,\mu$ in the Frobenius norm. -/
  right : frobNorm (gramDefect (decodeMatrix dec n ((q + 1) * b) vs)) ≤
    Real.sqrt (3 * (q + 1 : ℕ) * b) * μ
  /-- The forward bound in the spectral norm: the error of
  $\mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}$ is at most the projection error of
  the range of $\mathbf{U}$ plus the rounding term times $\|\mathbf{A}\|_2$. -/
  forward : specNorm (A - decodeMatrix dec m (q * b) us *
        (assembleRight b q fun j =>
          decodeMatrix dec ((j + 1) * b + b) b (ss.drop (coefOffsetS b j)))ᵀ *
        (decodeMatrix dec n ((q + 1) * b) vs)ᵀ) ≤
      specNorm ((1 - rangeProjector (decodeMatrix dec m (q * b) us)) * A) +
        (Real.sqrt (3 * q * b) * μ + Real.sqrt (1 + η₀) *
          ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)))) * specNorm A

/-- The stored output of a rounded run is nearly orthogonal and accurate. If the output words of
the program decode to a rounded run of $q$ steps with block width $b$ for $\mathbf{A}$, with
product allowances $\delta, \delta' \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$ and extension
parameters $(\eta_0, \mu, \varepsilon)$, and $\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$,
$\sqrt{3(q+1)b}\,\mu \le \eta_0$, then the decoded bases satisfy
$\|\mathbf{U}^{\mathsf{T}}\mathbf{U} - \operatorname{diag}(\mathbf{s}_U)\|_{\mathsf{F}} \le
\sqrt{3qb}\,\mu$ and $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} -
\operatorname{diag}(\mathbf{s}_V)\|_{\mathsf{F}} \le \sqrt{3(q+1)b}\,\mu$, with $\mathbf{s}$ the
indicator of the nonzero columns, and, with $\mathbf{P}_{\mathbf{U}}$ the orthogonal projector
onto the range of $\mathbf{U}$,
$$\|\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}\|_2 \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A}\|_2 + \Bigl(\sqrt{3qb}\,\mu +
\sqrt{1 + \eta_0}\,\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})
\bigr)\sqrt{qb(1 + \eta_0)}\Bigr)\|\mathbf{A}\|_2\,.$$ -/
theorem Rounded.storedBounds_of_storedOut {δ δ' η₀ μ ε εmv : ℝ} {ω us vs gs rs ss : List K}
    (h : StoredOut dec m n b q (IsRoundedStoredRun A δ δ' η₀ μ ε b q) ω us vs gs rs ss)
    (hδ : δ ≤ εmv * specNorm A) (hδ' : δ' ≤ εmv * specNorm A) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hmv : 0 ≤ εmv) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    Rounded.StoredBounds dec A η₀ μ ε εmv b q us vs ss := by
  have hle : (3 * q * b : ℝ) ≤ 3 * (q + 1 : ℕ) * b := by
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    push_cast
    nlinarith
  have hwU : Real.sqrt (3 * q * b) * μ ≤ η₀ :=
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) hμ).trans hw
  exact ⟨IsRoundedStoredRun.frobNorm_gramDefect_left_le h hμ hwU,
    IsRoundedStoredRun.frobNorm_gramDefect_right_le h hμ hw,
    IsRoundedStoredRun.specNorm_sub_mul_transpose_mul_transpose_le h hδ hδ' hμ hε hmv hw⟩

end Runs

/-! ### The canonical certificate after linking -/

section Certificate

variable {Lo : Type} [Has OperatorPairOp Lo] [Has SampleOp Lo]

/-- The specification of the linked program over a lower resource model: the full static count of
the linked tree as budget, its static peak as scratch, work and span of the budget, resident
memory of the five output blocks plus the scratch, and the postcondition of the abstract
certificate: the five output blocks decode to an exact run for the supplied matrix from the
start block of the tape. -/
noncomputable def linkedSpecification (R : ResourceModel Lo CmpTst) (E : Impl Lo CmpTst)
    (stream : ℕ) : Specification Lo CmpTst problem where
  budget := staticCost (linkedProgram E stream)
  scratch d := staticPeak R (linkedProgram E stream) d
  work d := R.work (staticCost (linkedProgram E stream) d)
  span d := R.span (staticCost (linkedProgram E stream) d)
  memory d := (outLens (d 0) (d 1) (d 2) (d 3)).sum + staticPeak R (linkedProgram E stream) d
  good d x τ _ μ := Good stream d x.val.1 τ μ

/-- The linked program is certified in total mode over every lower model whose interpretations
have the exact products with the supplied matrix, draws from the tape, and certify the scheme
`E` against the exact contract of a basis extension. For all sizes $(m, n, b, q)$, every real
$m \times n$ matrix and every tape, the counted run of the linked program succeeds within its
static budget, scratch, work, span and memory, consumes $nb$ words of the tape, releases its
scratch and leaves five output blocks that decode to an exact run. The only hypothesis on the
linked tree is that it is well typed for the lower resources, a decidable property of the
scheme. -/
theorem linked_certifies (L : AccessModel Lo CmpTst problem) (E : Impl Lo CmpTst) (stream : ℕ)
    (ht : (linkedProgram E stream).wellTyped L.resources problem.formats = true)
    (hA : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      IsExactMatvecPair id x.val.1 I)
    (hSample : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      IsSample I)
    (hE : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      E.Triple I .total ((exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands)) :
    (linkedProgram E stream).Certifies L (linkedSpecification L.resources E stream) := by
  refine (Algorithm.ofWp (M := L) (S := linkedSpecification L.resources E stream)
    (linkedProgram E stream) ht ?_ (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_).correct
  · intro d _ x I hI τ
    have hw := wp_program (Op := Operation) (I := I.link (linkTable E))
      (isExactMatvecPair_link (hA d x I hI)) (meets_extend_link (hE d x I hI))
      (isSample_link (hSample d x I hI)) stream τ
    rw [Wp, ← run_link] at hw
    exact Wp.mono hw fun _ h _ _ => h
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- The canonical exact certificate of the driver linked with a scheme `E`, over a lower model
whose interpretations have the exact products with the supplied matrix, draws from the tape, and
certify `E` against the exact contract of a basis extension. -/
noncomputable def linkedAlgorithm (L : AccessModel Lo CmpTst problem) (E : Impl Lo CmpTst)
    (stream : ℕ)
    (ht : (linkedProgram E stream).wellTyped L.resources problem.formats = true)
    (hA : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      IsExactMatvecPair id x.val.1 I)
    (hSample : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      IsSample I)
    (hE : ∀ d (x : problem.Input d) (I : Interp Lo CmpTst ℝ), L.contracts d x I →
      E.Triple I .total ((exactExtendRel (𝕜 := ℝ) id).spec ExtendOperands)) :
    Algorithm L (linkedSpecification L.resources E stream) where
  program := linkedProgram E stream
  correct := linked_certifies L E stream ht hA hSample hE

end Certificate

end NLAlib.Krylov.GolubKahan.Band
