/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.StoredWords
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Alg
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Prefix
public import NLAlib.Krylov.CG.HSPCG.StoredProblem
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Canonical rounded stored scalar PCG

The two actual matrix blocks precede the raw right-hand side and four uninitialized vector
capacities. Input admission states spectral windows for the decoded system and inverse
preconditioner. The fixed scalar program initializes zero, performs capped PCG with an actual
pairing stopping cache, and implements both matrix actions through dense scalar row loops.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.problem`: the raw seven-buffer problem.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.program`: the complete scalar-only tree.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.specification`: physical prefix and complete resources.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.algorithm`: total rounded scalar PCG certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded.Stored

open Ops
open scoped Matrix

/-- Both actual raw matrices are symmetric and have their declared spectral windows.
The right-hand side is unrestricted, including zero. -/
def accepts (lowerA upperA lowerP upperP : (Fin 2 → ℕ) → ℝ) (d : Fin 2 → ℕ)
    (systemRaw preconditionerRaw _rhs : List ℝ) : Prop :=
  let A := StoredOperator.denseMatrix (d 0) (d 0) systemRaw
  let P := StoredOperator.denseMatrix (d 0) (d 0) preconditionerRaw
  Aᵀ = A ∧ Pᵀ = P ∧ spectrum ℝ A ⊆ Set.Icc (lowerA d) (upperA d) ∧
    spectrum ℝ P ⊆ Set.Icc (lowerP d) (upperP d)

variable (lowerA upperA lowerP upperP : (Fin 2 → ℕ) → ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ rawA rawP rhs : List ℝ,
    rawA.length = d 0 * d 0 ∧ rawP.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
      accepts lowerA upperA lowerP upperP d rawA rawP rhs)

include supply in
/-- A joint raw mathematical witness supplies the two context blocks and the original
right-hand side. It supplies neither preprocessing nor an execution witness. -/
theorem context_supply (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ context : Fin 2 → List ℝ,
      ∃ x : (CG.RawProblem.problem HSPCG.Stored.outputs domain admitted).Input d,
      (∀ i, (context i).length = d 0 * d 0) ∧
        accepts lowerA upperA lowerP upperP d (context 0) (context 1) x.val.1 := by
  obtain ⟨rawA, rawP, rhs, ha, hp, hrhs, h⟩ := supply d hd
  refine ⟨![rawA, rawP], ⟨⟨rhs, fun i => if i = 0 then rhs.map some
    else List.replicate (HSPCG.Stored.outputs d i) none⟩, rfl, hrhs⟩, ?_, h⟩
  intro i
  fin_cases i
  · exact ha
  · exact hp

/-- The raw system and inverse-preconditioner words, original right-hand side and four
uninitialized output capacities are declared through the shared context problem constructor. -/
def problem : Problem ℝ 2 7 :=
  (CG.RawProblem.problem HSPCG.Stored.outputs domain admitted).withContext 2
    (fun d _ => d 0 * d 0)
    (fun d c rhs => accepts lowerA upperA lowerP upperP d (c 0) (c 1) rhs)
    (context_supply lowerA upperA lowerP upperP domain admitted supply)

variable {lowerA upperA lowerP upperP domain admitted supply}

/-- The reference system matrix is decoded from the actual first context block. -/
def matrix {d : Fin 2 → ℕ}
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 0)

/-- The reference inverse preconditioner is decoded from the actual second context block. -/
def preconditioner {d : Fin 2 → ℕ}
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 1)

/-- The vector-level tree forwards both raw contexts and initializes the supplied iterate.
Every operator call already consists of dense scalar rows; BLAS lowering follows separately. -/
def blasProgram : Program RCLikeBlas.Operation CmpTst 2 7 :=
  ⟨.frame [.var 0, .var 1]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨3, .var 5⟩,
      ⟨4, .var 6⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩]
    ((zeroStart (Op := Signature) (Tst := CmpTst)).linkContext 2 2
      (StoredContext.table 2 0 1))⟩

/-- The entire implementation has scalar operations as its target signature. This includes
all BLAS calls and both operator calls, with no remaining operator or vector primitive. -/
def program : Program ScalarOp CmpTst 2 7 := blasProgram.link RoundedScalarBlas.table

/-- Both raw matrices and every supplied vector capacity contribute to resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :
    (problem lowerA upperA lowerP upperP domain admitted supply).initialBytes d x =
      2 * d 0 * d 0 + 5 * d 0 := by
  have h := Problem.withContext.initialBytes_eq d x
  rw [CG.RawProblem.initialBytes_eq] at h
  refine h.trans ?_
  simp [HSPCG.Stored.outputs, List.ofFn_succ]
  ring

variable (lowerA upperA lowerP upperP domain admitted supply)

/-- The actual scalar program's complete canonical resources and physical rounded prefix.
The prefix length can be zero. An early stop has zero residual; reaching the cap makes no
convergence claim. The oracle is the actual stored scalar preconditioner action. -/
noncomputable def specification (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst
      (problem lowerA upperA lowerP upperP domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak RoundedScalarBlas.resources program
  work d := RoundedScalarBlas.resources.work (staticCost program d)
  span d := RoundedScalarBlas.resources.span (staticCost program d)
  memory d := 2 * d 0 * d 0 + 5 * d 0 + staticPeak RoundedScalarBlas.resources program d
  good d x _ _ mem := mem.pos = 0 ∧ ∃ m ≤ d 1, ∃ s rho,
    StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0) s mem ∧
      RunPrefix (matrix x) (preconditioner x)
        (StoredContext.oracle hM hu (d 0) (x.val.1.1 1)) (decv id (d 0) x.val.1.2)
        (E d) m s rho ∧ (m < d 1 → s.r = 0)

/-- Raw spectral windows and explicit scalar/cap precision imply total rounded execution,
physical initialized-prefix output, and every resource bound of the actual scalar-only tree.
No local oracle-correctness or successful-execution callback is required. -/
noncomputable def algorithm (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hAccuracy : ∀ d, domain d →
      Standard.Accuracy (StoredContext.relativeError u (d 0)) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lowerA d) (hp : ∀ d, domain d → 0 < lowerP d)
    (hAp : ∀ d, domain d → 6 * E d * upperA d ≤ lowerA d)
    (hPp : ∀ d, domain d → 6 * E d * upperP d ≤ lowerP d)
    (hwindow : ∀ d, domain d → E d *
      (1024 * (upperA d / lowerA d) * (upperP d / lowerP d)) ^ (d 1 + 1) ≤ 1 / 2) :
    Algorithm (RoundedScalarBlas.model
      (problem lowerA upperA lowerP upperP domain admitted supply) M)
      (specification lowerA upperA lowerP upperP domain admitted supply M u hM hu E) := by
  refine Algorithm.ofWp program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    obtain ⟨hS, hCmp⟩ := RoundedScalarBlas.model_laws hI
    obtain ⟨hS', hB⟩ := RoundedScalarBlas.laws hM hu hS
    have hD := RoundedScalarBlas.isFn_dot hS
    let μ := (problem lowerA upperA lowerP upperP domain admitted supply).initial d x
    have hlen (i : Fin 5) : μ.store.len (2+i.val) =
        if i = 0 then d 0 else HSPCG.Stored.outputs d i :=
      (Problem.withContext.initial_len_original d x i).trans
        (CG.RawProblem.initial_len d (Problem.withContext.originalInput x) i)
    have hb := Problem.withContext.initial_readBlock_original d x (0 : Fin 5)
      (show (Problem.withContext.originalInput x).val.2 0 = x.val.1.2.map some by
        rw [CG.RawProblem.input_buffers]; simp [Problem.withContext.originalInput])
    have hbl : x.val.1.2.length = d 0 :=
      CG.RawProblem.length_input d (Problem.withContext.originalInput x)
    rw [hbl] at hb
    have hExtra := Problem.withContext.extra_input x
    have hw := stored_zeroStart_wp (n := d 0) (cap := d 1) (cutoff := 2) (τ := τ)
      (μ := μ) (B := (2, 0)) (X := (3, 0)) (R := (4, 0)) (Z := (5, 0)) (P := (6, 0))
      hS' hM hu hB hD hCmp [(0, 0), (1, 0)] 0 1 (x.val.1.1 0) (x.val.1.1 1)
      (by simp) (by simp [μ, Problem.initial])
      (Problem.withContext.initial_readBlock_context d x 0)
      (Problem.withContext.initial_readBlock_context d x 1)
      (by simp) (hAccuracy d hd) hExtra.1 hExtra.2.1 (ha d hd) (hp d hd)
      hExtra.2.2.1 hExtra.2.2.2 (hAp d hd) (hPp d hd) (hwindow d hd)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [Mem.Live, μ, Problem.initial]) hb (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
        exact ⟨by simpa [μ, HSPCG.Stored.outputs] using (hlen 1).ge,
          by simpa [μ, HSPCG.Stored.outputs] using (hlen 2).ge,
          by simpa [μ, HSPCG.Stored.outputs] using (hlen 3).ge,
          by simpa [μ, HSPCG.Stored.outputs] using (hlen 4).ge⟩)
    change Mode.total.Holds (eval I τ (blasProgram.body.link RoundedScalarBlas.table)
      (Program.environment (b := 7) d) μ) _
    rw [Ops.run_link]
    apply wp_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])
    exact hw.mono fun mem h _ _ => by
      simpa [specification, matrix, preconditioner, μ, Problem.initial] using h
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl


end NLAlib.Krylov.CG.HSPCG.Rounded.Stored
