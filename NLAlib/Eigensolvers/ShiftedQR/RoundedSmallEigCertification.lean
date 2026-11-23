/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Randomized
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEigRoutine
public import NLAlib.Eigensolvers.SmallEig.Certification

/-!
# The rounded shifted QR algorithm with the small-eigenvalue program as a canonical certificate

The rounded shifted QR algorithm with no `SmallEig` oracle as one counted run: the program is
`NLAlib.ShiftedQR.roundedShQRSmallEig`, which runs the small-eigenvalue program
`NLAlib.SmallEig.smallEigProg` as its leaf. The program, fixed before every size
and input, is a canonical certificate (`NLAlib.Ops.Algorithm`) over the model of the
small-eigenvalue solver (`NLAlib.SmallEig.smallEigModel`: scalar arithmetic of a machine `Mch`,
exact dimension literals, comparisons and index conversion, draws of the tape streams and the
exact polar disk sampler; every contract a function), with explicit work and span polynomials;
and the probability that this counted run fails, exceeds a resource bound of the specification,
or fails to store the spectrum of a nearby matrix is at most $\varphi$.

Every primitive, query and structural instruction costs one unit, so the work and the span are
the number of instructions of the static count, `SmallEig`'s instructions included: no kernel
weight remains. Hence, unlike the certificate with the oracle, the shift degree $k$ may exceed
$n$.

The every-tape output claim (`NLAlib.Ops.Specification.good`) is the frame: the run writes only
the matrix, the output and the failure word. No accuracy claim holds on every tape: on a tape
where the small-eigenvalue program misses its forward accuracy a leaf block stores its words as
eigenvalues with the failure word $0$. The spectrum claim is the postcondition of
`NLAlib.Ops.Specification.Accepts` in
`NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`, bounded through the
probabilistic program logic (`NLAlib.Ops.Algorithm.measureReal_not_accepts_le_of_wp`).

## Main definitions

* `NLAlib.ShiftedQR.shqrSmallEigProgram`, `NLAlib.ShiftedQR.shqrSmallEigProblem`: the program and
  the problem.
* `NLAlib.ShiftedQR.shqrSmallEigWork`: the explicit work and span polynomial.
* `NLAlib.ShiftedQR.shqrSmallEigAlgorithm`: the certificate.

## Main results

* `NLAlib.ShiftedQR.shqrSmallEigProgram_work_le`: the work and span of every run.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`: the headline, on
  one run.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops SmallEig MeasureTheory ProbabilityTheory
open scoped Matrix

/-! ### The program and the problem -/

/-- **The rounded shifted QR program with the small-eigenvalue program**:
`NLAlib.ShiftedQR.roundedShQRSmallEig` with the Gaussian stream `sG` at the order `d 0 + 1`, the
shift degree `d 1`, `d 2` parameter words, the iteration cap `d 3` and the cap `d 4` of the
small-eigenvalue program, on the five supplied buffers (matrix, threshold word, parameter words,
output, failure word). -/
def shqrSmallEigProgram (sG : ℕ) : Program SmallEigOp Tst 5 5 :=
  (shqrSmallEigRoutine (O := SmallEigOp) (Q := Tst) sG).close 5 5

/-- **The inputs** at the sizes `d`: the matrix of order `d 0 + 1` and the reals
$B, \Gamma, \Sigma, \delta, \varphi$. -/
structure ShQRSmallEigData (d : Fin 5 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The condition bound. -/
  B : ℝ
  /-- The separation. -/
  Γ : ℝ
  /-- The norm bound. -/
  S : ℝ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$
are exact, and the sizes are those of some parameter reals. -/
def ShQRSmallEigSizes (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail) (d : Fin 5 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧
    ∃ B Γ S δ φ : ℝ, d 1 = shqrDegree (4 * B) ∧
      d 2 = (shqrSmallEigParams (d 0) (d 1) B Γ S δ φ c₁ c₂).length ∧
      d 3 = shqrCap (d 0) B Γ S δ ∧ d 4 = shqrSmallEigCap (d 0) (d 1) B Γ S δ φ c₁ c₂

/-- **The admitted inputs** of the rounded shifted QR algorithm with the small-eigenvalue
program on the machine `Mch`, with the tail records $c_1, c_2$, at the sizes
`NLAlib.ShiftedQR.ShQRSmallEigSizes`: every matrix of order `d 0 + 1` and all reals
$B, \Gamma, \Sigma, \delta, \varphi$ whose shift degree, number of parameter words and two caps
are the sizes `d 1`, `d 2`, `d 3`, `d 4`. The first operand holds the words of the matrix. The
reals are in no buffer: the second operand holds the deflation threshold word and the third
the parameter words, both computed from them. The accumulator holds the identity, which the
algorithm requires of it, and the failure word is blank. -/
noncomputable def shqrSmallEigInputs (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) :
    (shqrSmallEigRoutine (O := SmallEigOp) (Q := Tst) 0).Domain ℝ 5 5 where
  valid := ShQRSmallEigSizes Mch c₁ c₂
  In := ShQRSmallEigData
  accepts d x := d 1 = shqrDegree (4 * x.B) ∧
    d 2 = (shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂).length ∧
    d 3 = shqrCap (d 0) x.B x.Γ x.S x.δ ∧
    d 4 = shqrSmallEigCap (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) ShQRSmallEigData.matrix,
    .derived 1 (fun x => [shqrDeflationThreshold (d 0) (d 1) x.B x.Γ x.S x.δ x.φ]) (fun _ => rfl),
    .derivedOfLength (d 2) (fun x => shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂),
    .derived (2 * ((d 0 + 1) * (d 0 + 1)))
      (fun _ => matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ))
      (fun _ => length_matrixWords _),
    .blank 1]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Slot.derivedOfLength, Access.readable, Codec.complexMatrix,
          List.ofFn_succ])
  Unstored _ := ℝ × ℝ × ℝ × ℝ × ℝ
  unstored _ x := (x.B, x.Γ, x.S, x.δ, x.φ)
  faithful d x y hu h := by
    have h0 := h 0
    simp only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] at h0
    have hm := (Codec.complexMatrix (d 0 + 1)).encode_injective h0
    obtain ⟨_, _, _, _, _, _⟩ := x
    obtain ⟨_, _, _, _, _, _⟩ := y
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hu
    obtain rfl : _ = _ := hm
    rfl
  admitted := admitted
  inhabited d hd := by
    obtain ⟨-, B, Γ, S, δ, φ, hk, hp, hF, hT⟩ := hd
    exact ⟨⟨0, B, Γ, S, δ, φ⟩, hk, hp, hF, hT⟩

/-- **The problem** of the rounded shifted QR algorithm with the small-eigenvalue program on the
machine `Mch`, with the tail records $c_1, c_2$: the problem of the admitted inputs
`NLAlib.ShiftedQR.shqrSmallEigInputs`. -/
noncomputable abbrev shqrSmallEigProblem (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) : Problem ℝ 5 5 :=
  (shqrSmallEigInputs Mch c₁ c₂ admitted).problem

variable {Mch : Machine ℝ} {c₁ c₂ : PolyLogTail} {admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d}

/-- The shift degree of an input of the problem is the degree of (eqn:setk) at $4B$. -/
theorem shqrSmallEigProblem_degree_eq (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    d 1 = shqrDegree (4 * x.val.1.B) :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).accepts_data x).1

/-- The number of parameter words of an input of the problem. -/
theorem shqrSmallEigProblem_words_eq (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    d 2 = (shqrSmallEigParams (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁
      c₂).length :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).accepts_data x).2.1

/-- The iteration cap of an input of the problem. -/
theorem shqrSmallEigProblem_cap_eq (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    d 3 = shqrCap (d 0) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).accepts_data x).2.2.1

/-- The cap of the small-eigenvalue program of an input of the problem. -/
theorem shqrSmallEigProblem_smallEigCap_eq (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    d 4 = shqrSmallEigCap (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ
      c₁ c₂ :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).accepts_data x).2.2.2

/-- The five supplied buffers of an input: the matrix words, the deflation threshold word, the
parameter words, the identity accumulator and the failure word. -/
theorem shqrSmallEigProblem_buffers (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    x.val.2 = ![(matrixWords x.val.1.matrix).map some,
      [some (shqrDeflationThreshold (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ
        x.val.1.φ)],
      (shqrSmallEigParams (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁
        c₂).map some,
      (matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)).map some, [none]] := by
  rw [(shqrSmallEigInputs Mch c₁ c₂ admitted).buffers_eq x]
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact Slot.buffer_derivedOfLength (shqrSmallEigProblem_words_eq d x).symm
  · rfl
  · rfl

/-- The initial memory holds the input of the algorithm (`NLAlib.ShiftedQR.ShQRSmallEigInput`)
at the five supplied buffers. -/
theorem shqrSmallEigProblem_initial_input (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    ShQRSmallEigInput (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂ (0, 0)
      (1, 0) (2, 0) (3, 0) (4, 0) x.val.1.matrix
      ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x) := by
  have hb := shqrSmallEigProblem_buffers d x
  have hs : ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store =
      List.ofFn ![(matrixWords x.val.1.matrix).map some,
        [some (shqrDeflationThreshold (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ
        x.val.1.φ)],
        (shqrSmallEigParams (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁
        c₂).map some,
        (matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)).map some, [none]] := by
    change List.ofFn x.val.2 = _
    rw [hb]
  have hA := Problem.initial_readBlock (P := shqrSmallEigProblem Mch c₁ c₂ admitted) d x
    (0 : Fin 5) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := shqrSmallEigProblem Mch c₁ c₂ admitted) d x
    (2 : Fin 5)
    (xs := shqrSmallEigParams (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂)
    (by rw [hb]; rfl)
  have hU := Problem.initial_readBlock (P := shqrSmallEigProblem Mch c₁ c₂ admitted) d x
    (3 : Fin 5) (xs := matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ))
    (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, ⟨1, by simpa [HoldsMatrix] using hU⟩, ?_, ?_, ?_⟩
  · simp [Mem.Live, Problem.initial]
  · simp [Mem.Room, hs, Store.len, List.ofFn_succ]
  · refine ShQRViewsApart.of_apart ?_
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil]
    disjoint
  · simpa [HoldsMatrix] using hA
  · rw [hs]
    simp [Store.get, List.ofFn_succ]
  · simpa using hP

/-- The accumulator buffer holds the identity. -/
theorem shqrSmallEigProblem_initial_accumulator (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.readBlock 3 0
        (2 * ((d 0 + 1) * (d 0 + 1))) =
      some (matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)) := by
  have hb := shqrSmallEigProblem_buffers d x
  have hU := Problem.initial_readBlock (P := shqrSmallEigProblem Mch c₁ c₂ admitted) d x
    (3 : Fin 5) (xs := matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ))
    (by rw [hb]; rfl)
  simpa using hU

/-- The seven operands of the program's frame are live in the initial memory. -/
theorem shqrSmallEigProblem_initial_live (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).Live
      [(0, 0), (1, 0), (2, 0), (3, 0), (0, 0), (3, 0), (4, 0)] := by
  have hl := (shqrSmallEigProblem_initial_input (admitted := admitted) d x).1
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hl _ (by simp)

/-! ### The work and span polynomial -/

/-- The slot bounds of the program's initial indices: the five sizes, then five zero offsets. -/
def shqrSmallEigSlots : List WorkMono :=
  [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩, ⟨1, [0, 0, 0, 0, 1]⟩] ++
    List.replicate 5 (WorkMono.const 0)

-- The kernel's recursion over the whole instrumented tree exceeds its default depth.
set_option maxRecDepth 100000 in
/-- The monomial bound of the instructions of the instrumented program is
$967736\,b_0^3 b_1^4 b_2 b_3 b_4^2$ (`NLAlib.ShiftedQR.shqrSmallEigWork`). -/
theorem stmtWorkMono_shqrSmallEigProgram (sG : ℕ) :
    stmtWorkMono (shqrSmallEigProgram sG).body.instrument shqrSmallEigSlots =
      ⟨967736, [3, 4, 1, 1, 2]⟩ := by
  rw [stmtWorkMono_instrument]; kernel_rfl

/-- **The work (and span) polynomial** of the rounded shifted QR algorithm with the
small-eigenvalue program at the sizes $(n, k, n_p, F, T)$ = `d`:
$967736\,(n + 1)^3(k + 1)^4(n_p + 1)(F + 1)(T + 1)^2$, the
monomial bound of the instructions of the instrumented program, each of unit weight; the
instructions of the small-eigenvalue program are among them (one bound over the whole tree). The
parameter words (thresholds, scales and caps, real numbers with logarithms and roots) are
supplied in the input and their computation is not charged, as for the merged
algorithm. The monomial is an envelope of the paper's count $n^4 + n^3\log^2$, not its shape: the
cap $T$ = `NLAlib.SmallEig.smallEigCap` is the largest loop count ($m$, $t$, $m_2$), a logarithm of
$n_{\max}\Sigma/(\delta\varphi)$ up to constants (bounded in the proof of
`NLAlib.SmallEig.logb_inv_uSmallEig_le`). -/
def shqrSmallEigWork (d : Fin 5 → ℕ) : ℕ :=
  967736 * (d 0 + 1) ^ 3 * (d 1 + 1) ^ 4 * (d 2 + 1) * (d 3 + 1) * (d 4 + 1) ^ 2

/-- The number of instructions of the static count of the program is at most
`NLAlib.ShiftedQR.shqrSmallEigWork`. -/
theorem size_staticCost_shqrSmallEigProgram_le (sG : ℕ) (d : Fin 5 → ℕ) :
    Count.size (staticCost (shqrSmallEigProgram sG) d) ≤ shqrSmallEigWork d := by
  have hσ : SlotsLe [d 0 + 1, d 1 + 1, d 2 + 1, d 3 + 1, d 4 + 1]
      (Program.environment (b := 5) d).idx shqrSmallEigSlots := by
    change List.Forall₂ _ [d 0, d 1, d 2, d 3, d 4, 0, 0, 0, 0, 0] _
    simp [shqrSmallEigSlots, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp) (shqrSmallEigProgram sG).body.instrument hσ
  rw [stmtWorkMono_shqrSmallEigProgram] at h
  simpa [staticCost, WorkMono.eval, shqrSmallEigWork, mul_assoc] using h

/-- The work and span of every run: under the unit costs
`NLAlib.SmallEig.smallEigResources`, every successful counted run of the program has work and
span at most `NLAlib.ShiftedQR.shqrSmallEigWork` at its sizes. -/
theorem shqrSmallEigProgram_work_le {K : Type} (sG : ℕ) {I : Interp SmallEigOp Tst K}
    {τ : Tape K} {formats : Fin 5 → StorageFormat} {d : Fin 5 → ℕ} {m : Mem K}
    {st : St (SmallEigOp ⊕ Bookkeeping) Tst K}
    (hr : exec (shqrSmallEigProgram sG) I smallEigResources formats τ d m = some st) :
    smallEigResources.work st.cost ≤ shqrSmallEigWork d ∧
      smallEigResources.span st.cost ≤ shqrSmallEigWork d := by
  have h := (size_mono (exec_static hr).1).trans (size_staticCost_shqrSmallEigProgram_le sG d)
  exact ⟨(smallEigResources_work _).trans_le h, (smallEigResources_span _).trans_le h⟩

/-! ### The certificate -/

/-- The payload words of the five supplied buffers. -/
def shqrSmallEigInputWords (d : Fin 5 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + 1 + d 2 + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

theorem shqrSmallEigProblem_initialBytes (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    (shqrSmallEigProblem Mch c₁ c₂ admitted).initialBytes d x = shqrSmallEigInputWords d := by
  refine ((shqrSmallEigInputs Mch c₁ c₂ admitted).initialBytes_eq x).trans ?_
  simp [shqrSmallEigInputs, Slot.len, Slot.derivedOfLength, Codec.complexMatrix, List.ofFn_succ,
    shqrSmallEigInputWords, Nat.add_assoc]

/-- **The specification of the rounded shifted QR algorithm with the small-eigenvalue program**:
the budget, scratch and resident memory of the static count, the work and the span
`NLAlib.ShiftedQR.shqrSmallEigWork`, and on every tape the frame: the run writes only the
matrix, the output and the failure word. -/
noncomputable def shqrSmallEigSpecification (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) (sG : ℕ) :
    Specification SmallEigOp Tst (shqrSmallEigProblem Mch c₁ c₂ admitted) where
  budget := staticCost (shqrSmallEigProgram sG)
  scratch := staticPeak smallEigResources (shqrSmallEigProgram sG)
  work := shqrSmallEigWork
  span := shqrSmallEigWork
  memory d := shqrSmallEigInputWords d + staticPeak smallEigResources (shqrSmallEigProgram sG) d
  good d x _ _ m := (shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x |>.store.EqOff
    (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store

/-- The program terminates on every admitted input, tape and interpretation of the model, and
writes only the matrix, the output and the failure word.
A fragment of the tree `NLAlib.ShiftedQR.shqrSmallEigSpecification`. -/
theorem shqrSmallEigProgram_wp {sU sG : ℕ} {d : Fin 5 → ℕ} (hd : ShQRSmallEigSizes Mch c₁ c₂ d)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (shqrSmallEigProblem Mch c₁ c₂ admitted) Mch sU).contracts d x I)
    (τ : Tape ℝ) :
    Wp .total I τ (shqrSmallEigProgram sG).body (Program.environment (b := 5) d)
      (fun m => ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.EqOff
        (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store)
      ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x) := by
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := shqrSmallEigProblem_initial_input (admitted := admitted) d x
  have hW := roundedShQRSmallEig_terminates (O := SmallEigOp) (Q := Tst) (sG := sG) hS hL hd.1
    hQ hC hSmp hDisk (shqrSmallEigProblem_degree_eq d x) hin τ
  refine wp_frame ?_ ?_ (shqrSmallEigProblem_initial_live d x) (Wp.mono hW fun _ h => h.1)
  · simp [Program.environment, IExp.evalList, IExp.eval, shqrSmallEigDims,
      shqrSmallEigProblem_words_eq d x, shqrSmallEigProblem_cap_eq d x,
      shqrSmallEigProblem_smallEigCap_eq d x, List.ofFn_succ]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- The program passes the storage discipline of the costs. -/
theorem shqrSmallEigProgram_wellTyped (sG : ℕ) :
    (shqrSmallEigProgram sG).wellTyped smallEigResources
      (shqrSmallEigProblem Mch c₁ c₂ admitted).formats = true := by
  kernel_rfl

/-- **The rounded shifted QR algorithm with the small-eigenvalue program as a canonical
certificate**: the fixed program `NLAlib.ShiftedQR.shqrSmallEigProgram`, over the model
`NLAlib.SmallEig.smallEigModel` (no `SmallEig` oracle) with the unit costs, succeeds on every
admitted input, interpretation of the model and tape, within the static budget, scratch and
memory, with work and span at most `NLAlib.ShiftedQR.shqrSmallEigWork`, writing only the matrix,
the output and the failure word. The output's accuracy holds with probability at least
$1 - \varphi$ (`NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`).
Algorithm: shifted-qr-rounded (run model) -/
noncomputable def shqrSmallEigAlgorithm (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) (sU sG : ℕ) :
    Algorithm (smallEigModel (shqrSmallEigProblem Mch c₁ c₂ admitted) Mch sU)
      (shqrSmallEigSpecification Mch c₁ c₂ admitted sG) :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).cast (shqrSmallEigRoutine sG) rfl rfl).algorithm
    (fun _ x => shqrSmallEigSpec Mch x.B x.Γ x.S x.δ x.φ c₁ c₂)
    (fun _ _ _ _ hI => by
      obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
      exact shqrSmallEigRoutine_meets hS hL hQ hC hSmp hDisk)
    (fun d hd x hx _ => by
      have hw : (Slot.derivedOfLength (d 2) fun x : ShQRSmallEigData d =>
          shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂).words x =
            shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂ :=
        Slot.words_derivedOfLength hx.2.1.symm
      refine ⟨hd.1, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, x.matrix, 1, ?_⟩
      change [matrixWords x.matrix, [shqrDeflationThreshold (d 0) (d 1) x.B x.Γ x.S x.δ x.φ],
        (Slot.derivedOfLength (d 2) fun x : ShQRSmallEigData d =>
          shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂).words x,
        matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)] = _
      rw [hw]
      rfl)
    (fun d _ x τ m' hfr _ ys _ _ c _ => by
      change Store.EqOff (Fp.blocks [(0, 0), (3, 0), (4, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 2 * ((d 0 + 1) * (d 0 + 1)), 1]) _ _ at hfr
      refine hfr.mono ?_
      unfold shqrFp
      fp_sub)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le (size_staticCost_shqrSmallEigProgram_le sG d))
    (fun d _ => (smallEigResources_span _).trans_le (size_staticCost_shqrSmallEigProgram_le sG d))
    (fun d _ x =>
      Nat.add_le_add_right (shqrSmallEigProblem_initialBytes (admitted := admitted) d x).le _)
    (ht := shqrSmallEigProgram_wellTyped (admitted := admitted) sG)

/-! ### The headline on one run -/

/-- **The rounded shifted QR algorithm with no oracle, on one run**
([BanksGarzaVargasSrivastava2022, Theorem 6.3 with Theorem 1.4's quantifiers, corrected];
`SmallEig` by [BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3]). Let the machine
`Mch` have the standard model at $\boldsymbol{u}$; let the tape $\xi$ have the stream laws `law`,
with `law` $s_U$ uniform on $[0, 1]$ and `law` $s_G$ the standard real Gaussian law; let the
eigenvalue gap and the eigenvector condition of a complex Ginibre perturbation have the tails
$c_1$, $c_2$ with $b_1, b_2 > 0$. Let $(n, k, n_p, F, T)$ = `d` be admitted and let the input `x`
hold an upper Hessenberg $\mathbf{H}$ of order $n + 1$ with
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\kappa(\mathbf{V}) \le B$,
eigenvalues separated by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $\boldsymbol{u} \le \boldsymbol{u}_0$
(`NLAlib.ShiftedQR.uShQRSchur`). Let `I` meet the model, be measurable and read the tape only
in its windows. Then
$$\mathbb{P}\bigl[\mathsf{shqrSmallEigAlgorithm}(\mathbf{H}) \text{ fails, exceeds its
  budget, scratch, memory, work or span, writes outside the matrix, the output and the failure
  word, or lists no } \operatorname{spec}(\mathbf{H} + \mathbf{E}),\
  \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,,$$
on one counted run, with the work and the span `NLAlib.ShiftedQR.shqrSmallEigWork`.
Result: shifted-qr-rounded-small-eig-certificate-accuracy -/
theorem roundedShQRSmallEig_algorithm_measureReal_not_accepts_le {u : ℝ}
    (hM : StdModel u id Mch) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hU : law sU = volume.restrict (Set.Icc 0 1)) (hG : law sG = gaussianReal 0 1)
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition) (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {d : Fin 5 → ℕ} (hd : ShQRSmallEigSizes Mch c₁ c₂ d)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (shqrSmallEigProblem Mch c₁ c₂ admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {V : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ} {ev : Fin (d 0 + 1) → ℂ}
    (hHess : IsUpperHessenberg x.val.1.matrix) (hV : IsUnit V)
    (hHV : x.val.1.matrix * V = V * Matrix.diagonal ev)
    (hκ : pseudoConditionNumber V ≤ x.val.1.B) (hΓ : 0 < x.val.1.Γ)
    (hgap : ∀ i j, i ≠ j → x.val.1.Γ ≤ ‖ev i - ev j‖)
    (hHS : specNorm x.val.1.matrix ≤ x.val.1.S) (hδ : 0 < x.val.1.δ)
    (hδS : x.val.1.δ ≤ x.val.1.S) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uShQRSchur (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (shqrSmallEigSpecification Mch c₁ c₂ admitted sG).Accepts
        (shqrSmallEigAlgorithm Mch c₁ c₂ admitted sU sG).program I smallEigResources (ξ ω) d x
      fun _ m => ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.EqOff
          (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store ∧
        ShQRSpectrum (0, 0) (3, 0) (4, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := shqrSmallEigProblem_initial_input (admitted := admitted) d x
  -- the headline (`roundedShQRSmallEig_measureReal_not_spectrum_le`), applied as it is stated
  have hT := roundedShQRSmallEig_measureReal_not_spectrum_le (O := SmallEigOp) (Q := Tst)
    (sG := sG) hS hM hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hHess hV hHV hκ hΓ
    hgap hHS hδ hδS hφ hφ1 (shqrSmallEigProblem_degree_eq d x) hu hin hξ
  refine (shqrSmallEigAlgorithm Mch c₁ c₂ admitted sU sG).measureReal_not_accepts_le_of_wp
    hd x I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  refine hω (wp_frame ?_ ?_ (shqrSmallEigProblem_initial_live d x) hW)
  · simp [Program.environment, IExp.evalList, IExp.eval, shqrSmallEigDims,
      shqrSmallEigProblem_words_eq d x, shqrSmallEigProblem_cap_eq d x,
      shqrSmallEigProblem_smallEigCap_eq d x, List.ofFn_succ]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]


/-! ### With the proved random-matrix tails -/

/-- **The rounded shifted QR algorithm with no oracle, on one run, unconditional**.
The unconditional form of
`NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`
([BanksGarzaVargasSrivastava2022, Theorem 6.3 with Theorem 1.4's quantifiers, corrected]): the
eigenvalue-gap and eigenvector-condition tails of a complex Ginibre perturbation are proved, at
the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(2048e, 11/3, 2/3, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: shifted-qr-rounded-small-eig-certificate-accuracy -/
theorem roundedShQRSmallEig_algorithm_measureReal_not_accepts_le_unconditional
    {admitted : ∃ d, ShQRSmallEigSizes Mch ginibreGapTail
      ginibreConditionTail d} {u : ℝ}
    (hM : StdModel u id Mch) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hU : law sU = volume.restrict (Set.Icc 0 1)) (hG : law sG = gaussianReal 0 1)
    {d : Fin 5 → ℕ} (hd : ShQRSmallEigSizes Mch ginibreGapTail
      ginibreConditionTail d)
    (x : (shqrSmallEigProblem Mch ginibreGapTail ginibreConditionTail
      admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (shqrSmallEigProblem Mch ginibreGapTail
      ginibreConditionTail admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {V : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ} {ev : Fin (d 0 + 1) → ℂ}
    (hHess : IsUpperHessenberg x.val.1.matrix) (hV : IsUnit V)
    (hHV : x.val.1.matrix * V = V * Matrix.diagonal ev)
    (hκ : pseudoConditionNumber V ≤ x.val.1.B) (hΓ : 0 < x.val.1.Γ)
    (hgap : ∀ i j, i ≠ j → x.val.1.Γ ≤ ‖ev i - ev j‖)
    (hHS : specNorm x.val.1.matrix ≤ x.val.1.S) (hδ : 0 < x.val.1.δ)
    (hδS : x.val.1.δ ≤ x.val.1.S) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uShQRSchur (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ
      ginibreGapTail ginibreConditionTail)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (shqrSmallEigSpecification Mch ginibreGapTail
      ginibreConditionTail admitted sG).Accepts (shqrSmallEigAlgorithm Mch ginibreGapTail
        ginibreConditionTail admitted sU sG).program I smallEigResources (ξ ω) d x
      fun _ m => ((shqrSmallEigProblem Mch ginibreGapTail
        ginibreConditionTail admitted).initial d x).store.EqOff
          (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store ∧
        ShQRSpectrum (0, 0) (3, 0) (4, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := by
  apply roundedShQRSmallEig_algorithm_measureReal_not_accepts_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-! ### The randomized claim -/

/-- **The randomized claim of the certificate of rounded shifted QR with the small-eigenvalue
leaf** ([BanksGarzaVargasSrivastava2022, Theorem 6.3], corrected). The entries of the tape are
independent, uniform on $[0, 1]$ on the stream $s_U$ and standard Gaussian on the stream $s_G$.
For an upper Hessenberg input $\mathbf{H}$ that is diagonalized by some $\mathbf{V}$ with
$\kappa(\mathbf{V}) \le B$ and eigenvalues separated by $\Gamma > 0$, with
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}_0$ (`NLAlib.ShiftedQR.uShQRSchur`), and an interpretation
that is measurable and reads the tape only in its windows, the counted run writes only the
matrix, the output and the failure word and lists the spectrum of a matrix within $\delta$ of
the input, except with probability at most $\varphi$. The Ginibre tails $c_1$, $c_2$ are
hypotheses; `NLAlib.ShiftedQR.shqrSmallEigGinibreClaim` has them proved. -/
noncomputable def shqrSmallEigClaim (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d)
    (sU sG : ℕ) (hs : sU ≠ sG) {u : ℝ} (hM : StdModel u id Mch) (hA : c₁.BoundsGinibreGap)
    (hB : c₂.BoundsGinibreCondition) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    RandomizedClaim (shqrSmallEigAlgorithm Mch c₁ c₂ admitted sU sG) where
  law _ _ := TapeModel.streams [(sU, volume.restrict (Set.Icc 0 1)), (sG, gaussianReal 0 1)]
  admits d x := IsUpperHessenberg x.val.1.matrix ∧
    (∃ (V : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ) (ev : Fin (d 0 + 1) → ℂ), IsUnit V ∧
      x.val.1.matrix * V = V * Matrix.diagonal ev ∧ pseudoConditionNumber V ≤ x.val.1.B ∧
        ∀ i j, i ≠ j → x.val.1.Γ ≤ ‖ev i - ev j‖) ∧
    0 < x.val.1.Γ ∧ specNorm x.val.1.matrix ≤ x.val.1.S ∧ 0 < x.val.1.δ ∧
    x.val.1.δ ≤ x.val.1.S ∧ 0 < x.val.1.φ ∧ x.val.1.φ ≤ 1 ∧
    u ≤ uShQRSchur (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂
  interprets _ _ I := I.IsMeasurable ∧
    ∃ win : SmallEigOp → List ℕ → ℕ, ∀ o, I.TapeLocal o (win o)
  event d x _ _ m := ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.EqOff
      (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store ∧
    ShQRSpectrum (0, 0) (3, 0) (4, 0) x.val.1.matrix x.val.1.δ m
  bound _ x := x.val.1.φ
  realizable _ _ _ _ := TapeModel.realizable_uniform_gaussian hs
  holds := fun d hd x hx I hI hint Ω _ μ _ tape hlaw => by
    obtain ⟨-, law, hfix, hξ⟩ := hlaw
    obtain ⟨hIm, win, hloc⟩ := hint
    obtain ⟨hHess, ⟨V, ev, hV, hHV, hκ, hgap⟩, hΓ, hHS, hδ, hδS, hφ, hφ1, hu⟩ := hx
    exact roundedShQRSmallEig_algorithm_measureReal_not_accepts_le hM
      (hfix _ (List.Mem.head _)) (hfix _ (List.Mem.tail _ (List.Mem.head _))) hA hB hb₁ hb₂ hd
      x hI hIm hloc hHess hV hHV hκ hΓ hgap hHS hδ hδS hφ hφ1 hu hξ

/-- The randomized claim of rounded shifted QR with the small-eigenvalue leaf, with the proved
Ginibre tails, at the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail -->
$(2048e, 11/3, 2/3, 2)$ and `NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail -->
$(128e, 3, 2, 2)$. -/
noncomputable def shqrSmallEigGinibreClaim
    (admitted : ∃ d, ShQRSmallEigSizes Mch ginibreGapTail ginibreConditionTail d)
    (sU sG : ℕ) (hs : sU ≠ sG) {u : ℝ} (hM : StdModel u id Mch) :
    RandomizedClaim (shqrSmallEigAlgorithm Mch ginibreGapTail ginibreConditionTail admitted
      sU sG) :=
  shqrSmallEigClaim admitted sU sG hs hM boundsGinibreGap_ginibreGapTail
    boundsGinibreCondition_ginibreConditionTail ginibreGapTail_b_pos ginibreConditionTail_b_pos

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification (`NLAlib.Ops.Inputs.Checked`). The deterministic claim is termination
within the footprint only; the accuracy of the computed Schur form holds with probability over
the draws: `NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`. -/
theorem shqrSmallEig_checked (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) (sU sG : ℕ) :
    ((shqrSmallEigInputs Mch c₁ c₂ admitted).cast (shqrSmallEigRoutine sG) rfl rfl).Checked
      (shqrSmallEigAlgorithm Mch c₁ c₂ admitted sU sG) :=
  ((shqrSmallEigInputs Mch c₁ c₂ admitted).cast (shqrSmallEigRoutine sG) rfl rfl).checked_all _

end NLAlib.ShiftedQR
