/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig
public import NLAlib.Eigensolvers.SmallEig.Certificate

/-!
# The rounded shifted QR algorithm with the small-eigenvalue program as a canonical certificate

The certificate of `NLAlib.Eigensolvers.ShiftedQR.RoundedCertificate` with no `SmallEig` oracle:
the program is `NLAlib.ShiftedQR.roundedShQRSmallEig`, which runs the small-eigenvalue program
`NLAlib.SmallEig.smallEigProg` in the place of the kernel. The program, fixed before every size
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
* `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`: the certificate.

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
  ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4,
      .var 3 * (.var 1 + .const 1 + .var 2), .var 1 * (.var 0 + .const 1)]
    [⟨0, .var 5⟩, ⟨1, .var 6⟩, ⟨2, .var 7⟩, ⟨3, .var 8⟩, ⟨0, .var 5⟩, ⟨3, .var 8⟩, ⟨4, .var 9⟩]
    (roundedShQRSmallEig (O := SmallEigOp) (Q := Tst) sG).body⟩

/-- **The semantic input** at the sizes `d`, for the tail records $c_1, c_2$: the matrix of
order `d 0 + 1` and the reals $B, \Gamma, \Sigma, \delta, \varphi$ of the parameter words, with
the shift degree, the number of words and the two caps the ones they determine. -/
structure ShQRSmallEigData (c₁ c₂ : PolyLogTail) (d : Fin 5 → ℕ) where
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
  /-- The shift degree is the degree of (eqn:setk) at $4B$. -/
  degree_eq : d 1 = shqrDegree (4 * B)
  /-- The number of parameter words. -/
  words_eq : d 2 = (shqrSmallEigParams (d 0) (d 1) B Γ S δ φ c₁ c₂).length
  /-- The iteration cap. -/
  cap_eq : d 3 = shqrCap (d 0) B Γ S δ
  /-- The cap of the small-eigenvalue program. -/
  smallEigCap_eq : d 4 = shqrSmallEigCap (d 0) (d 1) B Γ S δ φ c₁ c₂

/-- The five raw buffers of an input: the matrix words, the deflation threshold word, the
parameter words, the identity accumulator and the failure word. -/
noncomputable def ShQRSmallEigData.buffers {c₁ c₂ : PolyLogTail} {d : Fin 5 → ℕ}
    (x : ShQRSmallEigData c₁ c₂ d) : Fin 5 → Buf ℝ :=
  ![(matrixWords x.matrix).map some,
    [some (shqrDeflationThreshold (d 0) (d 1) x.B x.Γ x.S x.δ x.φ)],
    (shqrSmallEigParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ c₁ c₂).map some,
    (matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)).map some, [none]]

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$
are exact, and the sizes are those of some parameter reals. -/
def ShQRSmallEigSizes (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail) (d : Fin 5 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧
    ∃ B Γ S δ φ : ℝ, d 1 = shqrDegree (4 * B) ∧
      d 2 = (shqrSmallEigParams (d 0) (d 1) B Γ S δ φ c₁ c₂).length ∧
      d 3 = shqrCap (d 0) B Γ S δ ∧ d 4 = shqrSmallEigCap (d 0) (d 1) B Γ S δ φ c₁ c₂

/-- **The problem** of the rounded shifted QR algorithm with the small-eigenvalue program on the
machine `Mch`, with the tail records $c_1, c_2$: the five raw buffers of
`NLAlib.ShiftedQR.ShQRSmallEigData.buffers` at the admitted sizes
`NLAlib.ShiftedQR.ShQRSmallEigSizes`. -/
noncomputable def shqrSmallEigProblem (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) : Problem ℝ 5 5 where
  formats _ := .cell
  valid := ShQRSmallEigSizes Mch c₁ c₂
  Data := ShQRSmallEigData c₁ c₂
  admissible _ x buffers := buffers = x.buffers
  admitted := admitted
  supply d hd := by
    obtain ⟨-, B, Γ, S, δ, φ, hk, hp, hF, hT⟩ := hd
    exact ⟨⟨0, B, Γ, S, δ, φ, hk, hp, hF, hT⟩, _, rfl⟩

variable {Mch : Machine ℝ} {c₁ c₂ : PolyLogTail} {admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d}

/-- The initial memory holds the input of the algorithm (`NLAlib.ShiftedQR.ShQRSmallEigInput`)
at the five supplied buffers. -/
theorem shqrSmallEigProblem_initial_input (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    ShQRSmallEigInput (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂ (0, 0)
      (1, 0) (2, 0) (3, 0) (4, 0) x.val.1.matrix
      ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x) := by
  have hb : x.val.2 = x.val.1.buffers := x.property
  have hs : ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store =
      List.ofFn x.val.1.buffers := by
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
  · simp [Mem.Room, hs, Store.len, ShQRSmallEigData.buffers, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil]
    disjoint
  · simpa [HoldsMatrix] using hA
  · rw [hs]
    simp [Store.get, ShQRSmallEigData.buffers, List.ofFn_succ]
  · simpa using hP

/-! ### The work and span polynomial -/

/-- The slot bounds of the program's initial indices: the five sizes, then five zero offsets. -/
def shqrSmallEigSlots : List WorkMono :=
  [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩, ⟨1, [0, 0, 0, 0, 1]⟩] ++
    List.replicate 5 (WorkMono.const 0)

-- The kernel evaluates the bound of the whole instrumented tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The monomial bound of the instructions of the instrumented program is
$960776\,b_0^3 b_1^4 b_2 b_3 b_4^2$ (`NLAlib.ShiftedQR.shqrSmallEigWork`). -/
theorem stmtWorkMono_shqrSmallEigProgram (sG : ℕ) :
    stmtWorkMono (shqrSmallEigProgram sG).body.instrument shqrSmallEigSlots =
      ⟨960776, [3, 4, 1, 1, 2]⟩ := by
  kernel_rfl

/-- **The work (and span) polynomial** of the rounded shifted QR algorithm with the
small-eigenvalue program at the sizes $(n, k, n_p, F, T)$ = `d`:
$960776\,(n + 1)^3(k + 1)^4(n_p + 1)(F + 1)(T + 1)^2$, the
monomial bound of the instructions of the instrumented program, each of unit weight; the
instructions of the small-eigenvalue program are among them (one bound over the whole tree). The
parameter words (thresholds, scales and caps, real numbers with logarithms and roots) are
supplied in the input and their computation is not charged, as for the merged
algorithm. The monomial is an envelope of the paper's count $n^4 + n^3\log^2$, not its shape: the
cap $T$ = `NLAlib.SmallEig.smallEigCap` is the largest loop count ($m$, $t$, $m_2$), a logarithm of
$n_{\max}\Sigma/(\delta\varphi)$ up to constants (bounded in the proof of
`NLAlib.SmallEig.logb_inv_uSmallEig_le`). -/
def shqrSmallEigWork (d : Fin 5 → ℕ) : ℕ :=
  960776 * (d 0 + 1) ^ 3 * (d 1 + 1) ^ 4 * (d 2 + 1) * (d 3 + 1) * (d 4 + 1) ^ 2

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
  2 * ((d 0 + 1) * (d 0 + 1)) + 1 + d 2 + 2 * (d 0 + 1) + 1

theorem shqrSmallEigProblem_initialBytes (d : Fin 5 → ℕ)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) :
    (shqrSmallEigProblem Mch c₁ c₂ admitted).initialBytes d x = shqrSmallEigInputWords d := sorry

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
writes only the matrix, the output and the failure word. -/
theorem shqrSmallEigProgram_wp {sU sG : ℕ} {d : Fin 5 → ℕ} (hd : ShQRSmallEigSizes Mch c₁ c₂ d)
    (x : (shqrSmallEigProblem Mch c₁ c₂ admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (shqrSmallEigProblem Mch c₁ c₂ admitted) Mch sU).contracts d x I)
    (τ : Tape ℝ) :
    Wp .total I τ (shqrSmallEigProgram sG).body (Program.environment (b := 5) d)
      (fun m => ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.EqOff
        (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store)
      ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x) := sorry

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
noncomputable def roundedShQRSmallEigAlgorithm (Mch : Machine ℝ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, ShQRSmallEigSizes Mch c₁ c₂ d) (sU sG : ℕ) :
    Algorithm (smallEigModel (shqrSmallEigProblem Mch c₁ c₂ admitted) Mch sU)
      (shqrSmallEigSpecification Mch c₁ c₂ admitted sG) :=
  Algorithm.ofWp (shqrSmallEigProgram sG) (shqrSmallEigProgram_wellTyped sG)
    (fun _ hd x _ hI τ => (shqrSmallEigProgram_wp hd x hI τ).mono fun _ h _ _ => h)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le (size_staticCost_shqrSmallEigProgram_le sG d))
    (fun d _ => (smallEigResources_span _).trans_le (size_staticCost_shqrSmallEigProgram_le sG d))
    (fun d _ x => by rw [shqrSmallEigProblem_initialBytes]; exact le_rfl)

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
$$\mathbb{P}\bigl[\mathsf{roundedShQRSmallEigAlgorithm}(\mathbf{H}) \text{ fails, exceeds its
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
    P.real {ω | ¬ (shqrSmallEigSpecification Mch c₁ c₂ admitted sG).Accepts smallEigResources d x
      (exec (roundedShQRSmallEigAlgorithm Mch c₁ c₂ admitted sU sG).program I smallEigResources
        (shqrSmallEigProblem Mch c₁ c₂ admitted).formats (ξ ω) d
        ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x))
      fun _ m => ((shqrSmallEigProblem Mch c₁ c₂ admitted).initial d x).store.EqOff
          (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store ∧
        ShQRSpectrum (0, 0) (3, 0) (4, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := sorry


/-! ### With the proved random-matrix tails -/

/-- **The rounded shifted QR algorithm with no oracle, on one run, unconditional**.
The unconditional form of
`NLAlib.ShiftedQR.roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`
([BanksGarzaVargasSrivastava2022, Theorem 6.3 with Theorem 1.4's quantifiers, corrected]): the
eigenvalue-gap and eigenvector-condition tails of a complex Ginibre perturbation are proved, at
the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
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
      ginibreConditionTail admitted sG).Accepts smallEigResources d x
      (exec (roundedShQRSmallEigAlgorithm Mch ginibreGapTail
        ginibreConditionTail admitted sU sG).program I smallEigResources
        (shqrSmallEigProblem Mch ginibreGapTail ginibreConditionTail
          admitted).formats (ξ ω) d
        ((shqrSmallEigProblem Mch ginibreGapTail ginibreConditionTail
          admitted).initial d x))
      fun _ m => ((shqrSmallEigProblem Mch ginibreGapTail
        ginibreConditionTail admitted).initial d x).store.EqOff
          (shqrFp (d 0) (0, 0) (3, 0) (4, 0)) m.store ∧
        ShQRSpectrum (0, 0) (3, 0) (4, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := by
  apply roundedShQRSmallEig_algorithm_measureReal_not_accepts_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end NLAlib.ShiftedQR
