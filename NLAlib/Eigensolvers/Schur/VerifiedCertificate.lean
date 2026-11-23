/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.VerifiedDense
public import NLAlib.Eigensolvers.Schur.Certification

/-!
# The verified dense Schur solver as a canonical certificate

The verified dense Schur solver (`NLAlib.Schur.verifiedSchur`) over the model of the
small-eigenvalue solver (`NLAlib.SmallEig.smallEigModel`) on a machine `Mch` with the standard
model at $\boldsymbol{u}$ is a canonical certificate (`NLAlib.Ops.Algorithm`) whose every-tape
claim (`good`) is the **flag-conditional Schur form**: on every admitted input, interpretation of
the model and tape, the run writes only the matrix, the accumulator and the flag, and if it stores
the flag $0$ then $\widehat{\mathbf{T}}$ is upper triangular and
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$. The admitted inputs are those whose $(\delta, \varphi)$ the precision
$\boldsymbol{u}$ of the machine supports ($\boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur`).
The work is the dense solver's and $O(n^3)$ for the check.

## Main definitions

* `NLAlib.Schur.verifiedSchurWithRoutine`, `NLAlib.Schur.verifiedSchurRoutine`,
  `NLAlib.Schur.verifiedSchurSpec`.
* `NLAlib.Schur.verifiedSchurInputs`, `NLAlib.Schur.verifiedSchurProgram`,
  `NLAlib.Schur.verifiedSchurProblem`, `NLAlib.Schur.verifiedSchurWork`,
  `NLAlib.Schur.verifiedSchurSpecification`, `NLAlib.Schur.verifiedSchurAlgorithm`,
  `NLAlib.Schur.verifiedSchurClaim`.

## Main results

* `NLAlib.Schur.verifiedSchurRoutine_meets`: the judgment of the routine, on every tape.
* `NLAlib.Schur.verifiedSchur_work_le`: the operation count.
* `NLAlib.Schur.verifiedSchur_checked`: what the certificate states.
* `NLAlib.Schur.verifiedSchur_algorithm_measureReal_not_accepts_le`: the flag is $0$ except with
  probability $\varphi$, on one counted run.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops SmallEig ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

/-! ### The routine -/

/-- **The routine of the verified Schur solver** around the solver `Solve`:
`[n, nr, nq, k, F, T] (A : update 2 (n + 1)², P : read nr + nq + 2) →
(U : write 2 (n + 1)², Fl : write 1)`, the tree `NLAlib.Schur.verifiedSchurWith` at the order
`n + 1`. The number of draws is that of the solver and depends on the data, so the routine
declares none. The tree has one variable for the matrix, named in both positions of the call. -/
def verifiedSchurWithRoutine (Solve : Stmt SmallEigOp Tst) : Routine SmallEigOp Tst :=
  routine% [n, nr, nq, k, F, T] (A : 2 * ((n + 1) * (n + 1)), P : nr + nq + 2) →
      (A, U : 2 * ((n + 1) * (n + 1)), Fl : 1)
    draws unspecified one variable {
    run (verifiedSchurWith Solve) [n + 1, nr, nq, k, F, T] (A, P, A, U, Fl)
  }

/-- **The routine of the verified dense Schur solver** on the Gaussian stream `sG`:
`NLAlib.Schur.verifiedSchurWithRoutine` around `NLAlib.Schur.denseSchur`. -/
abbrev verifiedSchurRoutine (sG : ℕ) : Routine SmallEigOp Tst :=
  verifiedSchurWithRoutine (denseSchur sG)

/-- What the flag certifies, on the blocks written: if the flag `fl` is $0$, then `ts` and `us`
are the words of an upper triangular $\widehat{\mathbf{T}}$ and a $\widehat{\mathbf{U}}$ with
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le e_U$. -/
def VerifiedSchurPost {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ eU : ℝ)
    (ts us : List ℝ) (fl : ℝ) : Prop :=
  fl = 0 → ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, ts = matrixWords T ∧
    us = matrixWords U ∧ T.IsUpperTriangular ∧ specNorm (A - U * T * Uᴴ) ≤ δ * specNorm A ∧
    specNorm (Uᴴ * U - 1) ≤ eU

/-- **The specification of the verified Schur routine** at the matrix $\mathbf{A}$, the
parameter words `ws` and the dimensions `dims`: on every tape, the blocks written satisfy
`NLAlib.Schur.VerifiedSchurPost`. -/
def verifiedSchurSpec {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ws : List ℝ)
    (dims : List ℕ) (δ eU : ℝ) : Routine.Spec ℝ :=
  spec% [n', nr, nq, k, F, T] (as, ps) → (ts, us, [fl])
    requires [n', nr, nq, k, F, T] = dims ∧ as = matrixWords A ∧ ps = ws
    ensures VerifiedSchurPost A δ eU ts us fl

/-- **The verified dense Schur routine meets its specification on every tape**: on a machine with
the standard model at $\boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur`, index literals, exact
natural literals up to $n + 1$, exact `toNat` and comparisons, draws that store the tape entry and
an exact polar disk sampler, for $0 < \delta \le 1$ and every complex $\mathbf{A}$ of order
$n + 1$, a flag $0$ certifies the Schur form with the errors $\delta$ and $58R\boldsymbol{u}$
(`NLAlib.Schur.verifiedSchur_writes`), $R$ = `NLAlib.Schur.denseSchurRotations` at the internal
backward error. -/
theorem verifiedSchurRoutine_meets {Mch : Machine ℝ} {I : Interp SmallEigOp Tst ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uVerifiedSchur n δ φ) :
    (verifiedSchurRoutine sG).Meets I
      (verifiedSchurSpec A (verifiedSchurParams u n δ φ)
        (n :: (denseSchurDims n (verifiedSchurDelta n δ) φ).tail) δ
        (58 * denseSchurRotations n (verifiedSchurDelta n δ) φ * u)) := by
  routine_intro [n', nr, nq, k, F, T] (a, p, uo, f) reads (ws, ps)
  obtain ⟨hd, rfl, rfl⟩ := hpre
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : n' = n ∧
      nr = (denseSchurRegParams n (verifiedSchurDelta n δ) φ).length ∧
      nq = (denseSchurThreshold n (verifiedSchurDelta n δ) φ ::
        (denseSchurShQRParams n (verifiedSchurDelta n δ) φ ++
          denseSchurLeafParams n (verifiedSchurDelta n δ) φ)).length ∧
      k = denseSchurDegree n (verifiedSchurDelta n δ) φ ∧
      F = denseSchurCap n (verifiedSchurDelta n δ) φ ∧
      T = denseSchurLeafCap n (verifiedSchurDelta n δ) φ := by
    simpa [denseSchurDims, denseSchurDimsWith] using hd
  have hlen : (verifiedSchurParams u n' δ φ).length =
      (denseSchurRegParams n' (verifiedSchurDelta n' δ) φ).length +
      (denseSchurThreshold n' (verifiedSchurDelta n' δ) φ ::
        (denseSchurShQRParams n' (verifiedSchurDelta n' δ) φ ++
          denseSchurLeafParams n' (verifiedSchurDelta n' δ) φ)).length + 2 := by
    simp [verifiedSchurParams, denseSchurParams, denseSchurParamsWith]
    omega
  rw [← hlen] at hps
  have hin : SchurPipelineInput (verifiedSchurParams u n' δ φ) a p uo f A m := by
    refine ⟨by room, ?_, by disjoint, hws, hps⟩
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    exact ⟨hroom.1, Store.le_len_of_readBlock hps (by rw [hlen]; omega),
      hroom.2.1, hroom.2.2⟩
  have hT := verifiedSchur_writes (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM hL hNat hQ hC hSmp
    hDisk hδ hδ1 hu hin τ
  refine (hT.in_frame (ρ := Env.frame [n',
    (denseSchurRegParams n' (verifiedSchurDelta n' δ) φ).length,
    (denseSchurThreshold n' (verifiedSchurDelta n' δ) φ ::
      (denseSchurShQRParams n' (verifiedSchurDelta n' δ) φ ++
        denseSchurLeafParams n' (verifiedSchurDelta n' δ) φ)).length,
    denseSchurDegree n' (verifiedSchurDelta n' δ) φ, denseSchurCap n' (verifiedSchurDelta n' δ) φ,
    denseSchurLeafCap n' (verifiedSchurDelta n' δ) φ] [a, p, uo, f]) rfl rfl (by room)).mono ?_ ?_
  · unfold schurFp
    fp_sub
  · rintro m' - ⟨⟨⟨T', hT'⟩, U', hU', -⟩, hfl, hout⟩
    obtain ⟨v, hv⟩ : ∃ v, m'.store.get f.1 f.2 = some v := by
      rcases hfl with h | h <;> exact ⟨_, h⟩
    refine ⟨trivial, [matrixWords T', matrixWords U', [v]],
      Mem.readBlocks_of_cons hT' (Mem.readBlocks_of_cons hU'
        (Mem.readBlocks_of_cons (by rw [BlockFn.readBlock_one, hv]; rfl) rfl)), ?_⟩
    intro hv0
    obtain ⟨-, U, T, hT₂, hU₂, hTu, hr, ho⟩ := hout (by rw [hv, hv0])
    have e1 : matrixWords T' = matrixWords T :=
      Option.some.inj ((Eq.symm hT').trans hT₂)
    have e2 : matrixWords U' = matrixWords U :=
      Option.some.inj ((Eq.symm hU').trans hU₂)
    exact ⟨U, T, e1, e2, hTu, hr, ho⟩

/-! ### The problem -/

/-- The sizes of a run of the verified dense Schur solver at $(n, \delta, \varphi)$: those of the
dense solver at the internal backward error. -/
noncomputable def verifiedSchurSizes (n : ℕ) (δ φ : ℝ) : Fin 6 → ℕ :=
  denseSchurSizes n (verifiedSchurDelta n δ) φ

/-- **The admitted sizes** of the verified dense Schur solver on the machine `Mch` at the unit
roundoff $\boldsymbol{u}$: the natural literals up to the order are exact and the sizes are those
of some $0 < \delta \le 1$, $0 < \varphi \le 1$ that the precision supports. -/
def VerifiedSchurSizes (Mch : Machine ℝ) (u : ℝ) (d : Fin 6 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧ ∃ δ φ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < φ ∧ φ ≤ 1 ∧
    u ≤ uVerifiedSchur (d 0) δ φ ∧ verifiedSchurSizes (d 0) δ φ = d

/-- The words of the verified solver have the count of its sizes and the two check words. -/
theorem length_verifiedSchurParams (u : ℝ) (n : ℕ) (δ φ : ℝ) :
    (verifiedSchurParams u n δ φ).length =
      verifiedSchurSizes n δ φ 1 + verifiedSchurSizes n δ φ 2 + 2 := by
  simp [verifiedSchurParams, verifiedSchurSizes, denseSchurSizes, denseSchurParams,
    denseSchurParamsWith]
  omega

/-- **The admitted inputs** of the verified dense Schur solver on the machine `Mch` at the unit
roundoff $\boldsymbol{u}$: every matrix of order `d 0 + 1` and all $0 < \delta \le 1$,
$0 < \varphi \le 1$ with $\boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur` whose sizes are `d`.
The first operand holds the words of the matrix. The reals are in no buffer: the second operand
holds the words `NLAlib.Schur.verifiedSchurParams` computed from them, at the `d 1 + d 2 + 2`
cells of its port. The accumulator and the flag are blank. -/
noncomputable def verifiedSchurInputs (Mch : Machine ℝ) (u : ℝ)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) :
    (verifiedSchurWithRoutine .skip).Domain ℝ 6 4 where
  valid := VerifiedSchurSizes Mch u
  In := SchurData
  accepts d x := verifiedSchurSizes (d 0) x.δ x.φ = d ∧ 0 < x.δ ∧ x.δ ≤ 1 ∧ 0 < x.φ ∧ x.φ ≤ 1 ∧
    u ≤ uVerifiedSchur (d 0) x.δ x.φ
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) SchurData.matrix,
    .derivedOfLength (d 1 + d 2 + 2) (fun x => verifiedSchurParams u (d 0) x.δ x.φ),
    .blank (2 * ((d 0 + 1) * (d 0 + 1))), .blank 1]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Slot.derivedOfLength, Access.readable, Codec.complexMatrix,
          List.ofFn_succ])
  Unstored _ := ℝ × ℝ
  unstored _ x := (x.δ, x.φ)
  faithful d x y hu h := by
    have h0 := h 0
    simp only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] at h0
    have hm := (Codec.complexMatrix (d 0 + 1)).encode_injective h0
    obtain ⟨_, _, _⟩ := x
    obtain ⟨_, _, _⟩ := y
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain rfl : _ = _ := hm
    rfl
  admitted := admitted
  inhabited d hd := by
    obtain ⟨-, δ, φ, hδ, hδ1, hφ, hφ1, hu, hs⟩ := hd
    exact ⟨⟨0, δ, φ⟩, hs, hδ, hδ1, hφ, hφ1, hu⟩

/-- **The problem** of the verified dense Schur solver: the problem of the admitted inputs
`NLAlib.Schur.verifiedSchurInputs`. -/
noncomputable abbrev verifiedSchurProblem (Mch : Machine ℝ) (u : ℝ)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) : Problem ℝ 6 4 :=
  (verifiedSchurInputs Mch u admitted).problem

/-- **The verified dense Schur program** at the order `d 0 + 1` and the dimensions `d 1`, …,
`d 5` on the four supplied buffers: the routine `NLAlib.Schur.verifiedSchurRoutine` on them. -/
def verifiedSchurProgram (sG : ℕ) : Program SmallEigOp Tst 6 4 :=
  (verifiedSchurRoutine sG).close 6 4

/-- The program is the frame of the verified solver at the order `d 0 + 1` on the supplied
buffers. -/
theorem verifiedSchurProgram_eq (sG : ℕ) :
    verifiedSchurProgram sG =
      ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩]
        (verifiedSchur (O := SmallEigOp) (Q := Tst) sG)⟩ := rfl

/-- **The work (and span) of the verified dense Schur solver** at the sizes
$(n, n_r, n_q, k, F, T)$ = `d`: the dense solver's
$384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$ (`NLAlib.Schur.denseSchur_work_le`),
the check's $1619(n + 1)^3$, the copy's $32(n + 1)^2$ and $128$ for the frames. -/
def verifiedSchurWork (d : Fin 6 → ℕ) : ℕ :=
  384547 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) * (d 4 + 1) * (d 5 + 1) ^ 2 +
    1619 * (d 0 + 1) ^ 3 + 32 * (d 0 + 1) ^ 2 + 128

/-- The payload words of the four supplied buffers. -/
def verifiedSchurInputWords (d : Fin 6 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + (d 1 + d 2 + 2) + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

/-- **The specification of the verified dense Schur solver**: the static budget, scratch and
memory, the work and span `NLAlib.Schur.verifiedSchurWork`, and on every tape the frame and the
flag-conditional Schur form: if the flag is $0$, the stored $\widehat{\mathbf{T}}$ is upper
triangular, $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf
H}\|_2 \le \delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le 58R\boldsymbol{u}$, $R$ the rotation count at the internal backward error. -/
noncomputable def verifiedSchurSpecification (Mch : Machine ℝ) (u : ℝ)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sG : ℕ) :
    Specification SmallEigOp Tst (verifiedSchurProblem Mch u admitted) where
  budget := staticCost (verifiedSchurProgram sG)
  scratch := staticPeak smallEigResources (verifiedSchurProgram sG)
  work := verifiedSchurWork
  span := verifiedSchurWork
  memory d := verifiedSchurInputWords d + staticPeak smallEigResources (verifiedSchurProgram sG) d
  good d x _ _ m := ((verifiedSchurProblem Mch u admitted).initial d x).store.EqOff
      (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
    (m.store.get 3 0 = some 0 → SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
      (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.val.1.δ) x.val.1.φ * u) m)

/-- **The operation count of the verified dense Schur solver** (on every tape): the instrumented
static count of `NLAlib.Schur.verifiedSchur` at the order $n + 1$, $n_r$ regularizer words, $n_q$
core words, the shift degree $k$, the iteration cap $F$, the leaf cap $T$ and zero offsets is at
most the dense solver's $384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$
(`NLAlib.Schur.denseSchur_work_le`) and $1619(n + 1)^3 + 32(n + 1)^2 + 64$ for the copy and the
check (`NLAlib.Schur.size_stmtCost_verifiedSchurWith_le`). -/
theorem verifiedSchur_work_le {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]
    [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] (sG n nr nq k F T : ℕ) :
    Count.size (stmtCost (verifiedSchur (O := O) (Q := Q) sG).instrument
        [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) ≤
      384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 +
        1619 * (n + 1) ^ 3 + 32 * (n + 1) ^ 2 + 64 := by
  have h1 := size_stmtCost_verifiedSchurWith_le (denseSchur (O := O) (Q := Q) sG) n nr nq k F T
  have h2 := denseSchur_work_le (O := O) (Q := Q) sG n nr nq k F T
  unfold verifiedSchur
  omega

/-- The four supplied buffers of an input: the matrix words, the parameter words, uninitialized
room for the accumulator and the flag. -/
theorem verifiedSchurProblem_buffers {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} (d : Fin 6 → ℕ)
    (x : (verifiedSchurProblem Mch u admitted).Input d) :
    x.val.2 = ![(matrixWords x.val.1.matrix).map some,
      (verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ).map some,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none, [none]] := by
  rw [(verifiedSchurInputs Mch u admitted).buffers_eq x]
  have hx := (verifiedSchurInputs Mch u admitted).accepts_data x
  funext i
  fin_cases i
  · rfl
  · refine Slot.buffer_derivedOfLength ?_
    rw [length_verifiedSchurParams, hx.1]
  · rfl
  · rfl

/-- The initial memory of an input holds the input of the verified solver at the four supplied
buffers. -/
theorem verifiedSchurProblem_initial_input {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} (d : Fin 6 → ℕ)
    (x : (verifiedSchurProblem Mch u admitted).Input d) :
    SchurPipelineInput (verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ) (0, 0) (1, 0) (2, 0)
      (3, 0) x.val.1.matrix ((verifiedSchurProblem Mch u admitted).initial d x) := by
  have hb := verifiedSchurProblem_buffers d x
  have hs : ((verifiedSchurProblem Mch u admitted).initial d x).store = List.ofFn x.val.2 := rfl
  have hA := Problem.initial_readBlock (P := verifiedSchurProblem Mch u admitted) d x
    (0 : Fin 4) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := verifiedSchurProblem Mch u admitted) d x
    (1 : Fin 4) (xs := verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, by simpa [HoldsMatrix] using hA, by simpa using hP⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, ⟨Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, Fp.disj_inBlock_of_ne (by omega)⟩

/-- The initial payload of an input is `NLAlib.Schur.verifiedSchurInputWords`. -/
theorem verifiedSchurProblem_initialBytes {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} (d : Fin 6 → ℕ)
    (x : (verifiedSchurProblem Mch u admitted).Input d) :
    (verifiedSchurProblem Mch u admitted).initialBytes d x = verifiedSchurInputWords d := by
  refine ((verifiedSchurInputs Mch u admitted).initialBytes_eq x).trans ?_
  simp [verifiedSchurInputs, Slot.len, Slot.derivedOfLength, Codec.complexMatrix, List.ofFn_succ,
    verifiedSchurInputWords, Nat.add_assoc]

-- The kernel evaluates the discipline over the whole tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The verified dense Schur program passes the storage discipline of the costs. -/
theorem verifiedSchurProgram_wellTyped (sG : ℕ) {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} :
    (verifiedSchurProgram sG).wellTyped smallEigResources
      (verifiedSchurProblem Mch u admitted).formats = true := by
  kernel_rfl

/-- The static count of the verified dense Schur program, its frame included, is at most
`NLAlib.Schur.verifiedSchurWork`. -/
theorem size_staticCost_verifiedSchurProgram_le (sG : ℕ) (d : Fin 6 → ℕ) :
    Count.size (staticCost (verifiedSchurProgram sG) d) ≤ verifiedSchurWork d := by
  have he : (Program.environment (b := 4) d).idx = [d 0, d 1, d 2, d 3, d 4, d 5, 0, 0, 0, 0] :=
    rfl
  have h := verifiedSchur_work_le (O := SmallEigOp) (Q := Tst) sG (d 0) (d 1) (d 2) (d 3) (d 4)
    (d 5)
  simp only [staticCost, verifiedSchurProgram_eq, he, Stmt.instrument, stmtCost, tally,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, useCost, IExp.evalList, IExp.eval,
    List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, map_add, map_zero, Count.one, size_single]
  unfold verifiedSchurWork
  omega

/-- **The verified dense Schur solver as a canonical certificate**: the fixed program
`NLAlib.Schur.verifiedSchurProgram`, over the model `NLAlib.SmallEig.smallEigModel` (no oracle)
with the unit costs on a machine with the standard model at $\boldsymbol{u}$, succeeds on every
admitted input, interpretation of the model and tape, within the static budget, scratch and
memory, with work and span at most `NLAlib.Schur.verifiedSchurWork`, writing only the matrix, the
accumulator and the flag, and with the **flag-conditional Schur form** as its every-tape claim:
a flag $0$ certifies $\widehat{\mathbf{T}}$ upper triangular,
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$ and the orthogonality bound. The flag is $0$ with probability at least
$1 - \varphi$ (`NLAlib.Schur.verifiedSchurClaim`).
Algorithm: verified-schur (run model) -/
noncomputable def verifiedSchurAlgorithm (Mch : Machine ℝ) {u : ℝ} (hM : StdModel u id Mch)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sU sG : ℕ) :
    Algorithm (smallEigModel (verifiedSchurProblem Mch u admitted) Mch sU)
      (verifiedSchurSpecification Mch u admitted sG) :=
  ((verifiedSchurInputs Mch u admitted).cast (verifiedSchurRoutine sG) rfl rfl).algorithm
    (fun d x => verifiedSchurSpec x.matrix (verifiedSchurParams u (d 0) x.δ x.φ) (List.ofFn d)
      x.δ (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.δ) x.φ * u))
    (fun d hd X I hI => by
      obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
      obtain ⟨hsz, hδ, hδ1, -, -, hu⟩ := (verifiedSchurInputs Mch u admitted).accepts_data X
      have h := verifiedSchurRoutine_meets (sG := sG) hS hM hL hd.1 hQ hC hSmp hDisk
        X.val.1.matrix hδ hδ1 hu
      have hdims : d 0 :: (denseSchurDims (d 0) (verifiedSchurDelta (d 0) X.val.1.δ)
          X.val.1.φ).tail = List.ofFn d := by
        have hs := fun i => congrFun hsz i
        simp [denseSchurDims, denseSchurDimsWith, List.ofFn_succ, ← hs 1, ← hs 2, ← hs 3,
          ← hs 4, ← hs 5, verifiedSchurSizes, denseSchurSizes]
      rw [hdims] at h
      exact h)
    (fun d _ x hx _ => by
      have hw : (Slot.derivedOfLength (d 1 + d 2 + 2) fun x : SchurData d =>
          verifiedSchurParams u (d 0) x.δ x.φ).words x =
          verifiedSchurParams u (d 0) x.δ x.φ :=
        Slot.words_derivedOfLength (by
          have hx' : verifiedSchurSizes (d 0) x.δ x.φ = d := hx.1
          rw [length_verifiedSchurParams, hx'])
      refine ⟨rfl, rfl, ?_⟩
      exact hw)
    (fun d _ x τ m' hfr _ ys hys hpost c _ => by
      change Store.EqOff (Fp.blocks [(0, 0), (2, 0), (3, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 2 * ((d 0 + 1) * (d 0 + 1)), 1]) _ _ at hfr
      change m'.readBlocks [(0, 0), (2, 0), (3, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 2 * ((d 0 + 1) * (d 0 + 1)), 1] = some ys at hys
      refine ⟨hfr.mono (by unfold schurFp; fp_sub), fun h0 => ?_⟩
      split_reads hys as (ts, us, fs)
      obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hfs
      have hv0 : v = 0 := by
        have h1 : m'.store.get 3 0 = some v := hv
        rw [h0] at h1
        exact (Option.some.inj h1).symm
      obtain ⟨U, T, rfl, rfl, hTu, hr, ho⟩ :=
        (show VerifiedSchurPost x.val.1.matrix x.val.1.δ _ ts us v from hpost) hv0
      exact ⟨h0, U, T, hts, hus, hTu, hr, ho⟩)
    (fun d _ => le_rfl) (fun d _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le (size_staticCost_verifiedSchurProgram_le sG d))
    (fun d _ => (smallEigResources_span _).trans_le (size_staticCost_verifiedSchurProgram_le sG d))
    (fun d _ x => Nat.add_le_add_right (verifiedSchurProblem_initialBytes d x).le _)
    (ht := verifiedSchurProgram_wellTyped sG)

/-- **The verified dense Schur solver, on one run.** Let the machine `Mch` have the standard model
at $\boldsymbol{u}$; let the tape $\xi$ have the stream laws `law`, with `law` $s_U$ uniform on
$[0, 1]$ and `law` $s_G$ the standard real Gaussian law. Let `d` be admitted and the input `x`
hold a complex $\mathbf{A}$ of order $n + 1$, $0 < \delta \le 1$, $0 < \varphi \le 1$ with
$\boldsymbol{u} \le \boldsymbol{u}_0$. Let `I` meet the model, be measurable and read the tape
only in its windows. Then
$$\mathbb{P}\bigl[\mathsf{verifiedSchurAlgorithm}(\mathbf{A}) \text{ fails, exceeds its budget,
  scratch, memory, work or span, writes outside } \mathbf{A}, \widehat{\mathbf{U}} \text{ and the
  flag, or stores no flag } 0 \text{ with a Schur output of } \mathbf{A}\bigr] \le \varphi\,,$$
on one counted run. On every tape a flag $0$ certifies the Schur form (the specification's
`good`). Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uVerifiedSchur`.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
for the solver; the a posteriori check has no printed source.
Result: verified-schur-certificate -/
theorem verifiedSchur_algorithm_measureReal_not_accepts_le {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) {admitted : ∃ d, VerifiedSchurSizes Mch u d}
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {d : Fin 6 → ℕ} (hd : VerifiedSchurSizes Mch u d)
    (x : (verifiedSchurProblem Mch u admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (verifiedSchurProblem Mch u admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (verifiedSchurSpecification Mch u admitted sG).Accepts
        (verifiedSchurAlgorithm Mch hM admitted sU sG).program I smallEigResources (ξ ω) d x
      fun _ m => ((verifiedSchurProblem Mch u admitted).initial d x).store.EqOff
          (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
        SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
          (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.val.1.δ) x.val.1.φ * u)
          m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  obtain ⟨hsz, hδ, hδ1, hφ, hφ1, hu⟩ := (verifiedSchurInputs Mch u admitted).accepts_data x
  have hin := verifiedSchurProblem_initial_input (admitted := admitted) d x
  have hT := verifiedSchur_measureReal_not_schur_le (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM
    hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hδ hδ1 hφ hφ1 hu hin hξ
  refine (verifiedSchurAlgorithm Mch hM admitted sU sG).measureReal_not_accepts_le_of_wp hd x
    I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  have hl5 : ((verifiedSchurProblem Mch u admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0), (3, 0)] := fun y hy => hin.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  refine hω (wp_frame ?_ ?_ hl5 (hW.mono le_rfl fun m _ h => (h.mono (by
    obtain ⟨-, hd1, -⟩ := verifiedSchur_params_basic (n := d 0) hδ hδ1 hu
    exact hd1) le_rfl)))
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, verifiedSchurSizes, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Inputs.Checked`): it writes only the matrix, the accumulator and the flag, and a flag
$0$ certifies the Schur form. That the flag is $0$ with probability at least $1 - \varphi$ is
`NLAlib.Schur.verifiedSchurClaim`. -/
theorem verifiedSchur_checked (Mch : Machine ℝ) {u : ℝ} (hM : StdModel u id Mch)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sU sG : ℕ) :
    ((verifiedSchurInputs Mch u admitted).cast (verifiedSchurRoutine sG) rfl rfl).Checked
      (verifiedSchurAlgorithm Mch hM admitted sU sG) :=
  ((verifiedSchurInputs Mch u admitted).cast (verifiedSchurRoutine sG) rfl rfl).checked_all _

/-! ### The randomized claim -/

/-- **The randomized claim of the verified dense Schur certificate**
([BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1] for the solver; the a posteriori check has no printed source). The entries of the
tape are independent, uniform on $[0, 1]$ on the stream $s_U$ and standard Gaussian on the
stream $s_G$. At every admitted input and for an interpretation that is measurable and reads the
tape only in its windows, the counted run writes only the matrix, the accumulator and the flag,
and stores the flag $0$ with an upper triangular $\widehat{\mathbf{T}}$ and a
$\widehat{\mathbf{U}}$ within $58 R \boldsymbol{u}$ of unitary whose product is within
$\delta \|\mathbf{A}\|_2$ of $\mathbf{A}$, except with probability at most $\varphi$. -/
noncomputable def verifiedSchurClaim (Mch : Machine ℝ) {u : ℝ} (hM : StdModel u id Mch)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sU sG : ℕ) (hs : sU ≠ sG) :
    RandomizedClaim (verifiedSchurAlgorithm Mch hM admitted sU sG) where
  law _ _ := TapeModel.streams [(sU, volume.restrict (Set.Icc 0 1)), (sG, gaussianReal 0 1)]
  admits _ _ := True
  interprets _ _ I := I.IsMeasurable ∧
    ∃ win : SmallEigOp → List ℕ → ℕ, ∀ o, I.TapeLocal o (win o)
  event d x _ _ m := ((verifiedSchurProblem Mch u admitted).initial d x).store.EqOff
      (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
    SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
      (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.val.1.δ) x.val.1.φ * u) m
  bound _ x := x.val.1.φ
  realizable _ _ _ _ := TapeModel.realizable_uniform_gaussian hs
  holds := fun d hd x _ I hI hint Ω _ μ _ tape hlaw => by
    obtain ⟨-, law, hfix, hξ⟩ := hlaw
    obtain ⟨hIm, win, hloc⟩ := hint
    exact verifiedSchur_algorithm_measureReal_not_accepts_le hM (hfix _ (List.Mem.head _))
      (hfix _ (List.Mem.tail _ (List.Mem.head _))) hd x hI hIm hloc hξ

end NLAlib.Schur
