/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedHeadline
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Probability.Distributions.DiskUniform

/-!
# Randomized kernels of the rounded shifted QR algorithm

The small-eigenvalue routine `SmallEig` of [BanksGarzaVargasSrivastava2022, Definition 1.2] as a
randomized kernel: on an upper Hessenberg matrix of order $d$ it reads a window of $W(d)$ entries
of one stream of the tape and, unless the window lies in a bad set of probability at most
$\varphi$, returns every eigenvalue, with multiplicity, within the forward error $\beta$. The
call always succeeds and writes only its output block. Forward error implies backward error
(`NLAlib.IsEigenvalueListing.exists_specNorm_sub_le`), so the leaf routine that calls the kernel
meets `NLAlib.ShiftedQR.RandomLeafContract` with the backward error $\beta$.

The window has a fixed length at each order, read at the call position; a routine that draws an
adaptive number of samples does not fit this model.

The disk sampler of the random shifts reads a radius word $R$ and a window of two entries
$x_0, x_1$ of one stream, and writes the pair of the polar sample
$R\sqrt{x_0}\,e^{2\pi i x_1}$ exactly (`NLAlib.polarDisk`): for uniform draws it is uniform on
$\mathbb{D}(0, R)$ (`NLAlib.map_polarDisk_eq_diskUniform`). The sample is exact, as in the
paper; a rounded sampler is not modelled.

## Main definitions

* `NLAlib.ShiftedQR.randomSmallEigRel`: the kernel's contract in operand form.
* `NLAlib.ShiftedQR.IsRandomSmallEig`: the interpretation's `smallEig` is such a kernel.
* `NLAlib.ShiftedQR.DiskSampleOp`, `NLAlib.ShiftedQR.polarDiskRel`,
  `NLAlib.ShiftedQR.IsPolarDiskSampler`: the exact polar disk sampler.

## Main results

* `NLAlib.ShiftedQR.IsRandomSmallEig.randomLeafContract`: the leaf routine that calls the kernel
  meets `NLAlib.ShiftedQR.RandomLeafContract`.

## Small-eigenvalue routines

A program in the kernel's place reads parameter words and draws an adaptive number of samples
([BanksGarzaVargasSrivastava2025]). Its contract is a routine contract
(`NLAlib.ShiftedQR.RandomSmallEigContract`, `NLAlib.ShiftedQR.TerminatingSmallEig`) on bounded
orders and norms, with the interface `[d, nq, T] (Bk, Q) → (Ev)`; the kernel meets it as a routine
(`NLAlib.ShiftedQR.smallEigKernel`, `NLAlib.ShiftedQR.IsRandomSmallEig.randomSmallEigContract`),
and a routine gives a leaf routine of the worklist (`NLAlib.ShiftedQR.seLeaf`,
`NLAlib.ShiftedQR.RandomSmallEigContract.randomLeafRoutineContract`).
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section SmallEig

variable {O Q : Type} [Has EigenvalueKernelOp O]

/-- **The contract in operand form of a randomized small-eigenvalue kernel** reading the stream
`s`, with window lengths `W`, bad window sets `Bad` and forward error `β`: at the dimensions
`[d]` the call reads the $2d^2$ words of a matrix $\mathbf{B}$ and $W(d)$ entries of the stream,
and writes $2d$ words. If $\mathbf{B}$ is upper Hessenberg and the window is not in
`Bad d B`, the words are a family $\mu$ with $\lvert\mu_i - \lambda_i\rvert \le \beta$ for a listing
$\lambda$ of the eigenvalues of $\mathbf{B}$ with multiplicity. -/
def randomSmallEigRel (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) (β : ℝ) : BlockRel ℝ where
  nd := 1
  stream := s
  win d := W (d.headD 0)
  inLens d := [2 * (d.headD 0 * d.headD 0)]
  outLens d := [2 * d.headD 0]
  rel d xs w ys := ∀ (N : ℕ) (as : List ℝ), d = [N] → xs = [as] →
    IsUpperHessenberg (matrixOfWords N as) →
    (fun j : Fin (W N) => w.getD j 0) ∉ Bad N (matrixOfWords N as) →
    ∃ roots ev : Fin N → ℂ, IsEigenvalueListing (matrixOfWords N as) ev ∧
      (∀ i, ‖roots i - ev i‖ ≤ β) ∧ ys = [matrixWords (Matrix.of fun i (_ : Fin 1) => roots i)]

/-- **A randomized small-eigenvalue kernel** ([BanksGarzaVargasSrivastava2022, Definition 1.2])
with the stream laws `law`, the stream `s`, the forward error `β` and the failure probability
`φ`: there are window lengths $W(d)$ and measurable bad sets of windows, each of probability at
most $\varphi$ under the product law of the stream at an upper Hessenberg input, such that the
interpretation's `smallEig` always succeeds on live, readable operands with room and meets
`NLAlib.ShiftedQR.randomSmallEigRel`. -/
def IsRandomSmallEig (law : ℕ → Measure ℝ) (s : ℕ) (β φ : ℝ) (I : Interp O Q ℝ) : Prop :=
  ∃ (W : ℕ → ℕ) (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)),
    (∀ d B, MeasurableSet (Bad d B)) ∧
    (∀ d (B : Matrix (Fin d) (Fin d) ℂ), IsUpperHessenberg B →
      (Measure.pi fun _ : Fin (W d) => law s).real (Bad d B) ≤ φ) ∧
    I.Meets .total (Has.inj EigenvalueKernelOp.smallEig)
      ((randomSmallEigRel s W Bad β).spec AnyOperands)

/-- **The forward contract of a randomized small-eigenvalue routine**
([BanksGarzaVargasSrivastava2025, Corollary 1.3]) with the stream laws `law`, the forward error
`β`, the failure probability `φ`, the order bound `kmax`, the cap `T`, the norm bound `S` and the
parameter words `qs`, all fixed outside the quantifiers: from an upper Hessenberg $\mathbf{B}$ of
order $d \le k_{\max}$ with $\|\mathbf{B}\|_2 \le \Sigma$, stored with the words, except with
probability at most $\varphi$, the run writes only its $2d$ output words and stores a family
$\mu$ with $\lvert\mu_i - \lambda_i\rvert \le \beta$ for a listing $\lambda$ of the eigenvalues
of $\mathbf{B}$ with multiplicity. The routine may read any number of streams, adaptively. The
interface is `[d, nq, T] (Bk, Q) → (Ev)`. -/
def RandomSmallEigContract (law : ℕ → Measure ℝ) (β φ : ℝ) (kmax T : ℕ) (S : ℝ) (qs : List ℝ)
    (SE : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w q o : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax →
    IsUpperHessenberg B → specNorm B ≤ S →
    PWrites law I SE.body (Env.frame [d, qs.length, T] [w, q, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock q.1 q.2 qs.length = some qs ∧
        μ.Live [w, q, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) ∧
        Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ

/-- **A terminating small-eigenvalue routine** on orders at most `kmax`, with the cap `T` and the
parameter words `qs`: from any matrix of order $d \le k_{\max}$ (no structure assumed) stored with
the words, on every tape, the run is total, writes only its $2d$ output words and leaves them
stored (the caller reads them). The order bound keeps the literals a run writes below a fixed
size. The interface is
`[d, nq, T] (Bk, Q) → (Ev)`. -/
def TerminatingSmallEig (kmax T : ℕ) (qs : List ℝ) (SE : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w q o : ℕ × ℕ} (tape : Tape ℝ) (μ : Mem ℝ) (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock q.1 q.2 qs.length = some qs →
    μ.Live [w, q, o] → o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape SE.body (Env.frame [d, qs.length, T] [w, q, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) μ

/-- The kernel as a routine `[d, nq, T] (Bk, Q) → (Ev)`: one call of `smallEig`; the parameter
words and the cap are ignored. -/
def smallEigKernel : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  call (Has.inj EigenvalueKernelOp.smallEig) [d] (Bk) → (Ev)
}

/-- **The forward contract of a small-eigenvalue routine with a separate word count**:
`NLAlib.ShiftedQR.RandomSmallEigContract` with the word-count dimension `nq` of the frame given
apart from the stored words `qs`. A routine that ignores its words (the kernel,
`NLAlib.ShiftedQR.smallEigKernel`) meets it whatever `nq` is; `RandomSmallEigContract` is the case
`nq = qs.length` (`NLAlib.ShiftedQR.RandomSmallEigContract.at`). -/
def RandomSmallEigContractAt (law : ℕ → Measure ℝ) (β φ : ℝ) (kmax nq T : ℕ) (S : ℝ)
    (qs : List ℝ) (SE : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w q o : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax →
    IsUpperHessenberg B → specNorm B ≤ S →
    PWrites law I SE.body (Env.frame [d, nq, T] [w, q, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock q.1 q.2 qs.length = some qs ∧
        μ.Live [w, q, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) ∧
        Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ

omit [Has EigenvalueKernelOp O] in
/-- The routine contract is the contract with the word count `qs.length`. -/
theorem RandomSmallEigContract.at {law : ℕ → Measure ℝ} {β φ : ℝ} {kmax T : ℕ} {S : ℝ}
    {qs : List ℝ} {SE : Impl O Q} {I : Interp O Q ℝ}
    (h : RandomSmallEigContract law β φ kmax T S qs SE I) :
    RandomSmallEigContractAt law β φ kmax qs.length T S qs SE I := h

/-- **A terminating small-eigenvalue routine with a separate word count**:
`NLAlib.ShiftedQR.TerminatingSmallEig` with the word-count dimension `nq` apart from the stored
words `qs`. -/
def TerminatingSmallEigAt (kmax nq T : ℕ) (qs : List ℝ) (SE : Impl O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {d : ℕ} {w q o : ℕ × ℕ} (tape : Tape ℝ) (μ : Mem ℝ) (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → HoldsMatrix w B μ.store → μ.store.readBlock q.1 q.2 qs.length = some qs →
    μ.Live [w, q, o] → o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape SE.body (Env.frame [d, nq, T] [w, q, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) μ

omit [Has EigenvalueKernelOp O] in
/-- Termination is termination with the word count `qs.length`. -/
theorem TerminatingSmallEig.at {kmax T : ℕ} {qs : List ℝ} {SE : Impl O Q} {I : Interp O Q ℝ}
    (h : TerminatingSmallEig kmax T qs SE I) : TerminatingSmallEigAt kmax qs.length T qs SE I :=
  h

/-- The kernel called as a routine (`NLAlib.ShiftedQR.smallEigKernel`) at any word count `nq`,
cap `T` and word view `q`: from an upper Hessenberg $\mathbf{B}$ of order $d$, except with
probability at most $\varphi$, it writes only its $2d$ output words and stores a family within
$\beta$ of a listing of the eigenvalues of $\mathbf{B}$. The words are not read. -/
theorem IsRandomSmallEig.smallEigKernel_pwrites {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) {d nq T : ℕ} {w q o : ℕ × ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : IsUpperHessenberg B) :
    PWrites law I (smallEigKernel (O := O) (Q := Q)).body (Env.frame [d, nq, T] [w, q, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.Live [w, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ := by
  obtain ⟨W, Bad, hBad, hφ, hI⟩ := h
  refine PWrites.of_window (s := s) (W := W d) (Bad := fun _ => Bad d B)
    (measurable_snd (hBad d B)) (fun _ _ => hφ d B hB) ?_
  rintro μ τ ⟨hH, hl, hroom, hdisj⟩ hgood
  unfold smallEigKernel
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [matrixWords B] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) =
      Tape.windowFn τ s μ.pos (W d) := by
    funext j
    simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  obtain ⟨roots, ev, hev, hfw, rfl⟩ := hrel d (matrixWords B) rfl hxs
    (by simpa using hB) (by
      change (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) ∉ _
      rw [hwin]
      simpa using hgood)
  rw [matrixOfWords_matrixWords] at hev
  refine ⟨roots, ev, hev, hfw, ?_⟩
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp
    (by simpa [Mem.readBlocks, randomSmallEigRel] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  simpa [HoldsMatrix] using hyy ▸ hy

/-- A randomized small-eigenvalue kernel, called as a routine, meets the routine contract with a
separate word count for every order bound, word count, cap, norm bound and words. -/
theorem IsRandomSmallEig.randomSmallEigContractAt {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) (kmax nq T : ℕ) (S : ℝ)
    (qs : List ℝ) :
    RandomSmallEigContractAt law β φ kmax nq T S qs (smallEigKernel (O := O) (Q := Q)) I :=
  fun B _ hB _ => (h.smallEigKernel_pwrites B hB).mono
    (fun _ ⟨hw, _, hl, hr, hd, _⟩ => ⟨hw, hl.mono (by simp), hr, hd⟩) le_rfl
    (fun _ h => h) le_rfl

/-- A randomized small-eigenvalue kernel (`NLAlib.ShiftedQR.IsRandomSmallEig`) with forward error
$\beta$ and failure probability $\varphi$, called as a routine
(`NLAlib.ShiftedQR.smallEigKernel`), meets the routine contract for every order bound, cap, norm
bound and parameter words. -/
theorem IsRandomSmallEig.randomSmallEigContract {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) (kmax T : ℕ) (S : ℝ) (qs : List ℝ) :
    RandomSmallEigContract law β φ kmax T S qs (smallEigKernel (O := O) (Q := Q)) I :=
  h.randomSmallEigContractAt kmax qs.length T S qs

/-- The kernel called as a routine terminates at any word count with any words: it always
succeeds on live, readable operands with room. -/
theorem IsRandomSmallEig.terminatingSmallEigAt {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) (kmax nq T : ℕ) (qs : List ℝ) :
    TerminatingSmallEigAt kmax nq T qs (smallEigKernel (O := O) (Q := Q)) I := by
  obtain ⟨W, Bad, -, -, hI⟩ := h
  intro d w q o τ μ B _ hH _ hl hroom _ _
  unfold smallEigKernel
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨hl.mono (by simp), ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, -, hys, -⟩
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
  exact ⟨y, hy⟩

/-- A randomized small-eigenvalue kernel, called as a routine, terminates for every order bound,
cap and parameter words: the kernel always succeeds on live, readable operands with room. -/
theorem IsRandomSmallEig.terminatingSmallEig {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) (kmax T : ℕ) (qs : List ℝ) :
    TerminatingSmallEig kmax T qs (smallEigKernel (O := O) (Q := Q)) I :=
  h.terminatingSmallEigAt kmax qs.length T qs

end SmallEig

section Routine

variable {O Q : Type}

/-- The routine contract is monotone in the norm bound. -/
theorem RandomSmallEigContractAt.mono_norm {law : ℕ → Measure ℝ} {β φ : ℝ} {kmax nq T : ℕ}
    {S S' : ℝ} {qs : List ℝ} {SE : Impl O Q} {I : Interp O Q ℝ}
    (h : RandomSmallEigContractAt law β φ kmax nq T S qs SE I) (hS : S' ≤ S) :
    RandomSmallEigContractAt law β φ kmax nq T S' qs SE I :=
  fun B hd hB hBn => h B hd hB (hBn.trans hS)

/-- The words of a routine stored as the tail of the parameter words: none, or the last $12$. -/
theorem readBlock_tail_twelve {s : Store ℝ} {b off : ℕ}
    {ps₀ qs : List ℝ} (hq12 : qs = [] ∨ qs.length = 12)
    (h : s.readBlock b off (ps₀ ++ qs).length = some (ps₀ ++ qs)) :
    s.readBlock b (off + ((ps₀ ++ qs).length - 12)) qs.length = some qs ∧
      (ps₀ ++ qs).length - 12 + qs.length ≤ (ps₀ ++ qs).length := by
  rcases hq12 with rfl | hqs
  · simp
  · have e : (ps₀ ++ qs).length - 12 = ps₀.length := by simp [hqs]
    rw [e]
    exact ⟨Store.readBlock_append_right h, by simp⟩

end Routine

section DiskSampler

/-- The operation of the exact disk sampler. -/
inductive DiskSampleOp where
  /-- `polar [] [R] [W]`: the polar sample of radius `R` from two entries of the stream, as the
  pair `W`. -/
  | polar
  deriving DecidableEq

/-- **The contract in operand form of the exact polar disk sampler** reading the stream `s`: the
call reads one radius word $R$ and a window $(x_0, x_1)$ of two entries of the stream, and writes
the real and imaginary parts of `NLAlib.polarDisk 0 R (x₀, x₁)`
$= R\sqrt{x_0}\,e^{2\pi i x_1}$. -/
def polarDiskRel (s : ℕ) : BlockRel ℝ where
  nd := 0
  stream := s
  win _ := 2
  inLens _ := [1]
  outLens _ := [2]
  rel _ xs w ys := ∀ R : ℝ, xs = [[R]] →
    ys = [[(polarDisk 0 R fun j : Fin 2 => w.getD j 0).re,
      (polarDisk 0 R fun j : Fin 2 => w.getD j 0).im]]

/-- The exact polar disk sampler on the stream `s`, as a block function. -/
noncomputable def polarDiskFn (s : ℕ) : BlockFn ℝ where
  nd := 0
  stream := s
  win _ := 2
  inLens _ := [1]
  outLens _ := [2]
  fn _ w xs := some [[(polarDisk 0 ((xs.headD []).headD 0) fun j : Fin 2 => w.getD j 0).re,
    (polarDisk 0 ((xs.headD []).headD 0) fun j : Fin 2 => w.getD j 0).im]]

variable {O Q : Type} [Has DiskSampleOp O]

/-- **An exact polar disk sampler** on the stream `s`: the interpretation's `polar` always
succeeds on live, readable operands with room and meets `NLAlib.ShiftedQR.polarDiskRel`. For a
uniform stream on $[0, 1]$ its sample is uniform on the disk of the radius word
(`NLAlib.map_polarDisk_eq_diskUniform`). -/
def IsPolarDiskSampler (s : ℕ) (I : Interp O Q ℝ) : Prop :=
  I.Meets .total (Has.inj DiskSampleOp.polar) ((polarDiskRel s).spec AnyOperands)

end DiskSampler

end NLAlib.ShiftedQR
