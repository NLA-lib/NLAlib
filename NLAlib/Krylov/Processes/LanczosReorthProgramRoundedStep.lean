/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ExecCharge
public import NLAlib.Krylov.Processes.LanczosReorthProgramRounding
public import NLAlib.Krylov.Processes.LanczosProgramRounded

/-!
# One rounded step of Lanczos with full reorthogonalization as a program

The rounded run of one step of `NLAlib.lanczosReorthLoop` inside its scope, at the run-time
handles `work` $= 8$, `scalars` $= 9$, `coef` $= 10$ (the matrix slot is $7$), for any product
routine certified by `NLAlib.Computation.IsMatvecRoutine` and any orthogonalization call with a
guarantee `G`: the work phase (product, both Paige updates, the coefficient $\alpha_{t+1}$ and
the norm $\nu_{t+1}$ before orthogonalization), the orthogonalization call and the norm
$\beta_{t+1}$ after it, and the commit (previous vector and guarded normalization). The
guarded normalization is proved under unit charges and transferred to any charge by
`NLAlib.Computation.exists_exec_withCharge_eq_some`.

## Main definitions

* `NLAlib.LanczosReorthImplementation.workspaceShape`: the store shape inside the scope.
* `NLAlib.LanczosReorthImplementation.workPhase`, `commitPhase`, `stepBody`: the phases of a
  step.
* `NLAlib.LanczosReorthImplementation.StoreContext`: the decoded store after $t$ steps.
* `NLAlib.LanczosReorthImplementation.IsOrthCall`: the certificate of an orthogonalization call.
* `NLAlib.LanczosReorthImplementation.RoundedStep`: the local guarantees of one step.

## Main results

* `NLAlib.LanczosReorthImplementation.exec_workPhase`, `exec_orth_nrm2`, `exec_commitPhase`.
* `NLAlib.LanczosReorthImplementation.exec_stepBody`: one step.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- The store shape of a run of `NLAlib.lanczosReorthLoop` inside its scope, all at `tag`: the
seven declared buffers ($N$, $N(q+1)$, $q$, $q+1$, $1$, $N$, $q$), the matrix slot of length
`slot`, and the scoped `work` ($N$), `scalars` ($2$) and `coef` ($q+1$). -/
def workspaceShape (tag : P) (N q slot : ℕ) : Array (P × ℕ) :=
  #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N), (tag, q),
    (tag, slot), (tag, N), (tag, 2), (tag, q + 1)]

/-- The work phase of step $t$ of `NLAlib.lanczosReorthLoop` at the run-time handles: the product
`mv`, the previous update, the coefficient $\alpha_{t+1}$, the projection update and the norm
$\nu_{t+1}$ of the work vector. -/
def workPhase (tag : P) (N t : ℕ) (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) :
    Builder P ι ℕ ℕ Unit := do
  mv 8 (IExp.var t)
  ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
  axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
  dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
  ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
  axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
  nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N)

/-- The commit phase of step $t$ of `NLAlib.lanczosReorthLoop` at the run-time handles: the copy of
the current column into the previous vector, then the guarded normalization of the work vector
into column $t + 1$. -/
def commitPhase (tag : P) (N t : ℕ) : Builder P ι ℕ ℕ Unit := do
  copyv tag 1 (IExp.const N * IExp.var t) 5 0 (IExp.const N)
  ifThenElse tag .eq ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩
    (forRange (IExp.const N) fun i =>
      ins (.lit tag ⟨1, IExp.const N * (IExp.var t + 1) + IExp.var i⟩ 0)) (do
      copyv tag 8 0 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N)
      rscl tag ⟨3, IExp.var t + 1⟩ 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N))

/-- Step $t$ of `NLAlib.lanczosReorthLoop` at the run-time handles: the work phase, the
orthogonalization call, the norm $\beta_{t+1}$ and the commit phase. -/
def stepBody (tag : P) (N t : ℕ) (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) : Builder P ι ℕ ℕ Unit := do
  workPhase tag N t mv
  orth 8 10 (IExp.var t)
  nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)
  commitPhase tag N t

/-- The decoded store of `NLAlib.lanczosReorthLoop` after $t$ steps: the shape
`NLAlib.LanczosReorthImplementation.workspaceShape`, the precondition `pre` of the product, and
the buffers holding $\mathbf{b}$, the columns $\mathbf{v}_1, \dots, \mathbf{v}_{t+1}$, the
coefficients $\alpha_1, \dots, \alpha_t$ and $\beta_0, \dots, \beta_t$, the previous vector
$\mathbf{v}_t$, the norms $\nu_1, \dots, \nu_t$ and the zero scalar. -/
structure StoreContext (tag : P) (dec : P → K → ℝ) (N q slot : ℕ) (b : Fin N → ℝ)
    (pre : Store P K → Prop) (t : ℕ) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ) (s : Store P K) :
    Prop where
  /-- The shape inside the scope. -/
  shape : s.shape = workspaceShape tag N q slot
  /-- The precondition of the product. -/
  holds_pre : pre s
  /-- The input. -/
  input : ∀ i : Fin N, ∃ w, s.read tag 0 i = some w ∧ dec tag w = b i
  /-- The completed basis columns. -/
  basis : ∀ c ≤ t, ∀ i : Fin N, ∃ w, s.read tag 1 (N * c + i) = some w ∧ dec tag w = v (c + 1) i
  /-- The completed diagonal coefficients. -/
  alpha : ∀ c < t, ∃ w, s.read tag 2 c = some w ∧ dec tag w = α (c + 1)
  /-- The initial and completed off-diagonal coefficients. -/
  beta : ∀ c ≤ t, ∃ w, s.read tag 3 c = some w ∧ dec tag w = β c
  /-- The previous vector. -/
  prev : ∀ i : Fin N, ∃ w, s.read tag 5 i = some w ∧ dec tag w = v t i
  /-- The completed norms before orthogonalization. -/
  nu : ∀ c < t, ∃ w, s.read tag 6 c = some w ∧ dec tag w = ν (c + 1)
  /-- The zero scalar of the zero test. -/
  zero : ∃ w, s.read tag 9 0 = some w ∧ dec tag w = 0

/-- The certificate of the orthogonalization call `routine` of step $t$ with guarantee `G`: it
composes with the following program and, from every store of shape
`NLAlib.LanczosReorthImplementation.workspaceShape` whose buffer $1$ holds a basis
$\mathbf{V}$ ($N \times (t+1)$, column-major) and whose `work` buffer holds $\mathbf{w}$, it
succeeds, writes only the reduced vector into `work` and the coefficients into `coef`, and the
decoded values meet `G`. -/
structure IsOrthCall (I : Interp P ι K (OpCount P ι)) (dec : P → K → ℝ) (tag : P)
    (N q slot t : ℕ)
    (G : Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) → (Fin N → ℝ) → Prop)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The call composes with the following program. -/
  composable : ExecutionComposable I routine
  /-- The call succeeds, its only effect and its guarantee. -/
  run : ∀ (s : St P K (OpCount P ι)) (V : Matrix (Fin N) (Fin (t + 1)) ℝ) (w : Fin N → ℝ),
    s.store.shape = workspaceShape tag N q slot → HoldsDecoded s.store dec tag 1 0 V →
    (∀ i : Fin N, ∃ x, s.store.read tag 8 i = some x ∧ dec tag x = w i) →
    ∃ (out : St P K (OpCount P ι)) (W : Fin N → K) (Hw : Fin (t + 1) → K) (mid : Store P K),
      exec I routine.run s = some out ∧
      s.store.writeBlock tag 8 0 (Array.ofFn W) = some mid ∧
      mid.writeBlock tag 10 0 (Array.ofFn Hw) = some out.store ∧
      G V w (fun i => dec tag (Hw i)) (fun i => dec tag (W i))

/-- The local guarantees of one rounded step with accuracy $\varepsilon$: from the previous and
current vectors $\mathbf{v}_p$, $\mathbf{v}_c$ and the previous coefficient $\beta_p$, the
computed product $\mathbf{u}$, the updates $\mathbf{w}$ and $\mathbf{z}$, the coefficient
$\alpha$, the stored norm $\nu$ of $\mathbf{z}$, the orthogonalization output $\mathbf{z}'$ with
coefficients $\mathbf{h}$ against the basis $\mathbf{V}$ (guarantee `G`), its norm $\beta$ and
the next vector $\mathbf{v}_n$ each meet their kernel error bound. -/
structure RoundedStep {N m : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ)
    (G : Matrix (Fin N) (Fin m) ℝ → (Fin N → ℝ) → (Fin m → ℝ) → (Fin N → ℝ) → Prop)
    (V : Matrix (Fin N) (Fin m) ℝ) (vp vc vn : Fin N → ℝ) (βp α ν β : ℝ)
    (uv wv zv z' : Fin N → ℝ) (h : Fin m → ℝ) : Prop where
  /-- The product. -/
  norm_mulVec_sub_le : ‖WithLp.toLp 2 (A *ᵥ vc - uv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 vc‖
  /-- The previous update. -/
  norm_sub_smul_sub_le : ‖WithLp.toLp 2 (uv - βp • vp - wv)‖ ≤
    ε * (‖WithLp.toLp 2 uv‖ + |βp| * ‖WithLp.toLp 2 vp‖)
  /-- The diagonal coefficient. -/
  abs_dotProduct_sub_le : |vc ⬝ᵥ wv - α| ≤ ε * ‖WithLp.toLp 2 vc‖ * ‖WithLp.toLp 2 wv‖
  /-- The projection update. -/
  norm_projection_sub_le : ‖WithLp.toLp 2 (wv - α • vc - zv)‖ ≤
    ε * (‖WithLp.toLp 2 wv‖ + |α| * ‖WithLp.toLp 2 vc‖)
  /-- The stored norm before orthogonalization is nonnegative. -/
  nu_nonneg : 0 ≤ ν
  /-- The stored norm before orthogonalization. -/
  abs_nu_sub_le : |ν - ‖WithLp.toLp 2 zv‖| ≤ ε * ‖WithLp.toLp 2 zv‖
  /-- The orthogonalization guarantee. -/
  orth : G V zv h z'
  /-- The norm after orthogonalization. -/
  abs_beta_sub_le : |β - ‖WithLp.toLp 2 z'‖| ≤ ε * ‖WithLp.toLp 2 z'‖
  /-- The normalization. -/
  norm_sub_smul_le : ‖WithLp.toLp 2 (z' - β • vn)‖ ≤ ε * ‖WithLp.toLp 2 z'‖
  /-- The next vector is nearly a unit vector unless $\beta = 0$. -/
  abs_norm_sq_sub_one_le : β ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ ε
  /-- The next vector is zero if $\beta = 0$. -/
  eq_zero_of_eq_zero : β = 0 → vn = 0

/-! ### The work phase -/

/-- The norm of the decoded work vector $\mathbf{z}$ stored into the cell $(k, e)$, $k \ne 8$,
under the relative-error model with accuracy $\varepsilon$ =
`NLAlib.lanczosImplementationRoundoffBound`, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$: the norm $\nu \ge
0$ vanishes iff $\mathbf{z} = \mathbf{0}$ and $\lvert \nu - \|\mathbf{z}\| \rvert \le \varepsilon
\|\mathbf{z}\|$; only the cell is written. -/
theorem exec_nrm2_work (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N : ℕ} (k : ℕ) (e : IExp ℕ) (hk : k ≠ 8) (st : St P K (OpCount P ι))
    (hdst : ∃ w s, st.store.write tag k e.eval w = some s) (zv : Fin N → ℝ)
    (hzv : ∀ i : Fin N, ∃ w, st.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (nn : ℝ),
      exec I (nrm2 tag ⟨k, e⟩ 8 0 (IExp.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k' i, (k' ≠ k ∨ i ≠ e.eval) → out.store.read p k' i = st.store.read p k' i) ∧
      (∃ w, out.store.read tag k e.eval = some w ∧ dec tag w = nn) ∧
      0 ≤ nn ∧ (nn = 0 ↔ zv = 0) ∧
      |nn - ‖WithLp.toLp 2 zv‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  let xz : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xz i) = zv := by funext i; simp [xz]
  obtain ⟨out, wn, hr, hwn, hpos, hnerr, hzero⟩ := h.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz
    st ⟨k, e⟩ 8 0 (IExp.const N) xz hwin.1 hwin.2.2.1
    (by
      intro i hi
      change i < N at hi
      obtain ⟨w, hw, hdw⟩ := hzv ⟨i, hi⟩
      exact ⟨w, by simpa using hw, by simp [xz, hi, hdw]⟩)
    (fun h8 => (hk h8).elim) hdst
  refine ⟨out, dec tag wn, hr, Store.shape_of_write_eq_some hwn,
    fun p k' i hk' => Store.read_of_write_eq_some_of_ne hwn hk',
    ⟨wn, Store.read_of_write_eq_some hwn, rfl⟩, hpos, ?_, ?_⟩
  · change dec tag wn = 0 ↔ (fun i : Fin N => xz i) = 0 at hzero
    rwa [hxs] at hzero
  · change |‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ - dec tag wn| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ at hnerr
    rw [hxs, abs_sub_comm] at hnerr
    exact hnerr.trans (mul_le_mul_of_nonneg_right
      (roundingFactor_succ_le_lanczosImplementationRoundoffBound N hu hsmall) (norm_nonneg _))

/-- The product and the previous update of step $t$: the product routine `mv` (certified with
coefficient $\varepsilon \|\mathbf{A}\|_2$) writes $\mathbf{u} \approx \mathbf{A}\mathbf{v}_c$
into `work` and the update overwrites it with $\mathbf{w} \approx \mathbf{u} - \beta_t
\mathbf{v}_p$; only `work` and the scratch scalar are written. -/
theorem exec_matvec_previous_update (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ} (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    {N q t slot : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (pre : Store P K → Prop) (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (hpre : pre st.store) (vc vp : Fin N → ℝ) (bt : ℝ)
    (hvc : ∀ i : Fin N, ∃ w, st.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (hvp : ∀ i : Fin N, ∃ w, st.store.read tag 5 i = some w ∧ dec tag w = vp i)
    (hbt : ∃ w, st.store.read tag 3 t = some w ∧ dec tag w = bt)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv wv : Fin N → ℝ),
      exec I (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → (k = 9 → i ≠ 1) → out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 8 i = some w ∧ dec tag w = wv i) ∧
      ‖WithLp.toLp 2 (A *ᵥ vc - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A * ‖WithLp.toLp 2 vc‖ ∧
      ‖WithLp.toLp 2 (uv - bt • vp - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |bt| * ‖WithLp.toLp 2 vp‖) := by
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  obtain ⟨st₁, W₁, hr₁, hw₁, he₁⟩ := hmv.run st vc hpre
    (by simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hvc)
    (fun i hi => ⟨N, by simp [hshape, workspaceShape], by simpa using hi⟩)
  have sh₁ := Store.shape_of_writeBlock_eq_some hw₁
  have f₁ : ∀ p k i, k ≠ 8 → st₁.store.read p k i = st.store.read p k i :=
    fun p k i hk => Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hk)
  have r₁ (i : Fin N) : st₁.store.read tag 8 i = some (W₁ i) := by
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (j := (i : ℕ)) (by simp)
  let uv : Fin N → ℝ := fun i => dec tag (W₁ i)
  let xp : ℕ → ℝ := fun i => if hi : i < N then vp ⟨i, hi⟩ else 0
  let yu : ℕ → ℝ := fun i => if hi : i < N then uv ⟨i, hi⟩ else 0
  obtain ⟨out, W₂, hr₂, sh₂, rd₂, f₂, he₂⟩ := h.exec_neg_axpy_norm_sub_le I tag st₁
    ⟨3, IExp.var t⟩ ⟨9, 1⟩ 5 0 8 0 (IExp.const N) bt xp yu hwin.2.1
    (by change ∃ w, st₁.store.read tag 3 t = some w ∧ _; rw [f₁ tag 3 t (by omega)]; exact hbt)
    (by intro i hi; change i < N at hi; rw [IExp.eval_zero, zero_add, f₁ tag 5 i (by omega)]
        simpa [xp, hi] using hvp ⟨i, hi⟩)
    (by intro i hi; change i < N at hi; refine ⟨W₁ ⟨i, hi⟩, ?_, ?_⟩
        · simpa using r₁ ⟨i, hi⟩
        · simp [yu, hi, uv])
    ⟨2, by rw [sh₁, hshape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  refine ⟨out, uv, fun i => dec tag (W₂ i), ?_, sh₂.trans sh₁,
    fun p k i h8 h9 => (f₂ p k i (Or.inl h8) h9).trans (f₁ p k i h8),
    fun i => ⟨W₂ i, by simpa using rd₂ i, rfl⟩, he₁, ?_⟩
  · rw [hmv.composable, hr₁, Option.bind_some]
    exact hr₂
  · have he := he₂.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1 (by positivity))
    have hxs : (fun i : Fin N => xp i) = vp := by funext i; simp [xp]
    have hys : (fun i : Fin N => yu i) = uv := by funext i; simp [yu]
    have heq : (fun i : Fin N => yu i - bt * xp i - dec tag (W₂ i)) =
        uv - bt • vp - (fun i : Fin N => dec tag (W₂ i)) := by
      ext i
      simp [xp, yu]
    change ‖WithLp.toLp 2 (fun i : Fin N => yu i - bt * xp i - dec tag (W₂ i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => yu i)‖ +
        |bt| * ‖WithLp.toLp 2 (fun i : Fin N => xp i)‖) at he
    rwa [heq, hxs, hys] at he

/-- The coefficient and the projection update of step $t$: `dot` stores
$\alpha \approx \mathbf{v}_c \cdot \mathbf{w}$ into cell $(2, t)$ and the update overwrites `work`
with $\mathbf{z} \approx \mathbf{w} - \alpha \mathbf{v}_c$; only `work`, the cell and the scratch
scalar are written. -/
theorem exec_dot_projection_update (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ} (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (tag : P) {N q t slot : ℕ}
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (ht : t < q) (vc wv : Fin N → ℝ)
    (hvc : ∀ i : Fin N, ∃ w, st.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (hwv : ∀ i : Fin N, ∃ w, st.store.read tag 8 i = some w ∧ dec tag w = wv i) (w0 : K)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (an : ℝ) (zv : Fin N → ℝ),
      exec I (do
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) :
          Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 8 i = some w ∧ dec tag w = zv i) ∧
      (∃ w, out.store.read tag 2 t = some w ∧ dec tag w = an) ∧
      |vc ⬝ᵥ wv - an| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 vc‖ * ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • vc - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 vc‖) := by
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hsucc := hwin.1
    push_cast at hsucc
    nlinarith
  let xc : ℕ → ℝ := fun i => if hi : i < N then vc ⟨i, hi⟩ else 0
  let yw : ℕ → ℝ := fun i => if hi : i < N then wv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xc i) = vc := by funext i; simp [xc]
  have hys : (fun i : Fin N => yw i) = wv := by funext i; simp [yw]
  have hxc (i : ℕ) (hi : i < N) (s : St P K (OpCount P ι))
      (hs : s.store.read tag 1 (N * t + i) = st.store.read tag 1 (N * t + i)) :
      ∃ w, s.store.read tag 1 ((IExp.const N * IExp.var t).eval + i) = some w ∧
        dec tag w = xc i := by
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_var]
    rw [hs]
    simpa [xc, hi] using hvc ⟨i, hi⟩
  have hyw (i : ℕ) (hi : i < N) : ∃ w, st.store.read tag 8 ((0 : IExp ℕ).eval + i) = some w ∧
      dec tag w = yw i := by
    obtain ⟨w, hw, hdw⟩ := hwv ⟨i, hi⟩
    exact ⟨w, by simpa using hw, by simp [yw, hi, hdw]⟩
  obtain ⟨st₃, an, hr₃, hw₃, he₃⟩ := h.exec_dot_abs_dotProduct_sub_le I tag st hz
    ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) xc yw hn
    (fun i hi => hxc i hi st rfl) hyw (by simp) (by simp)
    ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0 (by rw [hshape]; rfl) ht⟩
  have sh₃ := Store.shape_of_write_eq_some hw₃
  have f₃ : ∀ p k i, (k ≠ 2 ∨ i ≠ t) → st₃.store.read p k i = st.store.read p k i :=
    fun p k i hk => Store.read_of_write_eq_some_of_ne hw₃ hk
  obtain ⟨out, W₄, hr₄, sh₄, rd₄, f₄, he₄⟩ := h.exec_neg_axpy_norm_sub_le I tag st₃
    ⟨2, IExp.var t⟩ ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) (dec tag an)
    xc yw hwin.2.1 ⟨an, Store.read_of_write_eq_some hw₃, rfl⟩
    (fun i hi => hxc i hi st₃ (f₃ tag 1 _ (Or.inl (by omega))))
    (fun i hi => by rw [f₃ tag 8 _ (Or.inl (by omega))]; exact hyw i hi)
    ⟨2, by rw [sh₃, hshape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  refine ⟨out, dec tag an, fun i => dec tag (W₄ i), ?_, sh₄.trans sh₃, ?_,
    fun i => ⟨W₄ i, by simpa using rd₄ i, rfl⟩, ⟨an, ?_, rfl⟩, ?_, ?_⟩
  · rw [exec_run_bind I (b := dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t)
      8 0 (IExp.const N)) (fun _ => rfl), hr₃, Option.bind_some]
    exact hr₄
  · intro p k i h8 h9 h2
    have hk : k ≠ 2 ∨ i ≠ t := by
      by_cases hk : k = 2
      exacts [Or.inr (h2 hk), Or.inl hk]
    rw [f₄ p k i (Or.inl h8) h9, f₃ p k i hk]
  · rw [f₄ tag 2 t (Or.inl (by omega)) (by simp)]
    exact Store.read_of_write_eq_some hw₃
  · change |(fun i : Fin N => xc i) ⬝ᵥ (fun i : Fin N => yw i) - dec tag an| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xc i)‖ *
        ‖WithLp.toLp 2 (fun i : Fin N => yw i)‖ at he₃
    rw [hxs, hys] at he₃
    exact he₃.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (roundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall) (norm_nonneg _))
      (norm_nonneg _))
  · have he := he₄.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1 (by positivity))
    have heq : (fun i : Fin N => yw i - dec tag an * xc i - dec tag (W₄ i)) =
        wv - dec tag an • vc - (fun i : Fin N => dec tag (W₄ i)) := by
      ext i
      simp [xc, yw]
    change ‖WithLp.toLp 2 (fun i : Fin N => yw i - dec tag an * xc i - dec tag (W₄ i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => yw i)‖ +
        |dec tag an| * ‖WithLp.toLp 2 (fun i : Fin N => xc i)‖) at he
    rwa [heq, hxs, hys] at he

/-- The work phase of step $t < q$ (`NLAlib.LanczosReorthImplementation.workPhase`) under the
relative-error model with accuracy $\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`,
that is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$ and a product
routine certified with coefficient $\varepsilon\|\mathbf{A}\|_2$: from a store with the current
column $\mathbf{v}_c$, the previous vector $\mathbf{v}_p$ and $\beta_t$, it succeeds; the product
$\mathbf{u}$, the updates $\mathbf{w}$, $\mathbf{z}$ (left in `work`), the coefficient $\alpha$
(cell $(2, t)$) and the norm $\nu$ of $\mathbf{z}$ (cell $(6, t)$) meet their kernel error
bounds, and nothing else but the scratch scalar is written. -/
theorem exec_workPhase (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (pre : Store P K → Prop) (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (hpre : pre st.store) (ht : t < q) (vc vp : Fin N → ℝ) (bt : ℝ)
    (hvc : ∀ i : Fin N, ∃ w, st.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (hvp : ∀ i : Fin N, ∃ w, st.store.read tag 5 i = some w ∧ dec tag w = vp i)
    (hbt : ∃ w, st.store.read tag 3 t = some w ∧ dec tag w = bt)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv wv zv : Fin N → ℝ) (an nn : ℝ),
      exec I (workPhase tag N t mv).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) → (k = 6 → i ≠ t) →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 8 i = some w ∧ dec tag w = zv i) ∧
      (∃ w, out.store.read tag 2 t = some w ∧ dec tag w = an) ∧
      (∃ w, out.store.read tag 6 t = some w ∧ dec tag w = nn) ∧
      ‖WithLp.toLp 2 (A *ᵥ vc - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A * ‖WithLp.toLp 2 vc‖ ∧
      ‖WithLp.toLp 2 (uv - bt • vp - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |bt| * ‖WithLp.toLp 2 vp‖) ∧
      |vc ⬝ᵥ wv - an| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 vc‖ * ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • vc - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 vc‖) ∧
      0 ≤ nn ∧ |nn - ‖WithLp.toLp 2 zv‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  obtain ⟨w0, -, -⟩ := id hbt
  obtain ⟨st₂, uv, wv, hr₂, sh₂, f₂, hw₂, e₁, e₂⟩ := exec_matvec_previous_update I h tag pre mv
    hmv st hshape hpre vc vp bt hvc hvp hbt hsmall
  obtain ⟨st₄, an, zv, hr₄, sh₄, f₄, hz₄, ha₄, e₃, e₄⟩ := exec_dot_projection_update I h hz tag
    st₂ (sh₂.trans hshape) ht vc wv
    (fun i => by rw [f₂ tag 1 _ (by omega) (by omega)]; exact hvc i) hw₂ w0 hsmall
  obtain ⟨out, nn, hr₅, sh₅, f₅, hn₅, hnn, -, e₅⟩ := exec_nrm2_work I h hz tag 6 (IExp.var t)
    (by omega) st₄ ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0
      (by rw [sh₄, sh₂, hshape]; rfl) ht⟩ zv hz₄ hsmall
  refine ⟨out, uv, wv, zv, an, nn, ?_, sh₅.trans (sh₄.trans sh₂), ?_,
    fun i => by rw [f₅ tag 8 i (Or.inl (by omega))]; exact hz₄ i,
    by rw [f₅ tag 2 t (Or.inl (by omega))]; exact ha₄, hn₅, e₁, e₂, e₃, e₄, hnn, e₅⟩
  · have cu : ExecutionComposable I (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit) :=
      hmv.composable.bind ((executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl)))
    have cz : ExecutionComposable I (do
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) :
          Builder P ι ℕ ℕ Unit) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I (do
      (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N))
      (do
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N))
      nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit).run st = some out
    rw [cu, hr₂, Option.bind_some, cz, hr₄, Option.bind_some]
    exact hr₅
  · intro p k i h8 h9 h2 h6
    rw [f₅ p k i (by by_cases hk : k = 6; exacts [Or.inr (h6 hk), Or.inl hk]),
      f₄ p k i h8 h9 h2, f₂ p k i h8 h9]

/-! ### Orthogonalization and the commit -/

/-- The orthogonalization call of step $t < q$ and the norm after it: the certified call
reduces the work vector $\mathbf{z}$ against the basis $\mathbf{V}$ to $\mathbf{z}'$ with
coefficients $\mathbf{h}$ meeting `G`, and `nrm2` stores $\beta \ge 0$ into cell $(3, t+1)$,
$\beta = 0$ iff $\mathbf{z}' = \mathbf{0}$ and
$\lvert \beta - \|\mathbf{z}'\| \rvert \le \varepsilon \|\mathbf{z}'\|$. -/
theorem exec_orth_nrm2 (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (G : Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) → (Fin N → ℝ) → Prop)
    (horth : IsOrthCall I dec tag N q slot t G (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (ht : t < q) (w0 : K) (V : Matrix (Fin N) (Fin (t + 1)) ℝ)
    (hV : HoldsDecoded st.store dec tag 1 0 V) (zv : Fin N → ℝ)
    (hzv : ∀ i : Fin N, ∃ w, st.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (mid out : St P K (OpCount P ι)) (z' : Fin N → ℝ) (hv : Fin (t + 1) → ℝ) (bn : ℝ),
      exec I (orth 8 10 (IExp.var t)).run st = some mid ∧
      exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run mid = some out ∧
      mid.store.shape = st.store.shape ∧ out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → k ≠ 10 → mid.store.read p k i = st.store.read p k i) ∧
      (∀ p k i, (k ≠ 3 ∨ i ≠ t + 1) → out.store.read p k i = mid.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, mid.store.read tag 8 i = some w ∧ dec tag w = z' i) ∧
      (∃ w, out.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn) ∧
      G V zv hv z' ∧
      |bn - ‖WithLp.toLp 2 z'‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ := by
  obtain ⟨mid, W, Hw, mid₀, hr, hw₁, hw₂, herr⟩ := horth.run st V zv hshape hV hzv
  have shm : mid.store.shape = st.store.shape :=
    (Store.shape_of_writeBlock_eq_some hw₂).trans (Store.shape_of_writeBlock_eq_some hw₁)
  have rm (i : Fin N) : mid.store.read tag 8 i = some (W i) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl (by omega))]
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (j := (i : ℕ)) (by simp)
  obtain ⟨out, bn, hr₂, sho, fo, hbn, -, -, e⟩ := exec_nrm2_work I h hz tag 3 (IExp.var t + 1)
    (by omega) mid ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0
      (by rw [shm, hshape]; rfl) (by simpa using ht)⟩ (fun i => dec tag (W i))
    (fun i => ⟨W i, rm i, rfl⟩) hsmall
  exact ⟨mid, out, fun i => dec tag (W i), fun i => dec tag (Hw i), bn, hr, hr₂, shm,
    sho.trans shm,
    fun p k i h8 h10 => (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl h10)).trans
      (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl h8)),
    fun p k i hk => fo p k i (by simpa using hk), fun i => ⟨W i, rm i, rfl⟩,
    by simpa using hbn, herr, e⟩

/-- `NLAlib.LanczosReorthImplementation.exec_commitPhase` under unit charges. -/
private theorem exec_commitPhase_of_charge (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P) {N q t slot : ℕ}
    (predot normed : St P K (OpCount P ι))
    (hshape : normed.store.shape = workspaceShape tag N q slot)
    (hpshape : predot.store.shape = normed.store.shape) (ht : t < q) (vc : Fin N → ℝ)
    (hvc : ∀ i : Fin N, ∃ w, normed.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (zv : Fin N → ℝ)
    (hzp : ∀ i : Fin N, ∃ w, predot.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzn : ∀ i : Fin N, ∃ w, normed.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzero : ∃ w, normed.store.read tag 9 0 = some w ∧ dec tag w = 0)
    (hnorm : exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run predot =
      some normed)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (vn : Fin N → ℝ) (bn : ℝ),
      exec I (commitPhase tag N t).run normed = some out ∧
      out.store.shape = normed.store.shape ∧
      (∀ p k i, k ≠ 5 → (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
        out.store.read p k i = normed.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = vc i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 (N * (t + 1) + i) = some w ∧ dec tag w = vn i) ∧
      (∃ w, normed.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn) ∧
      (bn = 0 → vn = 0) ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  classical
  let xs : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xs i) = zv := by funext i; simp [xs]
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  choose words hread hdec using hvc
  obtain ⟨fallback, hf0, hdf0⟩ := hzero
  let Wc : ℕ → K := fun i => if hi : i < N then words ⟨i, hi⟩ else fallback
  have hWc (i : ℕ) (hi : i < N) :
      normed.store.read tag 1 ((IExp.const N * IExp.var t).eval + i) = some (Wc i) := by
    simpa only [Wc, dif_pos hi, IExp.eval_mul, IExp.eval_const, IExp.eval_var] using
      hread ⟨i, hi⟩
  obtain ⟨ready, hcopy, shcopy, hprev, fcopy, _⟩ := exec_copyv_frame I hc tag normed
    (IExp.const N) 1 5 (IExp.const N * IExp.var t) 0 Wc hWc (by omega)
    (by intro i hi; exact ⟨N, by rw [hshape]; rfl, by simpa using hi⟩)
  have hdst : ∃ w store, predot.store.write tag 3 (t + 1) w = some store :=
    ⟨fallback, Store.exists_write_eq_some_of_getElem?_shape fallback
      (by rw [hpshape, hshape]; rfl) (by omega)⟩
  have hy (i : ℕ) (hi : i < N) : ∃ len,
      ready.store.shape[1]? = some (tag, len) ∧ N * (t + 1) + i < len := by
    refine ⟨N * (q + 1), by rw [shcopy, hshape]; rfl, ?_⟩
    calc
      N * (t + 1) + i < N * (t + 1) + N := Nat.add_lt_add_left hi _
      _ = N * (t + 2) := by ring
      _ ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  obtain ⟨out, w, W, hg, shg, hrready, -, _, _, _, hvout, fg,
      hvzero, hvunit, hres, _⟩ := h.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed ready ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩ 8 1 0
    (IExp.const N * (IExp.var t + 1)) (IExp.const N) xs hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hzp ⟨i, hi⟩)
    (by
      intro i hi
      change i < N at hi
      rw [show ready.store.read tag 8 (IExp.eval 0 + i) = normed.store.read tag 8 i by
        simpa using fcopy tag 8 i (by omega)]
      simpa only [xs, dif_pos hi] using hzn ⟨i, hi⟩)
    (by simp) (by omega) (by simp) hdst (by simpa using hy) hnorm
    (by simpa using fcopy tag 3 (t + 1) (by omega))
    (by
      change ∃ w, ready.store.read tag 9 0 = some w ∧ dec tag w = 0
      rw [fcopy tag 9 0 (by omega)]
      exact ⟨fallback, hf0, hdf0⟩)
  refine ⟨out, fun i => dec tag (W i), dec tag w, ?_, shg.trans shcopy, ?_, ?_,
    fun i => ⟨W i, by simpa using hvout i, rfl⟩,
    ⟨w, (fcopy tag 3 (t + 1) (by omega)).symm.trans (by simpa using hrready), rfl⟩,
    hvzero, fun hne => (hvunit hne).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall), ?_⟩
  · rw [commitPhase, exec_run_bind I (b := copyv tag 1 (IExp.const N * IExp.var t) 5 0
      (IExp.const N)) (fun _ => rfl), hcopy, Option.bind_some]
    exact hg
  · intro p k i hk hi
    refine (fg p k i ?_).trans (fcopy p k i (Or.inl hk))
    by_cases he : k = 1
    · rcases hi he with hlt | hge
      · exact Or.inr (Or.inl (by simpa using hlt))
      · right; right
        simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_add, IExp.eval_var,
          IExp.eval_one, Nat.mul_add, Nat.mul_one, Nat.mul_succ, Nat.add_assoc] using hge
    · exact Or.inl he
  · intro i
    refine ⟨Wc i, ?_, by simpa only [Wc, dif_pos i.isLt] using hdec i⟩
    rw [fg tag 5 i (Or.inl (by omega))]
    simpa using hprev i i.isLt
  · have heq : (fun i : Fin N => xs i - dec tag w * dec tag (W i)) =
        zv - dec tag w • (fun i : Fin N => dec tag (W i)) := by
      ext i
      simp [xs]
    change ‖WithLp.toLp 2 (fun i : Fin N => xs i - dec tag w * dec tag (W i))‖ ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
    rw [heq, hxs] at hres
    exact hres.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.2 (norm_nonneg _))

/-- The commit phase of step $t < q$ (`NLAlib.LanczosReorthImplementation.commitPhase`), run
after the norm $\beta$ of the work vector $\mathbf{z}$ was stored into cell $(3, t+1)$: the
current column $\mathbf{v}_c$ is copied into the previous vector, and the guarded normalization
writes column $t + 1$ with $\mathbf{v}_n = \mathbf{0}$ if $\beta = 0$, and otherwise
$\lvert \|\mathbf{v}_n\|^2 - 1 \rvert \le \varepsilon$; in both cases
$\|\mathbf{z} - \beta\mathbf{v}_n\| \le \varepsilon\|\mathbf{z}\|$. Any charge. -/
theorem exec_commitPhase (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} (predot normed : St P K (OpCount P ι))
    (hshape : normed.store.shape = workspaceShape tag N q slot)
    (hpshape : predot.store.shape = normed.store.shape) (ht : t < q) (vc : Fin N → ℝ)
    (hvc : ∀ i : Fin N, ∃ w, normed.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (zv : Fin N → ℝ)
    (hzp : ∀ i : Fin N, ∃ w, predot.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzn : ∀ i : Fin N, ∃ w, normed.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzero : ∃ w, normed.store.read tag 9 0 = some w ∧ dec tag w = 0)
    (hnorm : exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run predot =
      some normed)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (vn : Fin N → ℝ) (bn : ℝ),
      exec I (commitPhase tag N t).run normed = some out ∧
      out.store.shape = normed.store.shape ∧
      (∀ p k i, k ≠ 5 → (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
        out.store.read p k i = normed.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = vc i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 (N * (t + 1) + i) = some w ∧ dec tag w = vn i) ∧
      (∃ w, normed.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn) ∧
      (bn = 0 → vn = 0) ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  obtain ⟨c₁, hnorm'⟩ :=
    exists_exec_withCharge_eq_some I (fun k => Finsupp.single k 1) _ hnorm predot.cnt
  obtain ⟨out, vn, bn, hr, rest⟩ := exec_commitPhase_of_charge
    { I with charge := fun k => Finsupp.single k 1 } h hz (fun _ => rfl) tag predot
    { normed with cnt := c₁ } hshape hpshape ht vc hvc zv hzp hzn hzero hnorm' hsmall
  obtain ⟨c₂, hr'⟩ := exists_exec_withCharge_eq_some _ I.charge _ hr normed.cnt
  exact ⟨{ out with cnt := c₂ }, vn, bn, hr', rest⟩

/-! ### One step -/

/-- The next decoded store after a step: a store that agrees with the store after $t$ steps
outside the buffers and cells the step writes, holds the previous column $\mathbf{v}_{t+1}$ in
the previous vector and the new values $\mathbf{v}_n$, $\alpha$, $\beta$, $\nu$ in column
$t + 1$ and cells $(2, t)$, $(3, t + 1)$, $(6, t)$, is the store after $t + 1$ steps of the
updated sequences. -/
theorem StoreContext.succ {tag : P} {dec : P → K → ℝ} {N q slot : ℕ} {b : Fin N → ℝ}
    {pre : Store P K → Prop} {t : ℕ} {v : ℕ → Fin N → ℝ} {α β ν : ℕ → ℝ} {s s' : Store P K}
    (hs : StoreContext tag dec N q slot b pre t v α β ν s)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (hshape : s'.shape = s.shape) {vn : Fin N → ℝ} {an bn nn : ℝ}
    (hframe : ∀ p k i, k ≠ 5 → k ≠ 8 → k ≠ 10 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
      (k = 6 → i ≠ t) → (k = 3 → i ≠ t + 1) → (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
      s'.read p k i = s.read p k i)
    (hvn : ∀ i : Fin N, ∃ w, s'.read tag 1 (N * (t + 1) + i) = some w ∧ dec tag w = vn i)
    (han : ∃ w, s'.read tag 2 t = some w ∧ dec tag w = an)
    (hbn : ∃ w, s'.read tag 3 (t + 1) = some w ∧ dec tag w = bn)
    (hprev : ∀ i : Fin N, ∃ w, s'.read tag 5 i = some w ∧ dec tag w = v (t + 1) i)
    (hnn : ∃ w, s'.read tag 6 t = some w ∧ dec tag w = nn) :
    StoreContext tag dec N q slot b pre (t + 1) (Function.update v (t + 2) vn)
      (Function.update α (t + 1) an) (Function.update β (t + 1) bn)
      (Function.update ν (t + 1) nn) s' := by
  have fr (k i : ℕ) (hk : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 5 ∧ k ≠ 6 ∧ k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) :
      s'.read tag k i = s.read tag k i :=
    hframe tag k i hk.2.2.2.1 hk.2.2.2.2.2.1 hk.2.2.2.2.2.2.2 (fun h => (hk.2.2.2.2.2.2.1 h).elim)
      (fun h => (hk.2.1 h).elim) (fun h => (hk.2.2.2.2.1 h).elim) (fun h => (hk.2.2.1 h).elim)
      (fun h => (hk.1 h).elim)
  refine ⟨hshape.trans hs.shape, hpreFrame s s' hs.holds_pre (fun k _ => by rw [hshape])
    (fun i => fr 7 i (by omega)), fun i => by rw [fr 0 i (by omega)]; exact hs.input i,
    fun c hc i => ?_, fun c hc => ?_, fun c hc => ?_,
    by simpa only [Function.update_of_ne (by omega : t + 1 ≠ t + 2)] using hprev, fun c hc => ?_,
    by rw [hframe tag 9 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]; exact hs.zero⟩
  · rcases (show c ≤ t ∨ c = t + 1 by omega) with hc | rfl
    · have hi : N * c + i < N * (t + 1) := by
        calc
          N * c + i < N * c + N := Nat.add_lt_add_left i.isLt _
          _ = N * (c + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ N * (t + 1) := Nat.mul_le_mul_left N (by omega)
      rw [hframe tag 1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (fun _ => Or.inl hi)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 2)] using hs.basis c hc i
    · simpa using hvn i
  · rcases (show c < t ∨ c = t by omega) with hc | rfl
    · rw [hframe tag 2 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 1)] using hs.alpha c hc
    · simpa using han
  · rcases (show c ≤ t ∨ c = t + 1 by omega) with hc | rfl
    · rw [hframe tag 3 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c ≠ t + 1)] using hs.beta c hc
    · simpa using hbn
  · rcases (show c < t ∨ c = t by omega) with hc | rfl
    · rw [hframe tag 6 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 1)] using hs.nu c hc
    · simpa using hnn

/-- The run of a step is the run of its phases. -/
private theorem exec_stepBody_eq (I : Interp P ι K (OpCount P ι)) (tag : P) (N t : ℕ)
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ExecutionComposable I (mv 8 (IExp.var t)))
    (hoc : ExecutionComposable I (orth 8 10 (IExp.var t)))
    {st s₁ mid normed out : St P K (OpCount P ι)}
    (h₁ : exec I (workPhase tag N t mv).run st = some s₁)
    (h₂ : exec I (orth 8 10 (IExp.var t)).run s₁ = some mid)
    (h₃ : exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run mid = some normed)
    (h₄ : exec I (commitPhase tag N t).run normed = some out) :
    exec I (stepBody tag N t mv orth).run st = some out := by
  have cw : ExecutionComposable I (workPhase tag N t mv) :=
    hmv.bind ((executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            ((executionComposable_single I (fun _ => rfl)).bind
              (executionComposable_single I (fun _ => rfl)))))))
  rw [stepBody, cw, h₁, Option.bind_some, hoc, h₂, Option.bind_some,
    exec_run_bind I (b := nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)) (fun _ => rfl),
    h₃, Option.bind_some]
  exact h₄

/-- One rounded step $t < q$ of the reorthogonalized loop
(`NLAlib.LanczosReorthImplementation.stepBody`) under the relative-error model with accuracy
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$, a product routine
certified with coefficient $\varepsilon\|\mathbf{A}\|_2$ (precondition `pre`, kept by the frame
of the matrix slot) and a certified orthogonalization call with guarantee `G`: from the decoded
store after $t$ steps, the step succeeds, the store is the decoded store after $t + 1$ steps of
the sequences updated by the new $\mathbf{v}_{t+2}$, $\alpha_{t+1}$, $\beta_{t+1}$, $\nu_{t+1}$,
the input norm is kept, and the step meets `NLAlib.LanczosReorthImplementation.RoundedStep`. -/
theorem exec_stepBody (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (b : Fin N → ℝ)
    (pre : Store P K → Prop)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (G : Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) → (Fin N → ℝ) → Prop)
    (horth : IsOrthCall I dec tag N q slot t G (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι)) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ)
    (hs : StoreContext tag dec N q slot b pre t v α β ν st.store)
    (ht : t < q) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv wv zv z' : Fin N → ℝ) (hv : Fin (t + 1) → ℝ)
      (an bn nn : ℝ) (vn : Fin N → ℝ),
      exec I (stepBody tag N t mv orth).run st = some out ∧
      StoreContext tag dec N q slot b pre (t + 1) (Function.update v (t + 2) vn)
        (Function.update α (t + 1) an) (Function.update β (t + 1) bn)
        (Function.update ν (t + 1) nn) out.store ∧
      out.store.read tag 4 0 = st.store.read tag 4 0 ∧
      RoundedStep A (lanczosImplementationRoundoffBound N (u tag)) G
        (LanczosReorthRun.basisOf v (t + 1)) (v t) (v (t + 1)) vn (β t) an nn bn uv wv zv z'
        hv := by
  obtain ⟨w0, hw0, hd0⟩ := hs.zero
  obtain ⟨s₁, uv, wv, zv, an, nn, hr₁, sh₁, f₁, hz₁, ha₁, hn₁, e₁, e₂, e₃, e₄, hnn, e₅⟩ :=
    exec_workPhase I h hz tag pre mv hmv st hs.shape hs.holds_pre ht (v (t + 1)) (v t) (β t)
      (hs.basis t le_rfl) hs.prev (hs.beta t le_rfl) hsmall
  obtain ⟨mid, normed, z', hv, bn, hr₂, hr₃, shm, shn, fm, fn, hzm, hbn, eorth, e₆⟩ :=
    exec_orth_nrm2 I h hz tag orth G horth s₁ (sh₁.trans hs.shape) ht w0 _
      (fun i c => by
        rw [show 0 + (i : ℕ) + N * c = N * c + i by ring, f₁ tag 1 _ (by omega) (by omega)
          (by omega) (by omega)]
        exact hs.basis c (by omega) i) zv hz₁ hsmall
  have fpre : ∀ p k i, k ≠ 8 → k ≠ 10 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
      (k = 6 → i ≠ t) → (k = 3 → i ≠ t + 1) →
      normed.store.read p k i = st.store.read p k i := fun p k i h8 h10 h9 h2 h6 h3 => by
    rw [fn p k i (by by_cases hk : k = 3; exacts [Or.inr (h3 hk), Or.inl hk]), fm p k i h8 h10,
      f₁ p k i h8 h9 h2 h6]
  obtain ⟨out, vn, bn', hr₄, sh₄, f₄, hp₄, hv₄, hbn', hvzero, hunit, e₇⟩ :=
    exec_commitPhase I h hz tag mid normed (shn.trans (sh₁.trans hs.shape))
      (shm.trans shn.symm) ht (v (t + 1))
      (fun i => by
        rw [fpre tag 1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hs.basis t le_rfl i)
      z' hzm (fun i => by rw [fn tag 8 i (Or.inl (by omega))]; exact hzm i)
      ⟨w0, by rw [fpre tag 9 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]; exact hw0, hd0⟩ hr₃ hsmall
  obtain rfl : bn' = bn := by
    obtain ⟨x, hx, hdx⟩ := hbn
    obtain ⟨y, hy, hdy⟩ := hbn'
    rw [hx] at hy
    cases hy
    rw [← hdx, ← hdy]
  have fall : ∀ p k i, k ≠ 5 → k ≠ 8 → k ≠ 10 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
      (k = 6 → i ≠ t) → (k = 3 → i ≠ t + 1) →
      (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
      out.store.read p k i = st.store.read p k i := fun p k i h5 h8 h10 h9 h2 h6 h3 h1 => by
    rw [f₄ p k i h5 h1, fpre p k i h8 h10 h9 h2 h6 h3]
  have fafter : ∀ p k i, k ≠ 5 → k ≠ 1 → k ≠ 8 → k ≠ 10 → k ≠ 3 →
      out.store.read p k i = s₁.store.read p k i := fun p k i h5 h1 h8 h10 h3 => by
    rw [f₄ p k i h5 (fun h => absurd h h1), fn p k i (Or.inl h3), fm p k i h8 h10]
  have hbn₄ : ∃ w, out.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn' := by
    obtain ⟨w, hw, hdw⟩ := hbn'
    exact ⟨w, by rw [f₄ tag 3 (t + 1) (by omega) (by omega)]; exact hw, hdw⟩
  refine ⟨out, uv, wv, zv, z', hv, an, bn', nn, vn,
    exec_stepBody_eq I tag N t mv orth hmv.composable horth.composable hr₁ hr₂ hr₃ hr₄,
    hs.succ hpreFrame (sh₄.trans (shn.trans sh₁)) fall hv₄
      (by rw [fafter tag 2 t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact ha₁)
      hbn₄ hp₄
      (by rw [fafter tag 6 t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hn₁),
    fall tag 4 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), e₁, e₂, e₃, e₄, hnn, e₅, eorth, e₆, e₇, hunit, hvzero⟩

end LanczosReorthImplementation

end NLAlib
