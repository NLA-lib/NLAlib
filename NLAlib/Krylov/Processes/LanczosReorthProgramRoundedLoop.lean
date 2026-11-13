/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramRoundedStep
public import NLAlib.Matrix.Computation.OrthRoutine

/-!
# The rounded loop of Lanczos with full reorthogonalization as a program

The rounded run of `NLAlib.lanczosReorthLoop` for any product routine certified by
`NLAlib.Computation.IsMatvecRoutine` and any orthogonalization routine family: the
initialization (the zero literals, the input norm and the guarded first column), the loop of
steps by the invariant `NLAlib.LanczosReorthImplementation.StoreContext`, and the scoped run with
its allocations and releases. For routines certified by `NLAlib.Computation.IsOrthRoutine`, the
decoded outputs satisfy `NLAlib.LanczosReorthOutputs`: every admissible prefix is a
`NLAlib.LanczosReorthRun`.

## Main definitions

* `NLAlib.LanczosReorthImplementation.initPhase`: the initialization at the run-time handles.
* `NLAlib.LanczosReorthImplementation.RoundedSteps`: the local guarantees of the first steps.

## Main results

* `NLAlib.LanczosReorthImplementation.exec_initPhase`: the initialization.
* `NLAlib.LanczosReorthImplementation.exec_loop`: the loop of steps.
* `NLAlib.LanczosReorthImplementation.exec_lanczosReorthLoop`: the scoped run for a generic
  orthogonalization guarantee.
* `NLAlib.LanczosReorthImplementation.exec_rounded_loop`: the rounded run of the loop for
  certified routines.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- The initialization of `NLAlib.lanczosReorthLoop` at the run-time handles: the zero scalar,
$\beta_0 = 0$, the zero previous vector, the input norm and the guarded normalization of
$\mathbf{b}$ into the first column. -/
def initPhase (tag : P) (N : ℕ) : Builder P ι ℕ ℕ Unit := do
  ins (.lit tag ⟨9, 0⟩ 0)
  ins (.lit tag ⟨3, 0⟩ 0)
  forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
  nrm2 tag ⟨4, 0⟩ 0 0 (IExp.const N)
  ifThenElse tag .eq ⟨4, 0⟩ ⟨9, 0⟩
    (forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
    (do copyv tag 0 0 1 0 (IExp.const N); rscl tag ⟨4, 0⟩ 1 0 (IExp.const N))

/-- The local guarantees `NLAlib.LanczosReorthImplementation.RoundedStep` of the first $t$ steps
of a rounded run with sequences $\mathbf{v}$, $\alpha$, $\beta$, $\nu$ and orthogonalization
guarantees `G`. The witnesses come before the bound on $j$, so that they can be chosen as
functions of $j$. -/
def RoundedSteps {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ)
    (G : (t : ℕ) → Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) →
      (Fin N → ℝ) → Prop)
    (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ j, ∃ (uv wv zv z' : Fin N → ℝ) (hv : ℕ → ℝ), j < t →
    RoundedStep A ε (G j) (LanczosReorthRun.basisOf v (j + 1)) (v j) (v (j + 1)) (v (j + 2))
      (β j) (α (j + 1)) (ν (j + 1)) (β (j + 1)) uv wv zv z' (fun i : Fin (j + 1) => hv i)

/-! ### The initialization -/

/-- The computed first column is close to the normalized input: if
$\|\mathbf{b} - s\mathbf{v}_1\| \le u'\|\mathbf{b}\|$,
$\lvert \|\mathbf{b}\| - s \rvert \le \gamma\|\mathbf{b}\|$ and
$\lvert \|\mathbf{v}_1\|^2 - 1 \rvert \le \varepsilon$ with $u', \gamma \le \varepsilon \le 1/100$,
then $\|\mathbf{b}/\|\mathbf{b}\| - \mathbf{v}_1\| \le 3\varepsilon$ for
$\mathbf{b} \ne \mathbf{0}$. -/
private theorem norm_inv_norm_smul_sub_le {N : ℕ} (b v1 : Fin N → ℝ) {s uu γ ε : ℝ}
    (hb : b ≠ 0) (hres : ‖WithLp.toLp 2 (b - s • v1)‖ ≤ uu * ‖WithLp.toLp 2 b‖)
    (herr : |‖WithLp.toLp 2 b‖ - s| ≤ γ * ‖WithLp.toLp 2 b‖)
    (hunit : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ ε) (hu : uu ≤ ε) (hγ : γ ≤ ε)
    (hε : ε ≤ 1 / 100) :
    ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v1)‖ ≤ 3 * ε := by
  have hnb : 0 < ‖WithLp.toLp 2 b‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hb (by simpa using congrArg WithLp.ofLp h0)
  set nb := ‖WithLp.toLp 2 b‖ with hnbdef
  have hv : ‖WithLp.toLp 2 v1‖ ≤ 2 := by
    have h1 : ‖WithLp.toLp 2 v1‖ ^ 2 ≤ 4 := by
      have := (abs_le.mp hunit).2
      linarith
    nlinarith [norm_nonneg (WithLp.toLp 2 v1)]
  have heq : WithLp.toLp 2 (nb⁻¹ • b - v1) = nb⁻¹ • WithLp.toLp 2 (b - s • v1) +
      (nb⁻¹ * (s - nb)) • WithLp.toLp 2 v1 := by
    ext i
    simp only [WithLp.toLp_sub, WithLp.toLp_smul, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply]
    field_simp
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hnb,
    abs_mul, abs_inv, abs_of_pos hnb]
  have h1 : nb⁻¹ * ‖WithLp.toLp 2 (b - s • v1)‖ ≤ uu := by
    rw [inv_mul_le_iff₀ hnb]; linarith
  have h2 : nb⁻¹ * |s - nb| ≤ γ := by
    rw [inv_mul_le_iff₀ hnb, abs_sub_comm]; linarith
  have h20 : 0 ≤ nb⁻¹ * |s - nb| := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 v1)]

/-- The zero literals of the initialization: the zero scalar, $\beta_0$ and the previous
vector. -/
private theorem exec_init_zeros (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P) {N q slot : ℕ}
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot) :
    ∃ (out : St P K (OpCount P ι)) (zero : K),
      exec I (do
        ins (.lit tag ⟨9, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) :
          Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 3 → k ≠ 5 → k ≠ 9 → out.store.read p k i = st.store.read p k i) ∧
      out.store.read tag 9 0 = some zero ∧ out.store.read tag 3 0 = some zero ∧
      (∀ i : Fin N, out.store.read tag 5 i = some zero) ∧ dec tag zero = 0 := by
  obtain ⟨zero, hzl, hd⟩ := (hsem.isArithErrSem (fun _ => trivial)).lit_zero tag
  obtain ⟨s0, _, e0, sh0, r0, f0⟩ := exec_scalar_lit I tag st ⟨9, 0⟩ 0 zero hzl
    ⟨2, by rw [hshape]; rfl, by norm_num⟩
  let st1 := { st with store := s0, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s1, _, e1, sh1, r1, f1⟩ := exec_scalar_lit I tag st1 ⟨3, 0⟩ 0 zero hzl
    ⟨q + 1, by change s0.shape[3]? = _; rw [sh0, hshape]; rfl,
      by simp only [IExp.eval_ofNat]; omega⟩
  let st2 := { st1 with store := s1, cnt := st1.cnt + I.charge (.lit tag) }
  obtain ⟨s2, e2, sh2, r2, f2⟩ := exec_forRange_literal_zero_var I tag zero hzl st2
    (.const N) 5 (fun i hi => ⟨N, by change s1.shape[5]? = _; rw [sh1, sh0, hshape]; rfl, hi⟩)
  refine ⟨{ st2 with store := s2, cnt := st2.cnt + N • I.charge (.lit tag) }, zero, ?_,
    sh2.trans (sh1.trans sh0), fun p k i h3 h5 h9 => ?_, ?_, ?_, fun i => r2 i i.isLt, hd⟩
  · rw [exec_run_bind I (b := ins (.lit tag ⟨9, 0⟩ 0)) (fun _ => rfl), e0, Option.bind_some,
      exec_run_bind I (b := ins (.lit tag ⟨3, 0⟩ 0)) (fun _ => rfl), e1, Option.bind_some]
    exact e2
  · change s2.read p k i = _
    rw [f2 p k i (Or.inr (Or.inl h5)), f1 p k i (Or.inr (Or.inl h3)),
      f0 p k i (Or.inr (Or.inl h9))]
  · change s2.read tag 9 0 = _
    rw [f2 tag 9 0 (Or.inr (Or.inl (by norm_num))), f1 tag 9 0 (Or.inr (Or.inl (by norm_num)))]
    exact r0
  · change s2.read tag 3 0 = _
    rw [f2 tag 3 0 (Or.inr (Or.inl (by norm_num)))]
    exact r1

/-- `NLAlib.LanczosReorthImplementation.exec_initPhase` under unit charges. -/
private theorem exec_initPhase_of_charge (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P) {N q slot : ℕ} (b : Fin N → ℝ)
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v1 : Fin N → ℝ) (zero : K) (w' : K),
      exec I (initPhase tag N).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 1 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 9 →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 i = some w ∧ dec tag w = v1 i) ∧
      out.store.read tag 3 0 = some zero ∧ (∀ i : Fin N, out.store.read tag 5 i = some zero) ∧
      out.store.read tag 9 0 = some zero ∧ dec tag zero = 0 ∧ out.store.read tag 4 0 = some w' ∧
      |‖WithLp.toLp 2 b‖ - dec tag w'| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (dec tag w' = 0 ↔ b = 0) ∧ (b = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - dec tag w' • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ := by
  have hu := hsem.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  obtain ⟨predot, zero, e012, shp, fp, rz, rb3, rp5, hd⟩ := exec_init_zeros I hsem tag st hshape
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hx (i : ℕ) (hi : i < N) :
      ∃ w, predot.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    rw [zero_add, fp tag 0 i (by omega) (by omega) (by omega)]
    simpa only [xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨scratch, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zero
    (show predot.store.shape[4]? = some (tag, 1) by rw [shp, hshape]; rfl) (by norm_num)
  obtain ⟨normed, w, en, hw, _, _, _⟩ :=
    hsem.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz predot ⟨4, 0⟩ 0 0 (.const N) xs
      hwin.1 hwin.2.2.1 hx (by norm_num) ⟨zero, scratch, hs⟩
  have shn : normed.store.shape = predot.store.shape := Store.shape_of_write_eq_some hw
  have fn : ∀ p k i, (k ≠ 4 ∨ i ≠ 0) → normed.store.read p k i = predot.store.read p k i :=
    fun p k i hk => Store.read_of_write_eq_some_of_ne hw hk
  have hNN : N ≤ N * (q + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.succ_le_succ (Nat.zero_le q))
  obtain ⟨out, w', W, eg, shape, _, rnorm, -, herr, hiff, hW, frame, hzv, hunit,
      hres, -⟩ := hsem.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed normed ⟨4, 0⟩ ⟨9, 0⟩ 0 1 0 0 (.const N) xs hwin.1 hwin.2.2.1 hx
      (fun i hi => by
        change ∃ w, normed.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i
        rw [fn tag 0 (0 + i) (Or.inl (by norm_num))]
        exact hx i hi)
      (by norm_num) (by norm_num) (by norm_num) ⟨zero, scratch, hs⟩
      (fun i hi => ⟨N * (q + 1), by rw [shn, shp, hshape]; rfl,
        by simpa only [IExp.eval_zero, zero_add] using hi.trans_le hNN⟩) en rfl
      ⟨zero, (fn tag 9 0 (Or.inl (by norm_num))).trans rz, hd⟩
  have hxs : (fun i : Fin N => xs i) = b := by funext i; simp only [xs, dif_pos i.isLt]
  change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - dec tag w'| ≤
    roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
  change dec tag w' = 0 ↔ (fun i : Fin N => xs i) = 0 at hiff
  change ‖WithLp.toLp 2 ((fun i : Fin N => xs i) - dec tag w' •
    (fun i : Fin N => dec tag (W i)))‖ ≤
      u tag * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
  rw [hxs] at herr hiff hres
  have fo (p : P) (k i : ℕ) (h1 : k ≠ 1) (h4 : k ≠ 4) :
      out.store.read p k i = predot.store.read p k i :=
    (frame p k i (Or.inl h1)).trans (fn p k i (Or.inl h4))
  refine ⟨out, fun i => dec tag (W i), zero, w', ?_, shape.trans (shn.trans shp),
    fun p k i h1 h3 h4 h5 h9 => (fo p k i h1 h4).trans (fp p k i h3 h5 h9),
    fun i => ⟨W i, by simpa only [IExp.eval_zero, zero_add] using hW i, rfl⟩,
    by rw [fo tag 3 0 (by norm_num) (by norm_num)]; exact rb3,
    fun i => by rw [fo tag 5 i (by norm_num) (by norm_num)]; exact rp5 i,
    by rw [fo tag 9 0 (by norm_num) (by norm_num)]; exact rz, hd, rnorm, herr, hiff,
    fun hb0 => hzv (hiff.mpr hb0), fun hbne => (hunit (fun he => hbne (hiff.mp he))).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall), hres⟩
  have hcomp : ExecutionComposable I (do
      ins (.lit tag ⟨9, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) : Builder P ι ℕ ℕ Unit) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl)))
  change exec I ((do
      ins (.lit tag ⟨9, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) :
        Builder P ι ℕ ℕ Unit) >>= fun _ => _).run st = _
  rw [hcomp, e012, Option.bind_some, exec_run_bind I
    (b := nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) (fun _ => rfl), en, Option.bind_some]
  exact (exec_normalize_branch_var_eq I tag normed (.const N) 0 1 0 ⟨4, 0⟩ ⟨9, 0⟩).trans eg

/-- The initialization (`NLAlib.LanczosReorthImplementation.initPhase`) under the relative-error
model with accuracy $\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$, any charge: from
a store of the workspace shape holding $\mathbf{b}$, it succeeds, writes the first column
$\mathbf{v}_1$, $\beta_0 = 0$, the zero previous vector, the zero scalar and the input norm $s$
with $\lvert \|\mathbf{b}\| - s \rvert \le \varepsilon\|\mathbf{b}\|$; for $\mathbf{b} \ne
\mathbf{0}$, $\lvert \|\mathbf{v}_1\|^2 - 1 \rvert \le \varepsilon$ and
$\|\mathbf{b}/\|\mathbf{b}\| - \mathbf{v}_1\| \le 3\varepsilon$, and $\mathbf{v}_1 = \mathbf{0}$
for $\mathbf{b} = \mathbf{0}$. -/
theorem exec_initPhase (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q slot : ℕ} (b : Fin N → ℝ)
    (st : St P K (OpCount P ι)) (hshape : st.store.shape = workspaceShape tag N q slot)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v1 : Fin N → ℝ),
      exec I (initPhase tag N).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 1 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 9 →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 i = some w ∧ dec tag w = v1 i) ∧
      (∃ w, out.store.read tag 3 0 = some w ∧ dec tag w = 0) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = 0) ∧
      (∃ w, out.store.read tag 9 0 = some w ∧ dec tag w = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      (b ≠ 0 → ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v1)‖ ≤
        3 * lanczosImplementationRoundoffBound N (u tag)) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ |‖WithLp.toLp 2 b‖ - dec tag w| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 b‖) ∧
      (b = 0 → v1 = 0) := by
  have hu := hsem.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  have hγ := roundingFactor_succ_le_lanczosImplementationRoundoffBound N hu hsmall
  obtain ⟨out, v1, zero, w', hr, sh, fr, hv1, r3, r5, r9, hd, r4, herr, -, hb0, hunit, hres⟩ :=
    exec_initPhase_of_charge { I with charge := fun k => Finsupp.single k 1 } hsem hz
      (fun _ => rfl) tag b st hshape hb hsmall
  obtain ⟨c₁, hr'⟩ := exists_exec_withCharge_eq_some _ I.charge _ hr st.cnt
  exact ⟨{ out with cnt := c₁ }, v1, hr', sh, fr, hv1, ⟨zero, r3, hd⟩, fun i => ⟨zero, r5 i, hd⟩,
    ⟨zero, r9, hd⟩, hunit, fun hbne => norm_inv_norm_smul_sub_le b v1 hbne hres herr
      (hunit hbne) hwin.2.2.2.2 hγ hsmall,
    ⟨w', r4, herr.trans (mul_le_mul_of_nonneg_right hγ (norm_nonneg _))⟩, hb0⟩

/-! ### The loop -/

/-- The guarantees of the first $t$ steps, with the sequences updated by step $t$ and its
guarantee, are the guarantees of the first $t + 1$ steps. -/
theorem RoundedSteps.update {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ε : ℝ}
    {G : (t : ℕ) → Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) →
      (Fin N → ℝ) → Prop}
    {v : ℕ → Fin N → ℝ} {α β ν : ℕ → ℝ} {t : ℕ} (hpf : RoundedSteps A ε G v α β ν t)
    {uv wv zv z' vn : Fin N → ℝ} {hv : Fin (t + 1) → ℝ} {an bn nn : ℝ}
    (hstep : RoundedStep A ε (G t) (LanczosReorthRun.basisOf v (t + 1)) (v t) (v (t + 1)) vn
      (β t) an nn bn uv wv zv z' hv) :
    RoundedSteps A ε G (Function.update v (t + 2) vn) (Function.update α (t + 1) an)
      (Function.update β (t + 1) bn) (Function.update ν (t + 1) nn) (t + 1) := by
  have ev : ∀ k, k < t + 2 → Function.update v (t + 2) vn k = v k :=
    fun k hk => Function.update_of_ne (by omega) _ _
  have ea : ∀ k, k < t + 1 → Function.update α (t + 1) an k = α k :=
    fun k hk => Function.update_of_ne (by omega) _ _
  have eb : ∀ k, k < t + 1 → Function.update β (t + 1) bn k = β k :=
    fun k hk => Function.update_of_ne (by omega) _ _
  have en : ∀ k, k < t + 1 → Function.update ν (t + 1) nn k = ν k :=
    fun k hk => Function.update_of_ne (by omega) _ _
  have hbasis : ∀ k, k ≤ t + 1 → LanczosReorthRun.basisOf (Function.update v (t + 2) vn) k =
      LanczosReorthRun.basisOf v k := by
    intro k hk
    ext i c
    simp only [LanczosReorthRun.basisOf, Matrix.of_apply]
    rw [ev _ (by omega)]
  intro j
  rcases (show j < t ∨ j = t ∨ t < j by omega) with hjt | rfl | hjt
  · obtain ⟨uv', wv', zv', z'', hv', hf⟩ := hpf j
    refine ⟨uv', wv', zv', z'', hv', fun _ => ?_⟩
    rw [ev j (by omega), ev (j + 1) (by omega), ev (j + 2) (by omega), ea (j + 1) (by omega),
      eb j (by omega), eb (j + 1) (by omega), en (j + 1) (by omega), hbasis (j + 1) (by omega)]
    exact hf hjt
  · refine ⟨uv, wv, zv, z', fun i => if hi : i < j + 1 then hv ⟨i, hi⟩ else 0, fun _ => ?_⟩
    have hhv : (fun i : Fin (j + 1) =>
        (fun i => if hi : i < j + 1 then hv ⟨i, hi⟩ else 0) (i : ℕ)) = hv := by
      funext i
      exact dif_pos i.isLt
    rw [ev j (by omega), ev (j + 1) (by omega), eb j (by omega), hbasis (j + 1) le_rfl, hhv]
    simpa only [Function.update_self] using hstep
  · exact ⟨0, 0, 0, 0, 0, fun hj => absurd hj (by omega)⟩

/-- The loop of $q$ steps of the reorthogonalized program at the run-time handles, under the
relative-error model with accuracy $\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`,
that is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$, product
routines certified with coefficient $\varepsilon\|\mathbf{A}\|_2$ and certified orthogonalization
calls with guarantees `G`: from the decoded store after no step, every step executes, the final
store is the decoded store after $q$ steps of sequences that keep $\mathbf{v}_0$, $\mathbf{v}_1$
and $\beta_0$, the input norm is kept and every step meets its guarantees. -/
theorem exec_loop (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q slot : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (b : Fin N → ℝ)
    (pre : Store P K → Prop)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (G : (t : ℕ) → Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) →
      (Fin N → ℝ) → Prop)
    (horth : ∀ t < q, IsOrthCall I dec tag N q slot t (G t) (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι)) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ)
    (hs : StoreContext tag dec N q slot b pre 0 v α β ν st.store)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v' : ℕ → Fin N → ℝ) (α' β' ν' : ℕ → ℝ),
      exec I (forRange (IExp.const q) fun j => stepBody tag N j mv orth).run st = some out ∧
      StoreContext tag dec N q slot b pre q v' α' β' ν' out.store ∧
      out.store.read tag 4 0 = st.store.read tag 4 0 ∧
      v' 0 = v 0 ∧ v' 1 = v 1 ∧ β' 0 = β 0 ∧
      RoundedSteps A (lanczosImplementationRoundoffBound N (u tag)) G v' α' β' ν' q := by
  obtain ⟨out, hr, hinv⟩ := exists_exec_loop_eq_some_of_forall I (n := IExp.const q)
    (body := fun j => (stepBody tag N j mv orth).run)
    (fun t s => ∃ (v' : ℕ → Fin N → ℝ) (α' β' ν' : ℕ → ℝ),
      StoreContext tag dec N q slot b pre t v' α' β' ν' s.store ∧
      s.store.read tag 4 0 = st.store.read tag 4 0 ∧ v' 0 = v 0 ∧ v' 1 = v 1 ∧ β' 0 = β 0 ∧
      RoundedSteps A (lanczosImplementationRoundoffBound N (u tag)) G v' α' β' ν' t)
    ⟨v, α, β, ν, hs, rfl, rfl, rfl, rfl, fun j => ⟨0, 0, 0, 0, 0, fun hj => absurd hj (by omega)⟩⟩
    (by
      rintro t ht s ⟨v', α', β', ν', hs', h4, hv0, hv1, hb0, hpf⟩
      have htq : t < q := by simpa using ht
      obtain ⟨out, uv, wv, zv, z', hv, an, bn, nn, vn, hr, hso, h4o, hstep⟩ :=
        exec_stepBody I h hz tag b pre hpreFrame mv (hmv t) orth (G t) (horth t htq) s v' α' β'
          ν' hs' htq hsmall
      exact ⟨out, hr, _, _, _, _, hso, h4o.trans h4,
        by rw [Function.update_of_ne (by omega), hv0],
        by rw [Function.update_of_ne (by omega), hv1],
        by rw [Function.update_of_ne (by omega), hb0], hpf.update hstep⟩)
  obtain ⟨v', α', β', ν', hso, h4, hv0, hv1, hb0, hpf⟩ := hinv
  refine ⟨out, v', α', β', ν', ?_, hso, h4, hv0, hv1, hb0, hpf⟩
  change exec I (.seq (.loop (IExp.const q) _) .skip) st = _
  rw [exec_seq_skip]
  exact hr

/-! ### The scoped run -/

/-- The run of the scoped program `NLAlib.lanczosReorthLoop` is the run of its initialization and
its loop between the three allocations and releases. -/
private theorem exec_lanczosReorthLoop_eq (I : Interp P ι K (OpCount P ι)) (tag : P) (N q : ℕ)
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    {st init out₃ : St P K (OpCount P ι)} (hsize : st.store.size = 8)
    (hi : exec I (initPhase tag N).run (((st.allocate tag (IExp.const N).eval
      (I.width tag)).allocate tag (2 : IExp ℕ).eval (I.width tag)).allocate tag
        (IExp.const q + 1).eval (I.width tag)) = some init)
    (hl : exec I (forRange (IExp.const q) fun j => stepBody tag N j mv orth).run init =
      some out₃) :
    exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run st =
      some (((out₃.release tag (IExp.const q + 1).eval (I.width tag)).release tag
        (2 : IExp ℕ).eval (I.width tag)).release tag (IExp.const N).eval (I.width tag)) := by
  have hinit : ExecutionComposable I (initPhase tag N) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            (executionComposable_single I (fun _ => rfl)))))
  have hbody := hinit (fun _ => forRange (IExp.const q) fun j => stepBody tag N j mv orth)
    (((st.allocate tag (IExp.const N).eval (I.width tag)).allocate tag (2 : IExp ℕ).eval
      (I.width tag)).allocate tag (IExp.const q + 1).eval (I.width tag))
  rw [hi, Option.bind_some, hl] at hbody
  change exec I (.seq (.alloc tag (IExp.const N) _) .skip) st = _
  rw [exec_seq_skip]
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  have hs₁ : (st.allocate tag (IExp.const N).eval (I.width tag)).store.size = 9 := by
    simp [St.allocate, hsize]
  have hs₂ : ((st.allocate tag (IExp.const N).eval (I.width tag)).allocate tag
      (2 : IExp ℕ).eval (I.width tag)).store.size = 10 := by
    simp [St.allocate, hsize]
  rw [hsize, hs₁, hs₂]
  exact hbody

/-- The scoped run of `NLAlib.lanczosReorthLoop` for a generic orthogonalization guarantee `G`,
under the relative-error model with accuracy $\varepsilon$ =
`NLAlib.lanczosImplementationRoundoffBound`, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$, product routines
certified with coefficient $\varepsilon\|\mathbf{A}\|_2$ (precondition `pre`, kept by the frame
of the matrix slot) and certified orthogonalization calls: from a store with the seven declared
buffers and the matrix slot holding $\mathbf{b}$, the three scoped allocations, the
initialization and every step execute; after the release the declared buffers hold the decoded
basis, coefficients, stored norms and previous vector, the input norm meets its bound,
$\mathbf{v}_1$ is close to $\mathbf{b}/\|\mathbf{b}\|$ for $\mathbf{b} \ne \mathbf{0}$, and every
step meets its local guarantees. -/
theorem exec_lanczosReorthLoop {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (G : (t : ℕ) → Matrix (Fin N) (Fin (t + 1)) ℝ → (Fin N → ℝ) → (Fin (t + 1) → ℝ) →
      (Fin N → ℝ) → Prop)
    (horth : ∀ t < q, IsOrthCall I dec tag N q slot t (G t) (orth 8 10 (IExp.var t)))
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = b i) ∧
      (∀ c ≤ q, ∀ i : Fin N, ∃ w, out.store.read tag 1 (N * c + i) = some w ∧
        dec tag w = v (c + 1) i) ∧
      (∀ c < q, ∃ w, out.store.read tag 2 c = some w ∧ dec tag w = α (c + 1)) ∧
      (∀ c ≤ q, ∃ w, out.store.read tag 3 c = some w ∧ dec tag w = β c) ∧
      (∀ c < q, ∃ w, out.store.read tag 6 c = some w ∧ dec tag w = ν (c + 1)) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = v q i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ |‖WithLp.toLp 2 b‖ - dec tag w| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 b‖) ∧
      v 0 = 0 ∧ β 0 = 0 ∧
      (b ≠ 0 → |‖WithLp.toLp 2 (v 1)‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      (b ≠ 0 → ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v 1)‖ ≤
        3 * lanczosImplementationRoundoffBound N (u tag)) ∧
      (b = 0 → v 1 = 0) ∧
      RoundedSteps A (lanczosImplementationRoundoffBound N (u tag)) G v α β ν q := by
  classical
  have hsize : st.store.size = 8 := by simpa [Store.shape] using congrArg Array.size hshape
  let st₃ : St P K (OpCount P ι) :=
    ((st.allocate tag (IExp.const N).eval (I.width tag)).allocate tag (2 : IExp ℕ).eval
      (I.width tag)).allocate tag (IExp.const q + 1).eval (I.width tag)
  have sh₃ : st₃.store.shape = workspaceShape tag N q slot := by
    simp only [st₃, St.shape_allocate, hshape, IExp.eval_const, IExp.eval_ofNat, IExp.eval_add]
    rfl
  have rd₃ : ∀ p k i, k < 8 → st₃.store.read p k i = st.store.read p k i := by
    intro p k i hk
    simp only [st₃]
    rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by simp [St.allocate, hsize]; omega),
      St.read_allocate_of_lt _ _ _ _ _ _ _ (by simp [St.allocate, hsize]; omega),
      St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]
  have hb₃ (i : Fin N) : ∃ w, st₃.store.read tag 0 i = some w ∧ dec tag w = b i := by
    rw [rd₃ tag 0 i (by omega)]
    exact hb i
  obtain ⟨init, v1, hri, shi, fi, hv1, hβ0, hp0, hz0, hunit1, hdir, h41, hb01⟩ :=
    exec_initPhase I hsem hz tag b st₃ sh₃ hb₃ hsmall
  have fi' (k i : ℕ) (hk : k = 0 ∨ k = 7) : init.store.read tag k i = st.store.read tag k i := by
    rw [fi tag k i (by omega) (by omega) (by omega) (by omega) (by omega), rd₃ tag k i (by omega)]
  obtain ⟨out₃, v, α, β, ν, hrl, hsl, h4l, hv0, hv1l, hb0, hpf⟩ :=
    exec_loop I hsem hz tag b pre hpreFrame mv hmv orth G horth init (Function.update 0 1 v1) 0
      0 0 ⟨shi.trans sh₃, hpreFrame st.store init.store hpre
        (fun k hk => by rw [shi, sh₃, hshape]; interval_cases k <;> rfl)
        (fun i => fi' 7 i (by omega)), fun i => by rw [fi' 0 i (by omega)]; exact hb i,
        fun c hc i => by obtain rfl : c = 0 := by omega
                         simpa using hv1 i,
        fun c hc => absurd hc (by omega),
        fun c hc => by obtain rfl : c = 0 := by omega
                       simpa using hβ0,
        fun i => by simpa using hp0 i, fun c hc => absurd hc (by omega), hz0⟩ hsmall
  have hsize₃ : out₃.store.size = 11 := by
    simpa [Store.shape, workspaceShape] using congrArg Array.size hsl.shape
  let out : St P K (OpCount P ι) :=
    ((out₃.release tag (IExp.const q + 1).eval (I.width tag)).release tag (2 : IExp ℕ).eval
      (I.width tag)).release tag (IExp.const N).eval (I.width tag)
  have rdo : ∀ p k i, k < 8 → out.store.read p k i = out₃.store.read p k i := by
    intro p k i hk
    change Store.read out₃.store.pop.pop.pop p k i = _
    rw [Store.read_pop_of_lt (by simp only [Array.size_pop, hsize₃]; omega),
      Store.read_pop_of_lt (by simp only [Array.size_pop, hsize₃]; omega),
      Store.read_pop_of_lt (by rw [hsize₃]; omega)]
  simp only [Function.update_self] at hv1l
  refine ⟨out, v, α, β, ν, exec_lanczosReorthLoop_eq I tag N q mv orth hsize hri hrl, ?_,
    fun i => by rw [rdo tag 0 _ (by omega)]; exact hsl.input i,
    fun c hc i => by rw [rdo tag 1 _ (by omega)]; exact hsl.basis c hc i,
    fun c hc => by rw [rdo tag 2 _ (by omega)]; exact hsl.alpha c hc,
    fun c hc => by rw [rdo tag 3 _ (by omega)]; exact hsl.beta c hc,
    fun c hc => by rw [rdo tag 6 _ (by omega)]; exact hsl.nu c hc,
    fun i => by rw [rdo tag 5 _ (by omega)]; exact hsl.prev i,
    by rw [rdo tag 4 _ (by omega), h4l]; exact h41, by simpa using hv0, by simpa using hb0,
    by rw [hv1l]; exact hunit1, by rw [hv1l]; exact hdir, by rw [hv1l]; exact hb01, hpf⟩
  change Store.shape out₃.store.pop.pop.pop = _
  rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hsl.shape, hshape]
  rfl

/-! ### Certified routines -/

/-- The rounded run of the generic loop: under the relative-error model with exact addition of
zero, for symmetric $\mathbf{A}$, product routines certified by
`NLAlib.Computation.IsMatvecRoutine` with coefficient $\varepsilon\|\mathbf{A}\|_2$, where
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$, is at most $1/100$, and
orthogonalization calls certified by `NLAlib.Computation.IsOrthRoutine` at
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$, $\varepsilon_i \ge 0$, at the executed
steps $t < q$, the loop `NLAlib.lanczosReorthLoop` succeeds from a state with the seven declared
buffers holding $\mathbf{b}$ and a matrix slot $7$, keeps the shape, and for
$\mathbf{b} \ne \mathbf{0}$ its outputs satisfy `NLAlib.LanczosReorthOutputs` for every
$\tau > 0$. The scheme enters only through its certificate. No printed source;
`docs/design/Krylov-LanczosReorth.md` §1.4. -/
theorem exec_rounded_loop {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (hε : 0 ≤ ε₁ ∧ 0 ≤ ε₂ ∧ 0 ≤ ε₃)
    (horth : ∀ t < q, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (hA : Aᵀ = A) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      (b ≠ 0 → LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ ε₁ ε₂ ε₃) := by
  classical
  have hε0 := lanczosImplementationRoundoffBound_nonneg N (hsem.nonneg (p := tag) trivial)
  obtain ⟨out, v, α, β, ν, hrun, shout, hbl, hVl, hαl, hβl, hνl, -, -, hv0, hb0, hunit1, hdir,
      -, hpf⟩ := exec_lanczosReorthLoop I tag hsem hz st N q slot A b hshape hb pre hpre
    hpreFrame mv hmv orth (fun _ V w h w' => IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (fun t ht => ⟨(horth t ht).composable, fun s V w hs hV hw => (horth t ht).run s V w trivial
      hV (by simpa using hw) (fun i hi => ⟨N, by simp [hs, workspaceShape], by simpa using hi⟩)
      (fun i hi => ⟨q + 1, by simp [hs, workspaceShape], by simp; omega⟩)
      (by omega) (by omega) (by omega)⟩) hsmall
  refine ⟨out, hrun, shout, fun hbne => ?_⟩
  choose U W Z Z' Hh hpf' using hpf
  refine ⟨v, α, β, ν, fun i j => ?_, fun i j => ?_, fun j c => ?_, fun j c => ?_,
    fun j c => ?_, hdir hbne, fun m hm0 hmq hadm => ?_⟩
  · rw [show 0 + (i : ℕ) + N * j = i by rw [Fin.val_eq_zero j]; ring]
    exact hbl i
  · rw [show 0 + (i : ℕ) + N * j = N * j + i by ring]
    exact hVl j (by omega) i
  · rw [show 0 + (j : ℕ) + q * c = j by rw [Fin.val_eq_zero c]; ring]
    exact hαl j j.isLt
  · rw [show 0 + (j : ℕ) + (q + 1) * c = j by rw [Fin.val_eq_zero c]; ring]
    exact hβl j (by omega)
  · rw [show 0 + (j : ℕ) + q * c = j by rw [Fin.val_eq_zero c]; ring]
    exact hνl j j.isLt
  have nsr : ∀ x y : Fin N → ℝ, ‖WithLp.toLp 2 (x - y)‖ = ‖WithLp.toLp 2 (y - x)‖ :=
    fun x y => by rw [WithLp.toLp_sub, WithLp.toLp_sub, norm_sub_rev]
  refine ⟨{
    H := A
    v := v
    u := fun n => U (n - 1)
    w := fun n => W (n - 1)
    z := fun n => Z (n - 1)
    z' := fun n => Z' (n - 1)
    α := α
    β := β
    ν := ν
    h := fun n => Hh (n - 1)
    eu := fun n => U (n - 1) - A *ᵥ v n
    ew := fun n => W (n - 1) - (U (n - 1) - β (n - 1) • v (n - 1))
    ez := fun n => Z (n - 1) - (W (n - 1) - α n • v n)
    eα := fun n => α n - v n ⬝ᵥ W (n - 1)
    δ := fun n => β n • v (n + 1) - Z' (n - 1)
    ε := lanczosImplementationRoundoffBound N (u tag)
    τ := τ
    η₀ := η₀
    ε₁ := ε₁
    ε₂ := ε₂
    ε₃ := ε₃
    transpose_H := hA
    ε_nonneg := hε0
    ε_le := hsmall
    ε₁_nonneg := hε.1
    ε₂_nonneg := hε.2.1
    ε₃_nonneg := hε.2.2
    k_pos := hm0
    v_zero := hv0
    β_zero := hb0
    u_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_eu_le := fun j hj => (nsr _ _).trans_le (hpf' j (by omega)).norm_mulVec_sub_le
    w_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_ew_le := fun j hj => (nsr _ _).trans_le (hpf' j (by omega)).norm_sub_smul_sub_le
    α_eq := fun j _ => (add_sub_cancel _ _).symm
    abs_eα_le := fun j hj => (abs_sub_comm _ _).trans_le (hpf' j (by omega)).abs_dotProduct_sub_le
    z_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_ez_le := fun j hj => (nsr _ _).trans_le (hpf' j (by omega)).norm_projection_sub_le
    abs_ν_sub_le := fun j hj => (hpf' j (by omega)).abs_nu_sub_le
    orth_eq := fun j hj => (hpf' j (by omega)).orth
    abs_β_sub_le := fun j hj => (hpf' j (by omega)).abs_beta_sub_le
    smul_v_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_δ_le := fun j hj => (nsr _ _).trans_le (hpf' j (by omega)).norm_sub_smul_le
    abs_norm_v_sq_sub_one_le := fun j hj1 hj2 => by
      rcases Nat.lt_or_ge j 2 with hj | hj
      · obtain rfl : j = 1 := by omega
        exact hunit1 hbne
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
        have hf := hpf' i (by omega)
        exact hf.abs_norm_sq_sub_one_le (ne_of_gt (lt_of_le_of_lt
          (mul_nonneg hτ.le hf.nu_nonneg) (hadm i (by omega))))
    admissible := hadm
    τ_pos := hτ }, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

end LanczosReorthImplementation

end NLAlib
