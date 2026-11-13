/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.IEEE
public import NLAlib.Computation.BLAS.Underflow
public import NLAlib.Computation.VectorErrors
public import NLAlib.Krylov.LinearSystems.CGProgramBody
public import NLAlib.Krylov.LinearSystems.CGProgramUnderflowKernels
public import NLAlib.Krylov.LinearSystems.CGOracleProgramTree

/-!
# Range-certified binary64 CG curvature prefixes

The product and curvature dot below are the actual active-step prefix of the registered
oracle CG tree. An input-domain matvec certificate supplies success and a mixed normwise
error. An input-only scalar range bound then certifies every product and accumulation of
the actual binary64 curvature dot, including gradual underflow. The persistent CG state
is preserved. A positive curvature margin also certifies the actual guard and step-length
division. Vector updates and whole-run success require further invariants.

## Main results

* `NLAlib.CGOracleImplementation.toStmt_cgOracleProg_compiled_eq_guarded_loop`:
  the registered loop contains the certified blocks in their actual control-flow order.
* `NLAlib.CGOracleImplementation.exec_product_of_isMatvecErrOn`: actual stored oracle call.
* `NLAlib.CGOracleImplementation.exec_curvature_of_sem_eq_finiteFloatSem`: the actual
  binary64 prefix and guarded step-length division with input-only range certificates.
* `NLAlib.CGOracleImplementation.exec_curvature_of_finiteFloatVectorDoubleOracle`:
  the concrete checked doubling oracle, in arbitrary dimension.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The registered compiled oracle CG tree contains exactly the displayed status-gated
loop. Within its active arm, the product-and-dot prefix precedes the curvature comparison;
the first instruction of its positive arm is the stored step-length division. The
parenthesized blocks are the very subexpressions certified below, not a replacement program.
The outer scope, initializer, rejection copy and remaining updates are retained verbatim.
No printed source. -/
theorem toStmt_cgOracleProg_compiled_eq_guarded_loop {P ι : Type}
    (tag : P) (o : ι) (N q : ℕ) :
    (cgOracleProg.compiled tag o).toStmt N ![q] = (scope do
      let _matrixSlot ← alloc tag 0
      let s ← alloc tag (.const N)
      let scalars ← alloc tag 9
      ins (.lit tag ⟨scalars, 6⟩ 0)
      ins (.lit tag ⟨scalars, 7⟩ 1)
      ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨scalars, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨scalars, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ())
      forRange (.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨scalars, 6⟩
        ((do
          stmt (.apply o tag s 0 3 0 1)
          dot tag ⟨scalars, 2⟩ 3 0 s 0 (.const N)) >>= fun _ =>
          ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩
            ((ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)) >>= fun _ => do
              axpy tag ⟨scalars, 3⟩ 3 0 1 0 (.const N)
              ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
              axpy tag ⟨scalars, 5⟩ s 0 2 0 (.const N)
              dot tag ⟨scalars, 1⟩ 2 0 2 0 (.const N)
              ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
              forRange (.const N) fun i => do
                ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨3, .var i⟩)
                ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨scalars, 2⟩)
              ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
              ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
                (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 8⟩))) (pure ()) :
        Builder P ι ℕ ℕ Unit).run := by
  rw [cgOracleProg.toStmt_compiled]
  rfl

/-- When the actual CG status decodes to zero, the checked binary64 outer status comparison
returns true and charges exactly one comparison. The resulting state preserves every stored
vector and scalar. No printed source. -/
theorem cmpStep_eq_some_true_of_sem_eq_finiteFloatSem_of_status_eq_zero
    {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (st : St Unit FiniteFloat C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν flag : ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N A b v ν 0 flag st.store false) :
    cmpStep I () .eq ⟨4, 0⟩ ⟨7, 6⟩ st =
      some (true, { st with cnt := st.cnt + I.charge (.cmp ()) }) := by
  obtain ⟨status, hs, hsd⟩ := h.statusValue
  obtain ⟨zero, hz, hzd⟩ := h.zero
  have hc := cmp_eq_eq_some_true_finiteFloatSem_of_zero status zero hsd hzd
  rw [← hsem] at hc
  simp only [cmpStep, IExp.eval_ofNat, hs, hz, Option.bind_some, hc, Option.map_some]

/-- When the actual CG status decodes to zero, its guarded execution equals execution of
the supplied active arm after exactly one comparison charge. The branch may be the actual
compiled-loop arm exposed by the structural equation above; this is branch selection,
not an assumption that the branch or the complete solver succeeds. No printed source. -/
theorem exec_ite_eq_exec_of_sem_eq_finiteFloatSem_of_status_eq_zero
    {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (st : St Unit FiniteFloat C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν flag : ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N A b v ν 0 flag st.store false)
    (active inactive : Builder Unit ι ℕ ℕ Unit) :
    exec I (ifThenElse () .eq ⟨4, 0⟩ ⟨7, 6⟩ active inactive).run st =
      exec I active.run { st with cnt := st.cnt + I.charge (.cmp ()) } := by
  have hg := cmpStep_eq_some_true_of_sem_eq_finiteFloatSem_of_status_eq_zero
    I hsem st N A b v ν flag h
  change exec I (.seq (.ite () .eq ⟨4, 0⟩ ⟨7, 6⟩ active.run inactive.run) .skip) st = _
  rw [exec_seq_skip, exec_ite, hg, Option.bind_some]
  rfl

/-- An input-domain mixed-error oracle executes the actual CG product call, preserving
all persistent vectors, constants and status cells. The domain is checked on the stored
search direction before the call. This includes dimension zero. No printed source. -/
theorem exec_product_of_isMatvecErrOn (I : Interp P ι K C) (tag : P) (o : ι)
    (dec : P → K → ℝ) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag : ℝ) (domain : (Fin N → ℝ) → Prop) (c η : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store false)
    (hmv : IsMatvecErrOn I o dec tag A domain c η) (hdomain : domain v.p) :
    ∃ (out : St P K C) (sv : Fin N → ℝ),
      exec I (.apply o tag 6 0 3 0 1) st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store false ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤ c * ‖WithLp.toLp 2 v.p‖ + η := by
  obtain ⟨out, W, hr, hw, he⟩ := hmv.exec_apply st 3 6 0 0 (by norm_num) v.p hdomain
    (by simpa only [IExp.eval_zero, zero_add] using h.direction)
    (fun i hi => ⟨N, by simp [h.shape, workspaceShape], by simpa using hi⟩)
  refine ⟨out, fun i => dec tag (W i), hr, ?_, ?_, he⟩
  · apply h.preserve_frame (Store.shape_of_writeBlock_eq_some hw)
    intro buf idx hcell
    apply Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl ?_)
    rcases hcell with hb | ⟨rfl, _⟩ <;> omega
  · intro i
    refine ⟨W i, ?_, rfl⟩
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw
      (j := (i : ℕ)) (by simp)

private theorem exec_curvature_dot_of_sem_eq_finiteFloatSem {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (st : St Unit FiniteFloat C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status flag : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag st.store false)
    (hs : ∀ i : Fin N, ∃ w, st.store.read () 6 i = some w ∧ floatDecode w.val = sv i)
    (hrange : (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
      (‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖) +
      N * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
        (2 + Float.Model.Format.binary64.unitRoundoff) *
          Float.Model.Format.binary64.underflowBound ≤ Float.Model.Format.binary64.maxFinite) :
    ∃ (out : St Unit FiniteFloat C) (w : FiniteFloat),
      exec I (dot () ⟨7, 2⟩ 3 0 6 0 (.const N)).run st = some out ∧
      StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag out.store false ∧
      out.store.read () 7 2 = some w ∧
      (∀ i : Fin N, ∃ z, out.store.read () 6 i = some z ∧ floatDecode z.val = sv i) ∧
      |v.p ⬝ᵥ sv - floatDecode w.val| ≤
        ((1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) - 1) *
          (‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖) +
        N * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
          (2 + Float.Model.Format.binary64.unitRoundoff) *
            Float.Model.Format.binary64.underflowBound := by
  let u := Float.Model.Format.binary64.unitRoundoff
  let η := Float.Model.Format.binary64.underflowBound
  have hu : 0 ≤ u := Float.Model.Format.unitRoundoff_nonneg _
  have hη : 0 ≤ η := Float.Model.Format.underflowBound_nonneg _
  have ha := isArithErrSem_finiteFloatSem
  rw [← hsem] at ha
  have hz := addsZeroExactly_finiteFloatSem
  rw [← hsem] at hz
  let pv : ℕ → ℝ := fun i => if hi : i < N then v.p ⟨i, hi⟩ else 0
  let sx : ℕ → ℝ := fun i => if hi : i < N then sv ⟨i, hi⟩ else 0
  have hpv : (fun i : Fin N => pv i) = v.p := by funext i; simp only [pv, dif_pos i.isLt]
  have hsv : (fun i : Fin N => sx i) = sv := by funext i; simp only [sx, dif_pos i.isLt]
  have hB : (∑ i ∈ Finset.range N, |pv i * sx i|) ≤
      ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖ := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => |pv i * sx i|) N]
    simpa only [hpv, hsv] using EuclideanSpace.sum_abs_mul_le_norm
      (fun i : Fin N => pv i) (fun i : Fin N => sx i)
  have hinput : (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range N, |pv i * sx i|) +
      N * (1 + u) ^ (2 * N) * (2 + u) * η ≤ Float.Model.Format.binary64.maxFinite := by
    calc
      _ ≤ (1 + u) ^ (2 * N) * (‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖) +
          N * (1 + u) ^ (2 * N) * (2 + u) * η :=
        _root_.add_le_add_left (mul_le_mul_of_nonneg_left hB
          (pow_nonneg (show 0 ≤ 1 + u by linarith) _)) _
      _ ≤ _ := hrange
  have hsafe k (hk : k < N) (s : ℕ → ℝ)
      (ht : IsDotTrace (fun _ => AbsRelErr u η) pv sx k s) :
      |pv k * sx k| ≤ Float.Model.Format.binary64.maxFinite ∧
      ∀ q, AbsRelErr u η (pv k * sx k) q →
        |s k + q| ≤ Float.Model.Format.binary64.maxFinite := by
    have hP : 1 ≤ (1 + u) ^ (2 * N) := one_le_pow₀ (by linarith)
    have hD : 0 ≤ (N : ℝ) * (1 + u) ^ (2 * N) * (2 + u) * η := by positivity
    have hsum := Finset.single_le_sum (f := fun i => |pv i * sx i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk)
    have hpad := mul_le_mul_of_nonneg_right hP
      (Finset.sum_nonneg (fun i (_ : i ∈ Finset.range N) => abs_nonneg (pv i * sx i)))
    exact ⟨by linarith, fun q hq => (ht.abs_add_le_of_absRelErr hu hη hk hq).trans hinput⟩
  obtain ⟨zero, _, _⟩ := h.zero
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show st.store.shape[7]? = some ((), 9) by simp [h.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  obtain ⟨out, w, hr, hwr, he⟩ := ha.exec_dot_abs_sum_mul_sub_le_of_absRelErr I () hz st
    ⟨7, 2⟩ 3 0 6 0 (.const N) pv sx hu hη
    (fun i hi => by
      have hi' : i < N := hi
      simpa only [IExp.eval_zero, zero_add, pv, dif_pos hi'] using h.direction ⟨i, hi'⟩)
    (fun i hi => by
      have hi' : i < N := hi
      simpa only [IExp.eval_zero, zero_add, sx, dif_pos hi'] using hs ⟨i, hi'⟩)
    (by norm_num) (by norm_num) ⟨zero, scratch, hw⟩ hsafe
  refine ⟨out, w, hr, h.preserve_scalar_write (by norm_num) (by norm_num) hwr,
    Store.read_of_write_eq_some hwr, ?_, ?_⟩
  · intro i
    obtain ⟨z, hz, hd⟩ := hs i
    exact ⟨z, (Store.read_of_write_eq_some_of_ne hwr (Or.inl (by norm_num))).trans hz, hd⟩
  · have hsum : (∑ i ∈ Finset.range N, pv i * sx i) = v.p ⬝ᵥ sv := by
      rw [← Fin.sum_univ_eq_sum_range]
      change ((fun i : Fin N => pv i) ⬝ᵥ (fun i : Fin N => sx i)) = _
      rw [hpv, hsv]
    simp only [IExp.eval_const, hsum] at he
    have hcoef : 0 ≤ (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) - 1 := by
      have := one_le_pow₀ (n := 2 * N) (show 1 ≤ 1 + u by linarith)
      change 0 ≤ (1 + u) ^ (2 * N) - 1
      linarith
    exact he.trans (_root_.add_le_add_left (mul_le_mul_of_nonneg_left hB hcoef) _)

/-- A finite binary64 CG step-length division succeeds from a proved curvature error
$\lvert q-\mu\rvert\le B$, a positive margin $B<q$, and the input-only quotient range
$\lvert\nu\rvert\le M(q-B)$. The actual stored quotient satisfies mixed error; above a
positive scale $\tau$ it also has relative error at most $u+\eta/\tau$. The persistent
CG state is preserved. This helper is consumed after the actual curvature prefix has
established its error; it makes no claim that arbitrary supplied curvatures are accurate.
No printed source. -/
theorem exec_step_length_of_sem_eq_finiteFloatSem_of_curvature_error
    {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (st : St Unit FiniteFloat C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag st.store false)
    (wμ : FiniteFloat) (hwμ : st.store.read () 7 2 = some wμ)
    (q B : ℝ) (herr : |q - floatDecode wμ.val| ≤ B) (hmargin : B < q)
    (hrange : |ν| ≤ Float.Model.Format.binary64.maxFinite * (q - B)) :
    ∃ (out : St Unit FiniteFloat C) (wα : FiniteFloat),
      exec I (Builder.ins (.bin () .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)).run st = some out ∧
      StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag out.store false ∧
      out.store.read () 7 3 = some wα ∧
      AbsRelErr Float.Model.Format.binary64.unitRoundoff
        Float.Model.Format.binary64.underflowBound (ν / floatDecode wμ.val)
          (floatDecode wα.val) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ |ν / floatDecode wμ.val| →
        RelErr (Float.Model.Format.binary64.unitRoundoff +
          Float.Model.Format.binary64.underflowBound / τ) (ν / floatDecode wμ.val)
            (floatDecode wα.val)) := by
  have hden : q - B ≤ floatDecode wμ.val := by linarith [(abs_le.mp herr).2]
  have hpos : 0 < floatDecode wμ.val := by linarith
  have hsafe : |ν / floatDecode wμ.val| ≤ Float.Model.Format.binary64.maxFinite := by
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hrange.trans (mul_le_mul_of_nonneg_left hden
      (Float.Model.Format.maxFinite_pos .binary64).le)
  obtain ⟨wν, hwν, hν⟩ := h.squaredResidual
  have ha := isArithErrSem_finiteFloatSem
  rw [← hsem] at ha
  obtain ⟨out, wα, hr, _, hshape, hread, he, hframe⟩ :=
    ha.exec_cg_division I () st ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩ wν wμ hwν hwμ hpos.ne'
      (by simpa only [hν] using hsafe)
      ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  rw [hν] at he
  refine ⟨out, wα, hr, ?_, hread, he, fun τ hτ hscale =>
    he.relErr_of_abs_ge (Float.Model.Format.unitRoundoff_nonneg .binary64)
      (Float.Model.Format.underflowBound_nonneg .binary64) hτ hscale⟩
  apply h.preserve_frame hshape
  intro buf idx hcell
  apply hframe () buf idx
  change () ≠ () ∨ buf ≠ 7 ∨ idx ≠ 3
  rcases hcell with hb | ⟨rfl, hj⟩
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num))

/-- The actual active CG product-and-curvature prefix executes with checked finite binary64
arithmetic in any dimension. Let $E=c\|\mathbf{p}\|+\eta_m$, $P=(1+u)^{2N}$ and
$D=NP(2+u)\eta$, with $u=2^{-53}$ and $\eta=2^{-1075}$. The input-domain matvec
contract and the input-only condition
$$P\|\mathbf{p}\|(\|\mathbf{A}\mathbf{p}\|+E)+D\le M$$
certify all oracle and scalar operations, where $M$ is the largest finite magnitude.
The actual product has normwise error at most $E$, and the actual curvature word has error
at most $(P-1)\|\mathbf{p}\|(\|\mathbf{A}\mathbf{p}\|+E)+D+\|\mathbf{p}\|E$ against
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$. All persistent CG cells are preserved.
If the error allowance is strictly smaller than the exact curvature, the actual IEEE
curvature comparison selects the positive branch. The claim covers this prefix of the
registered tree; downstream divisions and updates require additional range and
nonbreakdown invariants. In addition, the input bound $\lvert\nu\rvert\le
M(\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}-B)$ certifies the actual step-length
division after the charged comparison. Its readback has mixed error, and relative error
$u+\eta/\tau$ above an explicit positive quotient scale $\tau$. No printed source. -/
theorem exec_curvature_of_sem_eq_finiteFloatSem {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem) (o : ι)
    (st : St Unit FiniteFloat C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (domain : (Fin N → ℝ) → Prop) (c ηm : ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag st.store false)
    (hmv : IsMatvecErrOn I o (fun _ x => floatDecode x.val) () A domain c ηm)
    (hdomain : domain v.p)
    (hrange : (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
      (‖WithLp.toLp 2 v.p‖ * (‖WithLp.toLp 2 (A *ᵥ v.p)‖ +
        (c * ‖WithLp.toLp 2 v.p‖ + ηm))) +
      N * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
        (2 + Float.Model.Format.binary64.unitRoundoff) *
          Float.Model.Format.binary64.underflowBound ≤ Float.Model.Format.binary64.maxFinite) :
    let B := ((1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) - 1) *
      (‖WithLp.toLp 2 v.p‖ * (‖WithLp.toLp 2 (A *ᵥ v.p)‖ +
        (c * ‖WithLp.toLp 2 v.p‖ + ηm))) +
      N * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) *
        (2 + Float.Model.Format.binary64.unitRoundoff) *
          Float.Model.Format.binary64.underflowBound +
      ‖WithLp.toLp 2 v.p‖ * (c * ‖WithLp.toLp 2 v.p‖ + ηm)
    ∃ (out : St Unit FiniteFloat C) (sv : Fin N → ℝ) (w : FiniteFloat),
      exec I (do
        stmt (.apply o () 6 0 3 0 1)
        dot () ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder Unit ι ℕ ℕ Unit).run st = some out ∧
      StoreContext () (fun _ x => floatDecode x.val) N A b v ν status flag out.store false ∧
      (∀ i : Fin N, ∃ z, out.store.read () 6 i = some z ∧ floatDecode z.val = sv i) ∧
      out.store.read () 7 2 = some w ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤ c * ‖WithLp.toLp 2 v.p‖ + ηm ∧
      |v.p ⬝ᵥ (A *ᵥ v.p) - floatDecode w.val| ≤ B ∧
      (B < v.p ⬝ᵥ (A *ᵥ v.p) →
        0 < floatDecode w.val ∧
        cmpStep I () .lt ⟨7, 6⟩ ⟨7, 2⟩ out =
          some (true, { out with cnt := out.cnt + I.charge (.cmp ()) }) ∧
        (|ν| ≤ Float.Model.Format.binary64.maxFinite * (v.p ⬝ᵥ (A *ᵥ v.p) - B) →
          ∃ (next : St Unit FiniteFloat C) (wα : FiniteFloat),
            exec I (Builder.ins (.bin () .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)).run
              { out with cnt := out.cnt + I.charge (.cmp ()) } = some next ∧
            StoreContext () (fun _ x => floatDecode x.val)
              N A b v ν status flag next.store false ∧
            next.store.read () 7 3 = some wα ∧
            AbsRelErr Float.Model.Format.binary64.unitRoundoff
              Float.Model.Format.binary64.underflowBound
                (ν / floatDecode w.val) (floatDecode wα.val) ∧
            (∀ τ : ℝ, 0 < τ → τ ≤ |ν / floatDecode w.val| →
              RelErr (Float.Model.Format.binary64.unitRoundoff +
                Float.Model.Format.binary64.underflowBound / τ)
                  (ν / floatDecode w.val) (floatDecode wα.val)))) := by
  dsimp only
  obtain ⟨mid, sv, hr, hctx, hs, he⟩ :=
    exec_product_of_isMatvecErrOn I () o (fun _ x => floatDecode x.val) st N A b v
      ν status flag domain c ηm h hmv hdomain
  have hnorm : ‖WithLp.toLp 2 sv‖ ≤
      ‖WithLp.toLp 2 (A *ᵥ v.p)‖ + (c * ‖WithLp.toLp 2 v.p‖ + ηm) := by
    have ht := norm_sub_le (WithLp.toLp 2 (A *ᵥ v.p))
      (WithLp.toLp 2 (A *ᵥ v.p - sv))
    rw [← WithLp.toLp_sub, sub_sub_cancel] at ht
    exact ht.trans (_root_.add_le_add_right he _)
  have hP : 0 ≤ (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) := by positivity
  have hPm : 0 ≤ (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * N) - 1 := by
    have hu := Float.Model.Format.unitRoundoff_nonneg .binary64
    have := one_le_pow₀ (n := 2 * N) (show 1 ≤ 1 +
      Float.Model.Format.binary64.unitRoundoff by linarith)
    linarith
  have hprod := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (WithLp.toLp 2 v.p))
  obtain ⟨out, w, hd, hout, hw, hwords, hμ⟩ :=
    exec_curvature_dot_of_sem_eq_finiteFloatSem I hsem mid N A b v ν status flag sv hctx hs
      ((_root_.add_le_add_left (mul_le_mul_of_nonneg_left hprod hP) _).trans hrange)
  have hμ' := hμ.trans
    (_root_.add_le_add_left (mul_le_mul_of_nonneg_left hprod hPm) _)
  have herror := EuclideanSpace.abs_dotProduct_sub_le_of_norm_sub_le he hμ'
  refine ⟨out, sv, w, ?_, hout, hwords, hw, he, herror, ?_⟩
  · rw [exec_run_bind I (b := stmt (.apply o () 6 0 3 0 1)) (fun _ => rfl)]
    change (exec I (.seq (.apply o () 6 0 3 0 1) .skip) st).bind _ = _
    rw [exec_seq_skip, hr, Option.bind_some]
    exact hd
  · intro hmargin
    have hpos : 0 < floatDecode w.val := by linarith [(abs_le.mp herror).2]
    refine ⟨hpos, ?_, fun hνrange => ?_⟩
    · obtain ⟨zero, hz, hzdec⟩ := hout.zero
      have hcmp := cmp_lt_eq_some_true_finiteFloatSem_of_zero_of_pos zero w hzdec hpos
      rw [← hsem] at hcmp
      simp only [cmpStep, IExp.eval_ofNat, hz, hw, Option.bind_some, hcmp, Option.map_some]
    · exact exec_step_length_of_sem_eq_finiteFloatSem_of_curvature_error
        I hsem { out with cnt := out.cnt + I.charge (.cmp ()) } N A b v ν status flag
          hout w hw _ _ herror hmargin hνrange

/-- In every dimension, the actual registered CG product-and-curvature prefix with the
concrete checked binary64 doubling oracle succeeds and takes its positive-curvature guard
from input-only conditions. Put $R=\|\mathbf{p}\|$, $u=2^{-53}$, $\eta=2^{-1075}$,
$E=2uR+\sqrt{N}\eta$, $P=(1+u)^{2N}$ and $D=NP(2+u)\eta$.
The domain condition is $\lvert2p_i\rvert\le M$ for each input coordinate; the scalar range
condition is $PR(2R+E)+D\le M$. If the mixed error allowance
$B=(P-1)R(2R+E)+D+RE$ is less than $2R^2$, the actual curvature word is positive and the
actual IEEE guard returns true. The stored product error is at most $E$ and curvature error
at most $B$. No observed scalar range or desired trajectory is assumed. This certifies a
positive prefix on twice the identity. The input bound $\lvert\nu\rvert\le M(2R^2-B)$
also certifies the actual step-length division after the charged positive comparison, with
mixed error and scale-conditioned relative error. No complete solver run is asserted.
No printed source. -/
theorem exec_curvature_of_finiteFloatVectorDoubleOracle {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem) (o : ι)
    (st : St Unit FiniteFloat C) (N : ℕ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag : ℝ)
    (h : StoreContext () (fun _ x => floatDecode x.val) N
      ((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) b v ν status flag st.store false)
    (hh : I.height o = N) (ho : I.oracle o = finiteFloatVectorDoubleOracle N)
    (hdomain : ∀ i, |2 * v.p i| ≤ Float.Model.Format.binary64.maxFinite) :
    let u := Float.Model.Format.binary64.unitRoundoff
    let η := Float.Model.Format.binary64.underflowBound
    let R := ‖WithLp.toLp 2 v.p‖
    let E := 2 * u * R + Real.sqrt N * η
    let Q := (1 + u) ^ (2 * N)
    let D := N * Q * (2 + u) * η
    Q * (R * (2 * R + E)) + D ≤ Float.Model.Format.binary64.maxFinite →
    (Q - 1) * (R * (2 * R + E)) + D + R * E < 2 * R ^ 2 →
    ∃ (out : St Unit FiniteFloat C) (sv : Fin N → ℝ) (w : FiniteFloat),
      exec I (do
        stmt (.apply o () 6 0 3 0 1)
        dot () ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder Unit ι ℕ ℕ Unit).run st = some out ∧
      StoreContext () (fun _ x => floatDecode x.val) N
        ((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) b v ν status flag out.store false ∧
      (∀ i : Fin N, ∃ z, out.store.read () 6 i = some z ∧ floatDecode z.val = sv i) ∧
      out.store.read () 7 2 = some w ∧
      ‖WithLp.toLp 2 ((2 : ℝ) • v.p - sv)‖ ≤ E ∧
      |2 * R ^ 2 - floatDecode w.val| ≤ (Q - 1) * (R * (2 * R + E)) + D + R * E ∧
      0 < floatDecode w.val ∧
      cmpStep I () .lt ⟨7, 6⟩ ⟨7, 2⟩ out =
        some (true, { out with cnt := out.cnt + I.charge (.cmp ()) }) ∧
      (|ν| ≤ Float.Model.Format.binary64.maxFinite *
          (2 * R ^ 2 - ((Q - 1) * (R * (2 * R + E)) + D + R * E)) →
        ∃ (next : St Unit FiniteFloat C) (wα : FiniteFloat),
          exec I (Builder.ins (.bin () .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)).run
            { out with cnt := out.cnt + I.charge (.cmp ()) } = some next ∧
          StoreContext () (fun _ x => floatDecode x.val) N
            ((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) b v ν status flag next.store false ∧
          next.store.read () 7 3 = some wα ∧
          AbsRelErr u η (ν / floatDecode w.val) (floatDecode wα.val) ∧
          (∀ τ : ℝ, 0 < τ → τ ≤ |ν / floatDecode w.val| →
            RelErr (u + η / τ) (ν / floatDecode w.val) (floatDecode wα.val))) := by
  dsimp only
  intro hrange hmargin
  have hnorm : ‖WithLp.toLp 2
      (((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v.p)‖ =
        2 * ‖WithLp.toLp 2 v.p‖ := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.toLp_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcurv : v.p ⬝ᵥ (((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v.p) =
      2 * ‖WithLp.toLp 2 v.p‖ ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      ← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, smul_eq_mul]
  obtain ⟨out, sv, w, hr, hout, hwords, hw, he, herror, hbranch⟩ :=
    exec_curvature_of_sem_eq_finiteFloatSem I hsem o st N _ b v ν status flag
      _ _ _ h (isMatvecErrOn_finiteFloatVectorDoubleOracle I o N hh ho) hdomain
      (by simpa only [hnorm] using hrange)
  have hmargin' := hmargin
  rw [← hcurv] at hmargin'
  have hb := hbranch (by simpa only [hnorm] using hmargin')
  refine ⟨out, sv, w, hr, hout, hwords, hw, ?_, ?_, hb.1, hb.2.1, ?_⟩
  · simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using he
  · simpa only [hnorm, hcurv] using herror
  · simpa only [hnorm, hcurv] using hb.2.2

end NLAlib.CGOracleImplementation
