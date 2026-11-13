/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Count
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Profiles.BlasCert

/-!
# A bilinear form through an operator and a BLAS profile

One program computes the rectangular bilinear form `xᵀ A y` by a matrix-vector product and a
dot product. Its certificate assumes an exact operator and the rounded dot contract. Exact and
standard-model results use the same certificate.

## Main results

* `NLAlib.Ops.Examples.bilinear_spec`: the reusable certificate over the two operation contracts.
* `NLAlib.Ops.Examples.runs_bilinear_rounded`: the abstract componentwise forward bound.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K Op Tst : Type} [Has OperatorOp Op] [Has Blas1Op Op]

/-- Evaluate the bilinear form by a rectangular matrix-vector product and a dot product. -/
def bilinear : Stmt Op Tst := ops% [m, n] (x, y) → (z) {
  let v ← alloc m;
  call (Has.inj OperatorOp.matvec) [m, n] (y) → (v);
  call (Has.inj Blas1Op.dot) [m] (x, v) → (z)
}

/-- The bilinear-form implementation has two dimensions, two input blocks, and one output cell. -/
def bilinearImpl : Impl Op Tst := ⟨2, 2, 1, bilinear⟩

/-- One matrix-vector call and one dot-product call. -/
noncomputable def bilinearCount (m n : ℕ) : Count Op Tst :=
  Count.one (Has.inj OperatorOp.matvec) [m, n] + Count.one (Has.inj Blas1Op.dot) [m]

/-- The intermediate vector and the largest workspace of the two calls. -/
def bilinearPeak (W : Op → List ℕ → ℕ) (m n : ℕ) : ℕ :=
  m + max (W (Has.inj OperatorOp.matvec) [m, n]) (W (Has.inj Blas1Op.dot) [m])

/-- The static evaluator counts exactly the two abstract calls. -/
theorem stmtCost_bilinear (m n x y z : ℕ) :
    stmtCost (bilinear (Op := Op) (Tst := Tst)) [m, n, x, y, z] = bilinearCount m n := by
  simp [bilinear, stmtCost, useCost, bilinearCount]

/-- The static workspace includes the intermediate vector and the two operation workspaces. -/
theorem stmtPeak_bilinear (W : Op → List ℕ → ℕ) (m n x y z : ℕ) :
    stmtPeak W (bilinear (Op := Op) (Tst := Tst)) [m, n, x, y, z] = bilinearPeak W m n := by
  simp [bilinear, stmtPeak, bilinearPeak]

variable [Inhabited K]

/-- The componentwise dot-product bound after the exact operator has formed `A y`. -/
def IsBilinearErr (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (e : ℝ) (xs ys : List K) (v : K) : Prop :=
  |dec v - decv dec m xs ⬝ᵥ A.mulVec (decv dec n ys)| ≤
    e * ∑ i : Fin m, |decv dec m xs i * A.mulVec (decv dec n ys) i|

/-- The output cell satisfies the bilinear-form error bound. -/
@[simps (attr := storeNF)]
def bilinearRel (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (e : ℝ) : BlockRel K where
  nd := 2
  inLens _ := [m, n]
  outLens _ := [1]
  rel _ X _ Y := match X, Y with
    | [xs, ys], [[v]] => IsBilinearErr dec A e xs ys v
    | _, _ => False

/-- The matrix dimensions match and the output uses a buffer apart from both inputs. -/
@[admNF] def BilinearOperands (m n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [m, n] ∧ ∀ x ∈ ins, ∀ z ∈ outs, x.1 ≠ z.1

/-- The dot-product error bound becomes the bilinear-form bound when its second input is
the exact matrix-vector product. -/
theorem isBilinearErr_of_isDotErr {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {e : ℝ} {xs ys vs : List K} {v : K} (h : IsDotErr dec e m (vec xs) (vec vs) v)
    (hv : decv dec m vs = A.mulVec (decv dec n ys)) : IsBilinearErr dec A e xs ys v := by
  simpa only [IsBilinearErr, hv] using h.decoded

/-- One program certificate composes the exact operator with any admitted rounded dot product. -/
theorem bilinear_spec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {e : ℕ → ℝ} {ok : ℕ → Prop} {J : Interp Op Tst K} (hA : IsExactMatvec dec A J)
    (hD : J.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec e).spec (OutApart ok)))
    (hok : ok m) :
    (bilinearImpl (Op := Op) (Tst := Tst)).Triple J .total
      ((bilinearRel dec A (e m)).spec (BilinearOperands m n)) := by
  cert_intro [r, c] (x, y) → (z) reads (xs, ys)
  obtain ⟨rfl, rfl, hxz, hyz⟩ := hadm
  refine writes_alloc rfl fun s₁ hs₁ hv hB => ?_
  step hA as μ₁ hfr₁ ⟨hpos₁, vs, hvs, hrel⟩
  step hD as μ₂ hfr₂ ⟨hpos₂, v, hvout, hdot⟩
  intro s₂ _ hB₂
  exact ⟨by simp [hpos₂, hpos₁], [[v]], BlockFn.readBlocks_cells_one.mpr
    ⟨v, by kept, rfl⟩, isBilinearErr_of_isDotErr hdot hrel⟩

/-- The output is the only changed cell and it satisfies the bilinear-form error bound. -/
def BilinearRounded (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : ℝ)
    (z : ℕ × ℕ) (xs ys : List K) (μ μ' : Mem K) : Prop :=
  ∃ v, μ' = μ.upd z v ∧ IsBilinearErr dec A e xs ys v

/-- The output is the only changed cell and decodes to the exact bilinear form. -/
def BilinearExact (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (z : ℕ × ℕ) (xs ys : List K) (μ μ' : Mem K) : Prop :=
  ∃ v, μ' = μ.upd z v ∧ dec v = decv dec m xs ⬝ᵥ A.mulVec (decv dec n ys)

/-- A zero error bound gives the exact decoded bilinear form. -/
theorem BilinearRounded.exact {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {z : ℕ × ℕ} {xs ys : List K} {μ μ' : Mem K}
    (h : BilinearRounded dec A 0 z xs ys μ μ') : BilinearExact dec A z xs ys μ μ' := by
  obtain ⟨v, hm, he⟩ := h
  exact ⟨v, hm, by simpa [IsBilinearErr, sub_eq_zero] using he⟩

/-- Every interpretation satisfying the two operation contracts computes the bilinear form within
their two call counts and the declared scratch bound. -/
theorem runs_bilinear_rounded {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {e : ℕ → ℝ} {ok : ℕ → Prop} {J : Interp Op Tst K} (hA : IsExactMatvec dec A J)
    (hD : J.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec e).spec (OutApart ok)))
    (hok : ok m) (W : Op → List ℕ → ℕ) {τ : Tape K} {x y z : ℕ × ℕ} {μ : Mem K}
    {xs ys : List K} (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1) (hl : μ.Live [x, y, z])
    (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns J W τ bilinear (Env.frame [m, n] [x, y, z]) μ (bilinearCount m n)
      (bilinearPeak W m n) (BilinearRounded dec A (e m) z xs ys μ) := by
  refine ((bilinear_spec hA hD hok).runs_rel W (d := [m, n]) (ins := [x, y]) (outs := [z])
    (τ := τ) (xs := [xs, ys]) rfl ⟨rfl, by simp [hxz, hyz]⟩ hl
    (by simp [bilinearRel, Mem.readBlocks, hx, hy]) trivial ⟨by omega, trivial⟩).mono
    (le_of_eq (stmtCost_bilinear ..)) (le_of_eq (stmtPeak_bilinear ..)) ?_
  rintro μ' ⟨Y, hlen, hrel, rfl⟩
  obtain ⟨vs, rfl, hvs⟩ := map_length_eq_one hlen
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hvs
  exact ⟨v, rfl, hrel⟩

/-- Exact BLAS1 computes the exact bilinear form, from the same program certificate. -/
theorem runs_bilinear_exact {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {ok : ℕ → Prop} {J : Interp Op Tst K} (hA : IsExactMatvec dec A J)
    (hB : IsExactBlas1 dec ok J) (hok : ok m) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {x y z : ℕ × ℕ} {μ : Mem K} {xs ys : List K} (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hl : μ.Live [x, y, z]) (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns J W τ bilinear (Env.frame [m, n] [x, y, z]) μ (bilinearCount m n)
      (bilinearPeak W m n) (BilinearExact dec A z xs ys μ) :=
  (runs_bilinear_rounded hA hB.dot_zero hok W hxz hyz hl hx hy hz).mono le_rfl le_rfl
    fun _ h => h.exact

/-! ### Standard-model profiles -/

variable [Has ScalarOp Op] [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- Sequential summation gives error `(1 + u) ^ m - 1`, one matrix-vector call, `m`
multiplications, `m - 1` additions, a literal and at most one copy, using `2 m` scratch cells. -/
theorem runs_bilinear_link_seq {M : Machine K} {u : ℝ} {dec : K → ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K} (hI : IsScalar M I)
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (hA : IsExactMatvec dec A I) {τ : Tape K}
    {x y z : ℕ × ℕ} {μ : Mem K} {xs ys : List K} (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1)
    (hl : μ.Live [x, y, z]) (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns I (Blas.ws 0) τ (bilinear.link Blas.seq.table) (Env.frame [m, n] [x, y, z]) μ
      (Count.one (Has.inj OperatorOp.matvec) [m, n] +
        (m • Blas.sc .mul + (Blas.sc (.lit 0) +
          ((1 - (1 - m)) • Blas.sc .copy + (m - 1) • Blas.sc .add)))) (2 * m)
      (BilinearRounded dec A ((1 + u) ^ m - 1) z xs ys μ) := by
  have hcert := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  have hkept := Apart.proj_inj (G := Blas1Op) (H := OperatorOp) (Op := Op) .matvec
  have hmat := Interp.link_meets_kept (Blas.seq_table_kept hkept) hA
  have hr := hcert.transfer I τ bilinear _ μ _ _
    (BilinearRounded dec A ((Blas.seq.err u).dot m) z xs ys μ)
    (runs_bilinear_rounded hmat (hcert.meets I hI).2.dot trivial _ hxz hyz hl hx hy hz)
  refine hr.mono ?_ ?_ ?_
  · simp [bilinearCount, Blas.seq_cost_kept hkept, Blas.seq_cost_dot]
  · simp [bilinearPeak, Blas.seq, Profile.over, Blas.level1, Blas.ws, hkept, two_mul]
  · rintro μ' ⟨v, hm, he⟩
    refine ⟨v, hm, ?_⟩
    cases m with
    | zero => simpa [IsBilinearErr, dotProduct] using he
    | succ m => simpa only [Blas.seq.err_dot u (n := m + 1) (by omega)] using he

/-- Pairwise summation of depth `k` gives error `(1 + u) ^ (clog 2 m + 1) - 1`,
one matrix-vector call, `m` multiplications, and the scalar count `Blas.pairCount m`,
using `2 m + 2 clog 2 m` scratch cells. -/
theorem runs_bilinear_link_pairwise {M : Machine K} {u : ℝ} {dec : K → ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K} (hI : IsScalar M I)
    {k m n : ℕ} (hk : Nat.clog 2 m < k) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : IsExactMatvec dec A I) {τ : Tape K} {x y z : ℕ × ℕ} {μ : Mem K}
    {xs ys : List K} (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1) (hl : μ.Live [x, y, z])
    (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns I (Blas.ws Blas.pairWs) τ (bilinear.link (Blas.pairwise k).table)
      (Env.frame [m, n] [x, y, z]) μ
      (Count.one (Has.inj OperatorOp.matvec) [m, n] +
        (m • Blas.sc .mul + Blas.pairCount m)) (2 * m + 2 * Nat.clog 2 m)
      (BilinearRounded dec A ((1 + u) ^ (Nat.clog 2 m + 1) - 1) z xs ys μ) := by
  have hcert := Blas.pairwise_certifies (Op := Op) (Tst := Tst) hM hu k
  have hkept := Apart.proj_inj (G := Blas1Op) (H := OperatorOp) (Op := Op) .matvec
  have hmat := Interp.link_meets_kept (Blas.pairwise_table_kept k hkept) hA
  have hr := hcert.transfer I τ bilinear _ μ _ _
    (BilinearRounded dec A ((Blas.pairwise.err u).dot m) z xs ys μ)
    (runs_bilinear_rounded hmat (hcert.meets I hI).2.dot hk _ hxz hyz hl hx hy hz)
  rw [Blas.pairwise_wsLo, Blas.pairwise.err_dot] at hr
  refine hr.mono ?_ ?_ fun _ h => h
  · simp [bilinearCount, Blas.pairwise_cost_kept k hkept, Blas.pairwise_cost_dot k m hk]
  · simp [bilinearPeak, Blas.pairwise, Profile.over, Blas.level1, Blas.ws, hkept,
      Blas.pairWs, two_mul, add_assoc]

/-- The sequential implementation over exact scalar arithmetic computes the exact bilinear form
with the same evaluated scalar counts and scratch bound. -/
theorem runs_bilinear_link_seq_exact {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {I : Interp Op Tst K} (hI : IsScalar M I) {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : IsExactMatvec dec A I) {τ : Tape K} {x y z : ℕ × ℕ} {μ : Mem K}
    {xs ys : List K} (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1) (hl : μ.Live [x, y, z])
    (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns I (Blas.ws 0) τ (bilinear.link Blas.seq.table) (Env.frame [m, n] [x, y, z]) μ
      (Count.one (Has.inj OperatorOp.matvec) [m, n] +
        (m • Blas.sc .mul + (Blas.sc (.lit 0) +
          ((1 - (1 - m)) • Blas.sc .copy + (m - 1) • Blas.sc .add)))) (2 * m)
      (BilinearExact dec A z xs ys μ) := by
  have h := runs_bilinear_link_seq (τ := τ) hM.toStdModel_zero le_rfl hI hA hxz hyz hl hx hy hz
  simp only [add_zero, one_pow, sub_self] at h
  exact h.mono le_rfl le_rfl fun _ he => he.exact

/-- The pairwise implementation over exact scalar arithmetic computes the exact bilinear form
at every length covered by its depth, with the evaluated scalar counts and scratch bound. -/
theorem runs_bilinear_link_pairwise_exact {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {I : Interp Op Tst K} (hI : IsScalar M I) {k m n : ℕ}
    (hk : Nat.clog 2 m < k) {A : Matrix (Fin m) (Fin n) ℝ} (hA : IsExactMatvec dec A I)
    {τ : Tape K} {x y z : ℕ × ℕ} {μ : Mem K} {xs ys : List K}
    (hxz : x.1 ≠ z.1) (hyz : y.1 ≠ z.1) (hl : μ.Live [x, y, z])
    (hx : μ.store.readBlock x.1 x.2 m = some xs)
    (hy : μ.store.readBlock y.1 y.2 n = some ys) (hz : z.2 < μ.store.len z.1) :
    ConditionalRuns I (Blas.ws Blas.pairWs) τ (bilinear.link (Blas.pairwise k).table)
      (Env.frame [m, n] [x, y, z]) μ
      (Count.one (Has.inj OperatorOp.matvec) [m, n] +
        (m • Blas.sc .mul + Blas.pairCount m)) (2 * m + 2 * Nat.clog 2 m)
      (BilinearExact dec A z xs ys μ) := by
  have h := runs_bilinear_link_pairwise (τ := τ)
    hM.toStdModel_zero le_rfl hI hk hA hxz hyz hl hx hy hz
  simp only [add_zero, one_pow, sub_self] at h
  exact h.mono le_rfl le_rfl fun _ he => he.exact

/-! ### Joint witnesses -/

variable [Apart ScalarOp OperatorOp Op]

omit [Inhabited K] in
/-- For every nonnegative unit roundoff and rectangular matrix, the scalar, BLAS1 and operator
contracts used by the sequential result can be met jointly. -/
theorem exists_isBlas1_isExactMatvec {u : ℝ} (hu : 0 ≤ u) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ J : Interp Op Tst ℝ, StdModel u id exactMachine ∧ IsScalar exactMachine J ∧
      IsBlas1 id (Blas.seq.err u) (fun _ => True) J ∧ IsExactMatvec id A J := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec (Op := Op) (Tst := Tst) A
  have hB := (Blas.seq_certifies (stdModel_exact hu) hu (fun _ => True)).meets I hS
  exact ⟨_, stdModel_exact hu, hB.1, hB.2, Interp.link_meets_kept
    (Blas.seq_table_kept (Apart.proj_inj (G := Blas1Op) (H := OperatorOp) .matvec)) hA⟩

omit [Inhabited K] in
/-- The same contracts can be met jointly for pairwise summation at every recursion depth,
on precisely the lengths covered by that depth. -/
theorem exists_isBlas1_isExactMatvec_pairwise {u : ℝ} (hu : 0 ≤ u) (k : ℕ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ J : Interp Op Tst ℝ, StdModel u id exactMachine ∧ IsScalar exactMachine J ∧
      IsBlas1 id (Blas.pairwise.err u) (fun r => Nat.clog 2 r < k) J ∧ IsExactMatvec id A J := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec (Op := Op) (Tst := Tst) A
  have hB := (Blas.pairwise_certifies (stdModel_exact hu) hu k).meets I hS
  exact ⟨_, stdModel_exact hu, hB.1, hB.2, Interp.link_meets_kept
    (Blas.pairwise_table_kept k
      (Apart.proj_inj (G := Blas1Op) (H := OperatorOp) .matvec)) hA⟩

omit [Inhabited K] in
/-- Exact scalar arithmetic, BLAS1 and the rectangular operator can be realized together at all
vector lengths. -/
theorem exists_isExactBlas1_isExactMatvec (ok : ℕ → Prop) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ J : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine J ∧
      IsExactBlas1 id ok J ∧ IsExactMatvec id A J := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec (Op := Op) (Tst := Tst) A
  have hB := (Blas.seq_certifies_exact exactModel_exactMachine ok).meets I hS
  exact ⟨_, exactModel_exactMachine, hB.1, hB.2, Interp.link_meets_kept
    (Blas.seq_table_kept (Apart.proj_inj (G := Blas1Op) (H := OperatorOp) .matvec)) hA⟩

end NLAlib.Ops.Examples
