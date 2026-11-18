/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.GivensRotation
public import NLAlib.Matrix.FinitePrecision.StoredMatrix
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Logic.Writes
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.FinitePrecision.GivensChain
public import NLAlib.Matrix.Norms.Compare

/-!
# Products of stored complex matrices on strided views

A product $\mathbf{Z} = \mathbf{X}\mathbf{Y}$, or $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$,
of complex matrices stored as word pairs in column-major order on strided views (leading dimensions
of their own), accumulated by rounded complex multiply–adds (`NLAlib.Ops.Pair.linearCombination`).
The output is a separate view. Under the standard model the stored product is within
$8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$ of the exact one, $p$
the inner dimension.

## Main definitions

* `NLAlib.matMulOn`: the strided product, with the left factor optionally conjugate-transposed.
* `NLAlib.matMulWord`: the product the program stores on a machine.

## Main results

* `NLAlib.matMulOn_writes_word`, `NLAlib.matMulOn_conjTranspose_writes_word`: the program stores
  `NLAlib.matMulWord` (contiguous views).
* `NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le`: the error of the stored product.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O]

/-- **The product of two stored complex matrices on strided views**: for $c = 0$,
$\mathbf{Z} = \mathbf{X}\mathbf{Y}$ with $\mathbf{X}$ of size $m \times p$ (leading dimension
`ldx`), $\mathbf{Y}$ of size $p \times q$ (`ldy`) and $\mathbf{Z}$ of size $m \times q$ (`ldz`);
for $c \ge 1$, $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$ with $\mathbf{X}$ of size
$p \times m$. Entry $(i, j)$ is accumulated from $0$ by $p$ rounded complex multiply–adds. The
interface is `[m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z)`; the output is apart from the inputs, and
the four scratch pairs are scoped. -/
def matMulOn : Impl O Q := opsImpl% [m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z) {
  let One ← alloc 2;
  let A ← alloc 2;
  let S ← alloc 2;
  let T ← alloc 2;
  let R ← alloc 2;
  call (Has.inj (ScalarOp.lit 1)) [] () → (One);
  call (Has.inj (ScalarOp.lit 0)) [] () → (One[1]);
  for j < q {
    for i < m {
      call (Has.inj (ScalarOp.lit 0)) [] () → (S);
      call (Has.inj (ScalarOp.lit 0)) [] () → (S[1]);
      for l < p {
        ifPos c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (i * ldx + l)]) → (A);
          call (Has.inj ScalarOp.neg) [] (X[2 * (i * ldx + l) + 1]) → (A[1])
        };
        ifPos 1 - c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i)]) → (A);
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i) + 1]) → (A[1])
        };
        run Pair.linearCombination.body [] (A, One, Y[2 * (j * ldy + l)], S, T, R);
        call (Has.inj ScalarOp.copy) [] (R) → (S);
        call (Has.inj ScalarOp.copy) [] (R[1]) → (S[1])
      };
      call (Has.inj ScalarOp.copy) [] (S) → (Z[2 * (j * ldz + i)]);
      call (Has.inj ScalarOp.copy) [] (S[1]) → (Z[2 * (j * ldz + i) + 1])
    }
  }
}

/-- **The product stored by `NLAlib.matMulOn`** on the machine `M`: entry $(i, j)$ is accumulated
from the pair of the literal $0$ by the rounded complex multiply–adds $s \mapsto
\mathrm{fl}(x_{il}y_{lj} + \hat 1 s)$, $l = 0, \dots, p - 1$, with $\hat 1$ the pair of the
literals $1$ and $0$ (`NLAlib.linearComplex`). -/
noncomputable def matMulWord (M : Machine ℝ) {m p q : ℕ} (X : Matrix (Fin m) (Fin p) ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j => (List.finRange p).foldl
    (fun s l => linearComplex M (X i l) ⟨M.lit 1, M.lit 0⟩ (Y l j) s) ⟨M.lit 0, M.lit 0⟩

section Theorems

variable [Inhabited ℝ]

/-- `NLAlib.matMulOn` with $c = 0$ on contiguous views (leading dimensions the row counts), on a
scalar machine and every tape: from $\mathbf{X}$ ($m \times p$) at `x` and $\mathbf{Y}$
($p \times q$) at `y`, with room for the output at `z` apart from both, it writes only the output
and stores `NLAlib.matMulWord`. -/
theorem matMulOn_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ} {x y z : ℕ × ℕ} {X : Matrix (Fin m) (Fin p) ℂ}
    {Y : Matrix (Fin p) (Fin q) ℂ} (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store)
    (hl : μ.Live [x, y, z]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (m * p))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, m, p, m, 0] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M X Y) μ'.store) μ :=
  sorry

/-- `NLAlib.matMulOn` with $c = 1$ on contiguous views, under the standard model (negation is
exact): from $\mathbf{X}$ ($p \times m$) at `x` and $\mathbf{Y}$ ($p \times q$) at `y`, it writes
only the output and stores `NLAlib.matMulWord` of $\mathbf{X}^{\mathsf H}$ and $\mathbf{Y}$. -/
theorem matMulOn_conjTranspose_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : Ops.StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ}
    {x y z : ℕ × ℕ} {X : Matrix (Fin p) (Fin m) ℂ} {Y : Matrix (Fin p) (Fin q) ℂ}
    (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store) (hl : μ.Live [x, y, z])
    (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (p * m))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, p, p, m, 1] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M Xᴴ Y) μ'.store) μ :=
  sorry

end Theorems

/-- One rounded multiply–add $s \mapsto \mathrm{fl}(xy + \hat 1 s)$, with $\hat 1$ the pair of the
literals $1$ and $0$, is within $5\boldsymbol{u}|x||y| + (6\boldsymbol{u} +
5\boldsymbol{u}^2)|s|$ of $xy + s$. -/
theorem Ops.StdModel.norm_linearComplex_one_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (x y s : ℂ) :
    ‖linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + s)‖ ≤
      5 * u * (‖x‖ * ‖y‖) + (6 * u + 5 * u ^ 2) * ‖s‖ := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : |M.lit 1 - 1| ≤ u := by simpa using hM.lit 1
  have hone : ‖(⟨M.lit 1, M.lit 0⟩ : ℂ) - 1‖ ≤ u := by
    rw [h0, show (⟨M.lit 1, 0⟩ : ℂ) - 1 = ((M.lit 1 - 1 : ℝ) : ℂ) by
      apply Complex.ext <;> simp, Complex.norm_real, Real.norm_eq_abs]
    exact h1
  have hn1 : ‖(⟨M.lit 1, M.lit 0⟩ : ℂ)‖ ≤ 1 + u := by
    have := norm_sub_norm_le (⟨M.lit 1, M.lit 0⟩ : ℂ) 1
    rw [norm_one] at this
    linarith
  have h := hM.norm_linearWords_sub_le hu0 hu x ⟨M.lit 1, M.lit 0⟩ y s
  have e : linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + s) =
      (linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + ⟨M.lit 1, M.lit 0⟩ * s)) +
        ((⟨M.lit 1, M.lit 0⟩ : ℂ) - 1) * s := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hs := norm_nonneg s
  have hxy := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have h' : ‖linearComplex M x ⟨M.lit 1, M.lit 0⟩ y s - (x * y + ⟨M.lit 1, M.lit 0⟩ * s)‖ ≤
      5 * u * (‖x‖ * ‖y‖ + ‖(⟨M.lit 1, M.lit 0⟩ : ℂ)‖ * ‖s‖) := h
  nlinarith [mul_le_mul_of_nonneg_right hn1 hs, mul_le_mul_of_nonneg_right hone hs]

/-- The norm of a sum over a list is at most the sum of the norms. -/
theorem norm_list_sum_map_le {ι : Type*} (f : ι → ℂ) (ls : List ι) :
    ‖(ls.map f).sum‖ ≤ (ls.map fun l => ‖f l‖).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

/-- **A rounded accumulation of products**: the multiply–adds of `NLAlib.matMulWord`, from the
pair of the literal $0$, over a list of indices, are within
$(1 + a)^k(5\boldsymbol{u}T + k a S)$ of the exact sum, $a = 6\boldsymbol{u} + 5\boldsymbol{u}^2$,
$k$ the length, $T$ the sum of $|x_l||y_l|$ and $S \ge T$. -/
theorem Ops.StdModel.norm_foldl_linearComplex_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) {ι : Type*} (x y : ι → ℂ)
    (ls : List ι) {S : ℝ} (hS : (ls.map fun l => ‖x l‖ * ‖y l‖).sum ≤ S) :
    ‖ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s)
        ⟨M.lit 0, M.lit 0⟩ - (ls.map fun l => x l * y l).sum‖ ≤
      (1 + (6 * u + 5 * u ^ 2)) ^ ls.length *
        (5 * u * (ls.map fun l => ‖x l‖ * ‖y l‖).sum + ls.length * (6 * u + 5 * u ^ 2) * S) := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  set a := 6 * u + 5 * u ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  induction ls using List.reverseRecOn with
  | nil => simp [h0]; rfl
  | append_singleton ls l ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at hS ⊢
    have hn := mul_nonneg (norm_nonneg (x l)) (norm_nonneg (y l))
    have ih := ih (by linarith)
    set s := ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s)
      ⟨M.lit 0, M.lit 0⟩
    set t := (ls.map fun l => x l * y l).sum
    set T := (ls.map fun l => ‖x l‖ * ‖y l‖).sum
    have hT0 : 0 ≤ T := List.sum_nonneg (by simp; intro _ _; positivity)
    have ht : ‖t‖ ≤ T := by
      refine (norm_list_sum_map_le _ ls).trans (le_of_eq ?_)
      simp [T, norm_mul]
    have hS0 : 0 ≤ S := by linarith
    have hstep := hM.norm_linearComplex_one_sub_le hu0 hu (x l) (y l) s
    have hs : ‖s‖ ≤ ‖t‖ + ‖s - t‖ := by
      have := norm_add_le t (s - t); rwa [add_sub_cancel] at this
    have e : linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (t + x l * y l) =
        (linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (x l * y l + s)) + (s - t) := by ring
    rw [e]
    rw [← ha] at hstep
    have hP : 1 ≤ (1 + a) ^ ls.length := one_le_pow₀ (by linarith)
    set P := (1 + a) ^ ls.length
    have hP' : (1 + a) ^ (ls.length + 1) = P * (1 + a) := pow_succ _ _
    rw [hP']
    refine (norm_add_le _ _).trans ?_
    push_cast
    have h1 : a * ‖s‖ ≤ a * (S + ‖s - t‖) := mul_le_mul_of_nonneg_left (by linarith) ha0
    have h3 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + a)
    have hq : 0 ≤ 5 * u * (‖x l‖ * ‖y l‖) + a * S := add_nonneg (by positivity) (mul_nonneg ha0 hS0)
    have h4 : 5 * u * (‖x l‖ * ‖y l‖) + a * S ≤ P * (1 + a) * (5 * u * (‖x l‖ * ‖y l‖) + a * S) :=
      le_mul_of_one_le_left hq (by nlinarith)
    have e2 : P * (1 + a) * (5 * u * (T + ‖x l‖ * ‖y l‖) + ((ls.length : ℝ) + 1) * a * S) =
        (1 + a) * (P * (5 * u * T + ls.length * a * S)) +
          P * (1 + a) * (5 * u * (‖x l‖ * ‖y l‖) + a * S) := by ring
    rw [e2]
    linarith

/-- The growth of an accumulation of $p$ products: with $a = 6\boldsymbol{u} +
5\boldsymbol{u}^2$ and $32(p + 1)\boldsymbol{u} \le 1$,
$(1 + a)^p(5\boldsymbol{u} + pa) \le 8(p + 1)\boldsymbol{u}$. -/
theorem matMul_growth_le {u : ℝ} {p : ℕ} (hu0 : 0 ≤ u) (hu : 32 * ((p : ℝ) + 1) * u ≤ 1) :
    (1 + (6 * u + 5 * u ^ 2)) ^ p * (5 * u + p * (6 * u + 5 * u ^ 2)) ≤ 8 * ((p : ℝ) + 1) * u := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hu32 : u ≤ 1 / 32 := by nlinarith
  have hpu : (p : ℝ) * u ≤ 1 / 32 := by nlinarith
  have hpa : (p : ℝ) * (6 * u + 5 * u ^ 2) ≤ (6 + 5 / 32) * ((p : ℝ) * u) := by
    nlinarith [mul_nonneg hp0 hu0, mul_nonneg (mul_nonneg hp0 hu0) hu0]
  have hpa0 : 0 ≤ (p : ℝ) * (6 * u + 5 * u ^ 2) := by positivity
  have hP := one_add_pow_sub_one_le (x := 6 * u + 5 * u ^ 2) (n := p) (by positivity)
    (by nlinarith)
  have hP2 : (1 + (6 * u + 5 * u ^ 2)) ^ p ≤ 5 / 4 := by nlinarith
  have hq : 0 ≤ 5 * u + p * (6 * u + 5 * u ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hP2 hq]

/-- **The error of a stored product** ([Higham2002, §3.5], complex, with the accumulation from a
rounded zero and a rounded unit): under the standard model at $\boldsymbol{u}$ with
$32(p + 1)\boldsymbol{u} \le 1$,
$\|\mathrm{fl}(\mathbf{X}\mathbf{Y}) - \mathbf{X}\mathbf{Y}\|_2 \le
8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$, $p$ the inner
dimension. Each multiply–add rounds the running sum four times (the product by the rounded unit,
the subtraction of the exact zero product, the sum), so a term passes through at most $4p$
roundings; the complex products contribute the factor $\sqrt 2$. -/
theorem Ops.StdModel.specNorm_matMulWord_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) {m p q : ℕ} (hu : 32 * ((p : ℝ) + 1) * u ≤ 1)
    (X : Matrix (Fin m) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ) :
    specNorm (matMulWord M X Y - X * Y) ≤ 8 * (p + 1) * u * (frobNorm X * frobNorm Y) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  set c := 8 * ((p : ℝ) + 1) * u with hc
  have hc0 : 0 ≤ c := by positivity
  set Xa : Matrix (Fin m) (Fin p) ℂ := Matrix.of fun i l => ((‖X i l‖ : ℝ) : ℂ)
  set Ya : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun l j => ((‖Y l j‖ : ℝ) : ℂ)
  have hXa : frobNorm Xa = frobNorm X := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Xa])
  have hYa : frobNorm Ya = frobNorm Y := le_antisymm
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
    (frobNorm_le_of_norm_apply_le fun i l => by simp [Ya])
  have hu8 : u ≤ 1 / 8 := by
    have : (1 : ℝ) ≤ (p : ℝ) + 1 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    nlinarith
  have hent : ∀ i j, ‖(matMulWord M X Y - X * Y) i j‖ ≤ ‖((c : ℂ) • (Xa * Ya)) i j‖ := by
    intro i j
    set T := ∑ l, ‖X i l‖ * ‖Y l j‖ with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
    have hTr : ‖((c : ℂ) • (Xa * Ya)) i j‖ = c * T := by
      have e : ((c : ℂ) • (Xa * Ya)) i j = ((c * T : ℝ) : ℂ) := by
        simp [Xa, Ya, Matrix.mul_apply, T]
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hTr]
    have hL : ((List.finRange p).map fun l => ‖X i l‖ * ‖Y l j‖).sum = T :=
      (Fin.sum_univ_def _).symm
    have hF := hM.norm_foldl_linearComplex_sub_le hu0 hu8 (X i) (fun l => Y l j)
      (List.finRange p) (le_of_eq hL)
    rw [hL, List.length_finRange] at hF
    have hE : (matMulWord M X Y - X * Y) i j = (List.finRange p).foldl
        (fun s l => linearComplex M (X i l) ⟨M.lit 1, M.lit 0⟩ (Y l j) s) ⟨M.lit 0, M.lit 0⟩ -
          ((List.finRange p).map fun l => X i l * Y l j).sum := by
      simp [matMulWord, Matrix.mul_apply, Fin.sum_univ_def]
    rw [hE]
    refine hF.trans ?_
    have hk := matMul_growth_le hu0 hu
    nlinarith [mul_le_mul_of_nonneg_right hk hT0]
  refine (specNorm_le_frobNorm _).trans ((frobNorm_le_of_norm_apply_le hent).trans ?_)
  rw [frobNorm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
  exact mul_le_mul_of_nonneg_left ((frobNorm_mul_le Xa Ya).trans (by rw [hXa, hYa])) hc0

end NLAlib
