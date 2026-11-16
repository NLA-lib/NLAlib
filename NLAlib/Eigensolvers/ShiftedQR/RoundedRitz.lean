/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Potential
public import NLAlib.Eigensolvers.ShiftedQR.Radius
public import NLAlib.Matrix.FinitePrecision.RootsRounded
public import NLAlib.Matrix.QRIteration.StableStep
public import NLAlib.Eigensolvers.ShiftedQR.RoundedRowPoly
public import NLAlib.Matrix.QRIteration.RoundedStrategy

/-!
# Rounded potentials, `comptau` and `Optimal`

The scalar decisions of the finite-precision shifting strategy
[BanksGarzaVargasSrivastava2022, §§4–5], computed on a machine with the standard model:

* the potential $\psi_k(\mathbf{H})$, $k = 2^q$, as $q + 1$ rounded square roots of the rounded
  product of the last $k$ squared subdiagonal moduli (`NLAlib.ShiftedQR.roundedPotential`),
  within $20\boldsymbol{u}\,\psi_k(\mathbf{H})$, relatively (the paper's
  (eq:boundonpottilde) has $0.001\,\psi_k/k$, which does not fit the exceptional radius window
  $\tilde R \le 2.002^{1/k}\theta\alpha B^{1/k}\psi_k$ for $k \ge 2$);
* `comptau`, the rounded $\prod_\ell \lvert(\widehat{\mathbf{R}}_\ell)_{nn}\rvert$ of the last
  diagonal entries of the triangular factors of a degree $k$ rounded step
  (`NLAlib.ShiftedQR.comptau`), within $0.001$, relatively, of
  $\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|_2^{-1}$;
* `Optimal` (`NLAlib.ShiftedQR.optimalTest`): the rounded row
  $\mathrm{fl}(\mathbf{e}_n^{\mathsf T}p(\mathbf{H}))$, its rounded norm, and the comparison with
  the rounded $0.999\theta^k\psi_k^k$, which decides $\theta$-optimality against
  $0.998^{1/k}\theta$-optimality.

The words are read with the loop rules of `NLAlib.Eigensolvers.ShiftedQR.RoundedModuli`
and the row recurrence of `NLAlib.Eigensolvers.ShiftedQR.RoundedRowPoly`.

## Main definitions

* `NLAlib.ShiftedQR.roundedPotential`, `NLAlib.ShiftedQR.comptau`,
  `NLAlib.ShiftedQR.optimalTest`: the programs.

## Main results

* `NLAlib.ShiftedQR.subdiagProduct_writes_word`: the bottom product on any scalar machine.
* `NLAlib.ShiftedQR.roundedPotential_writes`: the rounded potential within $20\boldsymbol{u}\psi_k$.
* `NLAlib.ShiftedQR.comptau_writes`: `comptau` within $0.001$.
* `NLAlib.ShiftedQR.norm_toLp_rowPolyVec_sub_aeval_le`: the rounded last row of a shift
  polynomial.
* `NLAlib.ShiftedQR.optimalTest_writes`: the guarantees of `Optimal`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The bottom-product round of the exact-arithmetic potential program
(`NLAlib.ShiftedQR.subdiagProductRound`) is a product round. -/
theorem subdiagProductRound_eq :
    (subdiagProductRound : Stmt Op Tst) = normSqMulRound
      ⟨0, .var 2 + .const 2 *
        ((.var 0 - .const 1 - .var 1 + .var 5) * .var 0 +
          (.var 0 - .const 1 - .var 1 + .var 5 + .const 1))⟩ ⟨1, .var 3⟩ ⟨2, .var 4⟩ := rfl

/-! ### The bottom product and the rounded potential -/

/-- The subdiagonal entry $\mathbf{H}_{i+1,i}$, clamped to the last row and column outside the
matrix (as the scan's words are). -/
def subdiagEntry {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : ℕ) : ℂ :=
  H ⟨min (i + 1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- At a subdiagonal position the clamped entry is the entry. -/
theorem subdiagEntry_of_lt {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {i : ℕ}
    (hi : i < n) : subdiagEntry H i = H (⟨i, hi⟩ : Fin n).succ (⟨i, hi⟩ : Fin n).castSucc := by
  simp only [subdiagEntry]
  congr 1 <;> ext <;> simp <;> omega

/-- The product of the last $k \le n$ squared subdiagonal moduli, over the clamped entries. -/
theorem prod_range_norm_subdiagEntry_sq {n k : ℕ} (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∏ j ∈ Finset.range k, ‖subdiagEntry H (n - k + j)‖ ^ 2 = subdiagNormSqProd k H := by
  rw [subdiagNormSqProd_eq_prod_range k hkn H]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : n - k + j < n := by have := Finset.mem_range.mp hj; omega
  rw [dif_pos hj', subdiagEntry_of_lt H hj']

/-- The bottom product on any scalar machine: `NLAlib.ShiftedQR.subdiagProductWithScratch`
stores the rounded product of the rounded literal $1$ and the machine squared moduli of the last
$k \le n$ subdiagonal entries, for the matrix at `A`, three scratch words at `T` and the output
`P`, pairwise disjoint; it writes only `P` and `T` and keeps the tape position. -/
theorem subdiagProductWithScratch_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a t p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hk : k ≤ n) (hH : HoldsMatrix a H m.store)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hp : p.2 < m.store.len p.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 3))
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1))
    (htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ subdiagProductWithScratch.body (Env.frame [n + 1, k] [a, t, p])
      (Store.inBlock p.1 p.2 1 ⊔ Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (prodWords M
        (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)) m := by
  unfold subdiagProductWithScratch
  refine (writes_call_const (hS (.lit 1)) rfl trivial hp).seq_le le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hOne⟩
  have hH₁ := hH.of_eqOff hfr₁ hap.symm
  let xs : ℕ → ℕ × ℕ := fun i => (a.1, a.2 + 2 * ((n - k + i) * (n + 1) + (n - k + i + 1)))
  have hloop := writes_loop_normSqMulRound (τ := τ) (m := m₁) (N := k) hS
    (ρ := Env.frame [n + 1, k] [a, t, p]) (cnt := .var 1) rfl
    (xs := xs) (tl := t) (pl := p) (R := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
    (z := fun j => subdiagEntry H (n - k + j)) (v := M.lit 1)
    (x := ⟨0, .var 2 + .const 2 *
        ((.var 0 - .const 1 - .var 1 + .var 5) * .var 0 +
          (.var 0 - .const 1 - .var 1 + .var 5 + .const 1))⟩) (t := ⟨1, .var 3⟩) (p := ⟨2, .var 4⟩)
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval, xs])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i hi => by
      have hq := Idx.add_lt_mul (show n - k + i < n + 1 by omega)
        (show n - k + i + 1 < n + 1 by omega)
      exact Fp.inBlock_le_inBlock (by simp only [xs]; omega) (by simp only [xs]; omega))
    (fun i hi => by
      have hi' : n - k + i < n := by omega
      have h := hH₁.get_re (⟨n - k + i, hi'⟩ : Fin n).succ (⟨n - k + i, hi'⟩ : Fin n).castSucc
      rw [subdiagEntry_of_lt H hi']
      simpa [xs] using h)
    (fun i hi => by
      have hi' : n - k + i < n := by omega
      have h := hH₁.get_im (⟨n - k + i, hi'⟩ : Fin n).succ (⟨n - k + i, hi'⟩ : Fin n).castSucc
      rw [subdiagEntry_of_lt H hi']
      simpa [xs, Nat.add_assoc] using h)
    (by rw [hfr₁.len_eq]; exact ht) hOne hat hap htp
  rw [subdiagProductRound_eq]
  exact hloop.mono le_rfl fun m' _ h => ⟨h.1.trans hp₁, h.2⟩

/-- The scoped bottom product on any scalar machine (`NLAlib.ShiftedQR.subdiagProduct`): the
word of `NLAlib.ShiftedQR.subdiagProductWithScratch_writes_word`, its scratch released. -/
theorem subdiagProduct_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hk : k ≤ n) (hH : HoldsMatrix a H m.store) (hp : p.2 < m.store.len p.1)
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ subdiagProduct.body (Env.frame [n + 1, k] [a, p])
      (Store.inBlock p.1 p.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (prodWords M
        (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)) m := by
  have hpl := Store.lt_length_of_lt_len hp
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  change Writes .total I τ (Stmt.allocs [.const 3] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [3]) rfl
    (fun hBelow h => ⟨h.1, ((hBelow p.1 hpl).2 p.2).trans h.2⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 3 := by simpa [t] using hlens 0 (by simp)
  have hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 3) := Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hbody := subdiagProductWithScratch_writes_word (τ := τ) (m := ⟨store, m.pos⟩)
    (t := t) hS hk (hH.of_below hBelow hal)
    (by dsimp [t]; simpa only [Nat.zero_add] using ht.ge)
    (by rw [(hBelow p.1 hpl).1]; exact hp) hat hap htp
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)) (fun _ _ h => h)

/-- $m$ machine square roots are the $m$-fold iterate of the machine square root. -/
theorem sqrtIter_eq_iterate {K : Type} (M : Machine K) (m : ℕ) (a : K) :
    sqrtIter M m a = M.sqrt^[m] a := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih => exact ih (M.sqrt a)

/-- The in-place square-root loop on any scalar machine stores $m$ machine square roots
(`NLAlib.sqrtIter`) of its word. -/
theorem squareRoots_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {x : ℕ × ℕ} {v : ℝ} (hx : m.store.get x.1 x.2 = some v) :
    Writes .total I τ squareRoots.body (Env.frame [k] [x, x]) (Store.inBlock x.1 x.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get x.1 x.2 = some (sqrtIter M k v)) m := by
  unfold squareRoots
  refine writes_loop rfl (fun _ => Store.inBlock x.1 x.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.get x.1 x.2 = some (M.sqrt^[i] v))
    (And.intro rfl hx) ?_ |>.mono le_rfl fun m' _ h => ⟨h.1, by rw [sqrtIter_eq_iterate]; exact h.2⟩
  intro i _ m' _ ⟨hp, hVal⟩
  refine (writes_call_un (hS .sqrt) rfl rfl trivial hVal rfl
    (Store.lt_len_of_get hVal)).mono le_rfl ?_
  intro m'' _ ⟨hp', hSqrt⟩
  exact ⟨hp'.trans hp, by simpa only [Function.iterate_succ_apply'] using hSqrt⟩

/-- **The rounded potential** of the last $k = 2^q$ subdiagonal entries of an order-$n$ matrix
`A` into the word `P`: the rounded bottom product of squared moduli, then $q + 1$ square roots
in place. The interface is `[n, k, q] (A) → (P)`. -/
def roundedPotential : Impl Op Tst := opsImpl% [n, k, q] (A) → (P) {
  run subdiagProduct.body [n, k] (A, P);
  run squareRoots.body [q + 1] (P, P)
}

/-- The word the rounded potential stores: $q + 1$ machine square roots of the rounded bottom
product. -/
def roundedPotentialWord (M : Machine ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (k q : ℕ) : ℝ :=
  sqrtIter M (q + 1)
    (prodWords M (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)

/-- The program of the rounded potential stores `NLAlib.ShiftedQR.roundedPotentialWord` on any
scalar machine, and writes only its output word. -/
theorem roundedPotential_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {μ : Mem ℝ}
    {n k q : ℕ} {a p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hk : k ≤ n) (hH : HoldsMatrix a H μ.store) (hp : p.2 < μ.store.len p.1)
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ roundedPotential.body (Env.frame [n + 1, k, q] [a, p])
      (Store.inBlock p.1 p.2 1)
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.store.get p.1 p.2 = some (roundedPotentialWord M H k q)) μ := by
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  have hpl := Store.lt_length_of_lt_len hp
  unfold roundedPotential
  refine (subdiagProduct_writes_word (τ := τ) hS hk hH hp hap).frame_seq_le rfl rfl
    (by simp [Mem.Live, hal, hpl]) le_rfl ?_
  intro μ₁ _ ⟨hp₁, hP₁⟩
  refine ((squareRoots_writes_word (τ := τ) (k := q + 1) hS hP₁).in_frame rfl rfl
    (by simpa [Mem.Live] using Store.lt_length_of_get hP₁)).mono le_rfl ?_
  intro μ₂ _ ⟨hp₂, hR₂⟩
  exact ⟨hp₂.trans hp₁, hR₂⟩

/-- **The rounded potential is within $20\boldsymbol{u}\,\psi_k$**: under the standard model
with $20000\,k\boldsymbol{u} \le 1$, for $k = 2^q \le n$ the word
`NLAlib.ShiftedQR.roundedPotentialWord` ($q + 1$ rounded square roots of the rounded product of
the last $k$ squared subdiagonal moduli of $\mathbf{H}$) satisfies
$$\lvert\tilde\psi - \psi_k(\mathbf{H})\rvert \le 20\boldsymbol{u}\,\psi_k(\mathbf{H}):$$
$8(k + 1)\boldsymbol{u}$ in the product, divided by $2k$ in the root, and $3\boldsymbol{u}$ for
the rounded roots. This is at most the $0.001\,\psi_k/k$ of [BanksGarzaVargasSrivastava2022,
(eq:boundonpottilde)], where $\psi_k^k$ is taken as exact. -/
theorem abs_roundedPotentialWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {n k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) (hu : 20000 * k * u ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    |roundedPotentialWord M H k q - hessenbergPotential k H| ≤
      20 * u * hessenbergPotential k H := by
  have hu0 := hM.roundoff_nonneg
  have hk1 : 1 ≤ k := hkq ▸ Nat.one_le_two_pow
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set ψ := hessenbergPotential k H
  have hψ := hessenbergPotential_nonneg k H
  set P := subdiagNormSqProd k H
  have hPψ : P = ψ ^ (2 * k) := by
    simp only [P, ψ]
    rw [mul_comm, pow_mul, hessenbergPotential_pow (by omega), subdiagNormSqProd,
      Finset.prod_pow]
  set x := prodWords M (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k
  set y : ℝ := 8 * (k + 1) * u
  have hy0 : 0 ≤ y := by positivity
  have hyk : y ≤ 16 * k * u := by simp only [y]; nlinarith
  obtain ⟨hlo, hhi⟩ := prodWords_normSqFactors_bounds hM (k := k)
    (by nlinarith) (fun j => subdiagEntry H (n - k + j))
  rw [prod_range_norm_subdiagEntry_sq hkn H] at hlo hhi
  have hP0 : 0 ≤ P := hPψ ▸ by positivity
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (by nlinarith) hP0) hlo
  have hK := hM.abs_sqrtIter_sub_le hu0 (by nlinarith) (q + 1) hx0
  have he : ((2 : ℝ) ^ (q + 1))⁻¹ = (((2 * k : ℕ) : ℝ))⁻¹ := by
    rw [hkq]; push_cast; ring
  rw [he] at hK
  have hroot := abs_rpow_inv_natCast_sub_le (p := 2 * k) (by omega) hP0 hy0 (by nlinarith)
    hlo hhi
  have hPr : P ^ (((2 * k : ℕ) : ℝ))⁻¹ = ψ := by
    rw [hPψ]; exact Real.pow_rpow_inv_natCast hψ (by omega)
  rw [hPr] at hroot
  set r := x ^ (((2 * k : ℕ) : ℝ))⁻¹
  have hyk' : 2 * y / ((2 * k : ℕ) : ℝ) ≤ 16 * u := by
    push_cast
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hr1 : r ≤ (1 + 16 * u) * ψ := by
    have := (abs_le.mp hroot).2
    nlinarith [mul_le_mul_of_nonneg_right hyk' hψ]
  have hw : roundedPotentialWord M H k q = sqrtIter M (q + 1) x := rfl
  rw [hw]
  have hfin : |sqrtIter M (q + 1) x - ψ| ≤ 20 * u * ψ := by
    have h1 := abs_sub_le (sqrtIter M (q + 1) x) r ψ
    have h2 : 3 * u * r ≤ 3 * u * ((1 + 16 * u) * ψ) :=
      mul_le_mul_of_nonneg_left hr1 (by positivity)
    have h3 : 2 * y / ((2 * k : ℕ) : ℝ) * ψ ≤ 16 * u * ψ :=
      mul_le_mul_of_nonneg_right hyk' hψ
    have h4 : u ≤ 1 / 48 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hu0 hu0) hψ, mul_nonneg hu0 hψ]
  exact hfin

/-- **The rounded potential** ([BanksGarzaVargasSrivastava2022, (eq:boundonpottilde)]): on a
scalar machine with the standard model at $20000\,k\boldsymbol{u} \le 1$, for $k = 2^q \le n$ and
an order-$(n + 1)$ matrix $\mathbf{H}$ stored at `A`, the program `roundedPotential` writes only
its output word, and stores there a $\tilde\psi$ with
$$\lvert\tilde\psi - \psi_k(\mathbf{H})\rvert \le 20\boldsymbol{u}\,\psi_k(\mathbf{H}).$$
The relative error $20\boldsymbol{u}$ is exposed, not the paper's $0.001/k$ (which it implies
here): the radius word $\mathrm{fl}(2^{1/k}\theta\alpha B^{1/k}\tilde\psi)$ meets the exceptional
radius window $[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k$ for every $k \ge 1$ under,
for instance, $10^5 k\boldsymbol{u} \le 1$, which $0.001/k$ does not give for $k \ge 2$. Matrix
and output are disjoint views. -/
theorem roundedPotential_writes {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ}
    {n k q : ℕ} {a p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hkq : k = 2 ^ q) (hkn : k ≤ n) (hu : 20000 * k * u ≤ 1)
    (hH : HoldsMatrix a H μ.store) (hp : p.2 < μ.store.len p.1)
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ roundedPotential.body (Env.frame [n + 1, k, q] [a, p])
      (Store.inBlock p.1 p.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ψ : ℝ, μ'.store.get p.1 p.2 = some ψ ∧
        |ψ - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H) μ :=
  (roundedPotential_writes_word (τ := τ) hS hkn hH hp hap).mono le_rfl fun _ _ h =>
    ⟨h.1, _, h.2, abs_roundedPotentialWord_sub_le hM hkq hkn hu H⟩

/-! ### `comptau` -/

/-- A product over the positions of a list is the product of the mapped list. -/
theorem prod_range_getD_eq_prod_map (zs : List ℂ) (f : ℂ → ℝ) :
    ∏ j ∈ Finset.range zs.length, f (zs.getD j 0) = (zs.map f).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons, ← ih]
    simp [mul_comm]

/-- `comptau` with a caller-owned scratch view of three words: the rounded literal $1$, times
the machine squared moduli of the $k$ pairs of `D`, then one square root. The interface is
`[k] (D, T) → (P)`. -/
def comptauWithScratch : Impl Op Tst := opsImpl% [k] (D, T) → (P) {
  call (Has.inj (ScalarOp.lit 1)) [] () → (P);
  for j < k {
    run PairScalar.normSq.body [] (D[2 * j], T);
    call (Has.inj ScalarOp.mul) [] (P, T[2]) → (P)
  };
  call (Has.inj ScalarOp.sqrt) [] (P) → (P)
}

/-- **`comptau`** ([BanksGarzaVargasSrivastava2022, Lemma 3.9]): the rounded
$\prod_\ell\lvert d_\ell\rvert$ of the $k$ complex numbers stored as pairs in `D` (the last
diagonal entries of the triangular factors of a degree $k$ step), with three scratch words.
The interface is `[k] (D) → (P)`. -/
def comptau : Impl Op Tst := opsImpl% [k] (D) → (P) {
  let T ← alloc 3;
  run comptauWithScratch.body [k] (D, T, P)
}

/-- The word `comptau` stores: the machine square root of the rounded product of the rounded
literal $1$ and the machine squared moduli of the entries of `zs`. -/
def comptauWord (M : Machine ℝ) (zs : List ℂ) : ℝ :=
  M.sqrt (prodWords M (normSqFactors M (M.lit 1) fun j => zs.getD j 0) zs.length)

/-- `comptau` on any scalar machine stores `NLAlib.ShiftedQR.comptauWord` of the stored pairs
and writes only its output word. The pairs and the output are disjoint views. -/
theorem comptau_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {zs : List ℂ} {d p : ℕ × ℕ}
    (hD : m.store.readBlock d.1 d.2 (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]))
    (hl : m.Live [d, p]) (hp : p.2 < m.store.len p.1)
    (hdp : Fp.Disj (Store.inBlock d.1 d.2 (2 * zs.length)) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ comptau.body (Env.frame [zs.length] [d, p]) (Store.inBlock p.1 p.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (comptauWord M zs)) m := by
  have hpl := Store.lt_length_of_lt_len hp
  have hdl : d.1 < m.store.length := hl d (by simp)
  change Writes .total I τ (Stmt.allocs [.const 3] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [3]) rfl
    (fun hBelow h => ⟨h.1, ((hBelow p.1 hpl).2 p.2).trans h.2⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 3 := by simpa [t] using hlens 0 (by simp)
  have hdt : Fp.Disj (Store.inBlock d.1 d.2 (2 * zs.length)) (Store.inBlock t.1 t.2 3) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hD' : store.readBlock d.1 d.2 (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]) :=
    hBelow.readBlock_of hdl hD
  have hp' : p.2 < store.len p.1 := by rw [(hBelow p.1 hpl).1]; exact hp
  have hbody : Writes .total I τ comptauWithScratch.body
      (Env.frame [zs.length] [d, t, p]) (Store.inBlock p.1 p.2 1 ⊔ Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (comptauWord M zs))
      ⟨store, m.pos⟩ := by
    unfold comptauWithScratch
    refine (writes_call_const (hS (.lit 1)) rfl trivial hp').seq_le le_sup_left ?_
    intro m₁ hfr₁ ⟨hp₁, hOne⟩
    have hD₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) hdp.symm hD'
    have hloop := writes_loop_normSqMulRound (τ := τ) (m := m₁) (N := zs.length) hS
      (ρ := Env.frame [zs.length] [d, t, p]) (cnt := .var 0) rfl
      (xs := fun i => (d.1, d.2 + 2 * i)) (tl := t) (pl := p)
      (R := Store.inBlock d.1 d.2 (2 * zs.length)) (z := fun j => zs.getD j 0) (v := M.lit 1)
      (x := ⟨0, .var 1 + .const 2 * .var 4⟩) (t := ⟨1, .var 2⟩) (p := ⟨2, .var 3⟩)
      (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (fun i hi => Fp.inBlock_le_inBlock (by omega) (by omega))
      (fun i hi => by
        have h := Store.get_of_readBlock hD₁ (j := 2 * i) (by omega) 0
        rw [(getD_flatMap_pair zs hi).1] at h; exact h)
      (fun i hi => by
        have h := Store.get_of_readBlock hD₁ (j := 2 * i + 1) (by omega) 0
        rw [(getD_flatMap_pair zs hi).2] at h; simpa [Nat.add_assoc] using h)
      (by rw [hfr₁.len_eq]; simp only [t] at ht ⊢; omega) hOne hdt hdp htp
    refine (hloop.seq_le le_rfl ?_)
    intro m₂ _ ⟨hp₂, hP₂⟩
    refine (writes_call_un (hS .sqrt) rfl rfl trivial hP₂ rfl
      (Store.lt_len_of_get hP₂)).mono le_sup_left ?_
    intro m₃ _ ⟨hp₃, hR₃⟩
    exact ⟨hp₃.trans (hp₂.trans hp₁), hR₃⟩
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)) (fun _ _ h => h)

/-- The rounded product of moduli of a list: under the standard model with
$30000(k + 1)\boldsymbol{u} \le 1$, the word `NLAlib.ShiftedQR.comptauWord` of $k$ complex
numbers $d_1, \dots, d_k$ is within $10(k + 1)\boldsymbol{u}$, relatively, of
$\prod_\ell \lvert d_\ell\rvert$. -/
theorem abs_comptauWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (zs : List ℂ)
    (hu : 30000 * (zs.length + 1) * u ≤ 1) :
    |comptauWord M zs - (zs.map fun z => ‖z‖).prod| ≤
      10 * (zs.length + 1) * u * (zs.map fun z => ‖z‖).prod := by
  have h := abs_sqrt_prodWords_normSqFactors_sub_le hM (fun j => zs.getD j 0) hu
  rwa [prod_range_getD_eq_prod_map zs fun z => ‖z‖] at h

/-- **`comptau` is within $0.001$** ([BanksGarzaVargasSrivastava2022, Lemma 3.9], corrected: the
precision condition has $8004\kappa$ from a direct bound on the last diagonal entries, where the
paper's route through Lemma 3.7 needs $\kappa^2$ and $24000$): let
$\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with $\kappa(\mathbf{V}) \le \kappa$,
$\mathbf{H} \ne 0$, the shifts $s_1, \dots, s_k$ in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and at
distance at least $d > 0$ from every eigenvalue, the triangular factors
$\widehat{\mathbf{R}}_1, \dots, \widehat{\mathbf{R}}_k$ those of a backward-stable chain of relative
error $x \le (8004\kappa)^{-1}(d/((2 + 2C)\|\mathbf{H}\|_2))^k$, their last diagonal entries stored
as pairs in `D`, and the machine the standard model with $30000(k + 1)\boldsymbol{u} \le 1$. Then
`comptau` writes only its output word and stores there a $t$ with
$$\lvert t - \tau\rvert \le 0.001\,\tau, \qquad
\tau = \|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|_2^{-1},$$
$p(z) = \prod_\ell (z - s_\ell)$: the $0.0006$ of the exact factors plus the rounded product and
root. The pairs and the output are disjoint views. -/
theorem comptau_writes {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ}
    {n : ℕ} {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    {ds p : ℕ × ℕ}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hxu : x ≤ (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length)
    (hu : 30000 * (ss.length + 1) * u ≤ 1) (hlen : Rs.length = ss.length)
    (hD : μ.store.readBlock ds.1 ds.2 (2 * ss.length) = some (Rs.flatMap fun R =>
      [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]))
    (hl : μ.Live [ds, p]) (hp : p.2 < μ.store.len p.1)
    (hdp : Fp.Disj (Store.inBlock ds.1 ds.2 (2 * ss.length)) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ comptau.body (Env.frame [ss.length] [ds, p]) (Store.inBlock p.1 p.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get p.1 p.2 = some t ∧
        |t - ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹| ≤
          0.001 * ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹) μ := by
  set zs := Rs.map fun R => R (Fin.last n) (Fin.last n)
  have hzl : zs.length = ss.length := by simp [zs, hlen]
  have hfm : (zs.flatMap fun z => [z.re, z.im]) = Rs.flatMap fun R =>
      [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im] := by
    simp [zs, List.flatMap_map]
  have hw := comptau_writes_word (τ := τ) (zs := zs) hS (hzl ▸ hfm ▸ hD) hl hp (hzl ▸ hdp)
  rw [hzl] at hw
  refine hw.mono le_rfl fun μ' _ hμ => ⟨hμ.1, _, hμ.2, ?_⟩
  set X := ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹
  have hQ5 := h.abs_prod_last_sub_le hx hC hd hH0 hV hHV hκ hs hdist hxu
  have hT : (zs.map fun z => ‖z‖) = Rs.map fun R => ‖R (Fin.last n) (Fin.last n)‖ := by
    simp [zs, Function.comp_def]
  have hc := abs_comptauWord_sub_le hM zs (by rw [hzl]; exact hu)
  rw [hT, hzl] at hc
  set T := (Rs.map fun R => ‖R (Fin.last n) (Fin.last n)‖).prod
  have hX : 0 ≤ X := inv_nonneg.mpr (norm_nonneg _)
  have hTX : T ≤ 1.0006 * X := by linarith [(abs_le.mp hQ5).2]
  have hu0 := hM.roundoff_nonneg
  have hk : 10 * ((ss.length : ℝ) + 1) * u ≤ 1 / 3000 := by nlinarith
  have h1 := abs_sub_le (comptauWord M zs) T X
  have h2 : 10 * ((ss.length : ℝ) + 1) * u * T ≤ 1 / 3000 * (1.0006 * X) :=
    mul_le_mul hk hTX (List.prod_nonneg fun _ h => by
      obtain ⟨R, -, rfl⟩ := List.mem_map.mp h; exact norm_nonneg _) (by norm_num)
  linarith

/-! ### `Optimal` -/

section Optimal

variable [Has CmpTst Tst]

/-- **The decision of `Optimal`**: the rounded norm $t$ of the stored row `V` (three scratch
words `U`, into `Q[0]`), the threshold $\mathrm{fl}(c\,\mathrm{fl}(\sqrt{\cdot}))$ of the rounded
bottom product of the order-$n$ matrix `A` and the stored word `C` (into `Q[1]`), and the flag
`F` set to the literal $1$ if $t$ is below the threshold, to $0$ otherwise. The interface is
`[n, k] (A, C, V, U, Q) → (F)`. -/
def optimalDecide : Impl Op Tst := opsImpl% [n, k] (A, C, V, U, Q) → (F) {
  run pairVecNormWithScratch.body [n] (V, U, Q);
  run subdiagProduct.body [n, k] (A, Q[1]);
  call (Has.inj ScalarOp.sqrt) [] (Q[1]) → (Q[1]);
  call (Has.inj ScalarOp.mul) [] (C, Q[1]) → (Q[1]);
  if (Has.inj CmpTst.lt) [] (Q, Q[1]) {
    call (Has.inj (ScalarOp.lit 1)) [] () → (F)
  } else {
    call (Has.inj (ScalarOp.lit 0)) [] () → (F)
  }
}

/-- The threshold word of `NLAlib.ShiftedQR.optimalDecide`: the stored word $c$ times the rounded
square root of the rounded bottom product. -/
def optimalThresholdWord (M : Machine ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (k : ℕ) (c : ℝ) : ℝ :=
  M.mul c (M.sqrt (prodWords M (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k))

open Classical in
/-- The decision of `Optimal` on any scalar machine with exact comparisons: `optimalDecide` sets
the flag to the literal $1$ if the rounded norm `NLAlib.ShiftedQR.pairVecNormWord` of the stored
row is below `NLAlib.ShiftedQR.optimalThresholdWord`, to the literal $0$ otherwise, and writes only
the flag and its scratch. -/
theorem optimalDecide_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ}
    {a c v w q f : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : Fin (n + 1) → ℂ}
    {cv : ℝ} (hk : k ≤ n) (hH : HoldsMatrix a H m.store) (hc : m.store.get c.1 c.2 = some cv)
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r) m.store)
    (hw : w.2 + 3 ≤ m.store.len w.1) (hq : q.2 + 2 ≤ m.store.len q.1)
    (hf : f.2 < m.store.len f.1) (hl : m.Live [a, c, v, w, q, f])
    (hsep : Fp.Disj (Store.inBlock w.1 w.2 3 ⊔ Store.inBlock q.1 q.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock c.1 c.2 1 ⊔
        Store.inBlock v.1 v.2 (2 * (1 * (n + 1)))))
    (hwq : Fp.Disj (Store.inBlock w.1 w.2 3) (Store.inBlock q.1 q.2 2)) :
    Writes .total I τ (optimalDecide (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, k] [a, c, v, w, q, f])
      (Store.inBlock w.1 w.2 3 ⊔ Store.inBlock q.1 q.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 = some
        (if pairVecNormWord M r < optimalThresholdWord M H k cv then M.lit 1 else M.lit 0)) m := by
  have hlive : a.1 < m.store.length ∧ c.1 < m.store.length ∧ v.1 < m.store.length ∧
      w.1 < m.store.length ∧ q.1 < m.store.length ∧ f.1 < m.store.length := by
    simpa [Mem.Live] using hl
  have hq0 : Fp.Disj (Store.inBlock q.1 q.2 1) (Store.inBlock q.1 (q.2 + 1) 1) :=
    Fp.disj_inBlock_of_le le_rfl
  unfold optimalDecide
  have hn := pairVecNormWithScratch_writes_word (τ := τ) (m := m) (t := w) (p := q) hS hV hw
    (by omega) (hsep.symm.mono (by fp_sub) (by fp_sub))
    (hsep.symm.mono (by fp_sub) (by fp_sub)) (hwq.mono le_rfl (by fp_sub))
  refine hn.frame_seq_le rfl rfl (by simp [Mem.Live, hlive]) (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hN₁⟩
  have hH₁ := hH.of_eqOff hfr₁ (hsep.mono (by fp_sub) (by fp_sub))
  have hc₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hsep.mono (by fp_sub) (by fp_sub)) hc
  have hpr := subdiagProduct_writes_word (τ := τ) (m := m₁) (p := (q.1, q.2 + 1)) hS hk hH₁
    (by rw [hfr₁.len_eq]; dsimp only; omega) (hsep.symm.mono (by fp_sub) (by fp_sub))
  refine hpr.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hlive]) (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hP₂⟩
  have hN₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hq0.symm.mono le_rfl (by fp_sub)) hN₁
  have hc₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hsep.mono (by fp_sub) (by fp_sub)) hc₁
  refine (writes_call_un (hS .sqrt) (x := (q.1, q.2 + 1)) (z := (q.1, q.2 + 1)) rfl rfl trivial
    hP₂ rfl (Store.lt_len_of_get hP₂)).seq_le (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hR₃⟩
  have hN₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hq0.symm hN₂
  have hc₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (hsep.mono (by fp_sub) (by fp_sub)) hc₂
  refine (writes_call_bin (hS .mul) (x := c) (y := (q.1, q.2 + 1)) (z := (q.1, q.2 + 1)) rfl rfl
    trivial hc₃ hR₃ rfl (fun _ => ⟨by simp [Mem.Live, Store.lt_length_of_get hc₃,
      Store.lt_length_of_get hR₃], Store.lt_len_of_get hR₃⟩)).seq_le (by fp_sub) ?_
  intro m₄ hfr₄ ⟨hp₄, hT₄⟩
  have hN₄ := hfr₄.keep (Store.readsOnly_get _ _ _) hq0.symm hN₃
  have hfl : f.2 < m₄.store.len f.1 := by
    rw [hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hf
  refine writes_ite rfl rfl (hC.test_lt (d := []) hN₄ hT₄) ?_
  simp only [id_eq, decide_eq_true_eq]
  have hpos : m₄.pos = m.pos := hp₄.trans (hp₃.trans (hp₂.trans hp₁))
  by_cases hlt : pairVecNormWord M r < optimalThresholdWord M H k cv
  · have hlt' : pairVecNormWord M r < M.mul cv (M.sqrt (prodWords M
        (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)) := hlt
    rw [if_pos hlt', if_pos hlt]
    exact (writes_call_const (hS (.lit 1)) (z := f) (out := ⟨5, .var 7⟩) rfl trivial hfl).mono
      (by fp_sub) fun m₅ _ ⟨hp₅, hF⟩ => ⟨hp₅.trans hpos, hF⟩
  · have hlt' : ¬ pairVecNormWord M r < M.mul cv (M.sqrt (prodWords M
        (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)) := hlt
    rw [if_neg hlt', if_neg hlt]
    exact (writes_call_const (hS (.lit 0)) (z := f) (out := ⟨5, .var 7⟩) rfl trivial hfl).mono
      (by fp_sub) fun m₅ _ ⟨hp₅, hF⟩ => ⟨hp₅.trans hpos, hF⟩

end Optimal

section OptimalTest

variable [Has CmpTst Tst]

/-- `Optimal` with caller-owned scratch: the row recurrence from $\mathbf{e}_n$
(`NLAlib.ShiftedQR.rowInit`, `NLAlib.ShiftedQR.rowPolyLoop`) and the decision
(`NLAlib.ShiftedQR.optimalDecide`). The interface is
`[n, k] (A, S, C, V, Y, W, O, T, Z, U, Q) → (F)`. -/
def optimalTestWithScratch : Impl Op Tst :=
  opsImpl% [n, k] (A, S, C, V, Y, W, O, T, Z, U, Q) → (F) {
    run rowInit.body [n] (V, O);
    run rowPolyLoop.body [n, k] (V, A, S, O, W, T, Z, Y, V);
    run optimalDecide.body [n, k] (A, C, V, U, Q, F)
  }

/-- **`Optimal`** ([BanksGarzaVargasSrivastava2022, §4]): for the order-$n$ matrix `A`, the $k$
shifts stored as pairs at `S` and the threshold factor `C` (the word $0.999\theta^k$), the flag
`F` is the literal $1$ if the rounded $\|\mathrm{fl}(\mathbf{e}_n^{\mathsf T}p(\mathbf{A}))\|$
is below the rounded $c\,\psi_k(\mathbf{A})^k$, and $0$ otherwise. All scratch is scoped. The
interface is `[n, k] (A, S, C) → (F)`. -/
def optimalTest : Impl Op Tst := opsImpl% [n, k] (A, S, C) → (F) {
  let V ← alloc (2 * n);
  let Y ← alloc (2 * n);
  let W ← alloc (2 * (n * n));
  let O ← alloc 2;
  let T ← alloc 2;
  let Z ← alloc 2;
  let U ← alloc 3;
  let Q ← alloc 2;
  run optimalTestWithScratch.body [n, k] (A, S, C, V, Y, W, O, T, Z, U, Q, F)
}

/-- The flag word `Optimal` stores, on the machine `M`. -/
noncomputable def optimalTestWord (M : Machine ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (c : ℝ) : ℝ :=
  if pairVecNormWord M (rowPolyVec M (M.lit 1, M.lit 0) H ss (rowInitVec M n) ss.length) <
      optimalThresholdWord M H ss.length c then M.lit 1 else M.lit 0

/-- `Optimal` with scratch in fresh buffers `L, …, L + 7` (offset $0$, as an allocation gives
them) on any scalar machine with exact comparisons: it stores `NLAlib.ShiftedQR.optimalTestWord`
in `F` and writes only `F` and the scratch. -/
theorem optimalTestWithScratch_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n L : ℕ}
    {a s c f : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {cv : ℝ}
    (hk : ss.length ≤ n) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) = some (ss.flatMap fun z => [z.re, z.im]))
    (hc : m.store.get c.1 c.2 = some cv) (hf : f.2 < m.store.len f.1)
    (ha : a.1 < L) (hsL : s.1 < L) (hcL : c.1 < L) (hfL : f.1 < L)
    (hlen : m.store.length = L + 8) (hv : m.store.len L = 2 * (n + 1))
    (hy : m.store.len (L + 1) = 2 * (n + 1)) (hw : m.store.len (L + 2) = 2 * ((n + 1) * (n + 1)))
    (ho : m.store.len (L + 3) = 2) (ht : m.store.len (L + 4) = 2)
    (hz : m.store.len (L + 5) = 2) (hu : m.store.len (L + 6) = 3)
    (hq : m.store.len (L + 7) = 2)
    (has : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock c.1 c.2 1)) :
    Writes .total I τ (optimalTestWithScratch (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, ss.length] [a, s, c, (L, 0), (L + 1, 0), (L + 2, 0), (L + 3, 0),
        (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), f])
      (Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 = some (optimalTestWord M H ss cv)) m := by
  have hal : a.1 < m.store.length := by omega
  unfold optimalTestWithScratch
  have hi := rowInit_writes_word (τ := τ) (m := m) (n := n) (v := (L, 0)) (o := (L + 3, 0)) hS
    (by simp [hv]) (by simp [ho]) (by disjoint)
  refine hi.frame_seq_le rfl rfl (by simp [Mem.Live]; omega)
    (by intro b x hx; simp [fpNF] at hx ⊢; omega) ?_
  intro m₁ hfr₁ ⟨hp₁, hV₁, hO₁⟩
  have hl₁ : ∀ b, m₁.store.len b = m.store.len b := hfr₁.len_eq
  have hH₁ := hH.of_eqOff hfr₁ (by disjoint)
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs
  have hrp := rowPolyLoop_writes_word (τ := τ) (m := m₁) (v := (L, 0)) (a := a) (s := s)
    (o := (L + 3, 0)) (w := (L + 2, 0)) (t := (L + 4, 0)) (z := (L + 5, 0)) (y := (L + 1, 0))
    (oo := (M.lit 1, M.lit 0)) hS hV₁ hH₁ hs₁ hO₁ (by simp [hl₁, hw]) (by simp [hl₁, ht])
    (by simp [hl₁, hz]) (by simp [hl₁, hy]) (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
    (by disjoint) (by disjoint)
  refine hrp.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (by intro b x hx; simp [fpNF] at hx ⊢; omega) ?_
  intro m₂ hfr₂ ⟨hp₂, hV₂⟩
  have hl₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by rw [hfr₂.len_eq, hl₁]
  have hH₂ := hH₁.of_eqOff hfr₂ (by disjoint)
  have hc₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint)
    (hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hc)
  have hd := optimalDecide_writes_word (τ := τ) (m := m₂) (a := a) (c := c) (v := (L, 0))
    (w := (L + 6, 0)) (q := (L + 7, 0)) (f := f) hS hC hk hH₂ hc₂ hV₂ (by simp [hl₂, hu])
    (by simp [hl₂, hq]) (by rw [hl₂]; exact hf)
    (by simp [Mem.Live, hfr₁.length_eq, hfr₂.length_eq]; omega)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr
      ⟨has.mono le_rfl (by fp_sub), has.mono le_rfl (by fp_sub)⟩, by disjoint⟩⟩)
    (by disjoint)
  refine (hd.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hfr₂.length_eq]; omega)).mono
    (by intro b x hx; simp [fpNF] at hx ⊢; omega) ?_
  intro m₃ _ ⟨hp₃, hF₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hF₃⟩


/-- `Optimal` on any scalar machine with exact comparisons: with the order-$(n+1)$ matrix
$\mathbf{H}$ at `A`, the shifts `ss` ($k \le n$ of them) stored as pairs at `S`, the word $c$ at
`C`, and the flag word apart from these, `optimalTest` stores
`NLAlib.ShiftedQR.optimalTestWord` in `F` and writes only `F`. -/
theorem optimalTest_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ}
    {a s c f : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {cv : ℝ}
    (hk : ss.length ≤ n) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) = some (ss.flatMap fun z => [z.re, z.im]))
    (hc : m.store.get c.1 c.2 = some cv) (hf : f.2 < m.store.len f.1) (hl : m.Live [a, s, c, f])
    (has : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock c.1 c.2 1)) :
    Writes .total I τ (optimalTest (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, ss.length] [a, s, c, f]) (Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 = some (optimalTestWord M H ss cv)) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ c.1 < m.store.length ∧
      f.1 < m.store.length := by simpa [Mem.Live] using hl
  unfold optimalTest
  allocs_preserving [2 * (n + 1), 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2, 2, 2, 3, 2]
  case sizes => rfl
  case keep =>
    intro s s' p hBelow hp
    exact ⟨hp.1, ((hBelow f.1 hlive.2.2.2).2 f.2).trans hp.2⟩
  intro store hlen hlens hBelow
  have hl8 := fun i (hi : i < 8) => hlens i (by simpa using hi)
  have hw := optimalTestWithScratch_writes_word (τ := τ) (m := ⟨store, m.pos⟩)
    (L := m.store.length) hS hC hk (hH.of_below hBelow hlive.1)
    (hBelow.readBlock_of hlive.2.1 hs) (((hBelow c.1 hlive.2.2.1).2 c.2).trans hc)
    (by rw [(hBelow f.1 hlive.2.2.2).1]; exact hf) hlive.1 hlive.2.1 hlive.2.2.1 hlive.2.2.2
    (by simpa using hlen) (by simpa using hl8 0 (by norm_num))
    (by simpa using hl8 1 (by norm_num)) (by simpa using hl8 2 (by norm_num))
    (by simpa using hl8 3 (by norm_num)) (by simpa using hl8 4 (by norm_num))
    (by simpa using hl8 5 (by norm_num)) (by simpa using hl8 6 (by norm_num))
    (by simpa using hl8 7 (by norm_num)) has
  exact (hw.in_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (by simp [Mem.Live, hlen]; omega)).mono le_rfl fun _ _ h => h

end OptimalTest

/-! ### The guarantees of `Optimal` -/

/-- The product of the last $k \le n$ subdiagonal moduli is $\psi_k(\mathbf{H})^k$. -/
theorem prod_range_norm_subdiagEntry {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∏ j ∈ Finset.range k, ‖subdiagEntry H (n - k + j)‖ = hessenbergPotential k H ^ k := by
  have key : subdiagNormSqProd k H = hessenbergPotential k H ^ (2 * k) := by
    rw [mul_comm, pow_mul, hessenbergPotential_pow hk, subdiagNormSqProd, Finset.prod_pow]
  have h2 : (∏ j ∈ Finset.range k, ‖subdiagEntry H (n - k + j)‖) ^ 2 =
      (hessenbergPotential k H ^ k) ^ 2 := by
    rw [← Finset.prod_pow, prod_range_norm_subdiagEntry_sq hkn, key, ← pow_mul, mul_comm]
  exact (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (pow_nonneg (hessenbergPotential_nonneg k H) k) (by norm_num)).mp h2

/-- The last row of a shift polynomial with shifts $\lvert s\rvert \le C\|\mathbf{H}\|_2$ has
norm at most $((1 + C)\|\mathbf{H}\|_2)^k$. -/
theorem norm_toLp_aeval_shiftPoly_last_le {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {C : ℝ} (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) :
    ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
      ((1 + C) * specNorm H) ^ ss.length := by
  have hrow : (Polynomial.aeval H (shiftPoly ss)) (Fin.last n) =
      (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℂ) ᵥ* Polynomial.aeval H (shiftPoly ss) := by
    rw [Matrix.single_one_vecMul]; rfl
  rw [hrow]
  refine (norm_toLp_vecMul_le _ _).trans ?_
  rw [PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one]
  refine specNorm_aeval_shiftPoly_le fun s hs' => ?_
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_smul, specNorm_one, mul_one]
  linarith [hs s hs']

/-- The rounded threshold of `Optimal`: under the standard model with
$30000(k + 1)\boldsymbol{u} \le 1$, $0 < k \le n$ and $c \ge 0$, the word
`NLAlib.ShiftedQR.optimalThresholdWord` is within $(10k + 12)\boldsymbol{u}\,c\,\psi_k^k$ of
$c\,\psi_k(\mathbf{H})^k$. -/
theorem abs_optimalThresholdWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hu : 30000 * (k + 1) * u ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    |optimalThresholdWord M H k c - c * hessenbergPotential k H ^ k| ≤
      (10 * k + 12) * u * (c * hessenbergPotential k H ^ k) := by
  have hu0 := hM.roundoff_nonneg
  have hp := abs_sqrt_prodWords_normSqFactors_sub_le hM (fun j => subdiagEntry H (n - k + j)) hu
  rw [prod_range_norm_subdiagEntry hk hkn] at hp
  set P := hessenbergPotential k H ^ k
  have hP : 0 ≤ P := pow_nonneg (hessenbergPotential_nonneg k H) k
  set p := M.sqrt (prodWords M (normSqFactors M (M.lit 1) fun j => subdiagEntry H (n - k + j)) k)
  have hm := hM.mul c p
  simp only [id] at hm
  have hpP : p ≤ (1 + 10 * (k + 1) * u) * P := by linarith [(abs_le.mp hp).2]
  have hp0 : 0 ≤ p := by
    have : 10 * ((k : ℝ) + 1) * u ≤ 1 := by nlinarith
    nlinarith [(abs_le.mp hp).1]
  have hw : optimalThresholdWord M H k c = M.mul c p := rfl
  rw [hw]
  rw [abs_of_nonneg (mul_nonneg hc hp0)] at hm
  have h1 : |c * p - c * P| ≤ c * (10 * (k + 1) * u * P) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hp hc
  have h2 : u * (c * p) ≤ u * (c * ((1 + 10 * (k + 1) * u) * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpP hc) hu0
  have h3 : 10 * ((k : ℝ) + 1) * u ≤ 1 := by nlinarith
  have h4 := abs_sub_le (M.mul c p) (c * p) (c * P)
  have hcP : 0 ≤ c * P := mul_nonneg hc hP
  nlinarith [mul_nonneg hu0 hcP, mul_le_mul_of_nonneg_right h3 (mul_nonneg hu0 hcP)]

/-- **The rounded last row of a shift polynomial** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 4.5]): under the standard model with $100N^2\boldsymbol{u} \le 1$ ($N = n + 1$) and shifts
$\lvert s_j\rvert \le C\|\mathbf{H}\|_2$, the vector of $k$ rounded steps of the row recurrence
from $\mathbf{e}_n$ (`NLAlib.ShiftedQR.rowPolyVec`) satisfies
$$\|\widehat{\mathbf{r}}_k - \mathbf{e}_n^{\mathsf T}p(\mathbf{H})\| \le
6kN^{3/2}\boldsymbol{u}\,((2 + 2C)\|\mathbf{H}\|_2)^k.$$
The paper's constant $2n^2$ (with the norm rounding) does not follow from its proof, which
gives $n + kn^{3/2}$; here the per-step error is $12N^{3/2}\boldsymbol{u}$. -/
theorem norm_toLp_rowPolyVec_sub_aeval_le {M : Machine ℝ} {u C : ℝ} (hM : StdModel u id M)
    {n : ℕ} (hu : 100 * ((n + 1 : ℕ) : ℝ) ^ 2 * u ≤ 1)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) :
    ‖WithLp.toLp 2 (rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) ss.length -
        (Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
      6 * ss.length * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
        ((2 + 2 * C) * specNorm H) ^ ss.length := by
  have hu0 := hM.roundoff_nonneg
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN1 : 1 ≤ N := by simp only [N]; exact_mod_cast Nat.succ_pos n
  have hsq : √N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsq0 : 0 ≤ √N := Real.sqrt_nonneg N
  have hη1 : 12 * (N * √N * u) ≤ 1 := by
    have : N * √N ≤ N ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hu0
    nlinarith
  have h := norm_toLp_sub_aeval_shiftPoly_row_le (H := H) (ss := ss) (C := C)
    (η := 12 * (N * √N * u)) hs (by positivity) hη1
    (r := rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1)) rfl (fun j hj => by
      have hget : ss.getD j 0 = ss[j] := by simp [List.getD_eq_getElem?_getD, hj]
      have hNN : N * u ≤ N ^ 2 * u := mul_le_mul_of_nonneg_right (by nlinarith) hu0
      have h5 : 5 * N * u ≤ 1 := by nlinarith
      have h100 : u ≤ 1 / 100 := by nlinarith
      have := norm_toLp_rowMulVec_sub_le (n := n) hM hu0 h100 h5 (hs ss[j] (List.getElem_mem hj))
        (rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) j)
      have hrec : rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) (j + 1) =
          rowMulVec M (1, 0) (rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) j)
            (machineShiftedPrefix M H ss[j] (n + 1)) := by
        rw [rowPolyVec, hget]
      rw [hrec]
      exact this)
  refine h.trans (le_of_eq ?_)
  ring

/-- The scalar bookkeeping of `Optimal`: with $a, G, A \ge 0$, $k \ge 1$, a row error
$E = 6kaG$ with $30000kaG \le A$, a norm $X \le G$, a computed row of norm $R$ within $E$ of
$X$, its rounded norm $t$ within $\varepsilon R$ of $R$, $\varepsilon \le 8ka$, and a
threshold within $0.00012A$ of $0.999A$, the shifted value
$t + (0.999A - \mathrm{thr})$ is within $0.0009A$ of $X$. -/
private theorem abs_optimal_bookkeeping {k a G A X R t ε thr : ℝ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hG : 0 ≤ G) (hu : 30000 * k * a * G ≤ A) (hX : X ≤ G)
    (hR : |R - X| ≤ 6 * k * a * G) (ht : |t - R| ≤ ε * R) (hε : ε ≤ 8 * k * a)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hthr : |thr - 0.999 * A| ≤ 0.00012 * A) :
    |t + (0.999 * A - thr) - X| ≤ 0.0009 * A := by
  have hP : 0 ≤ k * a * G := by positivity
  have hRp : R ≤ X + 6 * (k * a * G) := by linarith [(abs_le.mp hR).2]
  have h1 : ε * R ≤ ε * G + ε * (6 * (k * a * G)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hε0
  have h2 : ε * G ≤ 8 * k * a * G := mul_le_mul_of_nonneg_right hε hG
  have h3 : ε * (6 * (k * a * G)) ≤ 6 * (k * a * G) := by
    have := mul_le_mul_of_nonneg_right hε1 (show 0 ≤ 6 * (k * a * G) by positivity)
    linarith
  rw [abs_le] at hR ht hthr ⊢
  constructor <;> nlinarith

/-- The computed norm of `Optimal` is within $0.0009(\theta\psi_k)^k$ of
$\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})\|$, after the threshold's rounding is moved to it: the
hypothesis of `NLAlib.isOptimalRitzValues_of_lt` and `NLAlib.not_isOptimalRitzValues_of_le`. -/
private theorem abs_optimal_shifted_sub_le {M : Machine ℝ} {u θ C : ℝ} (hM : StdModel u id M)
    (hNat : IsExactNatLit id M 1) {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} (hss : ss ≠ []) (hk : ss.length ≤ n) (hθ : 0 < θ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H)
    (hu : 30000 * ss.length * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * C) * specNorm H) ^ ss.length ≤ (θ * hessenbergPotential ss.length H) ^ ss.length)
    (hu1 : 100000 * ((n + 1 + ss.length : ℕ) : ℝ) ^ 2 * u ≤ 1) :
    |pairVecNormWord M (rowPolyVec M (M.lit 1, M.lit 0) H ss (rowInitVec M n) ss.length) +
        (0.999 * (θ * hessenbergPotential ss.length H) ^ ss.length -
          optimalThresholdWord M H ss.length (0.999 * θ ^ ss.length)) -
        ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖| ≤
      0.0009 * (θ * hessenbergPotential ss.length H) ^ ss.length := by
  have hu0 := hM.roundoff_nonneg
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 le_rfl
  have hk1 : 1 ≤ ss.length := List.length_pos_iff.mpr hss
  have hk1' : (1 : ℝ) ≤ ss.length := by exact_mod_cast hk1
  have hN1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hsq1 : 1 ≤ √((n + 1 : ℕ) : ℝ) := Real.one_le_sqrt.mpr hN1
  have hNk : ((n + 1 : ℕ) : ℝ) + ss.length = ((n + 1 + ss.length : ℕ) : ℝ) := by push_cast; ring
  have hNk2 : ((n + 1 : ℕ) : ℝ) + ss.length ≤ ((n + 1 + ss.length : ℕ) : ℝ) ^ 2 := by
    rw [hNk]; nlinarith
  have hsmall : (((n + 1 : ℕ) : ℝ) + ss.length) * u ≤ 1 / 100000 := by
    nlinarith [mul_le_mul_of_nonneg_right hNk2 hu0]
  have hN2 : ((n + 1 : ℕ) : ℝ) ^ 2 * u ≤ ((n + 1 + ss.length : ℕ) : ℝ) ^ 2 * u :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) 2) hu0
  have hrow : rowPolyVec M (M.lit 1, M.lit 0) H ss (rowInitVec M n) ss.length =
      rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) ss.length := by
    rw [h1, h0, rowInitVec_eq h0 h1]
  rw [hrow]
  have hE := norm_toLp_rowPolyVec_sub_aeval_le (C := C) hM (n := n) (ss := ss)
    (by nlinarith) hs
  have hG0 : 0 ≤ (2 + 2 * C) * specNorm H := by
    obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil ss hss
    have : 0 ≤ C * specNorm H := (norm_nonneg s0).trans (hs s0 hs0)
    nlinarith [specNorm_nonneg H]
  have hX : ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
      ((2 + 2 * C) * specNorm H) ^ ss.length := (norm_toLp_aeval_shiftPoly_last_le hs).trans
    (pow_le_pow_left₀ (by nlinarith [hG0]) (by nlinarith [hG0]) ss.length)
  have hku := mul_le_mul_of_nonneg_right hk1' hu0
  have hn := abs_pairVecNormWord_sub_le hM (N := n + 1) (by push_cast at hsmall ⊢; nlinarith)
    (rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) ss.length)
  have hR : |‖WithLp.toLp 2 (rowPolyVec M (1, 0) H ss (Pi.single (Fin.last n) 1) ss.length)‖ -
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖| ≤
      6 * ss.length * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
        ((2 + 2 * C) * specNorm H) ^ ss.length := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← WithLp.toLp_sub]; exact hE
  have ht := abs_optimalThresholdWord_sub_le hM (n := n) (k := ss.length) (by omega) hk
    (by nlinarith) (c := 0.999 * θ ^ ss.length) (by positivity) H
  have hcA : 0.999 * θ ^ ss.length * hessenbergPotential ss.length H ^ ss.length =
      0.999 * (θ * hessenbergPotential ss.length H) ^ ss.length := by rw [mul_pow]; ring
  rw [hcA] at ht
  have hA0 : 0 ≤ (θ * hessenbergPotential ss.length H) ^ ss.length :=
    pow_nonneg (mul_nonneg hθ.le (hessenbergPotential_nonneg _ _)) _
  have ht' : |optimalThresholdWord M H ss.length (0.999 * θ ^ ss.length) -
      0.999 * (θ * hessenbergPotential ss.length H) ^ ss.length| ≤
      0.00012 * (θ * hessenbergPotential ss.length H) ^ ss.length := by
    refine ht.trans ?_
    have : (10 * (ss.length : ℝ) + 12) * u ≤ 0.00012 := by nlinarith
    nlinarith
  refine abs_optimal_bookkeeping (k := ss.length) hk1' (by positivity) (by positivity) hu hX
    hR hn ?_ (by positivity) ?_ ht'
  · have e1 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_right (by positivity) hsq1
    have e2 : ((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) ≤
        ss.length * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) :=
      le_mul_of_one_le_left (by positivity) hk1'
    have e3 : 2 * ((n + 1 : ℕ) : ℝ) + 6 ≤ 8 * ss.length *
        (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) := by linarith
    have e4 := mul_le_mul_of_nonneg_right e3 hu0
    calc (2 * ((n + 1 : ℕ) : ℝ) + 6) * u ≤ 8 * ss.length *
          (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) * u := e4
      _ = _ := by ring
  · nlinarith [hku, hsmall]

section OptimalTarget

variable [Has CmpTst Tst]

/-- **`Optimal` decides optimality** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 4.5]): on a scalar machine with the standard model, exact literals $0, 1$ and exact
comparisons, let $\mathbf{H}$ of order $N = n + 1$ be stored at `A`, the $k \ge 1$ shifts
$s_j$, $k \le n$, $\lvert s_j\rvert \le C\|\mathbf{H}\|_2$, stored as pairs at `S`, the word
$0.999\theta^k$ at `C`, $\theta > 0$, $\psi_k(\mathbf{H}) > 0$, and
$$30000\,kN^{3/2}\boldsymbol{u}\,((2 + 2C)\|\mathbf{H}\|_2)^k \le (\theta\psi_k(\mathbf{H}))^k,
\qquad 10^5 (N + k)^2\boldsymbol{u} \le 1.$$
Then `optimalTest` writes only its flag word, and stores there $b \in \{0, 1\}$ with: $b = 1$
implies the shifts are $\theta$-optimal, and $b = 0$ implies they are not
$0.998^{1/k}\theta$-optimal. The computed norm, shifted by the threshold's rounding, meets the
$0.0009(\theta\psi_k)^k$ hypothesis of `NLAlib.isOptimalRitzValues_of_lt` and
`NLAlib.not_isOptimalRitzValues_of_le`. The paper's precision
$(2 \cdot 10^3 n^2)^{-1}(\psi_k/(\theta(2 + 2C)\|\mathbf{H}\|_2))^k$ rests on the constant $2n^2$,
which its proof does not give ($n + kn^{3/2}$); here $kN^{3/2}$. -/
theorem optimalTest_writes {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hNat : IsExactNatLit id M 1) (hC : IsCmp id I)
    {τ : Tape ℝ} {μ : Mem ℝ} {n : ℕ} {a s c f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {θ C : ℝ}
    (hss : ss ≠ []) (hk : ss.length ≤ n) (hθ : 0 < θ) (hψ : 0 < hessenbergPotential ss.length H)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H)
    (hu : 30000 * ss.length * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * C) * specNorm H) ^ ss.length ≤ (θ * hessenbergPotential ss.length H) ^ ss.length)
    (hu1 : 100000 * ((n + 1 + ss.length : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hH : HoldsMatrix a H μ.store)
    (hsS : μ.store.readBlock s.1 s.2 (2 * ss.length) = some (ss.flatMap fun z => [z.re, z.im]))
    (hc : μ.store.get c.1 c.2 = some (0.999 * θ ^ ss.length)) (hf : f.2 < μ.store.len f.1)
    (hl : μ.Live [a, s, c, f])
    (has : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock c.1 c.2 1)) :
    Writes .total I τ (optimalTest (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, ss.length] [a, s, c, f]) (Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ b : ℝ, μ'.store.get f.1 f.2 = some b ∧ (b = 0 ∨ b = 1) ∧
        (b = 1 → IsOptimalRitzValues θ H ss) ∧
        (b = 0 → ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((ss.length : ℝ)⁻¹) * θ) H ss)) μ := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 le_rfl
  refine (optimalTest_writes_word (τ := τ) hS hC hk hH hsS hc hf hl has).mono le_rfl
    fun μ' _ ⟨hp, hF⟩ => ⟨hp, _, hF, ?_⟩
  have ht := abs_optimal_shifted_sub_le hM hNat hss hk hθ hs hu hu1
  set t := pairVecNormWord M (rowPolyVec M (M.lit 1, M.lit 0) H ss (rowInitVec M n) ss.length)
  set thr := optimalThresholdWord M H ss.length (0.999 * θ ^ ss.length)
  set A := (θ * hessenbergPotential ss.length H) ^ ss.length
  have hw : optimalTestWord M H ss (0.999 * θ ^ ss.length) = if t < thr then 1 else 0 := by
    change (if t < thr then M.lit 1 else M.lit 0) = _
    rw [h0, h1]
  rw [hw]
  by_cases hlt : t < thr
  · simp only [hlt, if_true, one_ne_zero, false_or, true_implies, false_implies, and_true]
    exact ⟨trivial, isOptimalRitzValues_of_lt ht (by linarith)⟩
  · simp only [hlt, if_false, zero_ne_one, or_false, true_implies, false_implies, true_and]
    exact not_isOptimalRitzValues_of_le hθ hψ hss ht (by linarith [not_lt.mp hlt])

end OptimalTarget

end NLAlib.ShiftedQR
