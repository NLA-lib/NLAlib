/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Ops.Blas.NormSq
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Matrix.FinitePrecision.ProductRounded

/-!
# Rounded sums and products of squared moduli

Word pairs $(x, y)$ of complex numbers, their squared moduli
$\mathrm{fl}(\mathrm{fl}(x^2) + \mathrm{fl}(y^2))$ on a machine with the standard model, and their
rounded products and sums: one loop rule (`NLAlib.ShiftedQR.writes_loop_normSqOpRound`) gives
the stored word of a fold of squared moduli by any scalar operation, on any scalar machine; the
accuracy lemmas bound the rounded product of moduli
(`NLAlib.ShiftedQR.abs_sqrt_prodWords_normSqFactors_sub_le`) and the rounded Euclidean norm of
a stored vector (`NLAlib.ShiftedQR.abs_pairVecNormWord_sub_le`). Roots of a relatively perturbed
number are bounded once (`NLAlib.ShiftedQR.abs_rpow_inv_natCast_sub_le`).

## Main definitions

* `NLAlib.ShiftedQR.normSqWord`, `NLAlib.ShiftedQR.normSqFactors`, `NLAlib.ShiftedQR.foldWords`:
  the machine words.
* `NLAlib.ShiftedQR.normSqOpRound`: one round of a fold of squared moduli.
* `NLAlib.ShiftedQR.pairVecNormWithScratch`: the rounded Euclidean norm of a stored vector.

## Main results

* `NLAlib.ShiftedQR.writes_loop_normSqOpRound`, `NLAlib.ShiftedQR.writes_loop_normSqMulRound`:
  the fold and product loops on any scalar machine.
* `NLAlib.ShiftedQR.prodWords_normSqFactors_bounds`: the rounded product of squared moduli.
* `NLAlib.ShiftedQR.abs_sqrt_prodWords_normSqFactors_sub_le`: the rounded product of moduli.
* `NLAlib.ShiftedQR.foldWords_add_bounds`: a rounded sum of nonnegative words.
* `NLAlib.ShiftedQR.abs_pairVecNormWord_sub_le`: the rounded Euclidean norm.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- $(1 + \boldsymbol{u})^N \le 1 + 2N\boldsymbol{u}$ for $\boldsymbol{u} \ge 0$ and
$N\boldsymbol{u} \le 1$. -/
theorem one_add_pow_le_one_add_two_mul {u : ℝ} (hu : 0 ≤ u) {N : ℕ} (hN : N * u ≤ 1) :
    (1 + u) ^ N ≤ 1 + 2 * N * u := by
  have hNu : 0 ≤ (N : ℝ) * u := by positivity
  have h1 : (1 + u) ^ N ≤ Real.exp (N * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) N
  have h2 := Real.abs_exp_sub_one_le (x := N * u) (by rw [abs_of_nonneg hNu]; exact hN)
  rw [abs_of_nonneg hNu] at h2
  linarith [(abs_le.mp h2).2]



/-- The entries of a vector of length $N$ as a sequence, $0$ beyond $N$. -/
def vecGetD {N : ℕ} (r : Fin N → ℂ) (l : ℕ) : ℂ := if h : l < N then r ⟨l, h⟩ else 0

/-- A sum over `Fin N` is the sum over the first $N$ terms of the padded sequence. -/
theorem sum_fin_eq_sum_range_vecGetD {N : ℕ} (f : Fin N → ℂ) :
    ∑ l, f l = ∑ l ∈ Finset.range N, vecGetD f l := by
  rw [Finset.sum_range fun l => vecGetD f l]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [vecGetD, l.isLt]


variable {Op Tst : Type} [Has ScalarOp Op]

/-! ### The squared modulus of a pair and the fold loop -/

/-- The squared modulus $\mathrm{fl}(\mathrm{fl}(x^2) + \mathrm{fl}(y^2))$ of the pair
$(x, y)$ of a complex number on the machine `M`, as `NLAlib.Ops.PairScalar.normSq` computes it. -/
def normSqWord (M : Machine ℝ) (z : ℂ) : ℝ := M.add (M.mul z.re z.re) (M.mul z.im z.im)

/-- Under the standard model with $0 \le \boldsymbol{u} \le 1$, the machine squared modulus is
within the factors $(1 \mp \boldsymbol{u})^2$ of $\lvert z\rvert^2$. -/
theorem normSqWord_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) (z : ℂ) :
    (1 - u) ^ 2 * ‖z‖ ^ 2 ≤ normSqWord M z ∧ normSqWord M z ≤ (1 + u) ^ 2 * ‖z‖ ^ 2 := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn]
  exact hM.add_mul_self_bounds hu hu1 _ _

/-- The words of a product started at the word `v` and continued by the squared moduli of
`z 0, z 1, …`: the word sequence `NLAlib.prodWords` multiplies. -/
def normSqFactors (M : Machine ℝ) (v : ℝ) (z : ℕ → ℂ) : ℕ → ℝ
  | 0 => v
  | j + 1 => normSqWord M (z j)

/-- The words `w 0, w 1, …` combined left to right by the machine function `g`:
`foldWords g w 0` $= w_0$, `foldWords g w (j + 1)` $= g(\,$`foldWords g w j`$, w_{j+1})$. For
`g = M.mul` it is `NLAlib.prodWords` (`NLAlib.ShiftedQR.foldWords_mul`). -/
def foldWords (g : ℝ → ℝ → ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w 0
  | j + 1 => g (foldWords g w j) (w (j + 1))

/-- The fold of the machine multiplication is the rounded product. -/
theorem foldWords_mul (M : Machine ℝ) (w : ℕ → ℝ) (j : ℕ) :
    foldWords M.mul w j = prodWords M w j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [foldWords, prodWords, ih]

/-- One round of a fold of squared moduli by the scalar operation `o`: the squared modulus of
the pair `x` into the three scratch words `t`, then the accumulator word `p` combined in place
with the third of them. -/
def normSqOpRound (o : ScalarOp) (x t p : Operand) : Stmt Op Tst :=
  .seq (.frame [] [x, t] PairScalar.normSq)
    (.call (Has.inj o) [] [p, ⟨t.buf, t.off + .const 2⟩] [p])

/-- One round of a product of squared moduli. -/
abbrev normSqMulRound (x t p : Operand) : Stmt Op Tst := normSqOpRound .mul x t p

/-- The fold loop of squared moduli on any scalar machine: let the scalar operation `o` be the
machine function `g`. If, in round $i < N$, the operand `x` addresses a pair holding $z_i$, inside a
region `R` apart from the scratch view `t` (three words) and the accumulator word `p`, and `p` holds
$v$, then the loop stores in `p` the fold `NLAlib.ShiftedQR.foldWords` by `g` of $v$ and the machine
squared moduli of $z_0, \dots, z_{N-1}$, and writes only `p` and `t`.
A step in the proof of `writes_loop_normSqMulRound`, `pairVecNormWithScratch_writes_word`. -/
theorem writes_loop_normSqOpRound {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I)
    {o : ScalarOp} {g : ℝ → ℝ → ℝ} (hg : M.fn o = .bin fun a b => some (g a b))
    {τ : Tape ℝ} {m : Mem ℝ} {ρ : Env} {cnt : IExp} {N : ℕ} (hN : cnt.eval ρ.idx = some N)
    {x t p : Operand} {xs : ℕ → ℕ × ℕ} {tl pl : ℕ × ℕ} {R : Fp} {z : ℕ → ℂ} {v : ℝ}
    (hx : ∀ i < N, x.eval (ρ.pushIdx i) = some (xs i))
    (ht : ∀ i < N, t.eval (ρ.pushIdx i) = some tl)
    (ht2 : ∀ i < N, Operand.eval (ρ.pushIdx i) ⟨t.buf, t.off + .const 2⟩ = some (tl.1, tl.2 + 2))
    (hp : ∀ i < N, p.eval (ρ.pushIdx i) = some pl)
    (hxR : ∀ i < N, Store.inBlock (xs i).1 (xs i).2 2 ≤ R)
    (hre : ∀ i < N, m.store.get (xs i).1 (xs i).2 = some (z i).re)
    (him : ∀ i < N, m.store.get (xs i).1 ((xs i).2 + 1) = some (z i).im)
    (hroom : tl.2 + 3 ≤ m.store.len tl.1) (hv : m.store.get pl.1 pl.2 = some v)
    (hRt : Fp.Disj R (Store.inBlock tl.1 tl.2 3)) (hRp : Fp.Disj R (Store.inBlock pl.1 pl.2 1))
    (htp : Fp.Disj (Store.inBlock tl.1 tl.2 3) (Store.inBlock pl.1 pl.2 1)) :
    Writes .total I τ (.loop cnt (normSqOpRound o x t p)) ρ
      (Store.inBlock pl.1 pl.2 1 ⊔ Store.inBlock tl.1 tl.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get pl.1 pl.2 = some (foldWords g (normSqFactors M v z) N)) m := by
  have htl := Store.lt_length_of_lt_len (show tl.2 < m.store.len tl.1 by omega)
  refine writes_loop hN (fun _ => Store.inBlock pl.1 pl.2 1 ⊔ Store.inBlock tl.1 tl.2 3)
    (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧
      m'.store.get pl.1 pl.2 = some (foldWords g (normSqFactors M v z) i))
    ⟨rfl, by simpa [foldWords, normSqFactors] using hv⟩ ?_
  intro i hi m' hfr ⟨hpos, hProd⟩
  have hdis : Fp.Disj (Store.inBlock (xs i).1 (xs i).2 2)
      (Store.inBlock pl.1 pl.2 1 ⊔ Store.inBlock tl.1 tl.2 3) :=
    (Fp.disj_sup_right.mpr ⟨hRp, hRt⟩).mono (hxR i hi) le_rfl
  have hre' := hfr.keep (Store.readsOnly_get _ _ _) (hdis.symm.mono le_rfl (by fp_sub)) (hre i hi)
  have him' := hfr.keep (Store.readsOnly_get _ _ _) (hdis.symm.mono le_rfl (by fp_sub)) (him i hi)
  have hnorm := PairScalar.normSq_writes_word (τ := τ) (m := m') (x := xs i) (t := tl) hS
    hre' him' (by rw [hfr.len_eq]; exact hroom) (hRt.mono (hxR i hi) le_rfl)
  unfold normSqOpRound
  refine hnorm.frame_seq_le rfl (by simp [Operand.evalList, hx i hi, ht i hi])
    (by simp [Mem.Live, Store.lt_length_of_get hre', hfr.length_eq ▸ htl]) le_sup_right ?_
  intro m'' hfr' ⟨hp', hNorm⟩
  have hProd' := hfr'.keep (Store.readsOnly_get _ _ _) htp hProd
  have hpl'' := Store.lt_len_of_get hProd'
  have hplL := Store.lt_length_of_get hProd'
  have htlL := Store.lt_length_of_get hNorm
  have hI := hS o
  rw [hg] at hI
  refine (writes_call_bin hI (y := (tl.1, tl.2 + 2))
    (by simp [Operand.evalList, hp i hi, ht2 i hi])
    (by simp [Operand.evalList, hp i hi]) trivial hProd' hNorm rfl
    (fun _ => ⟨by simp [Mem.Live, hplL, htlL], hpl''⟩)).mono le_sup_left ?_
  intro m''' _ ⟨hp'', hMul⟩
  exact ⟨hp''.trans (hp'.trans hpos), by simpa [foldWords, normSqFactors, normSqWord] using hMul⟩

/-- The product loop of squared moduli on any scalar machine: the fold loop
(`NLAlib.ShiftedQR.writes_loop_normSqOpRound`) by the multiplication stores the rounded product
`NLAlib.prodWords` of $v$ and the machine squared moduli of $z_0, \dots, z_{N-1}$.
A step in the proof of `subdiagProductWithScratch_writes_word`, `comptau_writes_word`. -/
theorem writes_loop_normSqMulRound {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {ρ : Env} {cnt : IExp} {N : ℕ} (hN : cnt.eval ρ.idx = some N)
    {x t p : Operand} {xs : ℕ → ℕ × ℕ} {tl pl : ℕ × ℕ} {R : Fp} {z : ℕ → ℂ} {v : ℝ}
    (hx : ∀ i < N, x.eval (ρ.pushIdx i) = some (xs i))
    (ht : ∀ i < N, t.eval (ρ.pushIdx i) = some tl)
    (ht2 : ∀ i < N, Operand.eval (ρ.pushIdx i) ⟨t.buf, t.off + .const 2⟩ = some (tl.1, tl.2 + 2))
    (hp : ∀ i < N, p.eval (ρ.pushIdx i) = some pl)
    (hxR : ∀ i < N, Store.inBlock (xs i).1 (xs i).2 2 ≤ R)
    (hre : ∀ i < N, m.store.get (xs i).1 (xs i).2 = some (z i).re)
    (him : ∀ i < N, m.store.get (xs i).1 ((xs i).2 + 1) = some (z i).im)
    (hroom : tl.2 + 3 ≤ m.store.len tl.1) (hv : m.store.get pl.1 pl.2 = some v)
    (hRt : Fp.Disj R (Store.inBlock tl.1 tl.2 3)) (hRp : Fp.Disj R (Store.inBlock pl.1 pl.2 1))
    (htp : Fp.Disj (Store.inBlock tl.1 tl.2 3) (Store.inBlock pl.1 pl.2 1)) :
    Writes .total I τ (.loop cnt (normSqMulRound x t p)) ρ
      (Store.inBlock pl.1 pl.2 1 ⊔ Store.inBlock tl.1 tl.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get pl.1 pl.2 = some (prodWords M (normSqFactors M v z) N)) m := by
  simpa only [foldWords_mul] using writes_loop_normSqOpRound (τ := τ) hS (o := .mul) rfl hN hx
    ht ht2 hp hxR hre him hroom hv hRt hRp htp

/-! ### Scalar estimates -/

/-- A relative perturbation under a root: if $(1 - y)P \le x \le (1 + y)P$ with
$P \ge 0$, $0 \le y \le 1/2$ and $p \ge 1$, then
$\lvert x^{1/p} - P^{1/p}\rvert \le (2y/p)\,P^{1/p}$. -/
theorem abs_rpow_inv_natCast_sub_le {x P y : ℝ} {p : ℕ} (hp : 0 < p) (hP : 0 ≤ P)
    (hy : 0 ≤ y) (hy2 : y ≤ 1 / 2) (hlo : (1 - y) * P ≤ x) (hhi : x ≤ (1 + y) * P) :
    |x ^ ((p : ℝ)⁻¹) - P ^ ((p : ℝ)⁻¹)| ≤ 2 * y / p * P ^ ((p : ℝ)⁻¹) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have he : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hQ := Real.rpow_nonneg hP ((p : ℝ)⁻¹)
  -- the root of `1 + c` is at most `1 + c / p`
  have hroot : ∀ c : ℝ, 0 ≤ c → (1 + c) ^ ((p : ℝ)⁻¹) ≤ 1 + c / p := fun c hc => by
    have hb : 1 + c ≤ (1 + c / p) ^ p := by
      have hcp : 0 ≤ c / p := by positivity
      have := one_add_mul_le_pow (a := c / p) (by linarith) p
      rwa [mul_div_cancel₀ _ hp0.ne'] at this
    calc (1 + c) ^ ((p : ℝ)⁻¹) ≤ ((1 + c / p) ^ p) ^ ((p : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by linarith) hb he
      _ = 1 + c / p := Real.pow_rpow_inv_natCast (by positivity) hp.ne'
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (by linarith) hP) hlo
  have hup : x ^ ((p : ℝ)⁻¹) ≤ (1 + y / p) * P ^ ((p : ℝ)⁻¹) := by
    calc x ^ ((p : ℝ)⁻¹) ≤ ((1 + y) * P) ^ ((p : ℝ)⁻¹) := Real.rpow_le_rpow hx0 hhi he
      _ = (1 + y) ^ ((p : ℝ)⁻¹) * P ^ ((p : ℝ)⁻¹) := Real.mul_rpow (by linarith) hP
      _ ≤ (1 + y / p) * P ^ ((p : ℝ)⁻¹) := mul_le_mul_of_nonneg_right (hroot y hy) hQ
  have hlow : (1 - 2 * y / p) * P ^ ((p : ℝ)⁻¹) ≤ x ^ ((p : ℝ)⁻¹) := by
    have h1y : 0 < 1 - y := by linarith
    have hinv : (1 - y)⁻¹ ≤ 1 + 2 * y := by
      rw [inv_le_iff_one_le_mul₀ h1y]; nlinarith
    have hr : (1 - y) ^ ((p : ℝ)⁻¹) ≥ (1 + 2 * y / p)⁻¹ := by
      have h3 : ((1 - y)⁻¹) ^ ((p : ℝ)⁻¹) ≤ 1 + 2 * y / p := by
        calc ((1 - y)⁻¹) ^ ((p : ℝ)⁻¹) ≤ (1 + 2 * y) ^ ((p : ℝ)⁻¹) :=
              Real.rpow_le_rpow (by positivity) hinv he
          _ ≤ 1 + 2 * y / p := hroot (2 * y) (by linarith)
      rw [Real.inv_rpow h1y.le] at h3
      have hpos : 0 < (1 - y) ^ ((p : ℝ)⁻¹) := Real.rpow_pos_of_pos h1y _
      rw [ge_iff_le, inv_le_comm₀ (by positivity) hpos]
      exact h3
    have hq : 1 - 2 * y / p ≤ (1 + 2 * y / p)⁻¹ := by
      have hc : 0 ≤ 2 * y / p := by positivity
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc (1 - 2 * y / p) * P ^ ((p : ℝ)⁻¹) ≤ (1 - y) ^ ((p : ℝ)⁻¹) * P ^ ((p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right (hq.trans hr) hQ
      _ = ((1 - y) * P) ^ ((p : ℝ)⁻¹) := (Real.mul_rpow h1y.le hP).symm
      _ ≤ x ^ ((p : ℝ)⁻¹) := Real.rpow_le_rpow (mul_nonneg h1y.le hP) hlo he
  have hyp : y / p ≤ 2 * y / p := by
    rw [div_le_div_iff_of_pos_right hp0]; linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The rounded product of squared moduli: under the standard model with
$8(k+1)\boldsymbol{u} \le 1$, the product of the rounded literal $1$ and the machine squared
moduli of $z_0, \dots, z_{k-1}$, accumulated by $k$ rounded multiplications, is within the
factors $1 \mp 8(k+1)\boldsymbol{u}$ of $\prod_{j<k}\lvert z_j\rvert^2$. -/
theorem prodWords_normSqFactors_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {k : ℕ} (hku : 8 * (k + 1) * u ≤ 1) (z : ℕ → ℂ) :
    (1 - 8 * (k + 1) * u) * ∏ j ∈ Finset.range k, ‖z j‖ ^ 2 ≤
        prodWords M (normSqFactors M (M.lit 1) z) k ∧
      prodWords M (normSqFactors M (M.lit 1) z) k ≤
        (1 + 8 * (k + 1) * u) * ∏ j ∈ Finset.range k, ‖z j‖ ^ 2 := by
  have hu := hM.roundoff_nonneg
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hu1 : u ≤ 1 := by nlinarith
  set P := ∏ j ∈ Finset.range k, ‖z j‖ ^ 2
  have hP : 0 ≤ P := Finset.prod_nonneg fun _ _ => by positivity
  set w := normSqFactors M (M.lit 1) z
  have hlit : |M.lit 1 - 1| ≤ u := by simpa using hM.lit 1
  have hw0 : 1 - u ≤ w 0 ∧ w 0 ≤ 1 + u := by
    simp only [w, normSqFactors]; constructor <;> linarith [(abs_le.mp hlit).1, (abs_le.mp hlit).2]
  have hb := fun j => normSqWord_bounds hM hu hu1 (z j)
  have hS : ∏ i ∈ Finset.range (k + 1), w i = w 0 * ∏ j ∈ Finset.range k, normSqWord M (z j) := by
    rw [Finset.prod_range_succ', mul_comm]; rfl
  have hQlo : (1 - u) ^ (2 * k) * P ≤ ∏ j ∈ Finset.range k, normSqWord M (z j) := by
    rw [pow_mul, ← Finset.card_range k, ← Finset.prod_const, Finset.card_range,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => (hb j).1
  have hQhi : ∏ j ∈ Finset.range k, normSqWord M (z j) ≤ (1 + u) ^ (2 * k) * P := by
    rw [pow_mul, ← Finset.card_range k, ← Finset.prod_const, Finset.card_range,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun j _ => le_trans (by positivity) (hb j).1) fun j _ => (hb j).2
  have hQ0 : 0 ≤ ∏ j ∈ Finset.range k, normSqWord M (z j) :=
    le_trans (by have : 0 ≤ 1 - u := by linarith
                 positivity) hQlo
  have hW0 : 0 ≤ ∏ i ∈ Finset.range (k + 1), w i := by
    rw [hS]; exact mul_nonneg (by linarith [hw0.1]) hQ0
  have hfp := hM.abs_prodWords_sub_le w k
  simp only [id] at hfp
  have habs : ∏ i ∈ Finset.range (k + 1), |w i| = ∏ i ∈ Finset.range (k + 1), w i := by
    rw [← Finset.abs_prod, abs_of_nonneg hW0]
  rw [habs] at hfp
  obtain ⟨hf1, hf2⟩ := abs_le.mp hfp
  set W := ∏ i ∈ Finset.range (k + 1), w i
  -- the factors
  have hup1 : (1 + u) ^ k ≤ 1 + 2 * k * u :=
    one_add_pow_le_one_add_two_mul hu (by nlinarith)
  have hup2 : (1 + u) ^ (3 * k + 1) ≤ 1 + 2 * ((3 * k + 1 : ℕ) : ℝ) * u :=
    one_add_pow_le_one_add_two_mul hu (by push_cast; nlinarith)
  have hlo2 : 1 - (2 * k + 1) * u ≤ (1 - u) ^ (2 * k + 1) := by
    have := one_add_mul_le_pow (a := -u) (by linarith) (2 * k + 1)
    rw [← sub_eq_add_neg] at this
    push_cast at this; linarith
  have hWhi : W ≤ (1 + u) ^ (2 * k + 1) * P := by
    rw [hS, pow_succ, mul_comm ((1 + u) ^ (2 * k)) (1 + u), mul_assoc]
    exact mul_le_mul hw0.2 hQhi hQ0 (by linarith)
  have hWlo : (1 - u) ^ (2 * k + 1) * P ≤ W := by
    rw [hS, pow_succ, mul_comm ((1 - u) ^ (2 * k)) (1 - u), mul_assoc]
    exact mul_le_mul hw0.1 hQlo (by have : 0 ≤ 1 - u := by linarith
                                    positivity) (by linarith [hw0.1])
  constructor
  · have h1 : (1 - 2 * k * u) * W ≤ prodWords M w k := by nlinarith
    have h2 : (1 - 2 * k * u) * ((1 - (2 * k + 1) * u) * P) ≤ (1 - 2 * k * u) * W :=
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hlo2 hP).trans hWlo) (by nlinarith)
    nlinarith [mul_nonneg (mul_nonneg hk0 hu) (mul_nonneg hu hP), mul_nonneg hu hP,
      mul_nonneg (mul_nonneg hk0 hu) hP]
  · have h1 : prodWords M w k ≤ (1 + u) ^ k * W := by linarith
    have h2 : (1 + u) ^ k * W ≤ (1 + u) ^ (3 * k + 1) * P := by
      calc (1 + u) ^ k * W ≤ (1 + u) ^ k * ((1 + u) ^ (2 * k + 1) * P) :=
            mul_le_mul_of_nonneg_left hWhi (by positivity)
        _ = (1 + u) ^ (3 * k + 1) * P := by ring
    have h3 : (1 + u) ^ (3 * k + 1) * P ≤ (1 + 2 * ((3 * k + 1 : ℕ) : ℝ) * u) * P :=
      mul_le_mul_of_nonneg_right hup2 hP
    push_cast at h3
    nlinarith [mul_nonneg (mul_nonneg hk0 hu) hP, mul_nonneg hu hP]

/-- The rounded product of moduli: under the standard model with
$30000(k + 1)\boldsymbol{u} \le 1$, the machine square root of the rounded product of the rounded
literal $1$ and the machine squared moduli of $z_0, \dots, z_{k-1}$ is within
$10(k + 1)\boldsymbol{u}$, relatively, of $\prod_{j<k}\lvert z_j\rvert$. -/
theorem abs_sqrt_prodWords_normSqFactors_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (z : ℕ → ℂ) {k : ℕ} (hu : 30000 * (k + 1) * u ≤ 1) :
    |M.sqrt (prodWords M (normSqFactors M (M.lit 1) z) k) - ∏ j ∈ Finset.range k, ‖z j‖| ≤
      10 * (k + 1) * u * ∏ j ∈ Finset.range k, ‖z j‖ := by
  have hu0 := hM.roundoff_nonneg
  set T := ∏ j ∈ Finset.range k, ‖z j‖
  have hT : 0 ≤ T := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨hlo, hhi⟩ := prodWords_normSqFactors_bounds hM (k := k) (by nlinarith) z
  have hP : ∏ j ∈ Finset.range k, ‖z j‖ ^ 2 = T ^ 2 := by rw [Finset.prod_pow]
  rw [hP] at hlo hhi
  set x := prodWords M (normSqFactors M (M.lit 1) z) k
  set y : ℝ := 8 * (k + 1) * u
  have hy0 : 0 ≤ y := by positivity
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (by nlinarith) (sq_nonneg T)) hlo
  have hroot := abs_rpow_inv_natCast_sub_le (p := 2) (by norm_num) (sq_nonneg T) hy0
    (by nlinarith) hlo hhi
  have hT2 : (T ^ 2) ^ (((2 : ℕ) : ℝ))⁻¹ = T := Real.pow_rpow_inv_natCast hT (by norm_num)
  have hsx : x ^ (((2 : ℕ) : ℝ))⁻¹ = √x := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hT2, hsx] at hroot
  have hsq := hM.sqrt x hx0
  simp only [id] at hsq
  have h2 : √x ≤ (1 + y) * T := by
    have := (abs_le.mp hroot).2; norm_num at this ⊢; linarith
  have h3 := abs_sub_le (M.sqrt x) (√x) T
  have h4 : u * √x ≤ u * ((1 + y) * T) := mul_le_mul_of_nonneg_left h2 hu0
  have h5 : 2 * y / ((2 : ℕ) : ℝ) * T = y * T := by norm_num
  have h6 : u * y ≤ u := by
    have : y ≤ 1 := by simp only [y]; nlinarith
    nlinarith
  nlinarith [mul_nonneg hu0 hT, mul_le_mul_of_nonneg_right h6 hT]

/-! ### The rounded Euclidean norm of a stored vector -/

/-- A rounded sum of nonnegative words: under the standard model with $0 \le \boldsymbol{u}
\le 1$, the words $w_0, \dots, w_j \ge 0$ summed left to right by $j$ rounded additions give a
sum between $(1 - \boldsymbol{u})^j$ and $(1 + \boldsymbol{u})^j$ times $\sum_{i \le j} w_i$. -/
theorem foldWords_add_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu1 : u ≤ 1)
    {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j : ℕ) :
    (1 - u) ^ j * ∑ i ∈ Finset.range (j + 1), w i ≤ foldWords M.add w j ∧
      foldWords M.add w j ≤ (1 + u) ^ j * ∑ i ∈ Finset.range (j + 1), w i := by
  have hu := hM.roundoff_nonneg
  induction j with
  | zero => simp [foldWords]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    set S := ∑ i ∈ Finset.range (j + 1), w i
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
    have hu1' : 0 ≤ 1 - u := by linarith
    have hF0 : 0 ≤ foldWords M.add w j := le_trans (by positivity) h1
    have ha := abs_le.mp (hM.add (foldWords M.add w j) (w (j + 1)))
    simp only [id] at ha
    rw [abs_of_nonneg (add_nonneg hF0 (hw _))] at ha
    simp only [foldWords]
    rw [Finset.sum_range_succ, pow_succ, pow_succ]
    have hw1 := hw (j + 1)
    have hp1 : (1 - u) ^ j ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hp2 : 1 ≤ (1 + u) ^ j := one_le_pow₀ (by linarith)
    have hp0 : 0 ≤ (1 - u) ^ j := pow_nonneg (by linarith) j
    obtain ⟨ha1, ha2⟩ := ha
    have e1 := mul_le_mul_of_nonneg_left h1 hu1'
    have e2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 + u by linarith)
    have e3 : (1 - u) ^ j * (1 - u) * w (j + 1) ≤ (1 - u) * w (j + 1) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hw1
    have e4 : (1 + u) * w (j + 1) ≤ (1 + u) ^ j * (1 + u) * w (j + 1) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hw1
    constructor <;> nlinarith

/-- The rounded Euclidean norm of $k$ complex numbers: under the standard model with
$4(k + 2)\boldsymbol{u} \le 1$, the machine square root of the rounded sum of the exact literal
$0$ and the machine squared moduli of $z_0, \dots, z_{k-1}$ is within
$(2k + 6)\boldsymbol{u}$, relatively, of $\bigl(\sum_{j<k}\lvert z_j\rvert^2\bigr)^{1/2}$. -/
theorem abs_sqrt_sumNormSq_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (z : ℕ → ℂ) {k : ℕ} (hu : 4 * (k + 2) * u ≤ 1) :
    |M.sqrt (foldWords M.add (normSqFactors M (M.lit 0) z) k) -
        √(∑ j ∈ Finset.range k, ‖z j‖ ^ 2)| ≤
      (2 * k + 6) * u * √(∑ j ∈ Finset.range k, ‖z j‖ ^ 2) := by
  have hu0 := hM.roundoff_nonneg
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hu1 : u ≤ 1 := by nlinarith
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  set Q := ∑ j ∈ Finset.range k, ‖z j‖ ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => by positivity
  set w := normSqFactors M (M.lit 0) z
  have hb := fun j => normSqWord_bounds hM hu0 hu1 (z j)
  have hw : ∀ i, 0 ≤ w i := fun i => by
    cases i with
    | zero => simp [w, normSqFactors, h0]
    | succ j => exact le_trans (by positivity) (hb j).1
  have hsum : ∑ i ∈ Finset.range (k + 1), w i = ∑ j ∈ Finset.range k, normSqWord M (z j) := by
    rw [Finset.sum_range_succ']; simp [w, normSqFactors, h0]
  obtain ⟨hf1, hf2⟩ := foldWords_add_bounds hM hu1 hw k
  rw [hsum] at hf1 hf2
  have hs1 : (1 - u) ^ 2 * Q ≤ ∑ j ∈ Finset.range k, normSqWord M (z j) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => (hb j).1
  have hs2 : ∑ j ∈ Finset.range k, normSqWord M (z j) ≤ (1 + u) ^ 2 * Q := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => (hb j).2
  set x := foldWords M.add w k
  set y : ℝ := 2 * (k + 2) * u
  have hy0 : 0 ≤ y := by positivity
  have hup : (1 + u) ^ (k + 2) ≤ 1 + y :=
    (one_add_pow_le_one_add_two_mul hu0 (by push_cast; nlinarith)).trans (by push_cast; simp [y])
  have hlow : 1 - y ≤ (1 - u) ^ (k + 2) := by
    have := one_add_mul_le_pow (a := -u) (by linarith) (k + 2)
    rw [← sub_eq_add_neg] at this
    push_cast at this; simp only [y]; nlinarith
  have hpk0 : 0 ≤ (1 - u) ^ k := pow_nonneg (by linarith) k
  have hxlo : (1 - y) * Q ≤ x := by
    calc (1 - y) * Q ≤ (1 - u) ^ (k + 2) * Q := mul_le_mul_of_nonneg_right hlow hQ
      _ = (1 - u) ^ k * ((1 - u) ^ 2 * Q) := by ring
      _ ≤ (1 - u) ^ k * ∑ j ∈ Finset.range k, normSqWord M (z j) :=
          mul_le_mul_of_nonneg_left hs1 hpk0
      _ ≤ x := hf1
  have hxhi : x ≤ (1 + y) * Q := by
    calc x ≤ (1 + u) ^ k * ∑ j ∈ Finset.range k, normSqWord M (z j) := hf2
      _ ≤ (1 + u) ^ k * ((1 + u) ^ 2 * Q) := mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = (1 + u) ^ (k + 2) * Q := by ring
      _ ≤ (1 + y) * Q := mul_le_mul_of_nonneg_right hup hQ
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (by nlinarith) hQ) hxlo
  have hroot := abs_rpow_inv_natCast_sub_le (p := 2) (by norm_num) hQ hy0 (by nlinarith) hxlo hxhi
  have hsx : ∀ a : ℝ, a ^ (((2 : ℕ) : ℝ))⁻¹ = √a := fun a => by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsx, hsx] at hroot
  have hsq := hM.sqrt x hx0
  simp only [id] at hsq
  have hQs := Real.sqrt_nonneg Q
  have h2 : √x ≤ (1 + y) * √Q := by
    have := (abs_le.mp hroot).2; norm_num at this ⊢; linarith
  have h3 := abs_sub_le (M.sqrt x) (√x) √Q
  have h4 : u * √x ≤ u * ((1 + y) * √Q) := mul_le_mul_of_nonneg_left h2 hu0
  have h5 : 2 * y / ((2 : ℕ) : ℝ) * √Q = y * √Q := by norm_num
  have h6 : u * y ≤ u := by
    have : y ≤ 1 := by simp only [y]; nlinarith
    nlinarith
  have h7 : y * √Q + u * ((1 + y) * √Q) ≤ (2 * k + 6) * u * √Q := by
    simp only [y]; nlinarith [mul_le_mul_of_nonneg_right h6 hQs, mul_nonneg hu0 hQs]
  linarith

/-- **The rounded Euclidean norm of a stored complex vector** of length $k$ at `D`, with three
caller-owned scratch words `T`: the exact literal $0$, plus the machine squared moduli of the
$k$ pairs, then one square root, into the word `P`. The interface is `[k] (D, T) → (P)`. -/
def pairVecNormWithScratch : Stmt Op Tst := ops% [k] (D, T) → (P) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (P);
  for j < k {
    run PairScalar.normSq [] (D[2 * j], T);
    call (Has.inj ScalarOp.add) [] (P, T[2]) → (P)
  };
  call (Has.inj ScalarOp.sqrt) [] (P) → (P)
}

/-- The word `NLAlib.ShiftedQR.pairVecNormWithScratch` stores for the vector $\mathbf{r}$. -/
def pairVecNormWord (M : Machine ℝ) {N : ℕ} (r : Fin N → ℂ) : ℝ :=
  M.sqrt (foldWords M.add (normSqFactors M (M.lit 0) (vecGetD r)) N)

/-- The rounded Euclidean norm on any scalar machine: with the vector $\mathbf{r}$ stored at `D`
and the three scratch words and the output word apart from it and from each other,
`pairVecNormWithScratch` stores `NLAlib.ShiftedQR.pairVecNormWord` and writes only the output
and the scratch.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem pairVecNormWithScratch_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {r : Fin N → ℂ} {d t p : ℕ × ℕ}
    (hD : HoldsMatrix d (Matrix.replicateCol (Fin 1) r) m.store)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hp : p.2 < m.store.len p.1)
    (hdt : Fp.Disj (Store.inBlock d.1 d.2 (2 * (1 * N))) (Store.inBlock t.1 t.2 3))
    (hdp : Fp.Disj (Store.inBlock d.1 d.2 (2 * (1 * N))) (Store.inBlock p.1 p.2 1))
    (htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ pairVecNormWithScratch (Env.frame [N] [d, t, p])
      (Store.inBlock p.1 p.2 1 ⊔ Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (pairVecNormWord M r)) m := by
  unfold pairVecNormWithScratch
  refine (writes_call_const (hS (.lit 0)) rfl trivial hp).seq_le le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hZero⟩
  have hD₁ := hD.of_eqOff hfr₁ hdp.symm
  have hloop := writes_loop_normSqOpRound (τ := τ) (m := m₁) (N := N) hS (o := .add) rfl
    (ρ := Env.frame [N] [d, t, p]) (cnt := .var 0) rfl
    (xs := fun i => (d.1, d.2 + 2 * i)) (tl := t) (pl := p)
    (R := Store.inBlock d.1 d.2 (2 * (1 * N))) (z := vecGetD r) (v := M.lit 0)
    (x := ⟨0, .var 1 + .const 2 * .var 4⟩) (t := ⟨1, .var 2⟩) (p := ⟨2, .var 3⟩)
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i _ => by simp [Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (fun i hi => Fp.inBlock_le_inBlock (by omega) (by omega))
    (fun i hi => by
      have h := hD₁.get_re ⟨i, hi⟩ 0
      simpa [vecGetD, hi] using h)
    (fun i hi => by
      have h := hD₁.get_im ⟨i, hi⟩ 0
      simpa [vecGetD, hi, Nat.add_assoc] using h)
    (by rw [hfr₁.len_eq]; exact ht) hZero hdt hdp htp
  refine (hloop.seq_le le_rfl ?_)
  intro m₂ _ ⟨hp₂, hP₂⟩
  refine (writes_call_un (hS .sqrt) rfl rfl trivial hP₂ rfl
    (Store.lt_len_of_get hP₂)).mono le_sup_left ?_
  intro m₃ _ ⟨hp₃, hR₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hR₃⟩

/-- The rounded Euclidean norm is accurate: under the standard model with
$4(N + 2)\boldsymbol{u} \le 1$, `NLAlib.ShiftedQR.pairVecNormWord` of $\mathbf{r} \in
\mathbb{C}^N$ is within $(2N + 6)\boldsymbol{u}\|\mathbf{r}\|$ of $\|\mathbf{r}\|$. -/
theorem abs_pairVecNormWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (hu : 4 * (N + 2) * u ≤ 1) (r : Fin N → ℂ) :
    |pairVecNormWord M r - ‖WithLp.toLp 2 r‖| ≤ (2 * N + 6) * u * ‖WithLp.toLp 2 r‖ := by
  have h := abs_sqrt_sumNormSq_sub_le hM (vecGetD r) (k := N) hu
  have e : √(∑ j ∈ Finset.range N, ‖vecGetD r j‖ ^ 2) = ‖WithLp.toLp 2 r‖ := by
    rw [EuclideanSpace.norm_eq, Finset.sum_range fun j => ‖vecGetD r j‖ ^ 2]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [vecGetD, l.isLt]
  rw [e] at h
  exact h

end NLAlib.ShiftedQR
