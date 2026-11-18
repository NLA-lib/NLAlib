/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleRoutine
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleSpec
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheoremsBits
public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Matrix.Perturbation.EigenvalueMatching
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveSchur

/-!
# The rounded shifted QR algorithm: headline theorems

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of
[BanksGarzaVargasSrivastava2022, Theorem 1.4], in floating point, corrected: the decoupling loop
is capped, the deflation scan covers the bottom $k$ subdiagonal entries, and the precision
threshold is recomputed for the corrected constants of the blocks, and the output is a Schur form.
The program is the rounded deflation worklist in Schur mode (`NLAlib.ShiftedQR.solveRoundedWith`)
with the decoupling loop of Lemma 6.4 (`NLAlib.ShiftedQR.roundedDecoupleWith`: `Regularize`, then
$\mathrm{Sh}_{k,B}$, capped at $F$ rounds) and a small-block Schur solver as the leaf
(`NLAlib.ShiftedQR.roundedShQRWith L`), whose diagonal also gives `Regularize` its Ritz values
(`NLAlib.ShiftedQR.schurDiag`); `NLAlib.ShiftedQR.roundedShQRSmallEig` runs the `SmallEig`
program as the leaf. It is run with the parameter words of `NLAlib.ShiftedQR.shqrParams` and the
threshold word `NLAlib.ShiftedQR.shqrDeflationThreshold` on a machine with unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ (`NLAlib.ShiftedQR.uShQR`) and at most the
replay term (`NLAlib.ShiftedQR.uShQRSchurReplay`).

The parameters are those of `NLAlib.ShiftedQR.shqrParams_spec` (condition $4B$, separation
$\Gamma/4$ and iterate norm $4\Sigma$ inside the loop, block norm $2\Sigma$ in the worklist) and of
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` with $n_{\max} = n$,
$N_{\max} = 2\Sigma$, $S = 4\Sigma$, the loop's threshold word $t_L$
(`NLAlib.ShiftedQR.shqrLoopThreshold`) and $\omega_D$ from it.

What is not claimed here: no Hessenberg reduction or preprocessing of a general matrix
(`NLAlib.Eigensolvers.Schur.Dense`); nothing on the leaf's own cost or precision; no forward
error for the eigenvalues; no rounded disk sampler; nothing for repeated eigenvalues. Modelling
assumptions the paper does not make: the parameter words are exact reals. With a generic leaf the
leaf is an oracle, a hypothesis `NLAlib.Schur.RandomSchurLeafContract` (the Schur form of
[BanksGarzaVargasSrivastava2022, Definition 1.2]).

## Main definitions

* `NLAlib.ShiftedQR.roundedShQRSmallEig`: the program.
* `NLAlib.ShiftedQR.shqrParams`, `NLAlib.ShiftedQR.shqrDims`: its parameter words and
  dimensions.
* `NLAlib.ShiftedQR.ShQRInput`, `NLAlib.ShiftedQR.ShQRSpectrum`: the memory holding the input,
  and the memory holding the spectrum of a nearby matrix.

## Main results

* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`: the headline.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`: termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQR_le`: the bits of precision.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_relative`: the relative backward error.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_hermitian`: Hermitian inputs.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_work_le`: the operation count.
* `NLAlib.ShiftedQR.roundedShQRWith`,
  `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`,
  `NLAlib.ShiftedQR.roundedShQRWith_terminates`: the algorithm with a small-block Schur solver
  (`NLAlib.Schur.RandomSchurLeafContract`) in the place of the eigenvalue oracle.
* `NLAlib.ShiftedQR.roundedShQRSchurWith`,
  `NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`,
  `NLAlib.ShiftedQR.roundedShQRSchurWith_terminatingSchurCore`: the same algorithm as the Schur
  core stage of the dense Schur pipeline, with any small-block Schur solver.

The headline on one run, with explicit work and span bounds conjoined with correctness, is the
certificate `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`
(`NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEigCertificate`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The eigenvalue routine of a Schur leaf**: run the Schur leaf `L` on a scoped copy of the
block `Bk` with a scoped accumulator and copy the diagonal of the triangular result to `Ev` (the
eigenvalues of the leaf's perturbed block). `Regularize` needs only these Ritz values. The
interface is `[d, nq, T] (Bk, Qw) → (Ev)`, that of a small-eigenvalue routine. -/
def schurDiag (L : Impl O Q) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  let W ← alloc (2 * (d * d));
  let Ub ← alloc (2 * (d * d));
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (d * d)] (Bk, W);
  run L.body [d, nq, T] (W, Qw, W, Ub);
  for i < d {
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i)]) → (Ev[2 * i]);
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i) + 1]) → (Ev[2 * i + 1])
  }
}

/-- **A Schur leaf on the tail words**: run the Schur leaf `L` (`[d, 12, T] (Bk, Q) → (Bk, Ub)`)
with the last $12$ of the $n_p$ parameter words, `P[np - 12]`, as its words. The interface is
`[d, np, T] (Bk, P) → (Bk, Ub)`, that of the leaf routine of `NLAlib.ShiftedQR.solveRoundedWith`;
the decoupling loop hands the same tail to the leaf's eigenvalue routine
(`NLAlib.ShiftedQR.roundedDecoupleLoopWith`). -/
def leafOnTailWords (L : Impl O Q) : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Bk, Ub) {
  run L.body [d, 12, T] (Bk, P[np - 12], Bk, Ub)
}

/-- **The rounded shifted QR algorithm in Schur mode with a Schur leaf**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the routine of
[BanksGarzaVargasSrivastava2025, Corollary 1.3], with the Schur form): the worklist
`NLAlib.ShiftedQR.solveRoundedWith` in Schur mode with the decoupling loop
`NLAlib.ShiftedQR.roundedDecoupleWith` (whose Ritz values come from the leaf,
`NLAlib.ShiftedQR.schurDiag L`) and the Schur leaf `L` (`NLAlib.ShiftedQR.leafOnTailWords L`). The
leaf reads the last $12$ parameter words and the cap $T$. The interface is
`[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`.
Algorithm: shifted-qr-rounded -/
def roundedShQRWith (L : Impl O Q) : Impl O Q :=
  solveRoundedWith (roundedDecoupleWith (schurDiag L)) (leafOnTailWords L)

/-- **The rounded shifted QR algorithm as a Schur core stage** with the Schur leaf `L`: the
threshold word is the first parameter word, and the log shape is the one the decoupler needs,
$n_s = F(k + 1 + n_p')$ slots of $w = kN$ entries ($n_p' = n_p - 1$ the remaining words). The
interface is `[N, np, k, F, T] (A, P, U) → (A, U, Fl)`, that of the core stage of the dense Schur
pipeline (`NLAlib.Schur.RandomSchurCoreContract`).
Algorithm: shifted-qr-rounded -/
def roundedShQRSchurWith (L : Impl O Q) : Impl O Q :=
  opsImpl% [N, np, k, F, T] (A, P, U) → (A, U, Fl) {
    run (roundedShQRWith L).body [N, k, np - 1, F, T, F * (k + 1 + (np - 1)), k * N]
      (A, P, P[1], U, A, U, Fl)
  }

end Program

/-- **The parameter words of the rounded shifted QR algorithm** at the order $n + 1$, the shift
degree $k$, the condition bound $B$, the separation $\Gamma$, the norm bound $\Sigma$ (`S`), the
backward error $\delta$ and the failure $\varphi$: the words of
`NLAlib.ShiftedQR.roundedDecoupleParams` with the loop's threshold word $t_L$, Regularize's
radius, the iteration's threshold word, $\gamma = 0.2$, the class constant $4B$, its $\alpha$ and
Exc's $\varepsilon$, and $k = 2^{\log_2 k}$. -/
noncomputable def shqrParams (n k : ℕ) (B Γ S δ φ : ℝ) : List ℝ :=
  roundedDecoupleParams (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
    (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B)) k
    (Nat.log 2 k)

/-- The dimensions of a run: the order $n + 1$, the shift degree $k$, the number of parameter
words and the iteration cap $F$ (`NLAlib.ShiftedQR.shqrCap`). -/
noncomputable def shqrDims (n k : ℕ) (B Γ S δ φ : ℝ) : List ℕ :=
  [n + 1, k, (shqrParams n k B Γ S δ φ).length, shqrCap n B Γ S δ]

/-- **The memory holding the input** of the rounded shifted QR algorithm: the views of the
matrix, the threshold word, the parameter words, the output and the failure word are live, have
room and are apart; the matrix $\mathbf{H}$, the deflation threshold word and the parameter words
are stored. -/
def ShQRInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (a t p out f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    (∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix out U μ.store) ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ).length = some (shqrParams n k B Γ S δ φ)

/-- **The memory holding the spectrum of a nearby matrix**: the failure word is $0$ and the
output holds all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le e$. -/
def ShQRSpectrum {n : ℕ} (a out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : ℝ)
    (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧
    ∃ (Tm U E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a Tm μ'.store ∧ HoldsMatrix out U μ'.store ∧ Tm.IsUpperTriangular ∧
        specNorm E ≤ e ∧ (H + E).charpoly.roots = (List.ofFn fun i => Tm i i : Multiset ℂ)

/-- The regions the rounded shifted QR algorithm writes: the matrix, the output and the failure
word. -/
def shqrFp (n : ℕ) (a out f : ℕ × ℕ) : Fp :=
  Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock out.1 out.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1


section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The bits of precision** ([BanksGarzaVargasSrivastava2022, Theorem 1.4], corrected: the
printed argument $nB/(\delta\Gamma\varphi)$ is not invariant under scaling of $\mathbf{H}$, and
Optimal's rounding constant, [BanksGarzaVargasSrivastava2022, Lemma 4.5], is $kn^{3/2}$ in place
of $2n^2$): there are absolute constants $c_1, c_2$ such that for every order $n + 1$,
$B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$,
$$\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le
  c_1 k \log_2\frac{4(n + 1)B\Sigma^2}{\delta\min(\Gamma, \Sigma)\varphi} + c_2.$$
The argument is scale-invariant ($\delta$ is an absolute error, so $\Sigma^2/(\delta\Gamma)$, not
$\Sigma/(\delta\Gamma)$) and at least $4$; $\min(\Gamma, \Sigma)$ covers $n = 0$, where the gap is
vacuous and $\Gamma$ unbounded (for $n \ge 1$, $\Gamma \le 2\Sigma$). The constants $c_1 = 63$ and
$c_2 = 0$ suffice: $\boldsymbol{u}_{\mathrm{ShQR}}$ is at least the argument to the power
$-(53k + 40)$ (`NLAlib.ShiftedQR.one_le_uShQR_mul`). -/
theorem logb_inv_uShQR_le : ∃ c₁ c₂ : ℝ, ∀ {n k : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ →
    δ ≤ S → 0 < φ → φ ≤ 1 → k = shqrDegree (4 * B) →
    Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤
      c₁ * k * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) + c₂ := by
  refine ⟨63, 0, fun {n k B Γ S δ φ} hB hΓ hδ hδS hφ hφ1 hk => ?_⟩
  obtain ⟨hY4, h⟩ := one_le_uShQR_mul (n := n) hB hΓ hδ hδS hφ hφ1 hk
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  have hk4 : (4 : ℝ) ≤ k := hk ▸ (shqrDegree_facts (by linarith : (1 : ℝ) ≤ 4 * B)).1
  have hu : 0 < uShQR n k B Γ S δ φ :=
    uShQR_pos (by exact_mod_cast (show (0 : ℝ) < k by linarith)) hB hΓ hδ (hδ.trans_le hδS) hφ
  have hY0 : 0 < Y := by linarith
  have hL : 0 ≤ Real.logb 2 Y := Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (uShQR n k B Γ S δ φ)⁻¹ ≤ Y ^ (53 * k + 40) := by
    rw [inv_le_iff_one_le_mul₀ hu, mul_comm]; exact h
  calc Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤ Real.logb 2 (Y ^ (53 * k + 40)) :=
        Real.logb_le_logb_of_le (by norm_num) (inv_pos.mpr hu) h1
    _ = ((53 * k + 40 : ℕ) : ℝ) * Real.logb 2 Y := by rw [Real.logb_pow]
    _ ≤ 63 * k * Real.logb 2 Y := by push_cast; nlinarith
    _ = 63 * k * Real.logb 2 Y + 0 := by ring

end Theorems

/-! ### The algorithm with a Schur leaf -/

/-- The capacity $n_s w$ of the log of the Schur-mode worklist at the order $n + 1$, the shift
degree $k$, $n_p$ words and the cap $F$: $n_s = F(k + 1 + n_p)$ slots of $w = k(n + 1)$ entries. -/
def shqrSchurLogSize (n k np F : ℕ) : ℕ := F * (k + 1 + np) * (k * (n + 1))

/-- **The replay term of the precision threshold** of the Schur-mode algorithm with a leaf of
$R_L$ rotation-equivalents: the unit roundoff at which the replays of the logs on the couplings
and on the accumulator ($78\boldsymbol{u}\,n_s w N_0$ per round), the leaf products
($8(n + 1)(k + 2)\boldsymbol{u}N_0$ per round) and the scaling of the couplings by a leaf
accumulator within $\varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1 \le 27R_L\boldsymbol{u}$ of
a unitary ($2\varepsilon_L N_0$ per round), over $2(n + 1)$ rounds at $N_0 = 2\Sigma$, cost at most
a quarter of the budget $\min(\delta, \Gamma/(16(n + 1)B))$ (`NLAlib.ShiftedQR.shqrBudget`). -/
noncomputable def uShQRSchurReplay (n k np F RL : ℕ) (B Γ S δ : ℝ) : ℝ :=
  shqrBudget n B Γ δ /
    (16 * ((n : ℝ) + 1) *
      (78 * shqrSchurLogSize n k np F + 8 * ((n : ℝ) + 1) * (k + 2) + 54 * RL) * S)

/-- The rotation count of the accumulator of the Schur-mode algorithm with a leaf of $R_L$
rotation-equivalents: $2(n + 1)$ rounds of at most $n_s w$ replayed rotations and the leaf
products ($2k(k + 2)$), and $n + 1$ leaves. -/
def shqrSchurRotations (n k np F RL : ℕ) : ℕ :=
  2 * (n + 1) * (shqrSchurLogSize n k np F + 2 * k * (k + 2)) + (n + 1) * RL

section Routine

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- Two more stored words: if the first $2i$ words at `o` are stored and the words $2i$ and
$2i + 1$ are written one after the other, the first $2(i + 1)$ words are stored. -/
private theorem isSome_two_writes {s s₁ s₂ : Store ℝ} {o : ℕ × ℕ} {i : ℕ} {v₁ v₂ : ℝ}
    (h : ∀ j < 2 * i, (s.get o.1 (o.2 + j)).isSome)
    (hfr₁ : s.EqOff (Store.inBlock o.1 (o.2 + 2 * i) 1) s₁)
    (g₁ : s₁.get o.1 (o.2 + 2 * i) = some v₁)
    (hfr₂ : s₁.EqOff (Store.inBlock o.1 (o.2 + 2 * i + 1) 1) s₂)
    (g₂ : s₂.get o.1 (o.2 + 2 * i + 1) = some v₂) :
    ∀ j < 2 * (i + 1), (s₂.get o.1 (o.2 + j)).isSome := by
  intro j hj
  rcases Nat.lt_or_ge j (2 * i) with hj' | hj'
  · rw [hfr₂.get_eq (fun h' => by have := h'.2; omega),
      hfr₁.get_eq (fun h' => by have := h'.2; omega)]
    exact h j hj'
  · rcases Nat.lt_or_ge j (2 * i + 1) with hj'' | hj''
    · rw [show o.2 + j = o.2 + 2 * i by omega, hfr₂.get_eq (fun h' => by
        have := h'.2; omega), g₁]; rfl
    · rw [show o.2 + j = o.2 + 2 * i + 1 by omega, g₂]; rfl

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- **The eigenvalue routine of a completing Schur leaf terminates**: on a scalar machine, if
the Schur leaf `L` completes on orders at most $k_{\max}$ with the $12$ words `qs`
(`NLAlib.ShiftedQR.CompletingLeafRoutine`), then `NLAlib.ShiftedQR.schurDiag L` terminates as a
small-eigenvalue routine (`NLAlib.ShiftedQR.TerminatingSmallEigAt`) on the same orders. -/
theorem CompletingLeafRoutine.terminatingSmallEigAt_schurDiag {Mch : Machine ℝ}
    {I : Interp O Q ℝ} (hS : IsScalar Mch I) {kmax T : ℕ} {qs : List ℝ}
    {L : Impl O Q} (hLf : CompletingLeafRoutine kmax qs T L I) (hq : qs.length = 12) :
    TerminatingSmallEigAt kmax 12 T qs (schurDiag L) I := by
  intro d w q o tape μ B hd hB hqs hl ho hwo hqo
  have hwl : w.1 < μ.store.length := hl w (by simp)
  have hql : q.1 < μ.store.length := hl q (by simp)
  have hol : o.1 < μ.store.length := hl o (by simp)
  unfold schurDiag
  change Writes .total I tape (Stmt.allocs [IExp.const 2 * (IExp.var 0 * IExp.var 0),
    IExp.const 2 * (IExp.var 0 * IExp.var 0)] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * (d * d), 2 * (d * d)])
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (fun hBelow ⟨ys, hys⟩ => ⟨ys, (hBelow.readBlock hol _ _).trans hys⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hL0 : s₁.len Lc = 2 * (d * d) := by simpa using hlens 0 (by simp)
  have hL1 : s₁.len (Lc + 1) = 2 * (d * d) := by simpa using hlens 1 (by simp)
  have hab : ∀ {X : Fp}, (∀ b i, X b i → Lc ≤ b) →
      X ≤ Store.inBlock o.1 o.2 (2 * d) ⊔ Fp.above Lc :=
    fun hX b i h => Or.inr (hX b i h)
  refine (writes_unaryMap_of_disj_or_eq (hS .copy) (τ := tape) (m := ⟨s₁, μ.pos⟩) (x := w)
    (y := (Lc, 0)) (n := 2 * (d * d)) (Or.inl (Fp.disj_inBlock_of_ne (by omega)))
    (by rw [hBelow.readBlock hwl]; exact hB) (by simp [hL0])).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h <;> rw [h] <;> first | omega | (dsimp only; omega))
    (hab fun b i h => h.1 ▸ le_rfl) ?_
  rintro μ₁ hfr₁ ⟨-, hW₁⟩
  have hW₁' : HoldsMatrix (Lc, 0) B μ₁.store := by simpa [HoldsMatrix] using hW₁
  have hlen₁ : μ₁.store.length = Lc + 2 := hfr₁.length_eq.trans hlen
  have hqs₁ : μ₁.store.readBlock q.1 q.2 qs.length = some qs :=
    hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne (by dsimp only; omega))
      (by change s₁.readBlock q.1 q.2 qs.length = some qs; rw [hBelow.readBlock hql]; exact hqs)
  have hl₁ : μ₁.Live [(Lc, 0), q, (Lc + 1, 0)] := fun v hv => by
    rw [hlen₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> rw [h] <;> first | omega | (dsimp only; omega)
  refine (hLf (tape := tape) B hd hW₁' hqs₁ hl₁ (by dsimp only; rw [hfr₁.len_eq, hL1]; omega)
    (Fp.disj_inBlock_of_ne (by omega)) (Fp.disj_sup_right.mpr
      ⟨Fp.disj_inBlock_of_ne (by dsimp only; omega),
        Fp.disj_inBlock_of_ne (by dsimp only; omega)⟩)).frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame, hq])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun v hv => hl₁ v (by simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto))
    (hab fun b i h => by rcases h with h | h <;> (have := h.1; dsimp only at this; omega)) ?_
  rintro μ₂ hfr₂ ⟨Tb, Ub, hTb, -⟩
  have hlen₂ : μ₂.store.length = Lc + 2 := hfr₂.length_eq.trans hlen₁
  have hroomo : o.2 + 2 * d ≤ μ₂.store.len o.1 := by
    rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow o.1 hol).1]; exact ho
  refine (writes_loop (N := d) (by simp [IExp.eval, Env.frame])
    (fun _ => Store.inBlock o.1 o.2 (2 * d)) (fun _ _ => le_rfl)
    (fun i m => m.store.length = Lc + 2 ∧ o.2 + 2 * d ≤ m.store.len o.1 ∧
      HoldsMatrix (Lc, 0) Tb m.store ∧ ∀ j < 2 * i, (m.store.get o.1 (o.2 + j)).isSome)
    ⟨hlen₂, hroomo, hTb, fun j hj => by omega⟩ ?_).mono le_sup_left ?_
  · intro i hi m _ ⟨h1, h2, h3, h4⟩
    have hTo : Fp.Disj (Store.inBlock o.1 o.2 (2 * d)) (Store.inBlock (Lc, 0).1 (Lc, 0).2
        (2 * (d * d))) := Fp.disj_inBlock_of_ne (by dsimp only; omega)
    refine (writes_call_un (hS .copy) (x := (Lc, 2 * (i * d + i))) (z := (o.1, o.2 + 2 * i))
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx]) trivial
      (by simpa using h3.get_re ⟨i, hi⟩ ⟨i, hi⟩) rfl (by dsimp only; omega)).seq_le
      (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro m₁ hfr₁' ⟨-, g₁⟩
    refine (writes_call_un (hS .copy) (x := (Lc, 2 * (i * d + i) + 1))
      (z := (o.1, o.2 + 2 * i + 1))
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx]) trivial
      (by rw [hfr₁'.get_eq (fun h' => by have := h'.1; dsimp only at this; omega)]
          simpa [Nat.add_assoc] using h3.get_im ⟨i, hi⟩ ⟨i, hi⟩) rfl
      (by dsimp only; rw [hfr₁'.len_eq]; omega)).mono
      (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
    rintro m₂ hfr₂' ⟨-, g₂⟩
    have hfr := hfr₁'.trans' hfr₂'
    refine ⟨by rw [hfr.length_eq, h1], by rw [hfr.len_eq]; exact h2,
      h3.of_eqOff hfr (Fp.disj_sup_left.mpr ⟨hTo.mono (Fp.inBlock_le_inBlock (by omega)
        (by omega)) le_rfl, hTo.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl⟩),
      isSome_two_writes h4 hfr₁' g₁ hfr₂' g₂⟩
  · rintro m - ⟨-, -, -, h4⟩
    exact Option.isSome_iff_exists.mp (Store.isSome_readBlock_iff.mpr h4)

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- A Schur leaf on its $12$ words `qs` with its accumulator near a unitary if `P` has it on
the tail words of `ps ++ qs`: `NLAlib.ShiftedQR.leafOnTailWords L` is such a leaf routine with
the words `ps ++ qs`. -/
theorem TerminatingLeafRoutineIf.onTailWords {P : Prop} {εL : ℝ} {kmax T : ℕ} {qs : List ℝ}
    {L : Impl O Q} {I : Interp O Q ℝ} (hLf : TerminatingLeafRoutineIf P εL kmax qs T L I)
    (hq : qs.length = 12) (ps : List ℝ) :
    TerminatingLeafRoutineIf P εL kmax (ps ++ qs) T (leafOnTailWords L) I := by
  intro d w p ub tape μ B hd hB hp hl hroom hwu hpd
  have hq' : μ.store.readBlock p.1 (p.2 + ps.length) qs.length = some qs :=
    Store.readBlock_append_right hp
  have hsub : Store.inBlock p.1 (p.2 + ps.length) qs.length ≤
      Store.inBlock p.1 p.2 (ps ++ qs).length :=
    Fp.inBlock_le_inBlock (by omega) (by rw [List.length_append]; omega)
  have hl' : μ.Live [w, (p.1, p.2 + ps.length), ub] := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> rw [h]
    exacts [hl w (by simp), hl p (by simp), hl ub (by simp)]
  unfold ShiftedQR.leafOnTailWords
  exact (hLf (tape := tape) B hd hB hq' hl' hroom hwu (hpd.mono hsub le_rfl)).in_frame
    (by simp [IExp.evalList, IExp.eval, Env.frame, hq])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, hq])
    (fun v hv => hl' v (by simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto))

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- A terminating Schur leaf on its $12$ words `qs` terminates on the tail words of `ps ++ qs`
(`NLAlib.ShiftedQR.TerminatingLeafRoutineIf.onTailWords`). -/
theorem TerminatingLeafRoutine.onTailWords {εL : ℝ} {kmax T : ℕ} {qs : List ℝ}
    {L : Impl O Q} {I : Interp O Q ℝ} (hLf : TerminatingLeafRoutine εL kmax qs T L I)
    (hq : qs.length = 12) (ps : List ℝ) :
    TerminatingLeafRoutine εL kmax (ps ++ qs) T (leafOnTailWords L) I :=
  TerminatingLeafRoutineIf.terminating
    (TerminatingLeafRoutineIf.onTailWords (hLf.terminatingLeafRoutineIf True) hq ps) trivial

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- A completing Schur leaf on its $12$ words `qs` completes on the tail words of `ps ++ qs`
(`NLAlib.ShiftedQR.TerminatingLeafRoutineIf.onTailWords`). -/
theorem CompletingLeafRoutine.onTailWords {kmax T : ℕ} {qs : List ℝ}
    {L : Impl O Q} {I : Interp O Q ℝ} (hLf : CompletingLeafRoutine kmax qs T L I)
    (hq : qs.length = 12) (ps : List ℝ) :
    CompletingLeafRoutine kmax (ps ++ qs) T (leafOnTailWords L) I :=
  TerminatingLeafRoutineIf.completing
    (TerminatingLeafRoutineIf.onTailWords (hLf.terminatingLeafRoutineIf 0) hq ps)

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- A Schur leaf on its $12$ words `qs` is a Schur leaf on the tail words of `ps ++ qs`:
`NLAlib.ShiftedQR.leafOnTailWords L` meets the contract of `L` with the words `ps ++ qs`. -/
theorem _root_.NLAlib.Schur.RandomSchurLeafContract.onTailWords {law : ℕ → Measure ℝ}
    {εL βL φL Nmax : ℝ} {kmax T : ℕ} {qs : List ℝ} {L : Impl O Q} {I : Interp O Q ℝ}
    (hLf : Schur.RandomSchurLeafContract law εL βL φL kmax Nmax qs T L I)
    (hq : qs.length = 12) (ps : List ℝ) :
    Schur.RandomSchurLeafContract law εL βL φL kmax Nmax (ps ++ qs) T (leafOnTailWords L) I := by
  intro d w p ub B hd hBN
  unfold ShiftedQR.leafOnTailWords
  refine ((hLf (w := w) (p := (p.1, p.2 + ps.length)) (ub := ub) B hd hBN).in_frame
    (by simp [IExp.evalList, IExp.eval, Env.frame, hq])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, hq])
    (fun μ h v hv => h.2.2.1 v (by
      simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto))).mono
    ?_ le_rfl (fun _ h => h) le_rfl
  rintro μ ⟨hB, hp, hl, hroom, hap⟩
  have hsub : Store.inBlock p.1 (p.2 + ps.length) qs.length ≤
      Store.inBlock p.1 p.2 (ps ++ qs).length :=
    Fp.inBlock_le_inBlock (by omega) (by rw [List.length_append]; omega)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hap ⊢
  refine ⟨hB, Store.readBlock_append_right hp, fun v hv => ?_, hroom,
    ⟨hap.1.1.mono le_rfl hsub, hap.1.2⟩, hap.2.mono hsub le_rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h <;> rw [h]
  exacts [hl w (by simp), hl p (by simp), hl ub (by simp)]

/-- **The backward accuracy of a forward accuracy, on one listing**: if $\mathbf{M}$ of order
$d \le k_{\max}$ has $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \beta \le \Sigma$ and `ev'` lists the
spectrum of $\mathbf{M} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta_b$
(`NLAlib.SmallEig.forwardBackwardError` $k_{\max}$ $\Sigma$ $\beta$), then `ev'` is within $\beta$
of a listing of the spectrum of $\mathbf{M}$ (the Ostrowski–Elsner matching,
`NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`). -/
theorem exists_isEigenvalueListing_norm_sub_le_of_forwardBackwardError {d kmax : ℕ}
    (hd : d ≤ kmax) {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) {M E : Matrix (Fin d) (Fin d) ℂ}
    (hMS : specNorm M ≤ S) (hE : specNorm E ≤ SmallEig.forwardBackwardError kmax S β)
    {ev' : Fin d → ℂ} (hL : IsEigenvalueListing (M + E) ev') :
    ∃ ev : Fin d → ℂ, IsEigenvalueListing M ev ∧ ∀ i, ‖ev' i - ev i‖ ≤ β := by
  rcases d with _ | n
  · exact ⟨ev', Subsingleton.elim (M + E) M ▸ hL, fun i => i.elim0⟩
  obtain ⟨-, hbS, h2⟩ := SmallEig.forwardBackwardError_spec (kmax := kmax) hβ hβS
  obtain ⟨ev, hev, hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow (A' := M) hL
  refine ⟨ev, hev, fun i => ?_⟩
  rw [norm_sub_rev]
  refine (hb i).trans (le_trans ?_ (h2 n hd))
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hE' : specNorm (M - (M + E)) = specNorm E := by rw [sub_add_cancel_left, specNorm_neg]
  have hsum : specNorm (M + E) + specNorm M ≤ 3 * S := by
    linarith [specNorm_add_le M E]
  have h0 : 0 ≤ specNorm (M + E) + specNorm M := by positivity
  rw [hE']
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hsum hα) (by positivity))
    (Real.rpow_le_rpow (specNorm_nonneg _) hE (by positivity)) (by positivity)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- **The eigenvalue routine of a Schur leaf meets the small-eigenvalue contract**: on a scalar
machine with a measurable interpretation reading the tape only in its windows, if the Schur leaf
`L` meets `NLAlib.Schur.RandomSchurLeafContract` on orders at most $k_{\max}$ and norms at most
$N$ with the $12$ words `qs`, failure $\varphi_L \ge 0$ and a backward error at most the
backward accuracy $\delta_b$ (`NLAlib.SmallEig.forwardBackwardError` $k_{\max}$ $N$ $\beta$) of
a forward accuracy $0 < \beta \le N$, then `NLAlib.ShiftedQR.schurDiag L` meets
`NLAlib.ShiftedQR.RandomSmallEigContractAt` with the forward error $\beta$ and the failure
$\varphi_L$: the diagonal of the leaf's triangular block lists, within $\beta$, the spectrum of
the block. -/
theorem _root_.NLAlib.Schur.RandomSchurLeafContract.randomSmallEigContractAt_schurDiag
    {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {εL βL φL N β : ℝ} {kmax T : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLf : Schur.RandomSchurLeafContract law εL βL φL kmax N qs T L I) (hq : qs.length = 12)
    (hφL : 0 ≤ φL) (hβ : 0 < β) (hβN : β ≤ N)
    (hβL : βL ≤ SmallEig.forwardBackwardError kmax N β) :
    RandomSmallEigContractAt law β φL kmax 12 T N qs (schurDiag L) I := by
  intro d w q o B hd _ hBN
  unfold schurDiag
  change PWrites law I (Stmt.allocs [IExp.const 2 * (IExp.var 0 * IExp.var 0),
    IExp.const 2 * (IExp.var 0 * IExp.var 0)] _) _ _ _ _ _
  refine PWrites.allocs (ns := [2 * (d * d), 2 * (d * d)])
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (Pre₁ := fun Lc μ => μ.store.length = Lc + 2 ∧ μ.store.len Lc = 2 * (d * d) ∧
      μ.store.len (Lc + 1) = 2 * (d * d) ∧ HoldsMatrix w B μ.store ∧
      μ.store.readBlock q.1 q.2 qs.length = some qs ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
      w.1 < Lc ∧ q.1 < Lc ∧ o.1 < Lc) ?_ ?_ fun Lc => ?_
  · rintro μ s₁ ⟨hW, hqs, hl, ho, -, -⟩ hlen hlens hBelow
    have hwl : w.1 < μ.store.length := hl w (by simp)
    have hql : q.1 < μ.store.length := hl q (by simp)
    have hol : o.1 < μ.store.length := hl o (by simp)
    simp only [List.length_cons, List.length_nil] at hlen
    exact ⟨hlen, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      hW.of_below hBelow hwl, (hBelow.readBlock hql _ _).trans hqs,
      by rw [(hBelow o.1 hol).1]; exact ho, hwl, hql, hol⟩
  · rintro μ ⟨-, -, hl, -⟩ s s' p hBelow ⟨roots, ev, hev, hb, hO⟩
    exact ⟨roots, ev, hev, hb, hO.of_below hBelow (hl o (by simp))⟩
  set Mid₁ : Mem ℝ → Prop := fun μ => μ.store.length = Lc + 2 ∧
    μ.store.len (Lc + 1) = 2 * (d * d) ∧ HoldsMatrix (Lc, 0) B μ.store ∧
    μ.store.readBlock q.1 q.2 qs.length = some qs ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
    q.1 < Lc ∧ o.1 < Lc with hMid₁
  set Mid₂ : Mem ℝ → Prop := fun μ => μ.store.length = Lc + 2 ∧
    o.2 + 2 * d ≤ μ.store.len o.1 ∧ o.1 < Lc ∧ ∃ Tb : Matrix (Fin d) (Fin d) ℂ,
      HoldsMatrix (Lc, 0) Tb μ.store ∧ ∃ ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        ∀ i, ‖Tb i i - ev i‖ ≤ β with hMid₂
  have hWU : Fp.Disj (Store.inBlock Lc 0 (2 * (d * d))) (Store.inBlock (Lc + 1) 0 (2 * (d * d))) :=
    Fp.disj_inBlock_of_ne (by omega)
  refine (PWrites.seq (Mid := Mid₁) (F₁ := Store.inBlock Lc 0 (2 * (d * d)))
    (F₂ := (Store.inBlock Lc 0 (2 * (d * d)) ⊔ Store.inBlock (Lc + 1) 0 (2 * (d * d))) ⊔
      Store.inBlock o.1 o.2 (2 * d)) hI hloc (by linarith : (0 : ℝ) ≤ φL + 0)
    (PWrites.of_writes le_rfl fun μ τ h => ?_)
    (PWrites.seq (Mid := Mid₂) hI hloc le_rfl ?_
      (PWrites.of_writes le_rfl fun μ τ h => ?_))).mono (fun _ h => h) ?_ (fun _ h => h)
      (by simp)
  · -- the copy of the block to the scratch block `(Lc, 0)`
    obtain ⟨hlen, hL0, hL1, hW, hqs, ho, hwL, hqL, hoL⟩ := h
    refine ((writes_unaryMap_of_disj_or_eq (hS .copy) (τ := τ) (m := μ) (x := w) (y := (Lc, 0))
      (n := 2 * (d * d)) (Or.inl (Fp.disj_inBlock_of_ne (by omega)))
      hW
      (by simp [hL0])).in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with h | h <;> rw [h] <;> omega)).mono le_rfl ?_
    rintro μ₁ hfr ⟨-, hW₁⟩
    refine ⟨hfr.length_eq.trans hlen, by rw [hfr.len_eq]; exact hL1,
      by simpa [HoldsMatrix] using hW₁, ?_, by rw [hfr.len_eq]; exact ho, hqL, hoL⟩
    exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hqs
  · -- the Schur leaf on the scratch block
    refine ((hLf (w := (Lc, 0)) (p := q) (ub := (Lc + 1, 0)) B hd hBN).in_frame
      (by simp [IExp.evalList, IExp.eval, Env.frame, hq])
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
      (fun μ h v hv => h.2.2.1 v (by
        simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto))).mono_eqOff
      (fun μ ⟨hlen, hL1, hB, hqs, ho, hqL, hoL⟩ => ⟨hB, hqs, fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with h | h | h <;> rw [h] <;> omega,
        by dsimp only; omega, by
        simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
          Fp.disj_bot_right, and_true]
        exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), hWU⟩,
          Fp.disj_inBlock_of_ne (by omega)⟩⟩) ?_
    rintro μ μ' ⟨hlen, hL1, hB, hqs, ho, hqL, hoL⟩ hfr
      ⟨Ub, Tb, ⟨hTb, -⟩, hT, Vb, ⟨hVb, E, hE, hTE⟩, -⟩
    have hL : IsEigenvalueListing (B + E) fun i => Tb i i := by
      have := hVb.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul (A := B + E)
        (hTE ▸ hT)
      simpa [← hTE] using this
    obtain ⟨ev, hev, hb⟩ := exists_isEigenvalueListing_norm_sub_le_of_forwardBackwardError hd hβ
      hβN hBN (hE.trans hβL) hL
    exact ⟨hfr.length_eq.trans hlen, by rw [hfr.len_eq]; exact ho, hoL, Tb, hTb, ev, hev,
      hb⟩
  · -- the copy of the diagonal to the output
    obtain ⟨hlen, hroomo, hoL, Tb, hTb, ev, hev, hb⟩ := h
    have hTo : Fp.Disj (Store.inBlock o.1 o.2 (2 * d)) (Store.inBlock (Lc, 0).1 (Lc, 0).2
        (2 * (d * d))) := Fp.disj_inBlock_of_ne (by omega)
    refine (writes_loop (N := d) (by simp [IExp.eval, Env.frame])
      (fun _ => Store.inBlock o.1 o.2 (2 * d)) (fun _ _ => le_rfl)
      (fun i m => m.store.length = Lc + 2 ∧ o.2 + 2 * d ≤ m.store.len o.1 ∧
        HoldsMatrix (Lc, 0) Tb m.store ∧ ∀ j : Fin d, (j : ℕ) < i →
          m.store.get o.1 (o.2 + 2 * j) = some (Tb j j).re ∧
          m.store.get o.1 (o.2 + 2 * j + 1) = some (Tb j j).im)
      ⟨hlen, hroomo, hTb, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_).mono le_rfl ?_
    · intro i hi m _ ⟨h1, h2, h3, h4⟩
      refine (writes_call_un (hS .copy) (x := (Lc, 2 * (i * d + i))) (z := (o.1, o.2 + 2 * i))
        (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx]) trivial
        (by simpa using h3.get_re ⟨i, hi⟩ ⟨i, hi⟩) rfl (by dsimp only; omega)).seq_le
        (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
      rintro m₁ hfr₁' ⟨-, g₁⟩
      refine (writes_call_un (hS .copy) (x := (Lc, 2 * (i * d + i) + 1))
        (z := (o.1, o.2 + 2 * i + 1))
        (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx]) trivial
        (by rw [hfr₁'.get_eq (fun h' => by have := h'.1; dsimp only at this; omega)]
            simpa [Nat.add_assoc] using h3.get_im ⟨i, hi⟩ ⟨i, hi⟩) rfl
        (by dsimp only; rw [hfr₁'.len_eq]; omega)).mono
        (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
      rintro m₂ hfr₂' ⟨-, g₂⟩
      have hfr := hfr₁'.trans' hfr₂'
      refine ⟨by rw [hfr.length_eq, h1], by rw [hfr.len_eq]; exact h2,
        h3.of_eqOff hfr (Fp.disj_sup_left.mpr ⟨hTo.mono (Fp.inBlock_le_inBlock (by omega)
          (by omega)) le_rfl, hTo.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl⟩),
        fun j hj => ?_⟩
      rcases Nat.lt_or_ge (j : ℕ) i with hji | hji
      · obtain ⟨r1, r2⟩ := h4 j hji
        refine ⟨?_, ?_⟩
        · rw [hfr₂'.get_eq (fun h' => by have := h'.2; dsimp only at this; omega),
            hfr₁'.get_eq (fun h' => by have := h'.2; dsimp only at this; omega)]
          exact r1
        · rw [hfr₂'.get_eq (fun h' => by have := h'.2; dsimp only at this; omega),
            hfr₁'.get_eq (fun h' => by have := h'.2; dsimp only at this; omega)]
          exact r2
      · have hj' : (j : ℕ) = i := by omega
        have hjF : j = ⟨i, hi⟩ := Fin.ext hj'
        subst hjF
        refine ⟨?_, g₂⟩
        rw [hfr₂'.get_eq (fun h' => by have := h'.2; dsimp only at this; omega)]
        exact g₁
    · rintro m - ⟨-, -, -, h4⟩
      refine ⟨fun i => Tb i i, ev, hev, hb, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
      · have hj : (j : ℕ) = 0 := by have := j.2; omega
        simpa [hj] using (h4 i i.2).1
      · have hj : (j : ℕ) = 0 := by have := j.2; omega
        simpa [hj] using (h4 i i.2).2
  · intro b i h
    rcases h with h | ((h | h) | h) <;>
      first | exact Or.inl h | exact Or.inr (h.1 ▸ le_rfl) |
        exact Or.inr (show Lc ≤ b by have := h.1; omega)

/-- **The backward accuracy is at most the forward accuracy** at the headline's parameters:
$\delta_b \le \beta \le \omega/32320$ for $\beta$ = `NLAlib.ShiftedQR.shqrSmallEigAccuracy`,
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` $k$ $4\Sigma$ $\beta$, $k \ge 1$, $B \ge 1$,
$\Gamma > 0$ and $0 < \delta \le \Sigma$. -/
theorem forwardBackwardError_shqrSmallEigAccuracy_le {n k : ℕ} {B Γ S δ : ℝ} (hk : 0 < k)
    (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) :
    SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ) ≤
      shqrOmega n B Γ δ / 32320 := by
  have hS : 0 < S := hδ.trans_le hδS
  have hacc0 := shqrSmallEigAccuracy_pos (n := n) hB hΓ hδ hS
  have haccS := shqrSmallEigAccuracy_le (n := n) hB hΓ hδ hδS
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωS := shqrOmega_le_normBound (n := n) hB hΓ hδ hδS
  have hacc : shqrSmallEigAccuracy n B Γ S δ ≤ shqrOmega n B Γ δ / 32320 := by
    change shqrOmega n B Γ δ ^ 2 / (8080 * (4 * S)) ≤ _
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine le_trans ?_ hacc
  unfold SmallEig.forwardBackwardError
  set β := shqrSmallEigAccuracy n B Γ S δ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set r := β / (4 * (2 * k + 1) * (4 * S)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by positivity)]; nlinarith
  have hrk : r ^ k ≤ r := pow_le_of_le_one hr0 hr1 (by omega)
  calc 4 * S * r ^ k ≤ 4 * S * r := by gcongr
    _ = β / (4 * (2 * k + 1)) := by rw [hr]; field_simp
    _ ≤ β := div_le_self hacc0.le (by nlinarith)

/-- **The error budget of the Schur-mode run**: for $B \ge 1$, $\Gamma > 0$,
$0 < \delta \le \Sigma$, $k$ the degree of (eqn:setk) at $4B$,
$0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, $\boldsymbol{u}$ at most the replay term
`NLAlib.ShiftedQR.uShQRSchurReplay` at $n_p$ words and $R_L$ leaf rotations, a leaf accumulator
error $\varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$, a leaf backward error
$0 \le \beta_L \le \delta_b$ (`NLAlib.SmallEig.forwardBackwardError` $k$ $4\Sigma$ at
`NLAlib.ShiftedQR.shqrSmallEigAccuracy`), an order $n' + 1 \le n + 1$ and a log of
$n_s w \le$ `NLAlib.ShiftedQR.shqrSchurLogSize` entries, the per-round error of the worklist at
$N_0 = 2\Sigma$, over $2(n' + 1)$ rounds, is at most the budget
$\min(\delta, \Gamma/(16(n + 1)B))$ (`NLAlib.ShiftedQR.shqrBudget`): the cut level and the
decoupler a third each, the replays, the leaf products and the leaf accumulators a quarter. -/
theorem shqrSchurError_le {n n' k np RL : ℕ} {B Γ S δ φ u εL βL : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k np (shqrCap n B Γ S δ) RL B Γ S δ)
    (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hn' : n' ≤ n) {ns w : ℕ} (hnsw : ns * w ≤ shqrSchurLogSize n k np (shqrCap n B Γ S δ)) :
    2 * ((n' : ℝ) + 1) * (shqrCut n k B Γ S δ φ + shqrCap n B Γ S δ *
      ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1)) + βL +
      2 * εL * (2 * S) + 78 * u * ((ns : ℝ) * w) * (2 * S) +
      8 * ((n' : ℝ) + 1) * (k + 2) * u * (2 * S)) ≤ shqrBudget n B Γ δ := by
  have hS : 0 < S := hδ.trans_le hδS
  have hk0 : 0 < k := by have := hk ▸ two_le_shqrDegree (by linarith : 1 ≤ 4 * B); omega
  set b := shqrBudget n B Γ δ with hbdef
  have hb := shqrBudget_pos (n := n) hB hΓ hδ
  have hbS : b ≤ S := shqrBudget_le_left.trans hδS
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωb := shqrOmega_mul (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hc := shqrCut_le (k := k) (S := S) (φ := φ) hu0 hu hω.le
  have hc0 : 0 ≤ shqrCut n k B Γ S δ φ := by
    have hv1 : uShQR n k B Γ S δ φ ≤ 1 / 10 := uShQR_le_one_div_ten
    have hv0 : 0 ≤ uShQR n k B Γ S δ φ := hu0.trans hu
    unfold shqrCut shqrDecoupled
    exact div_nonneg (mul_nonneg (by linarith) (div_nonneg (by positivity) (by positivity)))
      (by linarith)
  set E := (shqrCap n B Γ S δ : ℝ) *
    ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1)) with hEdef
  have hE : E ≤ b / (6 * (n + 1)) :=
    (shqrLoopError_le_shqrDecoupleError (n := n) (k := k) (B := B) (Γ := Γ) (δ := δ) hS.le
      hu0).trans (shqrDecoupleError_le hk0 hB hS hu0 hu)
  have hE0 : 0 ≤ E := by
    have := shqrC_pos k (by linarith : 0 < 4 * B)
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k :=
      one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    have : (0 : ℝ) ≤ shqrCap n B Γ S δ := by positivity
    have : 0 ≤ (1 + shqrC k (4 * B)) * (4 * S) := by positivity
    rw [hEdef]
    exact mul_nonneg (by positivity) (mul_nonneg this (by linarith))
  have hβ := hβL.trans (forwardBackwardError_shqrSmallEigAccuracy_le (n := n) hk0 hB hΓ hδ hδS)
  set N : ℝ := (n : ℝ) + 1 with hN
  set N' : ℝ := (n' : ℝ) + 1 with hN'
  have hN1 : 1 ≤ N := by have := n.cast_nonneg (α := ℝ); linarith
  have hNN : N' ≤ N := by rw [hN, hN']; exact_mod_cast Nat.succ_le_succ hn'
  have hN'0 : 0 < N' := by positivity
  -- the head: the cut level, the decoupler and the leaf's backward error
  have hhead : 2 * N' * (shqrCut n k B Γ S δ φ + E + βL) ≤ b / 3 + b / 3 + b / 193920 := by
    have h1 : 2 * N' * (shqrCut n k B Γ S δ φ + E + βL) ≤
        2 * N * (shqrCut n k B Γ S δ φ + E + βL) := by gcongr
    have h2 : 2 * N * shqrCut n k B Γ S δ φ ≤ b / 3 := by
      have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * N)
      linarith
    have h3 : 2 * N * E ≤ b / 3 := by
      have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 2 * N)
      have e : 2 * N * (b / (6 * N)) = b / 3 := by field_simp; ring
      linarith
    have h4 : 2 * N * βL ≤ b / 193920 := by
      have := mul_le_mul_of_nonneg_left hβ (by positivity : (0 : ℝ) ≤ 2 * N)
      linarith
    linarith
  -- the tail: the replays, the leaf products and the leaf accumulators
  set Ls : ℝ := (shqrSchurLogSize n k np (shqrCap n B Γ S δ) : ℝ)
  set D : ℝ := 78 * Ls + 8 * N * (k + 2) + 54 * RL with hD
  have hD0 : 0 < D := by positivity
  have hur' : u * (16 * N * D * S) ≤ b := by
    have := hur; unfold uShQRSchurReplay at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hRL : 24 * RL * u ≤ 1 / 8 := by
    have h1 : u * (16 * N * D) ≤ 1 := by
      have : u * (16 * N * D) * S ≤ 1 * S := by linarith
      exact le_of_mul_le_mul_right this hS
    have h2 : (54 : ℝ) * RL ≤ D := by
      rw [hD]; have : (0 : ℝ) ≤ 78 * Ls + 8 * N * (k + 2) := by positivity
      linarith
    have h3 : u * (16 * D) ≤ u * (16 * N * D) := by
      have := mul_le_mul_of_nonneg_left hN1 (by positivity : (0 : ℝ) ≤ u * (16 * D))
      linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hu0
    linarith
  have hεL := hεLR.trans (one_add_mul_pow_sub_one_le hu0 hRL)
  have hnsw' : ((ns : ℝ) * w) ≤ Ls := by
    have := (Nat.cast_le (α := ℝ)).mpr hnsw
    push_cast at this; exact this
  have htail : 2 * N' * (2 * εL * (2 * S) + 78 * u * ((ns : ℝ) * w) * (2 * S) +
      8 * N' * (k + 2) * u * (2 * S)) ≤ b / 4 := by
    have h1 : 2 * εL * (2 * S) + 78 * u * ((ns : ℝ) * w) * (2 * S) +
        8 * N' * (k + 2) * u * (2 * S) ≤ 2 * S * u * D := by
      have a1 : 2 * εL * (2 * S) ≤ 2 * S * u * (54 * RL) := by
        have := mul_le_mul_of_nonneg_right hεL (by positivity : (0 : ℝ) ≤ 4 * S)
        linarith
      have a2 : 78 * u * ((ns : ℝ) * w) * (2 * S) ≤ 2 * S * u * (78 * Ls) := by
        have := mul_le_mul_of_nonneg_left hnsw' (by positivity : (0 : ℝ) ≤ 2 * S * u * 78)
        linarith
      have a3 : 8 * N' * (k + 2) * u * (2 * S) ≤ 2 * S * u * (8 * N * (k + 2)) := by
        have := mul_le_mul_of_nonneg_right hNN (by positivity : (0 : ℝ) ≤ 16 * (k + 2) * u * S)
        linarith
      rw [hD]; linarith
    have h0 : 0 ≤ 2 * S * u * D := by positivity
    calc _ ≤ 2 * N' * (2 * S * u * D) := by gcongr
      _ ≤ 2 * N * (2 * S * u * D) := by gcongr
      _ = u * (16 * N * D * S) / 4 := by ring
      _ ≤ b / 4 := by linarith
  linarith


-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypotheses, with their long real constants, make elaboration heavy.
/-- **The rounded shifted QR algorithm with a Schur leaf, at an order up to $n + 1$**: with the
machine, the streams, the leaf and the parameters of
`NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le` at the order $n + 1$, for an upper
Hessenberg $\mathbf{H}$ of order $n' + 1 \le n + 1$ in the class $(B, \Gamma)$ with
$\|\mathbf{H}\|_2 \le \Sigma$, except with probability $\varphi$ the run of
`NLAlib.ShiftedQR.roundedShQRWith L` at the order $n' + 1$ sets its flag to $0$ and stores an
upper triangular matrix and an accumulator tracked from $(\mathbf{U}, \mathbf{H})$ with the
backward error $\delta$ (`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler of
`NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at` and the
budget `NLAlib.ShiftedQR.shqrSchurError_le`). -/
theorem roundedShQRWith_pwrites_of_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ)
    {n' : ℕ} (hn' : n' ≤ n) {H V U : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ}
    {d : Fin (n' + 1) → ℂ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) {a t p uo f : ℕ × ℕ} :
    PWrites law I (roundedShQRWith L).body
      (Env.frame [n' + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n' + 1)]
        [a, t, p, uo, a, uo, f]) (shqrFp n' a uo f)
      (fun μ => μ.Live [a, t, p, uo, f] ∧
        μ.Room [a, t, p, uo, f] [2 * ((n' + 1) * (n' + 1)), 1,
          (shqrParams n k B Γ S δ φ ++ qs).length, 2 * ((n' + 1) * (n' + 1)), 1] ∧
        Fp.Apart [a, t, p, uo, f] [2 * ((n' + 1) * (n' + 1)), 1,
          (shqrParams n k B Γ S δ φ ++ qs).length, 2 * ((n' + 1) * (n' + 1)), 1] ∧
        HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧
        μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
        μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
          some (shqrParams n k B Γ S δ φ ++ qs))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar ((1 + 24 * u) ^ (2 * (n' + 1) *
            (shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length) *
              (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1) δ U H U' Tm) φ := by
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set F := shqrCap n B Γ S δ
  have hu0 := hM.roundoff_nonneg
  have hSp : 0 < S := hδ.trans_le hδS
  have hacc0 := shqrSmallEigAccuracy_pos (n := n) hB hΓ hδ hSp
  have haccS := shqrSmallEigAccuracy_le (n := n) hB hΓ hδ hδS
  obtain ⟨-, -, SR, IT⟩ := shqrParams_spec hB hΓ hδ hδS hφ hφ1 hk hu0 hu hacc0.le le_rfl
  have hu1 : u ≤ 1 / 100 := by
    have := (counts_of_le_uShQR hu0 hu).1
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hD : RandomDecouplingRoutineContract law (2 * B) (Γ / 2)
      (F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 + shqrSmallEigFailure n B Γ S δ φ)) k F
      T n' (2 * S) ps (F * (k + 1 + ps.length)) (k * (n' + 1)) (shqrDecoupled n k B Γ S δ φ)
      (fun _ => F * ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n + 1
    · rw [min_eq_left hkn] at hLeaf
      exact roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at hI hloc hS hM hL
        hNat hC hQ hDisk hU hB hΓ hδ hδS hφ hφ1 hk hacc0.le le_rfl hφL0 hu
        (hLeaf.randomSmallEigContractAt_schurDiag hS hI hloc hqs hφL0 hacc0 haccS hβL)
        (Or.inr hqs) rfl le_rfl hn' (Nat.mul_le_mul_left _ (by omega))
    · intro n'' N w q f lg H' V' d' hk' hn''
      omega
  have hLeaf' : Schur.RandomSchurLeafContract law εL βL φL (min k (n' + 1)) (2 * S) ps T
      (leafOnTailWords L) I := fun B' hd hB' =>
    (hLeaf.onTailWords hqs (shqrParams n k B Γ S δ φ)) B'
      (hd.trans (min_le_min le_rfl (by omega))) (hB'.trans (by linarith))
  have hbud := shqrSchurError_le (n' := n') (ns := F * (k + 1 + ps.length)) (w := k * (n' + 1))
    (φ := φ) hB hΓ hδ hδS hk hu0 hu hur hεLR hβL0 hβL hn'
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  have hbδ := shqrBudget_le_left (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hbΓ := shqrBudget_le_right (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hE0 : 0 ≤ (F : ℝ) * ((1 + shqrC k (4 * B)) * (4 * S) *
      ((1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1)) := by
    have := shqrC_pos k (by linarith : 0 < 4 * B)
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k :=
      one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    have : 0 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1 := by linarith
    positivity
  have hnn : ((n' : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn'
  have hΓn : Γ / (16 * (n + 1) * B) ≤ Γ / (16 * (n' + 1) * B) := by gcongr
  have hφR : 0 ≤ shqrRegularizeFailure n B Γ S δ φ := by
    have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
    unfold shqrRegularizeFailure; positivity
  have hφD : 0 ≤ F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 +
      shqrSmallEigFailure n B Γ S δ φ) := by
    have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
    positivity
  have hfail : 2 * ((n' : ℝ) + 1) * (F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 +
      shqrSmallEigFailure n B Γ S δ φ) + φL) ≤ φ :=
    le_trans (by gcongr) (IT.hfail φL hφL0 hφL)
  refine (solveRoundedWith_pwrites hS hM hu0 hu1 hL (hNat.mono (by omega)) hQ hC hI hloc _ hD _
    hLeaf' hφD hφL0 hεL hHess hV hHV hκ hΓ hgap SR.hfind SR.hcut SR.hc hβL0 hE0 (by linarith)
    (by linarith) (hbud.trans (hbΓ.trans hΓn))).mono (fun _ h => h) le_rfl ?_ hfail
  rintro μ' ⟨hf, U', Tm, hTm, hU', hT, htr⟩
  exact ⟨hf, U', Tm, hTm, hU', hT, htr.mono le_rfl (hbud.trans hbδ)⟩

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The headline's hypotheses, with their long real constants, make elaboration heavy.
/-- **The rounded shifted QR algorithm with a small-block Schur solver**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of Theorem 1.4, corrected,
with any small-block Schur solver in the place of `SmallEig`). Let the machine have the standard
model at $\boldsymbol{u}$, index literals, exact natural literals up to $n + 1$, exact `toNat` and
comparisons, a measurable interpretation reading the tape only in its windows, and a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it. Let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`: except
with probability $\varphi_L$ it stores an upper triangular $\mathbf{T}_b$ and an accumulator
$\mathbf{U}_b$ with $\|\mathbf{U}_b - \mathbf{V}_b\|_2 \le \varepsilon_L$ and $\mathbf{T}_b =
\mathbf{V}_b^{\mathsf H}(\mathbf{B} + \mathbf{F})\mathbf{V}_b$ for an exact unitary
$\mathbf{V}_b$ and $\|\mathbf{F}\|_2 \le \beta_L$, with $\beta_L, \varphi_L \ge 0$,
$0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$ (a leaf of $R_L$ rotation-equivalents),
$\beta_L$ at most the backward accuracy $\Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ of the forward
accuracy $\beta$ = `shqrSmallEigAccuracy` at $\Sigma' = 4\Sigma$ and
$\varphi_L \le$ `shqrSmallEigFailure`. Let
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u} \le$ the replay term
`NLAlib.ShiftedQR.uShQRSchurReplay` at $R_L$. Then
from a memory holding $\mathbf{H}$, an accumulator $\mathbf{U}_0$, the deflation threshold word
and the words of `shqrParams` followed by `qs`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRWith}_L(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the accumulator and the failure word, or lists no }
  \operatorname{spec}(\mathbf{H} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there `SmallEig` is an oracle returning
eigenvalues.

Note: The leaf is a hypothesis, `NLAlib.Schur.RandomSchurLeafContract`: this is the algorithm
with a small-block Schur oracle. The diagonal of the leaf's triangular block serves as its Ritz
values (`NLAlib.ShiftedQR.schurDiag`), turned into forward accuracy by the matching
(`NLAlib.SmallEig.forwardBackwardError`). Instance: `SmallEig`
(`NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`). The Schur form itself:
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`. -/
theorem roundedShQRWith_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T : ℕ}
    {qs : List ℝ} {L : Impl O Q} {RL : ℕ}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store)
    (ht : μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ))
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRWith L).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  have hB : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have h := (roundedShQRWith_pwrites_of_le hS hM hL hNat hQ hC hI hloc hDisk hU hB hΓ hδ hδS hφ
    hφ1 hk hLeaf hqs hεL hεLR hβL0 hβL hφL0 hφL hu hur le_rfl hHess hV hHV hκ hgap hHS
    (U := U₀)).measureReal_not_writes_le ⟨hl, hr, ha, hA, hU₀, ht, hp⟩ hξ
  refine le_trans ?_ h
  refine measureReal_mono fun ω' hω' hW => hω' ?_
  refine hW.mono le_rfl fun μ' _ ⟨hf, U', Tm, hTm, hU', hT, htr⟩ => ?_
  obtain ⟨W, ⟨hW, E, hE, rfl⟩, -⟩ := htr
  exact ⟨hf, _, U', E, hTm, hU', hT, hE,
    (hW.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul hT).charpoly_roots_eq_ofFn⟩

/-- **The rounded shifted QR algorithm with a completing small-block Schur solver terminates on
every tape**: on a scalar machine (no rounding model) with index literals, exact natural literals
up to $n + 1$, exact `toNat` and comparisons and an exact polar disk sampler, and a leaf `L` that
completes on orders at most $\min(k, n + 1)$ with the cap $T$ and $12$ words `qs`
(`NLAlib.ShiftedQR.CompletingLeafRoutine`, no accumulator bound), for any
$(n + 1) \times (n + 1)$ matrix $\mathbf{H}$, accumulator $\mathbf{U}_0$, any
$B, \Gamma, \Sigma, \delta, \varphi$ and $k$ the degree of (eqn:setk) at $4B$, the run of
`NLAlib.ShiftedQR.roundedShQRWith L` from a memory holding the input with the words
`NLAlib.ShiftedQR.shqrParams` followed by `qs` succeeds on every tape and writes only the matrix,
the accumulator and the failure word. -/
theorem roundedShQRWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {n : ℕ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {T : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : CompletingLeafRoutine (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store) {thr : ℝ}
    (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs)) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRWith L).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (fun _ => True) μ := by
  have hkq : k = 2 ^ Nat.log 2 k := by rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecouplerRoutine n k (shqrCap n B Γ S δ) T (shqrParams n k B Γ S δ φ ++ qs)
      (shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length)) (k * (n + 1))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n + 1
    · rw [min_eq_left hkn] at hLeaf
      exact roundedDecoupleWith_terminatingDecouplerRoutine_at (F := shqrCap n B Γ S δ) hS hL
        hNat hC hQ hDisk hkq (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
        (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
        (hLeaf.terminatingSmallEigAt_schurDiag hS hqs) (Or.inr hqs) rfl
        (Nat.mul_le_mul_left _ (by
          simp only [shqrParams, List.length_append, length_roundedDecoupleParams]; omega))
        (Nat.mul_le_mul_left _ (by omega))
    · intro n' w q f tape μ' H' hk' hn'
      omega
  exact (solveRoundedWith_completes hS hL hNat hQ hC _ hD _
    (hLeaf.onTailWords hqs _) (tape := τ) hl hr ha hA hU₀ ht hp).mono le_rfl fun _ _ _ => trivial

/-- **The rounded shifted QR algorithm with any small-block Schur solver is a Schur core**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] in Schur form, with a small-block Schur oracle).
Let the machine have the standard model at $\boldsymbol{u}$, index literals, exact natural
literals up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the
tape only in its windows, and a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler
on it. Let $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree
of (eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`, with
accumulator error $0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$, backward error $0 \le \beta_L \le
\Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ ($\beta$ = `shqrSmallEigAccuracy`, $\Sigma' = 4\Sigma$) and
failure $0 \le \varphi_L \le$ `shqrSmallEigFailure`; let $\boldsymbol{u} \le
\boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u}$ at most the replay term at $R_L$. Then
`roundedShQRSchurWith L` meets the Schur core contract on the orders at most $n + 1$, the class
$(B, \Gamma)$ and norms at most $\Sigma$, with the words: the deflation threshold, `shqrParams`,
`qs`. Except with probability $\varphi$ its flag is $0$, its matrix upper triangular, and the
pair is tracked from $(\mathbf{U}, \mathbf{H})$ with the backward error $\delta$ and the relative
accumulator error $(1 + 24\boldsymbol{u})^{R} - 1$, $R$ = `NLAlib.ShiftedQR.shqrSchurRotations`
($2(n + 1)(n_s w + 2k(k + 2)) + (n + 1)R_L$).
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there only the eigenvalues are computed, with an
eigenvalue oracle.

Note: The leaf is a hypothesis (`NLAlib.Schur.RandomSchurLeafContract`): this is the core with a
small-block Schur oracle, the general form of
`NLAlib.ShiftedQR.roundedShQRSchur_randomSchurCoreContract` (the `SmallEig` leaf). The proof is
`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler
of `NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` (`NLAlib.ShiftedQR.schurDiag`
of the leaf as its eigenvalue routine); the replay term keeps the replays, the products and the
leaf accumulators within a quarter of the merged budget (`NLAlib.ShiftedQR.shqrSchurError_le`).
Result: shifted-qr-rounded-schur-any-leaf -/
theorem roundedShQRSchurWith_randomSchurCoreContract {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ) :
    Schur.RandomSchurCoreContract law
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) δ φ (fun H => IsConditionedDiagonalizable B Γ H) k
      (shqrCap n B Γ S δ) T (n + 1) S
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
  intro n' a p uo f H U hn hHess hHS ⟨V, d, hV, hHV, hκ, hgap⟩
  have hw := roundedShQRWith_pwrites_of_le (t := p) (p := (p.1, p.2 + 1)) (a := a) (uo := uo)
    (f := f) (U := U) hS hM hL hNat hQ hC hI hloc hDisk hU hB hΓ hδ hδS hφ hφ1 hk hLeaf hqs hεL
    hεLR hβL0 hβL hφL0 hφL hu hur (by omega : n' ≤ n) hHess hV hHV hκ hgap hHS
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set thr := shqrDeflationThreshold n k B Γ S δ φ
  have hu0 := hM.roundoff_nonneg
  unfold roundedShQRSchurWith
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun μ h v hv => by
      have hl := h.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl _ (by simp), hl _ (by simp), hl uo (by simp), hl a (by simp),
        hl uo (by simp), hl f (by simp)])).mono ?_ le_rfl ?_ le_rfl
  · rintro μ ⟨hHU, hp, hl, hf, ha⟩
    have hp' : μ.store.readBlock p.1 (p.2 + 1) ps.length = some ps :=
      Store.readBlock_append_right (xs := [thr]) hp
    have ht : μ.store.get p.1 p.2 = some thr := by
      simpa using Store.get_of_readBlock hp (j := 0) (by simp) 0
    have hpl : p.2 + (1 + ps.length) ≤ μ.store.len p.1 := by
      simpa [Nat.add_comm 1] using Store.le_len_of_readBlock hp (by simp)
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq] at ha
    have hsub1 : Store.inBlock p.1 p.2 1 ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
      Fp.inBlock_le_inBlock le_rfl (by simp)
    have hsub2 : Store.inBlock p.1 (p.2 + 1) ps.length ≤
        Store.inBlock p.1 p.2 (thr :: ps).length :=
      Fp.inBlock_le_inBlock (by omega) (by simp; omega)
    refine ⟨fun v hv => ?_, ⟨Store.le_len_of_readBlock hHU.1 (by positivity), by omega,
      by dsimp only; omega, Store.le_len_of_readBlock hHU.2 (by positivity), hf, trivial⟩, ?_,
      hHU.1, hHU.2, ht, hp'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl f (by simp)]
    · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq]
      exact ⟨⟨ha.1.1.mono le_rfl hsub1, ha.1.1.mono le_rfl hsub2, ha.1.2.1, ha.1.2.2⟩,
        ⟨Fp.disj_inBlock_of_le le_rfl, ha.2.1.1.mono hsub1 le_rfl, ha.2.1.2.mono hsub1 le_rfl⟩,
        ⟨ha.2.1.1.mono hsub2 le_rfl, ha.2.1.2.mono hsub2 le_rfl⟩, ha.2.2.1,
        fun _ _ _ h => h, trivial⟩
  rintro μ' ⟨hf, U', Tm, hTm, hU', hT, htr⟩
  refine ⟨hf, U', Tm, ⟨hTm, hU'⟩, hT, htr.mono ?_ le_rfl⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hεL1 : 1 + εL ≤ (1 + 24 * u) ^ RL := by linarith
  have hY : (1 + εL) ^ (n' + 1) ≤ (1 + 24 * u) ^ (RL * (n' + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) hεL1 _
  have hE : 2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
      2 * k * (k + 2)) + RL * (n' + 1) ≤
      shqrSchurRotations n k ps.length (shqrCap n B Γ S δ) RL := by
    unfold shqrSchurRotations shqrSchurLogSize
    have h1 : n' + 1 ≤ n + 1 := by omega
    have := Nat.mul_le_mul_left (shqrCap n B Γ S δ * (k + 1 + ps.length))
      (Nat.mul_le_mul_left k h1)
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1)
      (Nat.add_le_add_right this (2 * k * (k + 2)))
    have := Nat.mul_le_mul_left RL h1
    nlinarith
  calc (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1
      ≤ (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + 24 * u) ^ (RL * (n' + 1)) - 1 := by
        gcongr
    _ ≤ _ := by rw [← pow_add]; gcongr

/-- **The Schur core with any terminating small-block Schur solver terminates on every tape**:
on a scalar machine with the standard model at $\boldsymbol{u} \le 1/100$, index literals, exact
natural literals up to $n + 1$, exact `toNat` and comparisons and an exact polar disk sampler, and
a leaf `L` that terminates on orders at most $\min(k, n + 1)$ with the cap $T$ and $12$ words
`qs`, its accumulator within $0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$ of a
unitary, `roundedShQRSchurWith L` meets `NLAlib.Schur.TerminatingSchurCore` on the orders at most
$n + 1$ with the relative accumulator error $(1 + 24\boldsymbol{u})^R - 1$,
$R$ = `NLAlib.ShiftedQR.shqrSchurRotations` (`NLAlib.ShiftedQR.solveRoundedWith_terminates`). -/
theorem roundedShQRSchurWith_terminatingSchurCore {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I) {k : ℕ} {B Γ S δ φ : ℝ}
    (hk : k = shqrDegree (4 * B)) {εL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) :
    Schur.TerminatingSchurCore
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) k (shqrCap n B Γ S δ) T (n + 1)
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
  intro n' a p uo f tape μ H U hn hHU hp hl hf ha
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set thr := shqrDeflationThreshold n k B Γ S δ φ
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hkq : k = 2 ^ Nat.log 2 k := by rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecouplerRoutine n' k (shqrCap n B Γ S δ) T ps
      (shqrCap n B Γ S δ * (k + 1 + ps.length)) (k * (n' + 1))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n' + 1
    · exact roundedDecoupleWith_terminatingDecouplerRoutine_at (F := shqrCap n B Γ S δ) hS hL
        (hNat.mono (by omega)) hC hQ hDisk hkq (shqrLoopThreshold n k B Γ S δ φ)
        (shqrRadius n B Γ S δ) (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B)
        (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
        (CompletingLeafRoutine.terminatingSmallEigAt_schurDiag hS
          (CompletingLeafRoutine.mono_kmax hLeaf.completing (kmax' := k)
            (le_min le_rfl (by omega))) hqs)
        (Or.inr hqs) rfl
        (Nat.mul_le_mul_left _ (by
          simp only [hps, shqrParams, List.length_append, length_roundedDecoupleParams]; omega))
        (Nat.mul_le_mul_left _ (by omega))
    · intro n'' w q f tape μ' H' hk' hn''
      omega
  have hp' : μ.store.readBlock p.1 (p.2 + 1) ps.length = some ps :=
    Store.readBlock_append_right (xs := [thr]) hp
  have ht : μ.store.get p.1 p.2 = some thr := by
    simpa using Store.get_of_readBlock hp (j := 0) (by simp) 0
  have hpl : p.2 + (1 + ps.length) ≤ μ.store.len p.1 := by
    simpa [Nat.add_comm 1] using Store.le_len_of_readBlock hp (by simp)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq] at ha
  have hsub1 : Store.inBlock p.1 p.2 1 ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock le_rfl (by simp)
  have hsub2 : Store.inBlock p.1 (p.2 + 1) ps.length ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  have hw := solveRoundedWith_terminates (n := n') (D := roundedDecoupleWith (schurDiag L))
    (L := leafOnTailWords L) (F := shqrCap n B Γ S δ) (T := T) (tape := tape)
    (t := p) (p := (p.1, p.2 + 1)) hS hM hu1 hL (hNat.mono (by omega)) hQ hC hεL hD
    (TerminatingLeafRoutine.onTailWords
      (hLeaf.mono_kmax (kmax' := min k (n' + 1)) (min_le_min le_rfl (by omega))) hqs _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl f (by simp)])
    ⟨Store.le_len_of_readBlock hHU.1 (by positivity), by omega, by dsimp only; omega,
      Store.le_len_of_readBlock hHU.2 (by positivity), hf, trivial⟩
    (by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq]
      exact ⟨⟨ha.1.1.mono le_rfl hsub1, ha.1.1.mono le_rfl hsub2, ha.1.2.1, ha.1.2.2⟩,
        ⟨Fp.disj_inBlock_of_le le_rfl, ha.2.1.1.mono hsub1 le_rfl, ha.2.1.2.mono hsub1 le_rfl⟩,
        ⟨ha.2.1.1.mono hsub2 le_rfl, ha.2.1.2.mono hsub2 le_rfl⟩, ha.2.2.1,
        fun _ _ _ h => h, trivial⟩)
    hHU.1 hHU.2 ht hp'
  unfold roundedShQRSchurWith
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl a (by simp),
        hl uo (by simp), hl f (by simp)])).mono le_rfl ?_
  rintro μ' - ⟨U', Tm, V, hTm, hU', hV, hb⟩
  refine ⟨U', Tm, V, ⟨hTm, hU'⟩, hV, hb.trans (mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _))⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hY : (1 + εL) ^ (n' + 1) ≤ (1 + 24 * u) ^ (RL * (n' + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hE : 2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
      2 * k * (k + 2)) + RL * (n' + 1) ≤
      shqrSchurRotations n k ps.length (shqrCap n B Γ S δ) RL := by
    unfold shqrSchurRotations shqrSchurLogSize
    have h1 : n' + 1 ≤ n + 1 := by omega
    have := Nat.mul_le_mul_left (shqrCap n B Γ S δ * (k + 1 + ps.length)) (Nat.mul_le_mul_left k h1)
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1)
      (Nat.add_le_add_right this (2 * k * (k + 2)))
    have := Nat.mul_le_mul_left RL h1
    nlinarith
  calc (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
          2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1
      ≤ (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + 24 * u) ^ (RL * (n' + 1)) - 1 := by
        gcongr
    _ ≤ _ := by rw [← pow_add]; gcongr

end Routine

end NLAlib.ShiftedQR
