/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems
public import NLAlib.Eigensolvers.SmallEig.Theorems
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSchurLeaf

/-!
# The rounded shifted QR algorithm with the small-eigenvalue program

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with no algorithmic oracle: the `SmallEig` kernel the
merged algorithm assumes (`NLAlib.ShiftedQR.IsRandomSmallEig`) is replaced by the program of
[BanksGarzaVargasSrivastava2025, Theorem 1.1] (`NLAlib.SmallEig.smallEigProg`), run as a routine
(`NLAlib.ShiftedQR.roundedShQRWith`). Its words follow those of the merged algorithm, its cap is a
dimension, and its forward contract on the trailing blocks of order $k$ and norm at most
$4\Sigma$ (`NLAlib.SmallEig.smallEigProg_randomSmallEigContract`) gives the merged accuracy and
failure. The headline is conditional only on the two random-matrix theorems (the hypotheses
`NLAlib.PolyLogTail.BoundsGinibreGap`, `NLAlib.PolyLogTail.BoundsGinibreCondition`), which are
proved at the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail -->
$(10000e, 5, 1/2, 2)$, `NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail -->
$(128e, 3, 2, 2)$: the `_unconditional` corollaries. One unit roundoff serves the whole run:
$\boldsymbol{u} \le \min(\boldsymbol{u}_{\mathrm{ShQR}},
\boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}})$, $O(\log^4)$ bits up to $(\log\log)^2$.

## Main definitions

* `NLAlib.ShiftedQR.roundedShQRSmallEig`: the program.
* `NLAlib.ShiftedQR.shqrSmallEigParams`, `NLAlib.ShiftedQR.shqrSmallEigCap`,
  `NLAlib.ShiftedQR.shqrSmallEigDims`, `NLAlib.ShiftedQR.uShQRSmallEig`,
  `NLAlib.ShiftedQR.ShQRSmallEigInput`: its words, cap, dimensions, precision and input.

## Main results

* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`: the headline.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`: termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQRSmallEig_le`, `NLAlib.ShiftedQR.shqrDegree_le_log`: the bits.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_work_le`: the operation count.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_relative`, `NLAlib.ShiftedQR.roundedShQRSmallEig_hermitian`.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le_unconditional` and the other
  `_unconditional` forms: with the proved random-matrix tails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops SmallEig

/-- **The parameter words of the algorithm with the small-eigenvalue program**: the words of
`NLAlib.ShiftedQR.shqrParams`, followed by the twelve words of
`NLAlib.SmallEig.smallEigForwardParams` at the order bound $k$, the norm bound $4\Sigma$, the
accuracy `NLAlib.ShiftedQR.shqrSmallEigAccuracy` and the failure
`NLAlib.ShiftedQR.shqrSmallEigFailure`. -/
noncomputable def shqrSmallEigParams (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    List ℝ :=
  shqrParams n k B Γ S δ φ ++
    smallEigForwardParams k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
      (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂

/-- The cap of the small-eigenvalue program in the algorithm. -/
noncomputable def shqrSmallEigCap (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  smallEigForwardCap k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂

/-- The dimensions of a run: the order $n + 1$, the shift degree $k$, the number of words, the
iteration cap `NLAlib.ShiftedQR.shqrCap` and the cap `NLAlib.ShiftedQR.shqrSmallEigCap`. -/
noncomputable def shqrSmallEigDims (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℕ :=
  [n + 1, k, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length, shqrCap n B Γ S δ,
    shqrSmallEigCap n k B Γ S δ φ c₁ c₂,
    shqrCap n B Γ S δ * (k + 1 + (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length), k * (n + 1)]

/-- **The precision threshold of the algorithm with the small-eigenvalue program**: the minimum of
`NLAlib.ShiftedQR.uShQR` and `NLAlib.SmallEig.uSmallEigForward` at the order bound $k$, the norm
bound $4\Sigma$, the accuracy `NLAlib.ShiftedQR.shqrSmallEigAccuracy` and the failure
`NLAlib.ShiftedQR.shqrSmallEigFailure`. -/
noncomputable def uShQRSmallEig (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (uShQR n k B Γ S δ φ)
    (uSmallEigForward k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
      (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂)

/-- **The memory holding the input** of the algorithm with the small-eigenvalue program: the
views of the matrix, the threshold word, the parameter words, the accumulator and the failure word
are live, have room and are apart; an accumulator, the matrix $\mathbf{H}$, the deflation
threshold word and the words `NLAlib.ShiftedQR.shqrSmallEigParams` are stored. -/
def ShQRSmallEigInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail)
    (a t p out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length,
        2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length,
        2 * ((n + 1) * (n + 1)), 1] ∧
    (∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix out U μ.store) ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length =
      some (shqrSmallEigParams n k B Γ S δ φ c₁ c₂)

/-- **The precision threshold is positive**: for tail records with $b_1, b_2 > 0$, $B \ge 1$,
$\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at
$4B$, `NLAlib.ShiftedQR.uShQRSmallEig` is positive, and the small-eigenvalue words have twelve
entries. -/
theorem uShQRSmallEig_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {n k : ℕ}
    {B Γ S δ φ : ℝ} (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) :
    0 < uShQRSmallEig n k B Γ S δ φ c₁ c₂ ∧
      (smallEigForwardParams k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
        (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂).length = 12 := by
  have hS : 0 < S := hδ.trans_le hδS
  have hk2 : 2 ≤ k := hk ▸ two_le_shqrDegree (by linarith)
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB hΓ hδ hS
  have hβS := shqrSmallEigAccuracy_le (n := n) hB hΓ hδ hδS
  have hφse := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hφse1 := (shqrSmallEigFailure_le (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ.le).trans
    hφ1
  obtain ⟨hδb, hδbS, -⟩ := forwardBackwardError_spec (kmax := k) hβ hβS
  refine ⟨lt_min (uShQR_pos (by omega) hB hΓ hδ hS hφ) ?_, length_smallEigParams _ _ _ _ _ _⟩
  exact (uSmallEig_spec hb₁ hb₂ (by omega) hδb hδbS hφse hφse1).1

/-! ### The Schur core with the small-eigenvalue program -/

/-- **The words of the Schur core with the small-eigenvalue program**: the deflation threshold
word, then `NLAlib.ShiftedQR.shqrSmallEigParams` (the merged words followed by the twelve forward
words of the leaf). -/
noncomputable def shqrSchurParams (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℝ :=
  shqrDeflationThreshold n k B Γ S δ φ :: shqrSmallEigParams n k B Γ S δ φ c₁ c₂

/-- The rotation count of the accumulator of the Schur core with the small-eigenvalue program:
`NLAlib.ShiftedQR.shqrSchurRotations` with the leaf's `NLAlib.SmallEig.smallEigLeafRotations` at
the order bound $k$ and the cap `NLAlib.ShiftedQR.shqrSmallEigCap`. -/
noncomputable def shqrSmallEigRotations (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  shqrSchurRotations n k (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length (shqrCap n B Γ S δ)
    (smallEigLeafRotations k (shqrSmallEigCap n k B Γ S δ φ c₁ c₂))

/-- **The precision threshold of the Schur core with the small-eigenvalue program**: the minimum
of `NLAlib.ShiftedQR.uShQRSmallEig`, $1/100$ and the replay term
`NLAlib.ShiftedQR.uShQRSchurReplay` at the leaf's rotation count
`NLAlib.SmallEig.smallEigLeafRotations` (order bound $k$, the cap
`NLAlib.ShiftedQR.shqrSmallEigCap`). -/
noncomputable def uShQRSchur (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (uShQRSmallEig n k B Γ S δ φ c₁ c₂) <| min (1 / 100) <|
    uShQRSchurReplay n k (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length (shqrCap n B Γ S δ)
      (smallEigLeafRotations k (shqrSmallEigCap n k B Γ S δ φ c₁ c₂)) B Γ S δ

/-- **The precision threshold of the Schur core is positive**: for tail records with
$b_1, b_2 > 0$, $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the
degree of (eqn:setk) at $4B$, `NLAlib.ShiftedQR.uShQRSchur` is positive. -/
theorem uShQRSchur_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {n k : ℕ}
    {B Γ S δ φ : ℝ} (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) : 0 < uShQRSchur n k B Γ S δ φ c₁ c₂ := by
  have hS : 0 < S := hδ.trans_le hδS
  have hb := shqrBudget_pos (n := n) hB hΓ hδ
  refine lt_min (uShQRSmallEig_pos hb₁ hb₂ hB hΓ hδ hδS hφ hφ1 hk).1 (lt_min (by norm_num) ?_)
  unfold uShQRSchurReplay
  positivity

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has SampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded shifted QR algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]): `NLAlib.ShiftedQR.roundedShQRWith` at the program
`NLAlib.SmallEig.smallEigProg` (the Schur leaf) with the Gaussian stream `sG`, in Schur mode. The
interface is `[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`. No eigenvalue oracle.
Algorithm: shifted-qr-rounded -/
def roundedShQRSmallEig (sG : ℕ) : Impl O Q :=
  roundedShQRWith (smallEigProg (O := O) (Q := Q) sG)

/-- **The rounded shifted QR algorithm as the Schur core of the dense pipeline**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1], in Schur form): `NLAlib.ShiftedQR.roundedShQRSchurWith` with the small-eigenvalue
program `NLAlib.SmallEig.smallEigProg` as the leaf. The interface is
`[N, np, k, F, T] (A, P, U) → (A, U, Fl)`; the threshold is the first word.
Algorithm: shifted-qr-rounded -/
def roundedShQRSchur (sG : ℕ) : Impl O Q :=
  roundedShQRSchurWith (smallEigProg (O := O) (Q := Q) sG)

end Program

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has SampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

section SchurCore

/-- **The rounded shifted QR algorithm with the small-eigenvalue program is a Schur core**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1], in Schur form). Let the machine have the standard model at $\boldsymbol{u}$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a measurable
interpretation reading the tape only in its windows whose draws store the tape entry, a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it and a stream $s_G$ with the
standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$. Let $B \ge 1$, $\Gamma > 0$,
$0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4B$ and
$\boldsymbol{u} \le \boldsymbol{u}_0$. Then `roundedShQRSchur` with the words
`shqrSchurParams`, the iteration cap $F$ and the leaf cap $T$ meets the Schur core contract on the
orders at most $n + 1$, the class $(B, \Gamma)$ and norms at most $\Sigma$: except with probability
$\varphi$ the flag is $0$, the stored matrix upper triangular and the pair tracked from the input
pair with the backward error $\delta$ and the relative accumulator error
$(1 + 24\boldsymbol{u})^R - 1$. Here $\boldsymbol{u}_0$ is `NLAlib.ShiftedQR.uShQRSchur`, $F$ is
`NLAlib.ShiftedQR.shqrCap`, $T$ is `NLAlib.ShiftedQR.shqrSmallEigCap` and $R$ is
`NLAlib.ShiftedQR.shqrSmallEigRotations`.
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there only the eigenvalues are computed, with an
oracle.

Note: General form, any small-block Schur solver:
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`, with the leaf contract of
`NLAlib.SmallEig.smallEigProg_randomSchurLeafContract`.
Result: shifted-qr-rounded-schur -/
theorem roundedShQRSchur_randomSchurCoreContract {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {k : ℕ} {B Γ S δ φ : ℝ} (hB1 : 1 ≤ B) (hΓ : 0 < Γ)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S δ φ c₁ c₂) :
    Schur.RandomSchurCoreContract law
      ((1 + 24 * u) ^ shqrSmallEigRotations n k B Γ S δ φ c₁ c₂ - 1) δ φ
      (fun H => IsConditionedDiagonalizable B Γ H) k (shqrCap n B Γ S δ)
      (shqrSmallEigCap n k B Γ S δ φ c₁ c₂) (n + 1) S (shqrSchurParams n k B Γ S δ φ c₁ c₂)
      (roundedShQRSchur (O := O) (Q := Q) sG) I := by
  have hS0 : 0 < S := hδ.trans_le hδS
  have hacc0 := shqrSmallEigAccuracy_pos (n := n) hB1 hΓ hδ hS0
  have haccS := shqrSmallEigAccuracy_le (n := n) hB1 hΓ hδ hδS
  have hφse := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hφse1 := (shqrSmallEigFailure_le (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ)
    hφ.le).trans hφ1
  have h12 := length_smallEigParams k (4 * S)
    (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂
  have hu0 : 0 ≤ u := hM.roundoff_nonneg
  simp only [uShQRSchur, uShQRSmallEig, le_min_iff] at hu
  obtain ⟨⟨hu1, hu2⟩, -, hu3⟩ := hu
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  unfold shqrSmallEigRotations shqrSchurParams shqrSmallEigParams roundedShQRSchur
  intro n' a p uo f H U hn hHess hHS hCD
  exact roundedShQRSchurWith_randomSchurCoreContract hS hM hL hNat hQ hC hI hloc hDisk hU hB1 hΓ
    hδ hδS hφ hφ1 hk (smallEigProg_randomSchurLeafContract hS hM hL (min_le_left k (n + 1))
      (hNat.mono (min_le_right _ _)) hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hacc0 haccS
      hφse hφse1 hu2) h12 (sub_nonneg.mpr (one_le_pow₀ hX1)) le_rfl
    (forwardBackwardError_spec (kmax := k) hacc0 haccS).1.le le_rfl hφse.le le_rfl hu1 hu3
    H U hn hHess hHS hCD

/-- **The Schur core with the small-eigenvalue program terminates on every tape**: on a scalar
machine with the standard model at $\boldsymbol{u} \le 1/100$, index literals, exact natural
literals up to $n + 1$, exact `toNat` and comparisons, draws that store the tape entry and an
exact polar disk sampler, for any $B, \Gamma, \Sigma, \delta, \varphi$, $k$ the degree of
(eqn:setk) at $4B$ and any tail records, `roundedShQRSchur` with the words `shqrSchurParams` meets
`NLAlib.Schur.TerminatingSchurCore` on the orders at most $n + 1$ with the relative accumulator
error $(1 + 24\boldsymbol{u})^R - 1$, $R$ = `NLAlib.ShiftedQR.shqrSmallEigRotations`. -/
theorem roundedShQRSchur_terminatingSchurCore {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {c₁ c₂ : PolyLogTail} {k : ℕ} {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) :
    Schur.TerminatingSchurCore ((1 + 24 * u) ^ shqrSmallEigRotations n k B Γ S δ φ c₁ c₂ - 1) k
      (shqrCap n B Γ S δ) (shqrSmallEigCap n k B Γ S δ φ c₁ c₂) (n + 1)
      (shqrSchurParams n k B Γ S δ φ c₁ c₂) (roundedShQRSchur (O := O) (Q := Q) sG) I := by
  have h12 := length_smallEigParams k (4 * S)
    (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  set m := min k (n + 1)
  have hR : m * m + 2 * (m + 1) * ((shqrSmallEigCap n k B Γ S δ φ c₁ c₂ + m) * m + 6) ≤
      smallEigLeafRotations k (shqrSmallEigCap n k B Γ S δ φ c₁ c₂) := by
    have hm : m ≤ k := min_le_left _ _
    unfold smallEigLeafRotations
    have := Nat.mul_le_mul hm hm
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hm 1))
      (Nat.add_le_add_right (Nat.mul_le_mul
        (Nat.add_le_add_left hm (shqrSmallEigCap n k B Γ S δ φ c₁ c₂)) hm) 6)
    omega
  unfold shqrSmallEigRotations shqrSchurParams shqrSmallEigParams roundedShQRSchur
  intro n' a p uo f tape μ H U hn hHU hp hl hf ha
  exact roundedShQRSchurWith_terminatingSchurCore (Γ := Γ) (S := S) (δ := δ) (φ := φ)
    (RL := smallEigLeafRotations k (shqrSmallEigCap n k B Γ S δ φ c₁ c₂)) hS hM hu1 hL hNat hQ hC
    hDisk hk (smallEigProg_terminates (kmax := m) hS hM hu1 hL (hNat.mono (min_le_right _ _)) hC hQ
      hSmp
      hDisk (smallEigCaps_smallEigParams _ _ _ _ _ _) h12.ge) h12
    (sub_nonneg.mpr (one_le_pow₀ hX1))
    (sub_le_sub_right (pow_le_pow_right₀ hX1 hR) 1) H U hn hHU hp hl hf ha

/-- **The memory holding the input of the Schur core**: the views of the matrix, the parameter
words, the accumulator and the failure word are live, have room and are apart; the pair
$(\mathbf{U}, \mathbf{H})$ and the words `NLAlib.ShiftedQR.shqrSchurParams` are stored. -/
def ShQRSchurInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) (a p uo f : ℕ × ℕ)
    (U H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, p, uo, f] ∧
    μ.Room [a, p, uo, f] [2 * ((n + 1) * (n + 1)),
      (shqrSchurParams n k B Γ S δ φ c₁ c₂).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)),
      (shqrSchurParams n k B Γ S δ φ c₁ c₂).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Schur.HoldsSchurPair a uo U H μ.store ∧
    μ.store.readBlock p.1 p.2 (shqrSchurParams n k B Γ S δ φ c₁ c₂).length =
      some (shqrSchurParams n k B Γ S δ φ c₁ c₂)

/-- **The rounded shifted QR algorithm computes a Schur form** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3] with the quantifiers of Theorem 1.4, corrected, in Schur form; `SmallEig` by
[BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3]). Let the machine have the
standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals up
to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the tape only in
its windows whose draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact
polar disk sampler on it and a stream $s_G$ with the standard real Gaussian law; let the eigenvalue
gap and the eigenvector condition of a complex Ginibre perturbation have the tails $c_1$, $c_2$
with $b_1, b_2 > 0$. Let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $B \ge 1$ and $k$ the
degree of (eqn:setk) at $4B$. Then from a memory holding $\mathbf{H}$, an accumulator
$\mathbf{U}_0$ and the words of `NLAlib.ShiftedQR.shqrSchurParams`, under a random tape with the
stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRSchur}(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the accumulator and the failure word, or stores no } (\widehat{\mathbf{U}},
  \widehat{\mathbf{T}}),\ \widehat{\mathbf{T}} \text{ upper triangular},\
  \widehat{\mathbf{T}} = \mathbf{W}^{\mathsf H}(\mathbf{H} + \mathbf{E})\mathbf{W},\
  \|\mathbf{E}\|_2 \le \delta,\ \|\widehat{\mathbf{U}} - \mathbf{U}_0\mathbf{W}\|_2 \le
  ((1 + 24\boldsymbol{u})^R - 1)\|\mathbf{U}_0\|_2\bigr] \le \varphi\,,$$
for an exact unitary $\mathbf{W}$. Here $\boldsymbol{u}_0$ is `NLAlib.ShiftedQR.uShQRSchur` and
$R$ is `NLAlib.ShiftedQR.shqrSmallEigRotations`.
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there only the eigenvalues are computed, with an
oracle.

Note: The contract form is `NLAlib.ShiftedQR.roundedShQRSchur_randomSchurCoreContract`; the
general form with any small-block Schur solver is
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`.
Result: shifted-qr-rounded-schur -/
theorem roundedShQRSchur_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hB1 : 1 ≤ B)
    (hΓ : 0 < Γ) (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ)
    (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S δ φ c₁ c₂) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hin : ShQRSchurInput k B Γ S δ φ c₁ c₂ a p uo f U₀ H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSchur (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, (shqrSchurParams n k B Γ S δ φ c₁ c₂).length, k, shqrCap n B Γ S δ,
        shqrSmallEigCap n k B Γ S δ φ c₁ c₂] [a, p, uo, a, uo, f]) (shqrFp n a uo f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Schur.HoldsSchurPair a uo U' Tm μ'.store ∧
          Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar ((1 + 24 * u) ^ shqrSmallEigRotations n k B Γ S δ φ c₁ c₂ - 1)
            δ U₀ H U' Tm) μ} ≤ φ := by
  obtain ⟨hl, hr, ha, hP, hp⟩ := hin
  exact (roundedShQRSchur_randomSchurCoreContract hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG
    hA hB hb₁ hb₂ hB1 hΓ hδ hδS hφ hφ1 hk hu H U₀ le_rfl hHess hHS
    ⟨V, d, hV, hHV, hκ, hgap⟩).measureReal_not_writes_le ⟨hP, hp, hl, hr.2.2.2.1, ha⟩ hξ

end SchurCore

/-- **The rounded shifted QR algorithm with no oracle** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3] with the quantifiers of Theorem 1.4, corrected; `SmallEig` by
[BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3]). Let the machine have the
standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals
up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the tape only in
its windows whose draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact
polar disk sampler on it and a stream $s_G$ with the standard real Gaussian law; let the eigenvalue
gap and the eigenvector condition of a complex Ginibre perturbation have the tails $c_1$, $c_2$
with $b_1, b_2 > 0$. Let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Then from a memory holding $\mathbf{H}$, the deflation threshold word and the
words of `NLAlib.ShiftedQR.shqrSmallEigParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRSmallEig}(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the output and the failure word, or lists no }
  \operatorname{spec}(\mathbf{H} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,.$$
Here $\boldsymbol{u}_0$ is `NLAlib.ShiftedQR.uShQRSchur`.
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there `SmallEig` is an oracle.

Note: The run terminates on every tape (`NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`).
General form: `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`.
Result: shifted-qr-rounded-small-eig-backward-error -/
theorem roundedShQRSmallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S δ φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ c₁ c₂) [a, t, p, out, a, out, f])
          (shqrFp n a out f)
      (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  obtain ⟨hl, hr, ha, ⟨U₀, hU₀⟩, hAm, ht, hp⟩ := hin
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hS0 : 0 < S := hδ.trans_le hδS
  have hacc0 := shqrSmallEigAccuracy_pos (n := n) hB1 hΓ hδ hS0
  have haccS := shqrSmallEigAccuracy_le (n := n) hB1 hΓ hδ hδS
  have hφse := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hφse1 := (shqrSmallEigFailure_le (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ)
    hφ.le).trans hφ1
  have h12 := length_smallEigParams k (4 * S)
    (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂
  simp only [uShQRSchur, uShQRSmallEig, le_min_iff] at hu
  obtain ⟨⟨hu1, hu2⟩, -, hu3⟩ := hu
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith [hM.roundoff_nonneg]
  exact roundedShQRWith_measureReal_not_spectrum_le hS hM hL hNat hQ hC hI hloc hDisk hU hHess hV
    hHV hκ hΓ hgap hHS hδ hδS hφ hφ1 hk (smallEigProg_randomSchurLeafContract hS hM hL
      (min_le_left k (n + 1)) (hNat.mono (min_le_right _ _)) hQ hC hI hloc hSmp hDisk hU hG hA hB
      hb₁ hb₂ hacc0 haccS hφse hφse1 hu2) h12 (sub_nonneg.mpr (one_le_pow₀ hX1)) le_rfl
    (forwardBackwardError_spec (kmax := k) hacc0 haccS).1.le le_rfl hφse.le le_rfl hu1 hu3 hl hr
    ha hAm hU₀ ht hp hξ

/-- **The algorithm with the small-eigenvalue program terminates on every tape**: on a scalar
machine with index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons,
draws that store the tape entry and an exact polar disk sampler, for any $(n + 1) \times (n + 1)$
matrix $\mathbf{H}$ (no structure assumed), any $B, \Gamma, \Sigma, \delta, \varphi$, $k$ the
degree of (eqn:setk) at $4B$ and any tail records, the run of
`NLAlib.ShiftedQR.roundedShQRSmallEig` from `NLAlib.ShiftedQR.ShQRSmallEigInput` succeeds on every
tape and writes only the matrix, the output and the failure word. No rounding model, unit
roundoff, class or random-matrix hypothesis is needed: the stored cap words are valid, and the
small-eigenvalue program completes on every machine (`NLAlib.SmallEig.smallEigProg_completes`). -/
theorem roundedShQRSmallEig_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {c₁ c₂ : PolyLogTail}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {B Γ S δ φ : ℝ}
    (hk : k = shqrDegree (4 * B)) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H μ) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ c₁ c₂) [a, t, p, out, a, out, f])
          (shqrFp n a out f)
      (fun _ => True) μ := by
  obtain ⟨hl, hr, ha, ⟨U₀, hU₀⟩, hA, ht, hp⟩ := hin
  have h12 := length_smallEigParams k (4 * S)
    (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂
  exact roundedShQRWith_terminates (T := shqrSmallEigCap n k B Γ S δ φ c₁ c₂) hS hL hNat hQ hC
    hDisk hk (smallEigProg_completes (kmax := min k (n + 1)) hS hL (hNat.mono (min_le_right _ _))
      hC hQ hSmp hDisk (smallEigCaps_smallEigParams _ _ _ _ _ _) h12.ge) h12 hl hr ha hA hU₀ ht
    hp τ

open Real in
/-- **The iteration cap is logarithmic**: there is an absolute constant $c$ with
$F \le c\log_2 Y + c$, $Y = 4(n + 1)B\Sigma^2/(\delta\min(\Gamma, \Sigma)\varphi)$, for
$F$ = `NLAlib.ShiftedQR.shqrCap`, every order $n + 1$, $B \ge 1$, $\Gamma > 0$,
$0 < \delta \le \Sigma$ and $0 < \varphi \le 1$: the cap is $\lceil\log(4\Sigma/\omega)/
\log(1/0.8016)\rceil + 1$ and $4\Sigma/\omega \le 4Y^8$ (`NLAlib.ShiftedQR.shqrArg_facts`), so
$c = 30$. -/
theorem shqrCap_le_log : ∃ c : ℝ, ∀ {n : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ → δ ≤ S →
    0 < φ → φ ≤ 1 →
    (shqrCap n B Γ S δ : ℝ) ≤
      c * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) + c := by
  refine ⟨30, fun {n B Γ S δ φ} hB hΓ hδ hδS hφ hφ1 => ?_⟩
  have hS : 0 < S := hδ.trans_le hδS
  obtain ⟨hY4, -, -, -, hrr, -, -⟩ :=
    shqrArg_facts (n := n) (k := shqrDegree (4 * B)) hB hΓ hδ hδS hφ hφ1 rfl
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  set ω := shqrOmega n B Γ δ
  have hω0 : 0 < ω := shqrOmega_pos hB hΓ hδ
  have hωS : ω ≤ S := shqrOmega_le_normBound hB hΓ hδ hδS
  have h4 : 1 ≤ 4 * S / ω := by rw [le_div_iff₀ hω0]; linarith
  have hc : 0.1984 ≤ log (1 / shqrContraction) := by
    have := one_sub_inv_le_log_of_pos (x := 1 / shqrContraction)
      (by unfold shqrContraction; norm_num)
    unfold shqrContraction at this ⊢; norm_num at this ⊢; linarith
  have hl0 : 0 ≤ log (4 * S / ω) := log_nonneg h4
  have hx0 : 0 ≤ log (4 * S / ω) / log (1 / shqrContraction) := div_nonneg hl0 (by linarith)
  have hcap : (shqrCap n B Γ S δ : ℝ) ≤ log (4 * S / ω) / log (1 / shqrContraction) + 2 := by
    have := Nat.ceil_lt_add_one hx0
    rw [shqrCap, Nat.cast_add, Nat.cast_one]
    linarith
  have hdiv : log (4 * S / ω) / log (1 / shqrContraction) ≤ log (4 * S / ω) / 0.1984 :=
    div_le_div_of_nonneg_left hl0 (by norm_num) hc
  have hYω : 4 * S / ω ≤ 4 * Y ^ 8 := by
    have h := hrr.2
    rw [div_le_iff₀ hω0]
    have e : ω / S * Y ^ 8 * S = ω * Y ^ 8 := by field_simp
    nlinarith
  have hY0 : 0 < Y := by linarith
  have hlog : log (4 * S / ω) ≤ log 4 + 8 * log Y := by
    calc log (4 * S / ω) ≤ log (4 * Y ^ 8) := log_le_log (by positivity) hYω
      _ = log 4 + 8 * log Y := by rw [log_mul (by norm_num) (by positivity), log_pow]; norm_num
  have h4l : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have hL : log Y = logb 2 Y * log 2 := by rw [logb, div_mul_cancel₀ _ (log_pos one_lt_two).ne']
  have hL0 : 0 ≤ logb 2 Y := logb_nonneg one_lt_two (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hm : logb 2 Y * log 2 ≤ logb 2 Y * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2.le hL0
  rw [hL] at hlog
  have : log (4 * S / ω) / 0.1984 ≤
      (2 * 0.6931471808 + 8 * (logb 2 Y * 0.6931471808)) / 0.1984 := by
    gcongr; linarith
  have h2 : (2 * 0.6931471808 + 8 * (logb 2 Y * 0.6931471808)) / 0.1984 ≤
      28 * logb 2 Y + 7 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

open Real in
/-- **The shift degree is $O(\log B\log\log B)$**: there is an absolute constant $c$ with
$k \le c(\log_2(4B) + 1)(\log_2\log_2(16B) + 1)$ for $k$ the degree of (eqn:setk) at $4B$, for
every $B \ge 1$ ([BanksGarzaVargasSrivastava2022, Theorem 1.4], the choice of $k$). -/
theorem shqrDegree_le_log : ∃ c : ℝ, ∀ {B : ℝ}, 1 ≤ B →
    (shqrDegree (4 * B) : ℝ) ≤ c * (Real.logb 2 (4 * B) + 1) *
      (Real.logb 2 (Real.logb 2 (16 * B)) + 1) := by
  refine ⟨128, fun {B} hB => ?_⟩
  have hB0 : 0 < B := by linarith
  set x := logb 2 (4 * B) with hx
  set y := logb 2 (logb 2 (16 * B)) with hy
  have hx2 : 2 ≤ x := by
    rw [hx, le_logb_iff_rpow_le (by norm_num) (by positivity)]; norm_num; linarith
  have h16 : 4 ≤ logb 2 (16 * B) := by
    rw [le_logb_iff_rpow_le (by norm_num) (by positivity)]; norm_num; linarith
  have hy2 : 2 ≤ y := by
    rw [hy, le_logb_iff_rpow_le (by norm_num) (by positivity)]; norm_num; linarith
  have hxy : logb 2 (x + 1) ≤ y := by
    have : x + 1 = logb 2 (8 * B) := by
      rw [show (8 : ℝ) * B = 2 * (4 * B) by ring, logb_mul (by norm_num) (by positivity),
        logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]; ring
    rw [this, hy]
    exact logb_le_logb_of_le (by norm_num) (by
      rw [← this]; linarith) (logb_le_logb_of_le (by norm_num) (by positivity) (by linarith))
  have hyy : logb 2 (y + 1) ≤ y := by
    rw [logb_le_iff_le_rpow (by norm_num) (by linarith)]
    have := one_add_mul_self_le_rpow_one_add (by norm_num : (-1 : ℝ) ≤ 1) (by linarith : 1 ≤ y)
    norm_num at this; linarith
  set T := 64 * (x + 1) * (y + 1) with hT
  have hT1 : 1 ≤ T := by nlinarith
  obtain ⟨q, hq1, hq2⟩ := exists_nat_pow_near hT1 (by norm_num : (1 : ℝ) < 2)
  have hqT : (q : ℝ) ≤ 6 + 2 * y := by
    have h1 : (q : ℝ) ≤ logb 2 T := by
      rw [le_logb_iff_rpow_le (by norm_num) (by linarith), rpow_natCast]; exact hq1
    have h2 : logb 2 T = 6 + logb 2 (x + 1) + logb 2 (y + 1) := by
      rw [hT, logb_mul (by positivity) (by linarith), logb_mul (by norm_num) (by linarith),
        show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, logb_pow, logb_self_eq_one (by norm_num)]
      ring
    linarith
  have hset : SatisfiesSetk (4 * B) (q + 1) := by
    rw [satisfiesSetk_iff (by positivity) (by omega)]
    have hl2 : 0 < log 2 := log_pos (by norm_num)
    have hl23 : log 2 ≤ log 3 := log_le_log (by norm_num) (by norm_num)
    have hlB : log (4 * B) = x * log 2 := by
      rw [hx, logb, div_mul_cancel₀ _ hl2.ne']
    have hp : (8 * ((q : ℝ) + 1) + 11) * x + 3 ≤ 2 ^ (q + 1) := by nlinarith
    have hp1 : (0 : ℝ) ≤ 2 ^ (q + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (q + 1) := one_le_pow₀ (by norm_num)
      linarith
    push_cast
    rw [hlB]
    calc (8 * ((q : ℝ) + 1) + 11) * (x * log 2) + 2 * log 2
        ≤ (2 ^ (q + 1) - 1) * log 2 := by nlinarith
      _ ≤ (2 ^ (q + 1) - 1) * log 3 := by gcongr
  have hle : shqrLogDegree (4 * B) ≤ q + 1 := Nat.sInf_le hset
  calc (shqrDegree (4 * B) : ℝ) = 2 ^ shqrLogDegree (4 * B) := by simp [shqrDegree]
    _ ≤ 2 ^ (q + 1) := pow_le_pow_right₀ (by norm_num) hle
    _ = 2 * 2 ^ q := by ring
    _ ≤ 2 * T := by linarith
    _ = 128 * (x + 1) * (y + 1) := by rw [hT]; ring

open Real in
/-- The argument of the bits of `NLAlib.SmallEig.uSmallEigForward` in the algorithm: for $B \ge 1$,
$\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at
$4B$, the argument $4k \cdot 4\Sigma/(\delta_b\varphi_{\mathrm{se}})$ at the backward accuracy
$\delta_b$ of the forward accuracy is at least $1$ and at most $Y^{26 + 36k}$,
$Y = 4(n + 1)B\Sigma^2/(\delta\min(\Gamma, \Sigma)\varphi)$. -/
theorem hiBd_smallEigForwardArg {n k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ)
    (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) :
    1 ≤ 4 * k * (4 * S) / (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ) *
        shqrSmallEigFailure n B Γ S δ φ) ∧
      HiBd (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) (26 + 36 * k)
        (4 * k * (4 * S) / (forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ) *
          shqrSmallEigFailure n B Γ S δ φ)) := by
  have hS : 0 < S := hδ.trans_le hδS
  obtain ⟨hY4, hkY, -, -, hrr, -, hφu⟩ := shqrArg_facts (n := n) hB hΓ hδ hδS hφ hφ1 hk
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  have hk1 : (1 : ℝ) ≤ k := by
    have := two_le_shqrDegree (B := 4 * B) (by linarith); rw [← hk] at this
    exact_mod_cast (by omega : 1 ≤ k)
  set β := shqrSmallEigAccuracy n B Γ S δ
  set φs := shqrSmallEigFailure n B Γ S δ φ
  have hβ0 : 0 < β := shqrSmallEigAccuracy_pos hB hΓ hδ hS
  have hβS : β ≤ 4 * S := shqrSmallEigAccuracy_le hB hΓ hδ hδS
  have hφs0 : 0 < φs := shqrSmallEigFailure_pos hφ
  have hφs1 : φs ≤ 1 := (shqrSmallEigFailure_le hφ.le).trans hφ1
  set r := β / (4 * (2 * k + 1) * (4 * S)) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]; nlinarith
  have hβr : LoBd Y 24 (β / S) := by
    have e : β / S = (shqrOmega n B Γ δ / S) ^ 2 / 32320 := by
      simp only [β, shqrSmallEigAccuracy, shqrRadius]; field_simp; ring
    rw [e]; exact (hrr.pow 2).div (HiBd.const hY4 (by norm_num : (0 : ℝ) < 32320)
      (by norm_num : (32320 : ℝ) ≤ 4 ^ 8))
  have hrY : LoBd Y 36 r := by
    have e : r = β / S / (16 * (2 * k + 1)) := by rw [hr]; field_simp; ring
    rw [e]
    exact hβr.div (((HiBd.const hY4 (by norm_num : (0 : ℝ) < 48) (by norm_num :
      (48 : ℝ) ≤ 4 ^ 3)).mul hkY).of_le (by positivity) (by nlinarith))
  have e : 4 * k * (4 * S) / (forwardBackwardError k (4 * S) β * φs) = 4 * k / (r ^ k * φs) := by
    simp only [forwardBackwardError, ← hr]; field_simp
  rw [e]
  have hrk : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : r ^ k * φs ≤ 1 := mul_le_one₀ hrk hφs0.le hφs1
    linarith
  · have h := ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul
      hkY).div ((hrY.pow k).mul hφu)
    refine h.mono (by linarith) (by ring_nf; omega)

open Real in
/-- **The bits of precision of the algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]): for tail records with $b_1, b_2 > 0$ there are constants $e_1, e_2, e_3$ such that
for every order $n + 1$, $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$k$ the degree of (eqn:setk) at $4B$,
$$\log_2\frac{1}{\boldsymbol{u}_0} \le e_1 k\log_2 Y + e_2k^2\log_2^2 Y + e_3, \qquad
  Y = \frac{4(n + 1)B\Sigma^2}{\delta\min(\Gamma, \Sigma)\varphi}\,,$$
$\boldsymbol{u}_0$ = `NLAlib.ShiftedQR.uShQRSmallEig`; with `NLAlib.ShiftedQR.shqrDegree_le_log`
this is $O(\log^4 Y)$ up to $(\log\log Y)^2$. -/
theorem logb_inv_uShQRSmallEig_le (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ e₁ e₂ e₃ : ℝ, ∀ {n k : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ → δ ≤ S → 0 < φ →
      φ ≤ 1 → k = shqrDegree (4 * B) →
      Real.logb 2 (uShQRSmallEig n k B Γ S δ φ c₁ c₂)⁻¹ ≤
        e₁ * k * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) +
          e₂ * k ^ 2 * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) ^ 2 + e₃ := by
  obtain ⟨E₁, E₂, hE⟩ := logb_inv_uSmallEig_le c₁ c₂ hb₁ hb₂
  refine ⟨93, max E₁ 0 * 3844, max E₂ 0, fun {n k B Γ S δ φ} hB hΓ hδ hδS hφ hφ1 hk => ?_⟩
  have hS : 0 < S := hδ.trans_le hδS
  obtain ⟨hY4, hu⟩ := one_le_uShQR_mul (n := n) hB hΓ hδ hδS hφ hφ1 hk
  obtain ⟨hY'1, hY'⟩ := hiBd_smallEigForwardArg (n := n) hB hΓ hδ hδS hφ hφ1 hk
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  set L := logb 2 Y
  have hL : 2 ≤ L := by
    rw [le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; linarith
  have hk2 : 2 ≤ k := hk ▸ two_le_shqrDegree (by linarith)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hβ0 := shqrSmallEigAccuracy_pos (n := n) hB hΓ hδ hS
  have hβS := shqrSmallEigAccuracy_le (n := n) hB hΓ hδ hδS
  have hφs0 := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hφs1 := (shqrSmallEigFailure_le (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ.le).trans
    hφ1
  obtain ⟨hδb, hδbS, -⟩ := forwardBackwardError_spec (kmax := k) hβ0 hβS
  -- the shifted QR term
  have hA : logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤ 93 * k * L := by
    have h := (LoBd.logb_inv_le ⟨uShQR_pos (by omega) hB hΓ hδ hS hφ, hu⟩ :
      logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤ ((53 * k + 40 : ℕ) : ℝ) * L)
    push_cast at h; nlinarith
  -- the small-eigenvalue term
  have hB' : logb 2 (uSmallEigForward k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
      (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂)⁻¹ ≤ max E₁ 0 * 3844 * k ^ 2 * L ^ 2 + max E₂ 0 := by
    have h := hE (nmax := k) (by omega) hδb hδbS hφs0 hφs1
    have hL' := hY'.logb_le
    have hL'0 : 0 ≤ logb 2 (4 * k * (4 * S) / (forwardBackwardError k (4 * S)
        (shqrSmallEigAccuracy n B Γ S δ) * shqrSmallEigFailure n B Γ S δ φ)) :=
      logb_nonneg (by norm_num) hY'1
    push_cast at hL' h
    set L' := logb 2 (4 * k * (4 * S) / (forwardBackwardError k (4 * S)
        (shqrSmallEigAccuracy n B Γ S δ) * shqrSmallEigFailure n B Γ S δ φ))
    have h1 : L' ≤ 62 * k * L := by nlinarith
    have h2 : L' ^ 2 ≤ 3844 * k ^ 2 * L ^ 2 := by nlinarith
    unfold uSmallEigForward
    calc _ ≤ E₁ * L' ^ 2 + E₂ := h
      _ ≤ max E₁ 0 * L' ^ 2 + max E₂ 0 := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
      _ ≤ max E₁ 0 * (3844 * k ^ 2 * L ^ 2) + max E₂ 0 := by gcongr
      _ = _ := by ring
  have hL0 : 0 ≤ 93 * (k : ℝ) * L := by positivity
  have h3 : 0 ≤ max E₁ 0 * 3844 * (k : ℝ) ^ 2 * L ^ 2 := by
    have := le_max_right E₁ 0; positivity
  have h4 : 0 ≤ max E₂ 0 := le_max_right _ _
  unfold uShQRSmallEig
  rcases min_choice (uShQR n k B Γ S δ φ) (uSmallEigForward k (4 * S)
    (shqrSmallEigAccuracy n B Γ S δ) (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂) with h | h <;>
    rw [h] <;> linarith

-- The kernel evaluates the bound of the whole instrumented tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- **The monomial work bound of the algorithm with the small-eigenvalue program**: the
monomial bound `NLAlib.Ops.stmtWorkMono` of the instrumented tree of
`NLAlib.ShiftedQR.roundedShQRSmallEig` at the slot bounds $(n + 1)$, $k$, $n_p$, $F$, $T$,
$F(k + 1 + n_p)$, $k(n + 1)$ and the offsets $0, n_p, n_p, 0, \dots$ is
$369224\,b_0^3 b_1^4 b_2 b_3 b_4^2$, by kernel evaluation. It serves both the count of the
program and that of its Schur core frame (`NLAlib.ShiftedQR.roundedShQRSchur`). -/
theorem stmtWorkMono_roundedShQRSmallEig (sG : ℕ) :
    stmtWorkMono (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument
      ([⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩, ⟨1, [0, 0, 0, 0, 1]⟩,
        ⟨1, [0, 1, 1, 1]⟩, ⟨1, [1, 1]⟩, WorkMono.const 0, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++
        List.replicate 4 (WorkMono.const 0)) =
      ⟨369224, [3, 4, 1, 1, 2]⟩ := by
  kernel_rfl

/-- **The operation count of the algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] and [BanksGarzaVargasSrivastava2025, Theorem 1.1],
running times, on every tape): the instrumented static count (`NLAlib.Ops.stmtCost` of
`NLAlib.Ops.Stmt.instrument`) of `NLAlib.ShiftedQR.roundedShQRSmallEig` at the order $n + 1$, the
shift degree $k$, $n_p$ words, the iteration cap $F$, the cap $T$, the log of $F(k + 1 + n_p)$
slots of $k(n + 1)$ entries (`NLAlib.ShiftedQR.shqrSmallEigDims`) and the zero offsets of its seven
operands is at most $369224(n + 1)^3(k + 1)^4(n_p + 1)(F + 1)(T + 1)^2$: the cost of `SmallEig`
is counted. -/
theorem roundedShQRSmallEig_work_le (sG n k np F T : ℕ) :
    Count.size (stmtCost (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument
        [n + 1, k, np, F, T, F * (k + 1 + np), k * (n + 1), 0, 0, 0, 0, 0, 0, 0]) ≤
      369224 * (n + 1) ^ 3 * (k + 1) ^ 4 * (np + 1) * (F + 1) * (T + 1) ^ 2 := by
  have hσ : SlotsLe [n + 1, k + 1, np + 1, F + 1, T + 1]
      [n + 1, k, np, F, T, F * (k + 1 + np), k * (n + 1), 0, 0, 0, 0, 0, 0, 0]
      ([⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩, ⟨1, [0, 0, 0, 0, 1]⟩,
        ⟨1, [0, 1, 1, 1]⟩, ⟨1, [1, 1]⟩, WorkMono.const 0, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++
        List.replicate 4 (WorkMono.const 0)) := by
    suffices F * (k + 1 + np) ≤ (k + 1) * ((np + 1) * (F + 1)) ∧
        k * (n + 1) ≤ (n + 1) * (k + 1) by
      simpa [SlotsLe, WorkMono.eval, WorkMono.const] using this
    have h1 : k + 1 + np ≤ (k + 1) * (np + 1) := by nlinarith
    have h2 := Nat.mul_le_mul_left F h1
    constructor <;> nlinarith
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument hσ
  rw [stmtWorkMono_roundedShQRSmallEig] at h
  simpa [WorkMono.eval, mul_assoc] using h

/-- The instructions of the Schur core: the instrumented static count of
`NLAlib.ShiftedQR.roundedShQRSchur` at the order $n + 1$, $n_q$ words, the shift degree $k$, the
iteration cap $F$, the leaf cap $T$, the parameter words at the offset $p$ and the other operands
at offset zero is at most $380748(n + 1)^3(k + 1)^4(p + n_q + 1)(F + 1)(T + 1)^2$: the frame's
$36$ structural instructions and the count of `NLAlib.ShiftedQR.roundedShQRSmallEig` at the frame's
dimensions and offsets (`NLAlib.ShiftedQR.stmtWorkMono_roundedShQRSmallEig`), the cost of
`SmallEig` included. -/
theorem size_stmtCost_roundedShQRSchur_le (sG n nq k F T p : ℕ) :
    Count.size (stmtCost (roundedShQRSchur (O := O) (Q := Q) sG).body.instrument
        [n + 1, nq, k, F, T, 0, p, 0, 0, 0, 0]) ≤
      380748 * (n + 1) ^ 3 * (k + 1) ^ 4 * (p + nq + 1) * (F + 1) * (T + 1) ^ 2 := by
  have hσ : SlotsLe [n + 1, k + 1, p + nq + 1, F + 1, T + 1]
      [n + 1, k, nq - 1, F, T, F * (k + 1 + (nq - 1)), k * (n + 1), 0, p, p + 1, 0, 0, 0, 0]
      ([⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩, ⟨1, [0, 0, 0, 0, 1]⟩,
        ⟨1, [0, 1, 1, 1]⟩, ⟨1, [1, 1]⟩, WorkMono.const 0, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++
        List.replicate 4 (WorkMono.const 0)) := by
    suffices nq ≤ p + nq + 1 + 1 ∧ F * (k + 1 + (nq - 1)) ≤ (k + 1) * ((p + nq + 1) * (F + 1)) ∧
        k * (n + 1) ≤ (n + 1) * (k + 1) ∧ p ≤ p + nq + 1 by
      simpa [SlotsLe, WorkMono.eval, WorkMono.const] using this
    have h1 : k + 1 + (nq - 1) ≤ (k + 1) * (p + nq + 1) := by nlinarith [Nat.sub_le nq 1]
    have h2 := Nat.mul_le_mul_left F h1
    refine ⟨by omega, by nlinarith, by nlinarith, by omega⟩
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument hσ
  rw [stmtWorkMono_roundedShQRSmallEig] at h
  have hin : Count.size (stmtCost (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument
      [n + 1, k, nq - 1, F, T, F * (k + 1 + (nq - 1)), k * (n + 1), 0, p, p + 1, 0, 0, 0, 0]) ≤
      369224 * ((n + 1) ^ 3 * (k + 1) ^ 4 * (p + nq + 1) * (F + 1) * (T + 1) ^ 2) := by
    simpa [WorkMono.eval, mul_assoc] using h
  have hframe : ∀ X, Count.size (stmtCost (roundedShQRSmallEig (O := O) (Q := Q) sG).body.instrument
      [n + 1, k, nq - 1, F, T, F * (k + 1 + (nq - 1)), k * (n + 1), 0, p, p + 1, 0, 0, 0, 0]) ≤ X →
      Count.size (stmtCost (roundedShQRSchur (O := O) (Q := Q) sG).body.instrument
        [n + 1, nq, k, F, T, 0, p, 0, 0, 0, 0]) ≤ 36 + X := fun X hX => by
    have e : (IExp.var 1 - IExp.const 1) = IExp.sub (IExp.var 1) (IExp.const 1) := rfl
    simp only [roundedShQRSmallEig] at hX
    simp [roundedShQRSchur, roundedShQRSchurWith, Stmt.instrument, tally, indexBookkeeping,
      operandBookkeeping, IExp.bookkeeping, stmtCost, useCost, IExp.evalList, IExp.eval,
      Count.one, size_single, e]
    omega
  have hM : 1 ≤ (n + 1) ^ 3 * (k + 1) ^ 4 * (p + nq + 1) * (F + 1) * (T + 1) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine (hframe _ hin).trans ?_
  simp only [mul_assoc] at hM ⊢
  omega

/-- **The algorithm with no oracle, relative form** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], the error relative to $\|\mathbf{H}\|_2$): with the machine, streams and tails of
`NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le` written out in the signature:
let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg, in the class $(B, \Gamma)$, with
$\Sigma > 0$, $\|\mathbf{H}\|_2 \le \Sigma \le c\|\mathbf{H}\|_2$, $c \ge 1$,
$0 < \delta \le 1$, $0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4B$, and the words and
the precision at the absolute error $\delta\Sigma/c$. Then the probability that the run fails,
writes outside the matrix, the output and the failure word, or lists no spectrum of
$\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta\|\mathbf{H}\|_2$ is at most
$\varphi$.
Result: shifted-qr-rounded-small-eig-backward-error -/
theorem roundedShQRSmallEig_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S c δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hS0 : 0 < S) (hHS : specNorm H ≤ S)
    (hSc : S ≤ c * specNorm H) (hc : 1 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S (δ * S / c) φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S (δ * S / c) φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S (δ * S / c) φ c₁ c₂) [a, t, p, out, a, out, f])
      (shqrFp n a out f) (ShQRSpectrum a out f H (δ * specNorm H)) μ} ≤ φ := by
  have hc0 : 0 < c := by linarith
  have h1 : 0 < δ * S / c := by positivity
  have h2 : δ * S / c ≤ S := by rw [div_le_iff₀ hc0]; nlinarith
  have h3 : δ * S / c ≤ δ * specNorm H := by rw [div_le_iff₀ hc0]; nlinarith
  have hT := roundedShQRSmallEig_measureReal_not_spectrum_le hS hM hL hNat hQ hC hI hloc hSmp
    hDisk hU hG hA hB hb₁ hb₂ hHess hV hHV hκ hΓ hgap hHS h1 h2 hφ hφ1 hk hu hin hξ
  have := hξ.isProbabilityMeasure
  refine le_trans ?_ hT
  refine measureReal_mono fun ω' hω' hW => hω' ?_
  exact hW.mono le_rfl fun μ' _ ⟨hf, Tm, U, E, hTm, hU, hT, hE, hR⟩ =>
    ⟨hf, Tm, U, E, hTm, hU, hT, hE.trans h3, hR⟩

/-- **The algorithm with no oracle on Hermitian inputs** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], at the condition $1$): with the machine, streams and tails written out in the
signature: let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg and Hermitian with eigenvalues
separated by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4$, and the words and the precision at
$B = 1$. Then the probability that the run fails, writes outside the matrix, the output and the
failure word, or lists no spectrum of $\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta$
is at most $\varphi$. -/
theorem roundedShQRSmallEig_hermitian {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {Γ S δ φ : ℝ}
    (hHess : IsUpperHessenberg H) (hH : H.IsHermitian) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ |hH.eigenvalues i - hH.eigenvalues j|) (hHS : specNorm H ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree 4)
    (hu : u ≤ uShQRSchur n k 1 Γ S δ φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRSmallEigInput k 1 Γ S δ φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k 1 Γ S δ φ c₁ c₂) [a, t, p, out, a, out, f])
          (shqrFp n a out f)
      (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  set U := (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hUo : HasOrthonormalCols U := hH.hasOrthonormalCols_eigenvectorUnitary
  have hHU : H * U = U * Matrix.diagonal fun i => (hH.eigenvalues i : ℂ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    refine (congrArg (· * U) h).trans ?_
    rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
    rfl
  have hgap' : ∀ i j, i ≠ j → Γ ≤ ‖(hH.eigenvalues i : ℂ) - (hH.eigenvalues j : ℂ)‖ := by
    intro i j hij
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap i j hij
  exact roundedShQRSmallEig_measureReal_not_spectrum_le hS hM hL hNat hQ hC hI hloc hSmp hDisk hU
    hG hA hB hb₁ hb₂ hHess hUo.isUnit hHU hUo.pseudoConditionNumber_eq_one.le hΓ hgap' hHS hδ hδS
    hφ hφ1 (by rw [mul_one]; exact hk) hu hin hξ

/-! ### With the proved random-matrix tails -/

/-- **The rounded shifted QR algorithm with no oracle, unconditional**.
The unconditional form of `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`
([BanksGarzaVargasSrivastava2022, Theorem 6.3]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: shifted-qr-rounded-small-eig-backward-error -/
theorem roundedShQRSmallEig_measureReal_not_spectrum_le_unconditional {Mch : Machine ℝ} {I : Interp
  O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1)
      → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S δ φ ginibreGapTail
      ginibreConditionTail)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ ginibreGapTail
      ginibreConditionTail a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ ginibreGapTail
        ginibreConditionTail) [a, t, p, out, a, out, f]) (shqrFp n a out f)
      (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  apply roundedShQRSmallEig_measureReal_not_spectrum_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- **The algorithm with no oracle, relative form, unconditional**.
The unconditional form of `NLAlib.ShiftedQR.roundedShQRSmallEig_relative`
([BanksGarzaVargasSrivastava2022, Theorem 6.3]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: shifted-qr-rounded-small-eig-backward-error -/
theorem roundedShQRSmallEig_relative_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n
  : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1)
      → ℂ} {k : ℕ}
    {B Γ S c δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hS0 : 0 < S) (hHS : specNorm H ≤ S)
    (hSc : S ≤ c * specNorm H) (hc : 1 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSchur n k B Γ S (δ * S / c) φ ginibreGapTail
      ginibreConditionTail)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S (δ * S / c) φ ginibreGapTail
      ginibreConditionTail a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S (δ * S / c) φ ginibreGapTail
        ginibreConditionTail) [a, t, p, out, a, out, f])
      (shqrFp n a out f) (ShQRSpectrum a out f H (δ * specNorm H)) μ} ≤ φ := by
  apply roundedShQRSmallEig_relative
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- The unconditional form of `NLAlib.ShiftedQR.roundedShQRSmallEig_hermitian`
([BanksGarzaVargasSrivastava2022, Theorem 6.3]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$. -/
theorem roundedShQRSmallEig_hermitian_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n
  : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {Γ S δ φ :
      ℝ}
    (hHess : IsUpperHessenberg H) (hH : H.IsHermitian) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ |hH.eigenvalues i - hH.eigenvalues j|) (hHS : specNorm H ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree 4)
    (hu : u ≤ uShQRSchur n k 1 Γ S δ φ ginibreGapTail
      ginibreConditionTail)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRSmallEigInput k 1 Γ S δ φ
      ginibreGapTail ginibreConditionTail a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k 1 Γ S δ φ ginibreGapTail
        ginibreConditionTail) [a, t, p, out, a, out, f]) (shqrFp n a out f)
      (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  apply roundedShQRSmallEig_hermitian
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end Theorems

end NLAlib.ShiftedQR
