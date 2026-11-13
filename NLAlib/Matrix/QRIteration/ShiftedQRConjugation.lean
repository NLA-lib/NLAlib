/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftedQR

/-!
# The shifted QR step as a sequence of conjugations by Givens rotations

The shifted QR step $\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$ (`NLAlib.shiftedQRStep`) is
reached from $\mathbf{H}$ by $n$ conjugations $\mathbf{Z} \mapsto \mathbf{G}_k \mathbf{Z}
\mathbf{G}_k^{\mathsf{H}}$, with $\mathbf{G}_k$ the rotation of step $k$ of Givens QR of
$\mathbf{H} - s\mathbf{I}$ (`NLAlib.givensHessenbergStep`): the last of the $n + 1$ steps of Givens
QR of a square matrix of order $n + 1$ is the identity. A program that rotates the rows of the
working matrix and conjugates a copy of $\mathbf{H}$ by the same rotations needs no accumulation of
$\mathbf{Q}$ and no product of matrices.

## Main results

* `NLAlib.givensHessenbergStep_last`: the last step of Givens QR of a square matrix is the
  identity.
* `NLAlib.shiftedQRStep_eq_conj_givensHessenbergState`: the shifted QR step is the conjugation
  of $\mathbf{H}$ by the unitary factor after $n$ steps.
* `NLAlib.conj_givensHessenbergState_succ`: the conjugation after $k + 1$ steps is one more
  conjugation by a rotation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The step $n$ of Givens QR of a square matrix of order $n + 1$ is the identity: there is no
entry $(n + 1, n)$ to clear. -/
theorem givensHessenbergStep_last (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    givensHessenbergStep W n = 1 := by
  unfold givensHessenbergStep
  rw [dif_neg (by omega)]

/-- The shifted QR step is the conjugation by the unitary factor after $n$ steps: the
$n + 1$ steps of Givens QR of $\mathbf{H} - s\mathbf{I}$ have the identity as last step, so
`NLAlib.shiftedQRStep` conjugates by the factor of the first $n$ steps. -/
theorem shiftedQRStep_eq_conj_givensHessenbergState (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s :
    ℂ) :
    shiftedQRStep H s =
      (givensHessenbergState (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) n).1ᴴ * H *
        (givensHessenbergState (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) n).1 := by
  have h : givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      (givensHessenbergState (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) n).1 := by
    unfold givensHessenbergQ
    rw [givensHessenbergState, givensHessenbergStep_last, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [shiftedQRStep, h]

/-- One more conjugation: the conjugation of $\mathbf{H}$ by the unitary factor after $k + 1$
steps of Givens QR of $\mathbf{W}_0$ is the rotation $\mathbf{G}_k$ of step $k$ applied on both
sides
to the conjugation after $k$ steps. -/
theorem conj_givensHessenbergState_succ {m p : ℕ} (W₀ : Matrix (Fin m) (Fin p) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    (givensHessenbergState W₀ (k + 1)).1ᴴ * H * (givensHessenbergState W₀ (k + 1)).1 =
      givensHessenbergStep (givensHessenbergState W₀ k).2 k *
        ((givensHessenbergState W₀ k).1ᴴ * H * (givensHessenbergState W₀ k).1) *
        (givensHessenbergStep (givensHessenbergState W₀ k).2 k)ᴴ := by
  rw [show (givensHessenbergState W₀ (k + 1)).1 = (givensHessenbergState W₀ k).1 *
      (givensHessenbergStep (givensHessenbergState W₀ k).2 k)ᴴ from rfl,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end NLAlib
