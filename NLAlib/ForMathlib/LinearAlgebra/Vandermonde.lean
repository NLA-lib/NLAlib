/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Lagrange basis polynomials and the inverse of a Vandermonde matrix

For distinct nodes $v_0, \dots, v_{t-1}$ in a field, with Lagrange basis polynomials $\ell_i$
(`Lagrange.basis Finset.univ v i`) and Vandermonde matrix $\mathbf{V} = (v_i^j)$
(`Matrix.vandermonde v`), the row of powers at any point $x$ is the combination
$(1, x, \dots, x^{t-1}) = \sum_i \ell_i(x)\,(1, v_i, \dots, v_i^{t-1})$ of the rows of
$\mathbf{V}$. So a matrix of power rows at points $y_a$ is
$\mathbf{L}\mathbf{V}$ with $\mathbf{L}_{ai} = \ell_i(y_a)$, and the columns of
$\mathbf{V}^{-1}$ are the coefficients of the $\ell_i$. Mathlib has both objects and no
statement relating them; each fact here is the evaluation of `Lagrange.eq_interpolate` at a
monomial. Upstream candidates for `Mathlib.LinearAlgebra.Lagrange` (which imports
`Mathlib.LinearAlgebra.Vandermonde`).

## Main results

* `Lagrange.sum_eval_basis_mul_pow`: $\sum_{i \in s} \ell_i(x)\,v_i^k = x^k$ for $k < \lvert s
  \rvert$.
* `Matrix.of_pow_eq_of_eval_basis_mul_vandermonde`,
  `Matrix.of_pow_mul_inv_vandermonde`: power rows are $\mathbf{L}\mathbf{V}$, and
  times $\mathbf{V}^{-1}$ they are $\mathbf{L}$.
* `Matrix.inv_vandermonde`: the entries of $\mathbf{V}^{-1}$ are the coefficients of the Lagrange
  basis polynomials.
-/

@[expose] public section

open Polynomial Finset

namespace Lagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- **Lagrange interpolation of a monomial**: for nodes $v_i$, $i \in s$, distinct on $s$, with
Lagrange basis polynomials $\ell_i$, every exponent $k < \lvert s \rvert$ and every point $x$,
$$\sum_{i \in s} \ell_i(x)\,v_i^k = x^k\,.$$
It is `Lagrange.eq_interpolate` for $X^k$, evaluated at $x$: the row of powers at $x$ is the
combination of the rows of the Vandermonde matrix with coefficients $\ell_i(x)$. -/
theorem sum_eval_basis_mul_pow {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {k : ℕ}
    (hk : k < #s) (x : F) :
    ∑ i ∈ s, (Lagrange.basis s v i).eval x * v i ^ k = x ^ k := by
  have h := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate (f := (X : F[X]) ^ k) hvs
    (by rw [degree_X_pow]; exact_mod_cast hk))
  simp only [interpolate_apply, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Lagrange

namespace Matrix

variable {F : Type*} [Field F] {t : ℕ}

/-- **Power rows are Lagrange combinations of Vandermonde rows**: for distinct nodes
$v_0, \dots, v_{t-1}$ with Lagrange basis polynomials $\ell_i$ and Vandermonde matrix
$\mathbf{V} = (v_i^j)$, and any points $y_a$,
$$\bigl(y_a^{\,j}\bigr)_{a,\,j < t} = \mathbf{L}\,\mathbf{V}\,,\qquad
\mathbf{L}_{ai} = \ell_i(y_a)\,.$$ -/
theorem of_pow_eq_of_eval_basis_mul_vandermonde {α : Type*} {v : Fin t → F}
    (hv : Function.Injective v) (y : α → F) :
    (Matrix.of fun (a : α) (j : Fin t) => y a ^ (j : ℕ)) =
      (Matrix.of fun (a : α) (i : Fin t) => (Lagrange.basis Finset.univ v i).eval (y a)) *
        vandermonde v := by
  ext a j
  simp only [Matrix.mul_apply, Matrix.of_apply, vandermonde_apply]
  exact (Lagrange.sum_eval_basis_mul_pow hv.injOn
    (by rw [Finset.card_univ, Fintype.card_fin]; exact j.isLt) (y a)).symm

/-- **Power rows times the inverse Vandermonde matrix**: for distinct nodes
$v_0, \dots, v_{t-1}$ with Lagrange basis polynomials $\ell_i$ and Vandermonde matrix
$\mathbf{V} = (v_i^j)$, and any points $y_a$,
$$\bigl(y_a^{\,j}\bigr)_{a,\,j < t}\,\mathbf{V}^{-1} = \mathbf{L}\,,\qquad
\mathbf{L}_{ai} = \ell_i(y_a)\,.$$ -/
theorem of_pow_mul_inv_vandermonde {α : Type*} {v : Fin t → F} (hv : Function.Injective v)
    (y : α → F) :
    (Matrix.of fun (a : α) (j : Fin t) => y a ^ (j : ℕ)) * (vandermonde v)⁻¹ =
      Matrix.of fun (a : α) (i : Fin t) => (Lagrange.basis Finset.univ v i).eval (y a) := by
  rw [of_pow_eq_of_eval_basis_mul_vandermonde hv y, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (det_vandermonde_ne_zero_iff.mpr hv).isUnit, Matrix.mul_one]

/-- **The inverse of a Vandermonde matrix**: for distinct nodes $v_0, \dots, v_{t-1}$ with
Lagrange basis polynomials $\ell_i$, the inverse of $\mathbf{V} = (v_i^j)$ has the coefficients
of $\ell_i$ as its column $i$,
$$\bigl(\mathbf{V}^{-1}\bigr)_{ji} = [X^j]\,\ell_i\,,$$
so $\sum_j \mathbf{c}_j(\mathbf{V}^{-1})_{ji}$ is $\ell_i$ applied to whatever the $\mathbf{c}_j$
are the powers of (a number, a matrix, a matrix times a vector). -/
theorem inv_vandermonde {v : Fin t → F} (hv : Function.Injective v) :
    (vandermonde v)⁻¹ =
      Matrix.of fun (j i : Fin t) => (Lagrange.basis Finset.univ v i).coeff (j : ℕ) := by
  refine Matrix.inv_eq_right_inv ?_
  ext k i
  simp only [Matrix.mul_apply, Matrix.of_apply, vandermonde_apply]
  have hdeg : (Lagrange.basis Finset.univ v i).natDegree < t := by
    rw [Lagrange.natDegree_basis hv.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := i.isLt
    omega
  have h := Polynomial.eval_eq_sum_range' hdeg (v k)
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => (Lagrange.basis Finset.univ v i).coeff j * v k ^ j)] at h
  have hsum : ∑ j : Fin t, v k ^ (j : ℕ) * (Lagrange.basis Finset.univ v i).coeff (j : ℕ) =
      (Lagrange.basis Finset.univ v i).eval (v k) := by
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hsum, Matrix.one_apply]
  split_ifs with hki
  · rw [hki]
    exact Lagrange.eval_basis_self hv.injOn (Finset.mem_univ i)
  · exact Lagrange.eval_basis_of_ne (fun h => hki h.symm) (Finset.mem_univ k)

end Matrix
