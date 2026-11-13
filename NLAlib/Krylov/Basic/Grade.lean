/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Krylov.Basic.Space
public import NLAlib.Matrix.Basic.OrthonormalBasis

/-!
# The grade of a vector

The grade $\nu$ of $\mathbf{b}$ with respect to $\mathbf{A}$ is the dimension of the largest
Krylov space. The Krylov spaces grow by one dimension per step up to $q = \nu$ and are constant,
and invariant under $\mathbf{A}$, from there on. It is the one breakdown vocabulary of the Krylov
layer: Lanczos and conjugate gradients break down, or terminate, exactly at the grade.

## Main definitions

* `NLAlib.krylovGrade`: the rank of the Krylov matrix with $\lvert n \rvert$ columns.

## Main results

* `NLAlib.rank_krylovMatrix`, `NLAlib.finrank_krylovSpace`: the dimension is $\min(q, \nu)$.
* `NLAlib.exists_hasOrthonormalCols_range_eq_krylovSpace`: an orthonormal basis of
  $\mathcal{K}_q$.
* `NLAlib.krylovMatrix_mulVec_injective_iff`: the Krylov vectors are independent iff $q \le \nu$.
* `NLAlib.aeval_mulVec_ne_zero_of_degree_lt_krylovGrade`: no nonzero real polynomial of degree
  below the grade annihilates $\mathbf{b}$.
* `NLAlib.krylovGrade_le_iff`: $\nu \le q$ iff $\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$.
* `NLAlib.mulVec_mem_krylovSpace_of_krylovGrade_le`: invariance from the grade on.
* `NLAlib.mem_krylovSpace_of_krylovGrade_le`: the solution of $\mathbf{A}\mathbf{x} = \mathbf{b}$
  lies in the Krylov space of the grade.
* `NLAlib.krylovGrade_le_of_mem_of_mulVec_eq`: $\nu \le k$ when $\mathbf{b} = \mathbf{A}\mathbf{y}$
  with $\mathbf{y} \in \mathcal{K}_k$.
* `NLAlib.krylovGrade_mul_mulVec`: invariance under an invertible change of variables, so that a
  preconditioned recurrence breaks down at the grade of its split system.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **grade** $\nu$ of $\mathbf{b}$ with respect to $\mathbf{A}$: the dimension of the largest
Krylov space, the rank of $\mathbf{K}_{\lvert n \rvert}(\mathbf{A}, \mathbf{b})$. The Krylov
spaces grow strictly up to $q = \nu$ and are constant from there on. $\nu = 0$ exactly when
$\mathbf{b} = \mathbf{0}$. [Saad2003, §6.2]. -/
noncomputable def krylovGrade (A : Matrix n n 𝕜) (b : n → 𝕜) : ℕ :=
  (krylovMatrix A b (Fintype.card n)).rank

/-! ### The first index at which the Krylov spaces stop growing -/

section Index

variable {A : Matrix n n 𝕜} {b : n → 𝕜}

/-- Linear independence of $\mathbf{b}, \dots, \mathbf{A}^q\mathbf{b}$ splits off the last
vector. -/
private lemma linearIndependent_pow_mulVec_succ_iff (q : ℕ) :
    LinearIndependent 𝕜 (fun i : Fin (q + 1) => A ^ (i : ℕ) *ᵥ b) ↔
      LinearIndependent 𝕜 (fun i : Fin q => A ^ (i : ℕ) *ᵥ b) ∧
        A ^ q *ᵥ b ∉ krylovSpace A b q := by
  have h : (fun i : Fin (q + 1) => A ^ (i : ℕ) *ᵥ b) =
      Fin.snoc (fun i : Fin q => A ^ (i : ℕ) *ᵥ b) (A ^ q *ᵥ b) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h, linearIndependent_finSnoc, krylovSpace_eq_span]

private lemma linearIndependent_pow_mulVec_of_forall_notMem {q : ℕ}
    (h : ∀ i < q, A ^ i *ᵥ b ∉ krylovSpace A b i) :
    LinearIndependent 𝕜 (fun i : Fin q => A ^ (i : ℕ) *ᵥ b) := by
  induction q with
  | zero => exact linearIndependent_empty_type
  | succ q ih =>
    exact (linearIndependent_pow_mulVec_succ_iff q).2
      ⟨ih fun i hi => h i (Nat.lt_succ_of_lt hi), h q (Nat.lt_succ_self q)⟩

/-- Once $\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$, the space $\mathcal{K}_q$ is invariant. -/
private lemma mulVec_mem_of_pow_mulVec_mem {q : ℕ} (hq : A ^ q *ᵥ b ∈ krylovSpace A b q)
    {x : n → 𝕜} (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b q := by
  have h := mulVec_mem_krylovSpace_succ hx
  rw [krylovSpace_succ] at h
  exact (sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).2 hq)) h

private lemma pow_mulVec_mem_of_pow_mulVec_mem {q : ℕ} (hq : A ^ q *ᵥ b ∈ krylovSpace A b q)
    (i : ℕ) : A ^ i *ᵥ b ∈ krylovSpace A b q := by
  have hb : b ∈ krylovSpace A b q := by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simpa using hq
    · exact self_mem_krylovSpace A b hpos
  exact krylovSpace_le_of_invariant hb (fun _ hx => mulVec_mem_of_pow_mulVec_mem hq hx)
    (i + 1) (pow_mulVec_mem_krylovSpace A b (Nat.lt_succ_self i))

private lemma krylovSpace_eq_of_pow_mulVec_mem {q q' : ℕ}
    (hq : A ^ q *ᵥ b ∈ krylovSpace A b q) (h : q ≤ q') :
    krylovSpace A b q' = krylovSpace A b q := by
  refine le_antisymm ?_ (krylovSpace_mono A b h)
  rw [krylovSpace_eq_span A b q']
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact pow_mulVec_mem_of_pow_mulVec_mem hq j

/-- The first index $m$ with $\mathbf{A}^m\mathbf{b} \in \mathcal{K}_m$ exists. -/
private lemma exists_index :
    ∃ m, (∀ i < m, A ^ i *ᵥ b ∉ krylovSpace A b i) ∧ A ^ m *ᵥ b ∈ krylovSpace A b m := by
  classical
  have hex : ∃ q, A ^ q *ᵥ b ∈ krylovSpace A b q := by
    by_contra hne
    push Not at hne
    have hli := linearIndependent_pow_mulVec_of_forall_notMem
      (A := A) (b := b) (q := Fintype.card n + 1) fun i _ => hne i
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  exact ⟨Nat.find hex, fun i hi => Nat.find_min hex hi, Nat.find_spec hex⟩

private lemma index_le_card {m : ℕ} (hm : ∀ i < m, A ^ i *ᵥ b ∉ krylovSpace A b i) :
    m ≤ Fintype.card n := by
  have := (linearIndependent_pow_mulVec_of_forall_notMem hm).fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this

private lemma finrank_krylovSpace_of_le {m q : ℕ}
    (hm : ∀ i < m, A ^ i *ᵥ b ∉ krylovSpace A b i) (hq : q ≤ m) :
    Module.finrank 𝕜 (krylovSpace A b q) = q := by
  rw [krylovSpace_eq_span, finrank_span_eq_card
    (linearIndependent_pow_mulVec_of_forall_notMem fun i hi => hm i (hi.trans_le hq)),
    Fintype.card_fin]

private lemma finrank_krylovSpace_eq_min {m : ℕ} (hm : ∀ i < m, A ^ i *ᵥ b ∉ krylovSpace A b i)
    (hm' : A ^ m *ᵥ b ∈ krylovSpace A b m) (q : ℕ) :
    Module.finrank 𝕜 (krylovSpace A b q) = min q m := by
  rcases le_total q m with h | h
  · rw [finrank_krylovSpace_of_le hm h, min_eq_left h]
  · rw [krylovSpace_eq_of_pow_mulVec_mem hm' h, finrank_krylovSpace_of_le hm le_rfl,
      min_eq_right h]

private lemma krylovGrade_eq_index {m : ℕ} (hm : ∀ i < m, A ^ i *ᵥ b ∉ krylovSpace A b i)
    (hm' : A ^ m *ᵥ b ∈ krylovSpace A b m) : krylovGrade A b = m := by
  change Module.finrank 𝕜 (krylovSpace A b (Fintype.card n)) = m
  rw [finrank_krylovSpace_eq_min hm hm', min_eq_right (index_le_card hm)]

end Index

/-- **The Krylov spaces stop growing exactly at the grade**: $\nu \le q$ iff
$\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$. [Saad2003, §6.2]. -/
theorem krylovGrade_le_iff {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} :
    krylovGrade A b ≤ q ↔ A ^ q *ᵥ b ∈ krylovSpace A b q := by
  obtain ⟨m, hm, hm'⟩ := exists_index (A := A) (b := b)
  rw [krylovGrade_eq_index hm hm']
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact krylovSpace_mono A b h (pow_mulVec_mem_of_pow_mulVec_mem hm' q)
  · by_contra hlt
    exact hm q (not_le.1 hlt) h

/-- **The dimension of a Krylov space**: $\dim\mathcal{K}_q(\mathbf{A}, \mathbf{b}) = \min(q, \nu)$,
$\nu$ the grade of $\mathbf{b}$ for $\mathbf{A}$. [Saad2003, Proposition 6.2]; it is (6.4) there.
Result: krylov-space-dimension -/
theorem finrank_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Module.finrank 𝕜 (krylovSpace A b q) = min q (krylovGrade A b) := by
  obtain ⟨m, hm, hm'⟩ := exists_index (A := A) (b := b)
  rw [krylovGrade_eq_index hm hm', finrank_krylovSpace_eq_min hm hm']

/-- The rank of the Krylov matrix is $\min(q, \nu)$. -/
theorem rank_krylovMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (krylovMatrix A b q).rank = min q (krylovGrade A b) :=
  finrank_krylovSpace A b q

/-- An orthonormal basis of the Krylov space: there are $k$ and a $\mathbf{Q}$ with $k$
orthonormal columns whose column space is $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$; necessarily
$k = \min(q, \nu)$, $\nu$ the grade (`finrank_krylovSpace`). It supplies the frame that the
statements about any orthonormal basis of a Krylov space (Lanczos-FA, compressions) are applied
to; the number of columns is left existential so that rewriting $\mathbf{b}$ or $q$ does not
change the type of $\mathbf{Q}$. -/
theorem exists_hasOrthonormalCols_range_eq_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    ∃ (k : ℕ) (Q : Matrix n (Fin k) 𝕜), HasOrthonormalCols Q ∧
      LinearMap.range Q.mulVecLin = krylovSpace A b q :=
  ⟨_, exists_hasOrthonormalCols_range_eq _ (Fintype.card_fin _)⟩

/-- The grade is at most the dimension. -/
theorem krylovGrade_le_card (A : Matrix n n 𝕜) (b : n → 𝕜) :
    krylovGrade A b ≤ Fintype.card n := by
  obtain ⟨m, hm, hm'⟩ := exists_index (A := A) (b := b)
  rw [krylovGrade_eq_index hm hm']
  exact index_le_card hm

/-- The Krylov vectors $\mathbf{b}, \dots, \mathbf{A}^{q-1}\mathbf{b}$ are linearly independent
exactly up to the grade: the Krylov matrix has full column rank iff $q \le \nu$. -/
theorem krylovMatrix_mulVec_injective_iff {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} :
    Function.Injective (krylovMatrix A b q).mulVec ↔ q ≤ krylovGrade A b := by
  obtain ⟨m, hm, hm'⟩ := exists_index (A := A) (b := b)
  rw [krylovGrade_eq_index hm hm', Matrix.mulVec_injective_iff]
  change LinearIndependent 𝕜 (fun i : Fin q => A ^ (i : ℕ) *ᵥ b) ↔ q ≤ m
  refine ⟨fun hli => ?_, fun hq => ?_⟩
  · have h := finrank_krylovSpace_eq_min hm hm' q
    rw [krylovSpace_eq_span, finrank_span_eq_card hli, Fintype.card_fin] at h
    omega
  · exact linearIndependent_pow_mulVec_of_forall_notMem fun i hi => hm i (hi.trans_le hq)

/-- From the grade on, the Krylov spaces are constant. -/
theorem krylovSpace_eq_of_krylovGrade_le {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (h : krylovGrade A b ≤ q) : krylovSpace A b q = krylovSpace A b (krylovGrade A b) :=
  krylovSpace_eq_of_pow_mulVec_mem (krylovGrade_le_iff.1 le_rfl) h

/-- From the grade on, the Krylov space is invariant under $\mathbf{A}$. -/
theorem mulVec_mem_krylovSpace_of_krylovGrade_le {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ}
    (h : krylovGrade A b ≤ q) (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b q :=
  mulVec_mem_of_pow_mulVec_mem (krylovGrade_le_iff.1 h) hx

/-- **The solution lies in the Krylov space of the grade**: for invertible $\mathbf{A}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star \in \mathcal{K}_q$ once $\nu \le q$.
[Saad2003, §6.2]. -/
theorem mem_krylovSpace_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : IsUnit A) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) {q : ℕ} (h : krylovGrade A b ≤ q) : xs ∈ krylovSpace A b q := by
  set K := krylovSpace A b q
  have hbK : b ∈ K := by
    simpa using pow_mulVec_mem_of_pow_mulVec_mem (krylovGrade_le_iff.1 h) 0
  let f : K →ₗ[𝕜] K := A.mulVecLin.restrict fun x hx =>
    mulVec_mem_krylovSpace_of_krylovGrade_le h hx
  have hinjA : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hA
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (hinjA (congrArg Subtype.val hxy))
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨b, hbK⟩
  have hy' : A *ᵥ (y : n → 𝕜) = A *ᵥ xs := by
    rw [hxs]
    exact congrArg Subtype.val hy
  rw [← hinjA hy']
  exact y.2

/-- The grade of a vector in $\mathbf{A}\mathcal{K}_k$: if $\mathbf{c} = \mathbf{A}\mathbf{y}$
with $\mathbf{y} \in \mathcal{K}_k(\mathbf{A}, \mathbf{c})$, then the grade $\nu$ of
$\mathbf{c}$ is at most $k$, for every $\mathbf{A}$: then
$\mathcal{K}_{k+1} \subseteq \mathbf{A}\mathcal{K}_k$ has dimension at most that of
$\mathcal{K}_k$. It is the converse of `NLAlib.mem_krylovSpace_of_krylovGrade_le`, without
invertibility; conjugate gradients use it to stop at the grade. -/
theorem krylovGrade_le_of_mem_of_mulVec_eq {A : Matrix n n 𝕜} {c y : n → 𝕜} {k : ℕ}
    (hy : y ∈ krylovSpace A c k) (hAy : A *ᵥ y = c) : krylovGrade A c ≤ k := by
  have hle : krylovSpace A c (k + 1) ≤ (krylovSpace A c k).map A.mulVecLin := by
    rw [krylovSpace_eq_span A c (k + 1)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    rcases j with _ | i
    · exact ⟨y, hy, by simp [hAy]⟩
    · refine ⟨A ^ i *ᵥ c, pow_mulVec_mem_krylovSpace A c (by omega), ?_⟩
      simp [Matrix.mulVec_mulVec, pow_succ']
  have h := (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le A.mulVecLin _)
  rw [finrank_krylovSpace, finrank_krylovSpace] at h
  omega

/-- The grade under a change of variables: for invertible $\mathbf{C}$, the grade of
$\mathbf{C}\mathbf{v}$ for $\mathbf{C}\mathbf{B}$ is that of $\mathbf{v}$ for
$\mathbf{B}\mathbf{C}$. The preconditioned recurrences break down at the grade of the split
system. -/
theorem krylovGrade_mul_mulVec {C : Matrix n n 𝕜} (hC : IsUnit C) (B : Matrix n n 𝕜)
    (v : n → 𝕜) : krylovGrade (C * B) (C *ᵥ v) = krylovGrade (B * C) v := by
  rw [krylovGrade, krylovGrade, krylovMatrix_mul_mulVec,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det C).mp hC)]

open Polynomial in
/-- A nonzero real polynomial of degree below the grade does not annihilate $\mathbf{b}$: for
every square $\mathbf{A}$ and every nonzero real polynomial $p$ with $\deg p < \nu$, $\nu$ the
grade of $\mathbf{b}$, $p(\mathbf{A})\mathbf{b} \ne \mathbf{0}$, since the Krylov vectors
$\mathbf{b}, \dots, \mathbf{A}^{\nu - 1}\mathbf{b}$ are linearly independent. -/
theorem aeval_mulVec_ne_zero_of_degree_lt_krylovGrade {A : Matrix n n 𝕜} {b : n → 𝕜}
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.degree < krylovGrade A b) : aeval A p *ᵥ b ≠ 0 := by
  have hm : p.natDegree + 1 ≤ krylovGrade A b := by
    have := (natDegree_lt_iff_degree_lt hp0).2 hp
    omega
  have hli : LinearIndependent 𝕜 (fun i : Fin (p.natDegree + 1) => A ^ (i : ℕ) *ᵥ b) := by
    have h := krylovMatrix_mulVec_injective_iff.mpr hm
    rw [Matrix.mulVec_injective_iff] at h
    exact h
  intro h0
  have hsum : ∑ i : Fin (p.natDegree + 1),
      (algebraMap ℝ 𝕜 (p.coeff i)) • (A ^ (i : ℕ) *ᵥ b) = 0 := by
    rw [← h0, aeval_eq_sum_range, Matrix.sum_mulVec,
      ← Fin.sum_univ_eq_sum_range (fun i => (p.coeff i • A ^ i) *ᵥ b)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_smul, Matrix.smul_mulVec]
  have h := Fintype.linearIndependent_iff.mp hli _ hsum ⟨p.natDegree, by omega⟩
  rw [map_eq_zero_iff _ (algebraMap ℝ 𝕜).injective, coeff_natDegree, leadingCoeff_eq_zero] at h
  exact hp0 h

end NLAlib
