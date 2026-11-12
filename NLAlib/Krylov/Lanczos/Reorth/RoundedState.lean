/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedAdvance
public import NLAlib.Krylov.Lanczos.Reorth.State
public import NLAlib.Krylov.Lanczos.RoundedInitialization

/-!
# Actual histories and packed state of rounded reorthogonalized Lanczos

Every executed round retains the actual local update, two-pass and normalization witnesses.
This unconditional history does not assume the stronger orthogonality and admissibility
properties of a `LanczosReorthRun`. Physical zero tails remain output storage, not extra rounds.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Local`: one actual rounded numerical transition.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.History`: the complete executed transition history.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Packed.advance`: preserved packed output archive.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K : Type} [Inhabited K]

/-- A rounded reorthogonalized transition exposes its actual word witnesses. The basis
columns used by the two passes decode to the same archived vectors as the recurrence. -/
def Local (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (em u : ℝ) (e : Blas1Err) (done : ℕ) (z : Lanczos.Rounded.Values n)
    (q : Fin n → ℝ) (a b nu : ℝ) : Prop :=
  ∃ ps qs basis first raw reduced ys : List K, ∃ beta alpha norm beta' : K,
    decv dec n ps = z.v done ∧ decv dec n qs = z.v (done + 1) ∧ dec beta = z.beta done ∧
    (∀ j < done + 1, (fun i : Fin n => dec (vec basis (j * n + i))) = z.v (j + 1)) ∧
    q = decv dec n ys ∧ a = dec alpha ∧ b = dec beta' ∧ nu = dec norm ∧
    Lanczos.Rounded.UpdateBounds em (e.dot n) e.axpy A (decv dec n ps) (decv dec n qs)
      (decv dec n first) (decv dec n raw) (dec beta) (dec alpha) ∧
    IsNrm2Err dec (e.dot n) u n (vec raw) norm ∧
    TwoPassOut dec (e.dot n) e.axpy n (done + 1) basis raw reduced ∧
    IsNrm2Err dec (e.dot n) u n (vec reduced) beta' ∧
    IsScalErr dec e.scal n beta' (vec reduced) (vec ys) ∧
    (decv dec n reduced = 0 → decv dec n ys = 0)

/-- The initialized numerical output followed by the actual executed rounded transitions.
The saved norm sequence uses index one for the first round. -/
inductive History (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rhs : Fin n → ℝ) (em u E : ℝ) (e : Blas1Err) :
    ℕ → Lanczos.Rounded.Values n → (ℕ → ℝ) → Prop
  /-- The actual rounded initialization starts the history. -/
  | initial {z : Lanczos.Rounded.Values n} (h : Lanczos.Rounded.Outcome A rhs E 0 z) :
      History dec A rhs em u E e 0 z 0
  /-- One actual rounded transition extends the history and saved norms. -/
  | next {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
      {q : Fin n → ℝ} {a b nu : ℝ}
      (h : History dec A rhs em u E e done z nus)
      (active : (if done = 0 then z.initialNorm else z.beta done) ≠ 0)
      (step : Local dec A em u e done z q a b nu) :
      History dec A rhs em u E e (done + 1) (z.next done q a b)
        (Function.update nus (done + 1) nu)

/-- The ordinary packed archive plus every raw-norm suffix entry, including initialized tails. -/
structure Packed (dec : K → ℝ) {n : ℕ} (cap done : ℕ) (V C : ℕ × ℕ)
    (z : Lanczos.Rounded.Values n) (nus : ℕ → ℝ) (s : Store K) : Prop
    extends Lanczos.Rounded.Packed dec cap done V C z s where
  /-- Actual or initialized saved raw norm at every requested round. -/
  nu : ∀ j < cap, StoresCell dec (C.1, C.2 + 2 * cap + 2 + j)
    (if j < done then nus (j + 1) else 0) s

/-- The history and the complete physical archive, including zero-valued future ghost entries. -/
structure Prefix (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (em u E : ℝ) (e : Blas1Err) (cap done : ℕ) (V C : ℕ × ℕ)
    (z : Lanczos.Rounded.Values n) (nus : ℕ → ℝ) (s : Store K) : Prop where
  /-- Executed transitions from the actual initialization. -/
  history : History dec A rhs em u E e done z nus
  /-- Actual initialized output cells. -/
  packed : Packed dec cap done V C z nus s
  /-- Future basis values are zero. -/
  future_v : ∀ j, done + 1 < j → z.v j = 0
  /-- Future ordinary coefficients are zero. -/
  future_coeff : ∀ j, done < j → z.alpha j = 0 ∧ z.beta j = 0

/-- The rounded reorthogonalized prefix with previous-vector scratch and its actual guard. -/
structure State (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (em u E : ℝ) (e : Blas1Err) (cap done : ℕ) (V C : ℕ × ℕ) (L : ℕ)
    (z : Lanczos.Rounded.Values n) (nus : ℕ → ℝ) (s : Store K) : Prop
    extends Prefix dec A rhs em u E e cap done V C z nus s where
  /-- Actual previous direction. -/
  prev : StoresVec dec (L, 0) (z.v done) s
  /-- Actual self-dot controls continuation. -/
  guard : ∃ sigma, s.get (L + 2) 0 = some sigma ∧ 0 ≤ dec sigma ∧
    (0 < dec sigma ↔ (if done = 0 then z.initialNorm else z.beta done) ≠ 0)

/-- One complete rounded round changes only the next archived entries and its scratch. -/
theorem Packed.advance {dec : K → ℝ} {n cap done L : ℕ} {V C : ℕ × ℕ}
    {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ} {s s' : Store K}
    (h : Packed dec cap done V C z nus s) (hd : done < cap)
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hf : s.EqOff (Reorth.advanceFp n cap done L V C) s')
    {q : Fin n → ℝ} {a b nu : ℝ}
    (hq : StoresVec dec (V.1, V.2 + (done + 1) * n) q s')
    (ha : StoresCell dec (C.1, C.2 + done) a s')
    (hb : StoresCell dec (C.1, C.2 + cap + done + 1) b s')
    (hn : StoresCell dec (C.1, C.2 + 2 * cap + 2 + done) nu s') :
    Packed dec cap (done + 1) V C (z.next done q a b)
      (Function.update nus (done + 1) nu) s' := by
  refine ⟨h.toPacked.advance_of_disjoint hd hf
    (fun _ he => Reorth.advanceFp_disj_basis hvc hv he)
    (fun _ hi ha hb => Reorth.advanceFp_disj_coeff hvc hc hi ha hb) hq ha hb, ?_⟩
  intro j hj
  by_cases he : j = done
  · subst j
    simpa only [Nat.lt_succ_self, ↓reduceIte, Function.update_self] using hn
  · have hjd : (j < done + 1) = (j < done) := propext (by omega)
    simpa only [hjd, Function.update_of_ne (show j + 1 ≠ done + 1 by omega)] using
      (h.nu j hj).keep hf (Reorth.advanceFp_disj_nu hvc hc hd he)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
